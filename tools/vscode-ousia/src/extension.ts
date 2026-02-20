import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  Trace,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  await startClient();

  context.subscriptions.push(
    vscode.commands.registerCommand("ousia.restartLanguageServer", async () => {
      await restartClient(true);
    })
  );

  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(async (event) => {
      if (
        event.affectsConfiguration("ousia.server.path") ||
        event.affectsConfiguration("ousia.server.args")
      ) {
        await restartClient(false);
      }

      if (event.affectsConfiguration("ousia.trace.server")) {
        await applyTraceSetting();
      }
    })
  );
}

async function startClient(): Promise<boolean> {
  const config = vscode.workspace.getConfiguration("ousia");
  const serverPath = config.get<string>("server.path", "oac");
  const serverArgs = config.get<string[]>("server.args", []);
  const sanitizedServerArgs = serverArgs.filter((arg) => arg !== "--stdio");

  const workspaceFolder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;

  const serverOptions: ServerOptions = {
    command: serverPath,
    args: [...sanitizedServerArgs, "lsp"],
    options: workspaceFolder ? { cwd: workspaceFolder } : undefined,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ language: "ousia", scheme: "file" }],
    outputChannelName: "Ousia Language Server",
  };

  const nextClient = new LanguageClient(
    "ousiaLanguageServer",
    "Ousia Language Server",
    serverOptions,
    clientOptions
  );

  try {
    await nextClient.start();
    client = nextClient;
    await applyTraceSetting(nextClient);
    return true;
  } catch (error) {
    client = undefined;
    const message = error instanceof Error ? error.message : String(error);
    void vscode.window.showErrorMessage(
      `Unable to start Ousia language server with command \`${serverPath} lsp\`: ${message}`
    );
    return false;
  }
}

async function restartClient(notifyUser: boolean): Promise<void> {
  await stopClient();
  const started = await startClient();
  if (notifyUser && started) {
    void vscode.window.showInformationMessage("Ousia language server restarted.");
  }
}

async function applyTraceSetting(
  targetClient: LanguageClient | undefined = client
): Promise<void> {
  if (!targetClient) {
    return;
  }

  const traceSetting = vscode
    .workspace
    .getConfiguration("ousia")
    .get<string>("trace.server", "off");

  switch (traceSetting) {
    case "messages":
      await targetClient.setTrace(Trace.Messages);
      break;
    case "verbose":
      await targetClient.setTrace(Trace.Verbose);
      break;
    default:
      await targetClient.setTrace(Trace.Off);
      break;
  }
}

async function stopClient(): Promise<void> {
  if (!client) {
    return;
  }

  const currentClient = client;
  client = undefined;
  await currentClient.stop();
}

export async function deactivate(): Promise<void> {
  await stopClient();
}
