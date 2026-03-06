#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXTENSION_DIR="$ROOT_DIR/tools/vscode-ousia"

require_command() {
	local command_name="$1"
	if ! command -v "$command_name" >/dev/null 2>&1; then
		printf 'error: missing required command: %s\n' "$command_name" >&2
		exit 1
	fi
}

resolve_code_bin() {
	if [[ -n "${CODE_BIN:-}" ]]; then
		printf '%s\n' "$CODE_BIN"
		return
	fi

	local candidate
	for candidate in code code-insiders; do
		if command -v "$candidate" >/dev/null 2>&1; then
			printf '%s\n' "$candidate"
			return
		fi
	done

	printf '\n'
}

require_command node
require_command npm
require_command npx

CODE_BIN="$(resolve_code_bin)"
if [[ -z "$CODE_BIN" ]]; then
	printf 'error: could not find a VS Code CLI (`code` or `code-insiders`). Set CODE_BIN=/path/to/code.\n' >&2
	exit 1
fi

if [[ "$CODE_BIN" == */* ]]; then
	if [[ ! -x "$CODE_BIN" ]]; then
		printf 'error: CODE_BIN is not executable: %s\n' "$CODE_BIN" >&2
		exit 1
	fi
elif ! command -v "$CODE_BIN" >/dev/null 2>&1; then
	printf 'error: VS Code CLI not found on PATH: %s\n' "$CODE_BIN" >&2
	exit 1
fi

if [[ ! -f "$EXTENSION_DIR/package.json" ]]; then
	printf 'error: expected extension package at %s/package.json\n' "$EXTENSION_DIR" >&2
	exit 1
fi

PACKAGE_NAME="$(node -p "require(process.argv[1]).name" "$EXTENSION_DIR/package.json")"
PACKAGE_VERSION="$(node -p "require(process.argv[1]).version" "$EXTENSION_DIR/package.json")"
VSIX_PATH="$EXTENSION_DIR/${PACKAGE_NAME}-${PACKAGE_VERSION}.vsix"

printf 'Installing extension dependencies in %s\n' "$EXTENSION_DIR"
(
	cd "$EXTENSION_DIR"
	if [[ -f package-lock.json ]]; then
		npm ci
	else
		npm install
	fi
)

printf 'Building VS Code extension\n'
(
	cd "$EXTENSION_DIR"
	npm run build
)

printf 'Packaging VSIX to %s\n' "$VSIX_PATH"
(
	cd "$EXTENSION_DIR"
	rm -f "$VSIX_PATH"
	npx --yes @vscode/vsce package --out "$VSIX_PATH"
)

printf 'Installing VSIX with %s\n' "$CODE_BIN"
"$CODE_BIN" --install-extension "$VSIX_PATH" --force

printf 'Installed %s\n' "$VSIX_PATH"
