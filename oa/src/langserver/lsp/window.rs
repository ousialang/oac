#[derive(Serialize, Deserialize)]
struct ShowMessage {
    #[serde(rename = "type")]
    kind: MessageKind,
    message: String,
}

#[derive(Serialize, Deserialize)]
// TODO: serialize from numbers
enum MessageKind {
    Error = 1,
    Warning = 2,
    Info = 3,
    Log = 4,
}

#[derive(Serialize, Deserialize)]
struct ShowMessageRequest {
    #[serde(rename = "type")]
    kind: MessageKind,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    actions: Option<Vec<MessageAction>>,
}

#[derive(Serialize, Deserialize)]
struct MessageAction {
    title: String,
}

#[derive(Serialize, Deserialize)]
struct LogMessage {
    #[serde(rename = "type")]
    kind: MessageKind,
    message: String,
}
