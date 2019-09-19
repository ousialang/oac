use serde_json::Value as JsonValue;

#[derive(Serialize, Deserialize)]
struct Event {
    any: JsonValue,
}
