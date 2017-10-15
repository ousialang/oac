#[derive(Clone, Debug)]
pub struct Feedback {
    pub level: u8, // ERROR, WARNING, NOTE
    pub title: String,
    pub body: String,
}

impl Default for Feedback {
    fn default() -> Feedback {
        Feedback {
            level: 0,
            title: "Unknown issue".to_string(),
            body: "This is a compiler error.".to_string(),
        }
    }
}

fn write_feedbacks(feedbacks: Vec<Feedback>) {
    for fb in feedbacks {
        match fb.level {
            0 => { write_error(fb); }
            1 => { write_error(fb); }
            2 => { write_error(fb); }
            _ => { write_error(fb); }
        }
    }
}

fn write_error(fb: Feedback) {

}
