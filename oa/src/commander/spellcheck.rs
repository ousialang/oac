extern crate fst;
extern crate fst_levenshtein;

//use subcommands::fuck::{add_task, Spellcorrect};
use self::fst_levenshtein::Levenshtein;
use std::env::Args;
use utils::io::FATAL;
use utils::resources::resource_path;

pub fn spellcheck(args: Args) -> ! {
    let query = args[0];
    let levenshtein_distance = query.len().log2();
    let levenshtein_automaton = Levenshtein::new(query, levenshtein_distance)?;
    let dictionary = fst::Set::from_path(resource_path("commands"));
    let stream = dictionary.search(levenshtein_automaton).into_stream();
    let results = stream.into_str_vec()?;
    println!("{} Did you mean '{}'?",
             FATAL,
             results[0]);
    args[0] = results[0];
    //fuck::add_task(fuck::Spellcorrect(args), None);
}
