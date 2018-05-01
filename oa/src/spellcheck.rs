use fst::{IntoStreamer, Set as FstSet, SetBuilder, Streamer};
use fst_levenshtein::Levenshtein;

pub fn spellcheck_subcommand(subcmd_name: String) -> Result<Vec<String>, Error> {
    let max_distance = subcmd_name.chars().len().log2();
    let subcmd_names = subcommands().map(|s| s.name)?;
    let dictionary = FstSet::from_iter(subcmd_names)?;
    let automaton = Levenshtein::new(subcmd_name, max_distance)?;
    dictionary.search(automaton).into_stream().into_str_vec()?
}
