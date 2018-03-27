use constants::SUBCOMMANDS_FST;
use utils::feedback::Level;
use utils::resources::Resource;

use fst::{IntoStreamer, Streamer, Set, SetBuilder};
use fst_levenshtein::Levenshtein;


struct SubcommandSpellchecker {
    query: &str,
    levenshtein_fst: Levenshtein,
    dictionary: fst::Set,
}

impl SubcommandSpellchecker {
    fn new(query: &str) -> Option<Spellchecker> {
        let max_distance = query.len().log2().floor();
        let dictionary_path = resource_path(SUBCOMMANDS_FST);
        let dictionary = fst::Set::from_path(dictionary_path);
        match Levenshtein::new(query, max_distance) {
            Ok(fst) => Spellchecker {
                query: query,
                levenshtein_fst: fst,
                dictionary: dictionary,
            },
            Err(_) => None,
        }
    }

    fn suggestions(&self) -> Vec<&str> {
        self.dictionary
            .search(self.levenshtein_fst)
            .into_stream()
            .into_str_vec()?;
    }
}
