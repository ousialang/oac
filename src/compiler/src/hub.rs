use clap::ArgMatches;
use hlua::Lua;
use rayon::{ThreadPool, ThreadPoolBuilder};
use rusqlite;

use std::env::current_dir;
use std::fs::File;
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};

use cache::Cache;
use feedback::{Feedback, Logger, View};
use usage;

pub struct Hub<V: View> {
    lua: Lua<'static>,
    thread_pool: ThreadPool,
    target: PathBuf,
    cache: Option<Cache>,
    view: V,
}

impl<V> Hub<V>
where
    V: View
{
    pub fn from_args(args: &ArgMatches, view: V) -> Hub<V> {
        Hub {
            lua: Lua::new(),
            thread_pool: ThreadPoolBuilder::new().build().unwrap(),
            target: PathBuf::new(), /*args.value_of(usage::TARGET)
                .map(|s| PathBuf::from(s))
                .or_else(|| {
                    current_dir()
                        .map(|mut p| {
                            p.push("target");
                            p
                        })
                        .ok()
                })*/
            cache: Cache::load("").ok(),
            view: view,
        }
    }
}
