use self::clap::{App, AppSettings};


const APP: App = App::new("oa")
    .setting(AppSettings::AllowExternalSubcommands)
    .setting(AppSettings::StrictUtf8)
    .setting(AppSettings::VersionlessSubcommands)
    .setting(AppSettings::DisableHelpSubcommand)
    .setting(AppSettings::DisableVersion);
