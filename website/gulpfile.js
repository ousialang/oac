const gulp = require("gulp");
const sass = require("gulp-ruby-sass");
const run = require("gulp-run-command").default;
const run_sequence = require("run-sequence");
const watch = require("gulp-watch");


const SCSS_FILES = "./assets/scss/**/*.{scss,sass}";


gulp.task("sass:build", function() {
	// The obvious way of doing this would be through gulp-sass, which uses
	// libsass behind the scens. Bulma however is written in .sass syntax and
	// unfortunately libsass only supports .scss syntax. This is also why we
	// can't use gulp-watch-sass's incremental build.
	// See https://stackoverflow.com/a/29722670/5148606 and
	// https://github.com/jgthms/bulma/issues/1502.
	return sass(SCSS_FILES)
		.on("error", sass.logError)
		.pipe(gulp.dest("./static/css/"));
});


gulp.task("sass:watch", ["sass:build"], function() {
	return gulp.watch(SCSS_FILES, ["sass:build"]);
});


gulp.task("flask:serve", run("python3 flask run", {
	env: {
		FLASK_APP: "index.py"
	}
}));


gulp.task("flask:watch", run("python3 -m flask run", {
	env: {
		FLASK_APP: "index.py",
		FLASK_DEBUG: "1"
	}
}));


gulp.task("default", function() {
	run_sequence(["flask:watch", "sass:watch"]);
});
