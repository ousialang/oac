#include "feedback.hpp"
#include "help.hpp"
#include "repl.hpp"
#include "version.hpp"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include "fbs_commands.hpp"

std::string main_ousia_dir() {
#ifdef PLATFORM_IS_MAC
	return "/Library/ousia/";
#else
	return NULL;
#endif
}

int main(int argc, char* argv[]) {
	if (argc == 1) { return print_usage(); }
	static const std::map<char*,void*> commands_entry_points = {
		{"build", *commands::build::main},
		{"help", *commands::help::main},
		{"version", *commands::version::main}
	}
	try {
		void* command_entry_point = commands_entry_points.at(argc[0]);
	} catch (std::out_of_range& const e) {
		return run_foreign_command(argc, argv);
	}
	return (&command_entry_point)(argc, argv);
}

int run_foreign_command(int argc, char* argv[]) {
	char* file_name = resource_name_to_file_name("plugins/" + argv[0]).c_str();
	if (FILE* file = fopen(file_name, "rb")) {
		fclose(file);
		return run_plugin(file, argc, argv);
	} else {
		return suggest_spelling_correction(argv[0]);
	}
}

int run_plugin(file_name, argc, argv) {
	exec(file_name, argc, argv);
}

int suggest_spelling_correction(std::string term) {
	auto commands = available_commands->commands();
	std::cout << "Unknown command: " << term << std::endl
	          << "Did you mean "
}

Commands* available_commands() {
	std::ifstream fbs(resource_name_to_file_name("fbs/commands"), std::ifstream::binary);
	if (!fbs_is_open()) { return NULL; }
	std::filebuf* fbs_buf = fbs.rdbuf();
	std::size_t fbs_size = fbs_buf->pubseekoff (0, fbs.end, fbs.in);
	fbs_buf->pubseekpos(0, fbs.in);
	uint8_t* fbs_data = new char[fbs_size];
	fbs_buf->sgetn(fbs_data, fbs_size);
	fbs_close();
	return GetCommands(fbs_data);
}

int print_usage() {
	Commands* commands = available_commands();
	if (!commands) { return EX_UNAVAILABLE; }
	std::cout << "Usage: ousia <command> [options] [<arguments>]" << std::endl << std::endl
			  << "The available commands are:" << std::endl;
	for (auto cmd : commands->commands()) {
		std::cout << "  * " << cmd->name->str() << std::endln << "    "
		          << cmd->short_description()->str();
	}
	std::cout << "Type \"ousia help <command>\" for more information about a command.";
	return EX_OK;
}
