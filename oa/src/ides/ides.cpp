#include <ctime>
#include <iostream>
#include <string>
#include <sysexits.h>
#include <boost/asio.hpp>

using boost::asio::ip::tcp;

int main() {
	try {
		boost::asio::io_service io_service;
		tcp::acceptor acceptor(io_service, tcp::endpoint(tcp::v4(), 0));
		while (1) {
			tcp::socket socket(io_service);
			acceptor.accept(socket);
			std::string message = "wabba lubba dub dub";
			boost::system::error_code ignored_error;
			boost::asio::write(socket, boost::asio::buffer(message),
							   boost::asio::transfer_all(), ignored_error);
		}
	} catch (std::exception &e) {
		std::cerr << e.what() << std::endl;
	}
	return EX_OK;
}
