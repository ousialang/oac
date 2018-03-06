/*using namespace boost::network;
using namespace boost::network::http;

struct handler;
typedef http::server<handler> http_server;

struct handler {
    void operator() (http_server::request const &request,
                     http_server::response &response) {
        response = http_server::response::stock_reply(
            http_server::response::ok, "Hello, world!");
    }
};

int main(int arg, char* argv[]) {
    handler handler;
    http_server::options options(handler);
    http_server server_(
        options.address("0.0.0.0").port("0"));
    server_.run();
}*/
