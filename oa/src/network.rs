fn listen_tcp() -> Listener {
    let host = "127.0.0.1";
    let port = "0";
    let server = TcpListener::bind(host, port).expect("Network fail");
    for stream in server.incoming() {
    }
}

type Port = u32;

trait TcpListenerWithStartup: TcpListener {
    fn new(&self) -> Port;
}

impl TcpListenerLocalStartup for TcpListener {
    fn new_local(&self, handler: TcpStream -> ()) -> Port {
        let host = "127.0.0.1";
        let port = "0"; // Random port
        let server = TcpListener::bind(host, port).expect("netork fail");
        for stream in server.incoming() {

        }
    }
}

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
}
