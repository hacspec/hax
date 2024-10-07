use tiny_http::{Header, Response, Server};

fn get_server() -> Server {
    let mut port = std::env::var_os("HAX_DEBUGGER_PORT")
        .and_then(|s| s.into_string().ok())
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(8000);
    loop {
        if let Ok(server) = Server::http(format!("0.0.0.0:{}", port)) {
            eprintln!("Hax webapp is available on http://localhost:{:?}", port);
            return server;
        }
        std::thread::sleep(std::time::Duration::from_millis(300));
        eprintln!("Could not listen to port {:?}, trying another", port);
        port += 1;
    }
}

pub fn run(get_json: impl Fn() -> String) {
    let server = get_server();
    let ct_html = Header::from_bytes(&b"Content-Type"[..], &b"text/html"[..]).unwrap();
    let ct_js = Header::from_bytes(&b"Content-Type"[..], &b"text/javascript"[..]).unwrap();
    let ct_utf8 = Header::from_bytes(&b"charset"[..], &b"utf-8"[..]).unwrap();
    for request in server.incoming_requests() {
        let response = match request.url() {
            "/" => Response::from_string(include_str!("static/index.html"))
                .with_header(ct_html.clone())
                .with_header(ct_utf8.clone()),
            "/script.js" => Response::from_string(include_str!("static/script.js"))
                .with_header(ct_js.clone())
                .with_header(ct_utf8.clone()),
            path if path.starts_with("/debug-hax-engine.json") => {
                Response::from_string(get_json()).with_header(ct_utf8.clone())
            }
            _ => Response::from_string("Unknown route".to_string()).with_status_code(404),
        };
        let _ = request.respond(response);
    }
}
