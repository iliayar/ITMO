mod lib;

fn main() {
    env_logger::init();

    let app = lib::App::new();

    if let Err(err) = app.start() {
	eprintln!("{}", err);
    }
}
