mod lib;
mod app;
pub use lib::*;

use log::*;
use clap::Parser;
use app::App;

fn main() {
    env_logger::init();

    let app = App::parse();
    if let Err(err) = app.run() {
	error!("{}", err);
    }
}
