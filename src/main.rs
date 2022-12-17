mod app;
mod lib;
pub use lib::*;

use app::App;
use clap::Parser;
use log::*;

fn main() {
    env_logger::init();

    let app = App::parse();
    if let Err(err) = app.run() {
        error!("{}", err);
    }
}
