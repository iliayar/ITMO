use clap;

#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[arg(long)]
    pub file: String,

    #[arg(long)]
    pub numbilets: usize,

    #[arg(long)]
    pub parameter: u64,
}
