use clap::{Parser, ValueEnum};

use crate::{AdjacentGraph, DrawingApi, EdgesGraph, Graph, ReactiveBackend, SimpleBackend};

#[derive(ValueEnum, Debug, Clone)]
pub enum Format {
    Adjacent,
    EdgesList,
}

#[derive(ValueEnum, Debug, Clone)]
pub enum Backend {
    SDL2,
    Iced,
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct App {
    #[arg(short, long)]
    format: Format,
    #[arg(short, long)]
    backend: Backend,
}

impl App {
    pub fn run(self) -> Result<(), anyhow::Error> {
        let size = (800, 600);
        let mut drawing_api: Box<dyn DrawingApi> = match self.backend {
            Backend::SDL2 => Box::new(SimpleBackend::new(size)),
            Backend::Iced => Box::new(ReactiveBackend::new(size)),
        };

        let mut stdin = std::io::stdin().lock();
        let mut graph: Box<dyn Graph> = match self.format {
            Format::Adjacent => Box::new(AdjacentGraph::from_stream(
                drawing_api.as_mut(),
                &mut stdin,
            )?),
            Format::EdgesList => {
                Box::new(EdgesGraph::from_stream(drawing_api.as_mut(), &mut stdin)?)
            }
        };

        graph.draw_graph();
        graph.show();

        Ok(())
    }
}
