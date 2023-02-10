use std::io::BufRead;

use crate::{Graph, HasDrawingApi};

use super::common::*;

use log::*;

pub struct AdjacentGraph<'a> {
    matrix: Vec<Vec<bool>>,
    drawing_api: &'a mut dyn crate::DrawingApi,
}

impl<'a> AdjacentGraph<'a> {
    pub fn new(drawing_api: &'a mut dyn crate::DrawingApi, matrix: Vec<Vec<bool>>) -> Self {
        assert!(matrix.len() == matrix[0].len(), "Matrix must be squared");
        Self {
            matrix,
            drawing_api,
        }
    }

    pub fn from_stream(
        drawing_api: &'a mut dyn crate::DrawingApi,
        stream: &mut dyn BufRead,
    ) -> Result<Self, anyhow::Error> {
        let mut matrix = Vec::new();

        let mut nedges: Option<usize> = Option::None;

        for mb_line in stream.lines() {
            let line = mb_line?;
            let edges: Vec<Result<usize, _>> = line.split(" ").map(|e| e.parse()).collect();

            match nedges {
                None => {
                    nedges = Some(edges.len());
                }
                Some(nedges) if nedges != edges.len() => {
                    return Err(anyhow::anyhow!(
                        "Inconsistent number of edges: {} and {}",
                        nedges,
                        edges.len()
                    ));
                }
                _ => {}
            }

            let mut row = Vec::new();
            for e in edges.into_iter() {
                row.push(e? == 1);
            }
            matrix.push(row);
        }

        if matrix.len() != matrix[0].len() {
            return Err(anyhow::anyhow!(
                "Number of rows is not equal to number of columns"
            ));
        }

        Ok(Self::new(drawing_api, matrix))
    }
}

impl<'a> HasDrawingApi for AdjacentGraph<'a> {
    fn drawing_api(&mut self) -> &mut dyn crate::DrawingApi {
        self.drawing_api
    }
}

impl<'a> Graph for AdjacentGraph<'a> {
    fn draw_graph(&mut self) {
        let drawing_settings = DrawingSettings::default();
        let state = self.get_state(drawing_settings, &(0..self.matrix.len()).collect());

        self.draw_vertices(&state);

        for (from, edges) in self.matrix.clone().iter().enumerate() {
            for (to, has_edge) in edges.iter().enumerate() {
                if *has_edge {
                    self.draw_edge(&state, from, to);
                }
            }
        }
    }
}
