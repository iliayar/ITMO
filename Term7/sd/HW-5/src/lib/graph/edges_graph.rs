use std::collections::HashSet;
use std::io::BufRead;

use super::common::*;
use super::graph::AbstractGraph;
use crate::Point;
use crate::{Graph, HasDrawingApi};

use log::*;

pub struct EdgesGraph<'a> {
    edges: Vec<(usize, usize)>,
    vertices: HashSet<usize>,
    drawing_api: &'a mut dyn crate::DrawingApi,
}

impl<'a> EdgesGraph<'a> {
    pub fn new(drawing_api: &'a mut dyn crate::DrawingApi, edges: Vec<(usize, usize)>) -> Self {
        let mut vertices = HashSet::<usize>::new();
        for (from, to) in edges.iter() {
            vertices.insert(*from);
            vertices.insert(*to);
        }

        Self {
            edges,
            drawing_api,
            vertices,
        }
    }

    pub fn from_stream(
        drawing_api: &'a mut dyn crate::DrawingApi,
        stream: &mut dyn BufRead,
    ) -> Result<Self, anyhow::Error> {
        let mut edges = Vec::new();

        for mb_line in stream.lines() {
            let line = mb_line?;
            let from_to: Vec<Result<usize, _>> = line.split(" ").map(|e| e.parse()).collect();
            let from = from_to[0].clone()?;
            let to = from_to[1].clone()?;
            edges.push((from, to));
        }

        Ok(Self::new(drawing_api, edges))
    }
}

impl<'a> HasDrawingApi for EdgesGraph<'a> {
    fn drawing_api(&mut self) -> &mut dyn crate::DrawingApi {
        self.drawing_api
    }
}

impl<'a> AbstractGraph for EdgesGraph<'a> {}

impl<'a> Graph for EdgesGraph<'a> {
    fn draw_graph(&mut self) {
        let drawing_settings = DrawingSettings::default();
        let state = self.get_state(drawing_settings, &self.vertices.clone());

        self.draw_vertices(&state);

        for (from, to) in self.edges.clone().into_iter() {
            self.draw_edge(&state, from, to);
        }
    }
}
