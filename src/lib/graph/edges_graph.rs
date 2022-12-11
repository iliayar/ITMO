use std::collections::HashSet;

use super::graph::AbstractGraph;
use crate::Point;
use crate::{Graph, HasDrawingApi};

pub struct EdgesGraph<'a> {
    edges: Vec<(usize, usize)>,
    vertices: HashSet<usize>,
    drawing_api: &'a mut dyn crate::DrawingApi,
}

impl<'a> EdgesGraph<'a> {
    pub fn new(edges: Vec<(usize, usize)>, drawing_api: &'a mut dyn crate::DrawingApi) -> Self {
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
}

impl<'a> HasDrawingApi for EdgesGraph<'a> {
    fn drawing_api(&mut self) -> &mut dyn crate::DrawingApi {
        self.drawing_api
    }
}

impl<'a> AbstractGraph for EdgesGraph<'a> {}

impl<'a> Graph for EdgesGraph<'a> {
    fn draw_graph(&mut self) {
        for vertice in self.vertices.iter() {
            self.drawing_api
                .draw_circle(Point::new(*vertice as i64, *vertice as i64), 1);
        }
        for (from, to) in self.edges.iter() {
            self.drawing_api.draw_line(
                Point::new(*from as i64, *from as i64),
                Point::new(*to as i64, *to as i64),
            );
        }
    }
}
