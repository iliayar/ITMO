use std::collections::HashSet;

use super::common;
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
	let radius = 5.;
        let width = self.drawing_api.get_drawing_area_width();
        let height = self.drawing_api.get_drawing_area_height();
        let points = common::arrange_vertices_in_circle(&self.vertices, width, height, radius);

        for (v, point) in points.iter() {
            self.drawing_api.draw_circle(*point, radius as i64);
        }

        for (from, to) in self.edges.iter() {
            let from_point = points.get(from);
            let to_point = points.get(to);

            if from_point.is_none() || to_point.is_none() {
                error!("Cannot draw edges between {} and {}", from, to);
            }

            self.drawing_api
                .draw_line(*from_point.unwrap(), *to_point.unwrap());
        }
    }
}
