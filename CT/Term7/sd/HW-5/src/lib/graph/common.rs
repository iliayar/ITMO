use std::collections::{HashMap, HashSet};

use crate::{Graph, Point};

use log::*;

#[derive(Debug)]
pub struct NodeCoords {
    pub circle_center: Point,
    pub edges_anchor: Point,
}

pub fn arrange_vertices_in_circle(
    vertices: &HashSet<usize>,
    width: i64,
    height: i64,
    vertice_radius: f64,
) -> HashMap<usize, NodeCoords> {
    let mut res = HashMap::new();

    let nvertices = vertices.len();
    let radius = (height / 2).min(width / 2) as f64 - 2. * vertice_radius;
    let angle_step = 2. * std::f64::consts::PI / nvertices as f64;

    for (i, v) in vertices.iter().enumerate() {
        let angle = angle_step * i as f64;
        let circle_y = (radius * angle.sin()) as i64 + height / 2;
        let circle_x = (radius * angle.cos()) as i64 + width / 2;
        let circle_center = Point::new(circle_x, circle_y);

        let anchor_y = ((radius - vertice_radius) * angle.sin()) as i64 + height / 2;
        let anchor_x = ((radius - vertice_radius) * angle.cos()) as i64 + width / 2;
        let edges_anchor = Point::new(anchor_x, anchor_y);

        let coords = NodeCoords {
            circle_center,
            edges_anchor,
        };

        debug!("Calculated point: {:?}", coords);
        res.insert(*v, coords);
    }

    res
}

pub fn calculate_arrow_head(from: Point, to: Point) -> (Point, Point) {
    let vec = ((to.x - from.x) as f64, (to.y - from.y) as f64);
    let len = (vec.0.powi(2) + vec.1.powi(2)).sqrt();
    let vec = (vec.0 / len, vec.1 / len);

    debug!("Vec: {:?}", vec);

    let perp_up = (-vec.1, vec.0);
    let perp_down = (vec.1, -vec.0);

    let scale = 15.;
    let coef = 0.3;
    let p1 = (
        to.x as f64 - (vec.0 - coef * perp_up.0) * scale,
        to.y as f64 - (vec.1 - coef * perp_up.1) * scale,
    );

    let p2 = (
        to.x as f64 - (vec.0 - coef * perp_down.0) * scale,
        to.y as f64 - (vec.1 - coef * perp_down.1) * scale,
    );

    debug!("Arrow heads: {:?}, {:?}", p1, p2);

    (
        Point::new(p1.0 as i64, p1.1 as i64),
        Point::new(p2.0 as i64, p2.1 as i64),
    )
}

pub struct DrawingSettings {
    pub node_radius: f64,
    pub font_size: u16,
}

pub struct DrawingState {
    settings: DrawingSettings,
    points: HashMap<usize, NodeCoords>,
}

impl Default for DrawingSettings {
    fn default() -> Self {
        Self {
            node_radius: 20.,
            font_size: 20,
        }
    }
}

pub trait DrawingHelper: Graph {
    fn draw_vertices(&mut self, state: &DrawingState) {
        for (v, point) in state.points.iter() {
            self.drawing_api()
                .draw_circle(point.circle_center, state.settings.node_radius as i64);

            let text_achor = Point::new(
                point.circle_center.x + state.settings.node_radius as i64,
                point.circle_center.y + state.settings.node_radius as i64,
            );
            self.drawing_api()
                .draw_text(text_achor, &format!("{}", v), state.settings.font_size);
        }
    }

    fn draw_edge(&mut self, state: &DrawingState, from: usize, to: usize) {
        let from_point = state.points.get(&from);
        let to_point = state.points.get(&to);

        if from_point.is_none() || to_point.is_none() {
            error!("Cannot draw edges between {} and {}", from, to);
        }

        let from_anchor = from_point.unwrap().edges_anchor;
        let to_anchor = to_point.unwrap().edges_anchor;
        self.drawing_api().draw_line(from_anchor, to_anchor);

        let (head1, head2) = calculate_arrow_head(from_anchor, to_anchor);
        self.drawing_api().draw_line(to_anchor, head1);
        self.drawing_api().draw_line(to_anchor, head2);
    }

    fn get_state(&mut self, settings: DrawingSettings, vertices: &HashSet<usize>) -> DrawingState {
        let width = self.drawing_api().get_drawing_area_width();
        let height = self.drawing_api().get_drawing_area_height();
        let points = arrange_vertices_in_circle(vertices, width, height, settings.node_radius);

        DrawingState { settings, points }
    }
}

impl<T: Graph> DrawingHelper for T {}
