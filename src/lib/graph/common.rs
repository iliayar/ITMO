use std::collections::{HashMap, HashSet};

use crate::Point;

use log::*;

pub fn arrange_vertices_in_circle(
    vertices: &HashSet<usize>,
    width: i64,
    height: i64,
    vertice_radius: f64,
) -> HashMap<usize, Point> {
    let mut res = HashMap::new();

    let nvertices = vertices.len();
    let radius = (height / 4).min(width / 4) as f64 - vertice_radius;
    let angle_step = 2. * std::f64::consts::PI / nvertices as f64;

    for (i, v) in vertices.iter().enumerate() {
        let angle = angle_step * i as f64;
        let x = (radius * angle.sin() - vertice_radius * angle.sin()) as i64 + height / 2;
        let y = (radius * angle.cos() - vertice_radius * angle.cos()) as i64 + width / 2;
        let point = Point::new(x, y);
        debug!("Calculated point: {:?}", point);
        res.insert(*v, point);
    }

    res
}
