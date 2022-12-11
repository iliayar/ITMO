use crate::DrawingApi;

use log::*;

pub struct TermLog {}

impl DrawingApi for TermLog {
    fn get_drawing_area_width(&self) -> i64 {
        100
    }

    fn get_drawing_area_height(&self) -> i64 {
        100
    }

    fn draw_circle(&mut self, center: crate::Point, radius: i64) {
        info!("Drawing circle in {:?} with radius {}", center, radius);
    }

    fn draw_line(&mut self, start: crate::Point, end: crate::Point) {
        info!("Drawing line from {:?} -> {:?}", start, end);
    }
}

impl TermLog {
    pub fn new() -> Self {
        Self {}
    }
}
