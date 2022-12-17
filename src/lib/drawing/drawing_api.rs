
use crate::Point;


pub trait DrawingApi {
    fn get_drawing_area_width(&self) -> i64;
    fn get_drawing_area_height(&self) -> i64;

    fn draw_circle(&mut self, center: Point, radius: i64);
    fn draw_line(&mut self, start: Point, end: Point);
    fn draw_text(&mut self, anchor: Point, text: &str, size: u16);

    fn run(&mut self);
}
