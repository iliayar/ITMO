
use crate::DrawingApi;


pub trait HasDrawingApi {
    fn drawing_api(&mut self) -> &mut dyn DrawingApi;
}

pub trait Graph: HasDrawingApi {
    fn draw_graph(&mut self);
}

pub trait AbstractGraph: HasDrawingApi {
}
