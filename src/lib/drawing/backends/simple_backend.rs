use crate::DrawingApi;

use sdl2::gfx::primitives::DrawRenderer;
use sdl2::{self, pixels::Color};

use log::*;

use crossfont;

pub struct SimpleBackend {
    size: (u32, u32),
    sdl_context: sdl2::Sdl,
    video_subsystem: sdl2::VideoSubsystem,
    canvas: sdl2::render::WindowCanvas,
    ttf_context: sdl2::ttf::Sdl2TtfContext,
}

impl SimpleBackend {
    pub fn new(size: (u32, u32)) -> Self {
        let sdl_context = sdl2::init().unwrap();
        let video_subsystem = sdl_context.video().unwrap();

        let window = video_subsystem.window("Graph", size.0, size.1).build().unwrap();

        let size = window.size();

        let mut canvas = window.into_canvas().build().unwrap();
        canvas.set_draw_color(Color::RGB(255, 255, 255));
        canvas.clear();

        let ttf_context = sdl2::ttf::init().unwrap();

        Self {
            sdl_context,
            video_subsystem,
            canvas,
            size,
            ttf_context,
        }
    }
}

impl DrawingApi for SimpleBackend {
    fn get_drawing_area_width(&self) -> i64 {
        self.size.0 as i64
    }

    fn get_drawing_area_height(&self) -> i64 {
        self.size.1 as i64
    }

    fn draw_circle(&mut self, center: crate::Point, radius: i64) {
        self.canvas
            .circle(
                center.x as i16,
                center.y as i16,
                radius as i16,
                Color::RGB(0, 0, 0),
            )
            .unwrap();
    }

    fn draw_line(&mut self, start: crate::Point, end: crate::Point) {
        self.canvas.set_draw_color(Color::RGB(0, 0, 0));
        self.canvas
            .draw_line(
                (start.x as i32, start.y as i32),
                (end.x as i32, end.y as i32),
            )
            .unwrap();
    }

    fn run(&mut self) {
        self.canvas.present();

        let mut event_pump = self.sdl_context.event_pump().unwrap();
        'running: loop {
            for event in event_pump.poll_iter() {
                match event {
                    sdl2::event::Event::Quit { .. } => break 'running,
                    _ => {}
                }
            }
        }
    }

    fn draw_text(&mut self, anchor: crate::Point, text: &str, size: u16) {
	let mut pattern = crossfont::ft::fc::Pattern::new();
	pattern.add_family("Ubuntu");
        let fc = crossfont::ft::fc::font_match(
            crossfont::ft::fc::Config::get_current(),
            &pattern,
        ).unwrap();
	let found_font = fc.file(0).unwrap();

        let texture_creator = self.canvas.texture_creator();
        let font = self.ttf_context.load_font(found_font, size).unwrap();

        let surface = font.render(text).blended(Color::RGB(0, 0, 0)).unwrap();
        let texture = texture_creator
            .create_texture_from_surface(surface)
            .unwrap();

        let sdl2::render::TextureQuery { width, height, .. } = texture.query();
        let rect = sdl2::rect::Rect::new(anchor.x as i32, anchor.y as i32, width, height);

        self.canvas.copy(&texture, None, Some(rect)).unwrap();
    }
}
