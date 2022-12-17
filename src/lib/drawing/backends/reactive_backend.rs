use crate::{DrawingApi, Point};

use iced::widget::canvas::{Frame, Geometry, Path, Program, Stroke, Text};
use log::*;

use iced::widget::{column, text, Canvas};
use iced::{
    executor, window, Alignment, Application, Color, Command, Element, Length, Settings,
    Subscription, Theme,
};

pub struct ReactiveBackend {
    graph: Graph,
    size: (u32, u32),
}

impl ReactiveBackend {
    pub fn new(size: (u32, u32)) -> Self {
        Self {
            graph: Graph::new(),
            size,
        }
    }
}

impl DrawingApi for ReactiveBackend {
    fn get_drawing_area_width(&self) -> i64 {
        800
    }

    fn get_drawing_area_height(&self) -> i64 {
        600
    }

    fn draw_circle(&mut self, center: Point, radius: i64) {
        self.graph.add_circle(center, radius);
    }

    fn draw_line(&mut self, start: Point, end: Point) {
        self.graph.add_line(start, end);
    }

    fn draw_text(&mut self, anchor: Point, text: &str, size: u16) {
        self.graph.add_text(anchor, text, size);
    }

    fn run(&mut self) {
        App::run(Settings {
            flags: (self.graph.clone(),),
            window: window::Settings {
                size: (800, 600),
                resizable: false,
                decorations: true,
                ..window::Settings::default()
            },
            ..Settings::default()
        })
        .unwrap();
    }
}

#[derive(Debug, Clone)]
enum Draw {
    Circle {
        center: Point,
        radius: i64,
    },
    Line {
        start: Point,
        end: Point,
    },
    Text {
        anchor: Point,
        text: String,
        size: u16,
    },
}

impl Draw {
    fn into_geometry(&self, bounds: iced::Rectangle) -> Geometry {
        let mut frame = Frame::new(bounds.size());

        match self {
            Draw::Circle { center, radius } => {
                let circle = Path::circle(center.clone().into(), *radius as f32);
                frame.stroke(&circle, Stroke::default());
            }
            Draw::Line { start, end } => {
                let line = Path::line(start.clone().into(), end.clone().into());
                frame.stroke(&line, Stroke::default());
            }
            Draw::Text { anchor, text, size } => {
                frame.fill_text(Text {
                    content: String::from(text),
                    position: anchor.clone().into(),
                    size: *size as f32,
                    ..Text::default()
                });
            }
        };

        frame.into_geometry()
    }
}

struct App {
    graph: Graph,
}

#[derive(Debug)]
enum Message {
    Draw(Draw),
}

impl Application for App {
    type Executor = executor::Default;
    type Message = Message;
    type Flags = (Graph,);
    type Theme = Theme;

    fn new((graph,): Self::Flags) -> (App, Command<Message>) {
        (App { graph }, Command::none())
    }

    fn title(&self) -> String {
        "Graph".to_string()
    }

    fn update(&mut self, message: Message) -> Command<Message> {
        Command::none()
    }

    fn subscription(&self) -> Subscription<Message> {
        Subscription::none()
    }

    fn view(&self) -> Element<Message> {
        Canvas::new(self.graph.clone())
            .width(Length::Fill)
            .height(Length::Fill)
            .into()
    }
}

#[derive(Default, Clone)]
struct Graph {
    draws: Vec<Draw>,
}

impl Graph {
    fn new() -> Self {
        Self { draws: Vec::new() }
    }

    fn add_circle(&mut self, center: Point, radius: i64) {
        self.draws.push(Draw::Circle { center, radius });
    }

    fn add_line(&mut self, start: Point, end: Point) {
        self.draws.push(Draw::Line { start, end });
    }

    fn add_text(&mut self, anchor: Point, text: &str, size: u16) {
        self.draws.push(Draw::Text {
            anchor,
            text: String::from(text),
            size,
        });
    }
}

impl Program<Message> for Graph {
    type State = ();

    fn draw(
        &self,
        state: &Self::State,
        theme: &Theme,
        bounds: iced::Rectangle,
        cursor: iced::widget::canvas::Cursor,
    ) -> Vec<Geometry> {
        self.draws.iter().map(|d| d.into_geometry(bounds)).collect()
    }
}

impl Into<iced::Point> for Point {
    fn into(self) -> iced::Point {
        iced::Point::new(self.x as f32, self.y as f32)
    }
}
