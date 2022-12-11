mod lib;
pub use lib::*;

// use nannou::prelude::*;

// use iced::widget::{button, column, text};
// use iced::{Alignment, Element, Sandbox, Settings};

// use simple;

use log::*;

fn main() {
    env_logger::init();

    // let mut drawing_api = TermLog::new();
    // let mut graph = EdgesGraph::new(
    //     vec![(0, 1), (1, 2), (2, 3), (3, 0), (2, 0)],
    //     &mut drawing_api,
    // );

    // graph.draw_graph();

    // nannou::sketch(|app, frame| view(app, frame)).run();

    // Counter::run(Settings::default()).unwrap();

    // let mut app = simple::Window::new("Hello, World!", 640, 480);
    // app.set_color(255, 0, 255, 255);
    // app.draw_rect(simple::Rect::new(10, 20, 30, 40));

    // while app.next_frame() {}
}

// struct Counter {
//     value: i32,
// }

// #[derive(Debug, Clone, Copy)]
// enum Message {
//     IncrementPressed,
//     DecrementPressed,
// }

// impl Sandbox for Counter {
//     type Message = Message;

//     fn new() -> Self {
//         Self { value: 0 }
//     }

//     fn title(&self) -> String {
//         String::from("Counter - Iced")
//     }

//     fn update(&mut self, message: Message) {
//         match message {
//             Message::IncrementPressed => {
//                 self.value += 1;
//             }
//             Message::DecrementPressed => {
//                 self.value -= 1;
//             }
//         }
//     }

//     fn view(&self) -> Element<Message> {
//         column![
//             button("Increment").on_press(Message::IncrementPressed),
//             text(self.value).size(50),
//             button("Decrement").on_press(Message::DecrementPressed),
//         ]
//         .padding(20)
//         .align_items(Alignment::Center)
//         .into()
//     }
// }

// fn view(app: &App, frame: Frame) {
//     error!("App rect: {:?}", app.window_rect());
//     let draw = app.draw();
//     draw.background().color(WHITE);

//     draw.ellipse().color(BLACK).x_y(100., 100.).radius(20.);
//     draw.ellipse().color(WHITE).x_y(100., 100.).radius(18.);
//     draw.text("0").x_y(100., 100.).color(BLACK);

//     draw.ellipse().color(BLACK).x_y(200., 100.).radius(20.);
//     draw.ellipse().color(WHITE).x_y(200., 100.).radius(18.);
//     draw.text("1").x_y(200., 100.).color(BLACK);

//     draw.line().start(pt2(120., 100.)).end(pt2(180., 100.)).color(BLACK).weight(2.);

//     draw.to_frame(app, &frame).unwrap();
// }
