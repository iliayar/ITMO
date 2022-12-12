mod lib;
pub use lib::*;

// use druid::widget::{Button, Flex, Label};
// use druid::{AppLauncher, LocalizedString, PlatformError, Widget, WidgetExt, WindowDesc};

use log::*;

fn main() {
    env_logger::init();

    // let mut drawing_api = TermLog::new();
    let mut drawing_api = SimpleBackend::new();
    let mut graph = EdgesGraph::new(
        vec![(0, 1), (1, 2), (2, 3), (3, 0), (2, 0)],
        &mut drawing_api,
    );

    graph.draw_graph();
    graph.show();

    // let main_window = WindowDesc::new(ui_builder);
    // let data = 0_u32;
    // AppLauncher::with_window(main_window)
    //     .launch(data)
    //     .unwrap();
}

// fn ui_builder() -> impl Widget<u32> {
//     error!("AYAYA");
//     let text =
//         LocalizedString::new("hello-counter").with_arg("count", |data: &u32, _env| (*data).into());
//     let label = Label::new(text).padding(0.5).center();
//     let button = Button::new("increment")
//         .on_click(|_ctx, data, _env| *data += 1)
//         .padding(0.5);
//     Flex::column().with_child(label).with_child(button)
// }
