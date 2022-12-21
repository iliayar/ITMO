mod lib;

use std::{borrow::BorrowMut, cell::RefCell, rc::Rc};

pub use lib::*;

fn main() {
    env_logger::init();

    let mut clock: Rc<RefCell<SetableClock>> =
        Rc::new(RefCell::new(SetableClock::now()));
    let mut stat = EventsStatisticsWithClock::new(clock.clone());

    for i in 0..50 {
        stat.inc_event("event_1");
        stat.inc_event("event_1");
        stat.inc_event("event_1");
        stat.inc_event("event_2");
        clock
            .as_ref()
            .borrow_mut()
            .sleep(chrono::Duration::minutes(1));
    }

    stat.print_statistics();
}
