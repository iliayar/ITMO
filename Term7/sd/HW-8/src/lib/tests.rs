use std::collections::HashMap;

use crate::*;
use chrono::Duration;
use rstest::{fixture, rstest};

#[fixture]
fn clock() -> Rc<RefCell<SetableClock>> {
    Rc::new(RefCell::new(SetableClock::from_timestamp(1671562800)))
}

#[rstest]
#[case(0)]
#[case(1)]
#[case(10)]
#[case(100)]
fn test_constant_single_event_rpm(#[case] rpm: usize, clock: Rc<RefCell<SetableClock>>) {
    let mut stat = EventsStatisticsWithClock::new(clock.clone());

    for _ in 0..60 {
        for _ in 0..rpm {
            stat.inc_event("event");
        }

        clock
            .as_ref()
            .borrow_mut()
            .sleep(chrono::Duration::minutes(1));
    }

    assert_eq!(stat.get_event_statistics_by_name("event"), rpm as f64);
}

#[rstest]
#[case(vec![("event", 0)])]
#[case(vec![("event_1", 0), ("event_2", 1)])]
#[case(vec![("event_1", 1), ("event_2", 1), ("event_3", 1)])]
#[case(vec![("event_1", 5), ("event_2", 10)])]
#[case(vec![("event_1", 40), ("event_2", 50), ("event_3", 60)])]
fn test_constant_multiple_events_rpm(
    #[case] events_rpm: Vec<(&str, usize)>,
    clock: Rc<RefCell<SetableClock>>,
) {
    let mut stat = EventsStatisticsWithClock::new(clock.clone());

    for _ in 0..60 {
        for (event, rpm) in events_rpm.iter() {
            for _ in 0..*rpm {
                stat.inc_event(event);
            }
        }

        clock
            .as_ref()
            .borrow_mut()
            .sleep(chrono::Duration::minutes(1));
    }

    let events = stat.get_all_event_statistics();
    let mut expected_events = HashMap::new();
    for (event, rpm) in events_rpm.iter() {
        if *rpm != 0 {
            expected_events.insert(String::from(*event), *rpm as f64);
        }
    }

    assert_eq!(events, expected_events);
}

#[rstest]
#[case(vec![
    (0, Duration::minutes(29)),
    (60 * 15, Duration::minutes(30)),
], 15.)]
#[case(vec![
    (30 * 10, Duration::minutes(29)),
    (30 * 20, Duration::minutes(30)),
], 15.)]
#[case(vec![
    (20 * 10, Duration::minutes(15)),
    (20 * 20, Duration::minutes(15)),
    (20 * 30, Duration::minutes(15)),
], 20.)]
fn test_avg_spikes(
    #[case] spikes: Vec<(usize, Duration)>,
    #[case] rpm: f64,
    clock: Rc<RefCell<SetableClock>>,
) {
    let mut stat = EventsStatisticsWithClock::new(clock.clone());

    for (nevents, duration) in spikes.iter() {
        for _ in 0..*nevents {
            stat.inc_event("event");
        }

        clock.as_ref().borrow_mut().sleep(*duration);
    }

    assert_eq!(stat.get_event_statistics_by_name("event"), rpm);
}
