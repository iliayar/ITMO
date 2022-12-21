use std::{cell::RefCell, collections::HashMap, rc::Rc};

use chrono::{NaiveDateTime, Timelike};

use crate::Clock;

use log::*;

pub trait EventsStatistics {
    fn inc_event(&mut self, name: &str);
    fn get_event_statistics_by_name(&self, name: &str) -> f64;
    fn get_all_event_statistics(&self) -> HashMap<String, f64>;
    fn print_statistics(&self);
}

pub struct EventsStatisticsWithClock {
    clock: Rc<RefCell<dyn Clock>>,
    events: HashMap<String, Vec<NaiveDateTime>>,
}

impl EventsStatisticsWithClock {
    pub fn new(clock: Rc<RefCell<dyn Clock>>) -> Self {
        Self {
            clock,
            events: HashMap::new(),
        }
    }

    fn now(&self) -> NaiveDateTime {
        self.clock.borrow().now()
    }
}

impl EventsStatistics for EventsStatisticsWithClock {
    fn inc_event(&mut self, name: &str) {
        if !self.events.contains_key(name) {
            self.events.insert(String::from(name), vec![]);
        }

        let now = self.now();
        self.events.get_mut(name).unwrap().push(now);
    }

    fn get_event_statistics_by_name(&self, name: &str) -> f64 {
        self.events
            .get(name)
            .map(|events| count_rpm(self.now(), events))
            .unwrap_or(0.)
    }

    fn get_all_event_statistics(&self) -> HashMap<String, f64> {
        self.events
            .iter()
            .map(|(name, events)| (String::from(name), count_rpm(self.now(), events)))
            .collect()
    }

    fn print_statistics(&self) {
        for (name, num_events) in self.get_all_event_statistics() {
            println!("{}: {}", name, num_events);
        }
    }
}

fn count_rpm(now: NaiveDateTime, events: &Vec<NaiveDateTime>) -> f64 {
    let now = cut_seconds(now);
    let one_minute = chrono::Duration::minutes(1);
    let mut start = now - chrono::Duration::hours(1);

    let mut num_events = 0;
    let mut buckets = 0;

    while start < now {
        num_events += events
            .iter()
            .filter(|t| **t < start + one_minute && **t >= start)
            .count();

        start += one_minute;
        buckets += 1;
    }
    assert_eq!(
        buckets, 60,
        "With these constant there must be exactly 60 minutes"
    );

    num_events as f64 / buckets as f64
}

fn cut_seconds(time: NaiveDateTime) -> NaiveDateTime {
    NaiveDateTime::from_timestamp_opt(time.timestamp() - time.timestamp() % 60, 0).unwrap()
}
