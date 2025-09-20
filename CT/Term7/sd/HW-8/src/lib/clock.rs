use chrono::NaiveDateTime;

pub trait Clock {
    fn now(&self) -> NaiveDateTime;
}

pub struct NormalClock {}

impl NormalClock {
    pub fn new() -> Self {
        Self {}
    }
}

impl Clock for NormalClock {
    fn now(&self) -> NaiveDateTime {
        chrono::Local::now().naive_local()
    }
}

pub struct SetableClock {
    time: NaiveDateTime,
}

impl SetableClock {
    pub fn now() -> Self {
        Self {
            time: chrono::Local::now().naive_local(),
        }
    }

    pub fn from_timestamp(timestamp: i64) -> Self {
        Self {
            time: chrono::NaiveDateTime::from_timestamp_opt(timestamp, 0).unwrap(),
        }
    }

    pub fn sleep(&mut self, duration: chrono::Duration) {
        self.time += duration;
    }
}

impl Clock for SetableClock {
    fn now(&self) -> NaiveDateTime {
        self.time
    }
}
