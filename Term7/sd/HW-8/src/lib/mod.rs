mod clock;
mod events_statistics;

pub use clock::{Clock, NormalClock, SetableClock};
pub use events_statistics::{EventsStatistics, EventsStatisticsWithClock};

#[cfg(test)]
mod tests;
