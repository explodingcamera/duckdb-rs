//! Convert [Timestamp Types](https://duckdb.org/docs/sql/data_types/timestamp) to time types.

use crate::types::{FromSql, FromSqlError, FromSqlResult, ToSql, ToSqlOutput, ValueRef};
use crate::{Error, Result};
use num_integer::Integer;
use time::format_description::well_known::{Iso8601, Rfc3339};
use time::format_description::FormatItem;
use time::macros::format_description;
use time::{Date, OffsetDateTime, PrimitiveDateTime, Time};

use super::{TimeUnit, Value};

const TIME_ENCODING: &[FormatItem<'_>] = format_description!(version = 2, "[hour]:[minute]:[second].[subsecond]");
const DATE_FORMAT: &[FormatItem<'_>] = format_description!(version = 2, "[year]-[month]-[day]");
const PRIMITIVE_DATE_TIME_ENCODING: &[FormatItem<'_>] = format_description!(
    version = 2,
    "[year]-[month]-[day] [hour]:[minute]:[second].[subsecond digits:3]"
);

/// ISO 8601 calendar date without timezone => "YYYY-MM-DD"
impl ToSql for Date {
    #[inline]
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        let date_str = self
            .format(&DATE_FORMAT)
            .map_err(|err| Error::ToSqlConversionFailure(err.into()))?;
        Ok(ToSqlOutput::from(date_str))
    }
}

/// "YYYY-MM-DD" => ISO 8601 calendar date without timezone.
impl FromSql for Date {
    #[inline]
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        if let Ok(date_time) = PrimitiveDateTime::column_result(value) {
            return Ok(date_time.date());
        }

        match value {
            ValueRef::Date32(d) => {
                let timestamp = OffsetDateTime::from_unix_timestamp(d as i64 * 24 * 60 * 60)
                    .map_err(|err| FromSqlError::Other(Box::new(err)))?;
                Ok(timestamp.date())
            }
            ValueRef::Text(s) => Self::parse(std::str::from_utf8(s).unwrap(), &DATE_FORMAT)
                .map_err(|err| FromSqlError::Other(Box::new(err))),
            _ => Err(FromSqlError::InvalidType),
        }
    }
}

/// ISO 8601 time without timezone => "HH:MM:SS.SSS"
impl ToSql for Time {
    #[inline]
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        let time_str = self
            .format(&TIME_ENCODING)
            .map_err(|err| Error::ToSqlConversionFailure(err.into()))?;
        println!("time_str: {}", time_str);
        Ok(ToSqlOutput::from(time_str))
    }
}

/// "HH:MM"/"HH:MM:SS"/"HH:MM:SS.SSS" => ISO 8601 time without timezone.
impl FromSql for Time {
    #[inline]
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        if let Ok(date_time) = PrimitiveDateTime::column_result(value) {
            return Ok(date_time.time());
        }

        match value {
            ValueRef::Time64(TimeUnit::Microsecond, d) => {
                let seconds = d / 1_000_000;
                let nanos = ((d % 1_000_000) * 1_000) as u32;

                Ok(OffsetDateTime::from_unix_timestamp(seconds)
                    .map_err(|err| FromSqlError::Other(Box::new(err)))?
                    .time()
                    + time::Duration::nanoseconds(nanos as i64))
            }
            ValueRef::Text(s) => {
                let s = std::str::from_utf8(s).unwrap();
                let format = match s.len() {
                    //23:56
                    5 => format_description!("[hour]:[minute]"),
                    //23:56:04
                    8 => format_description!("[hour]:[minute]:[second]"),
                    //23:56:04.789
                    _ => format_description!("[hour]:[minute]:[second].[subsecond]"),
                };
                Time::parse(s, &format).map_err(|err| FromSqlError::Other(Box::new(err)))
            }
            _ => Err(FromSqlError::InvalidType),
        }
    }
}

/// ISO 8601 combined date and time without timezone =>
/// "YYYY-MM-DD HH:MM:SS.SSS"
impl ToSql for PrimitiveDateTime {
    #[inline]
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        let date_time_str = self
            .format(&PRIMITIVE_DATE_TIME_ENCODING)
            .map_err(|err| Error::ToSqlConversionFailure(err.into()))?;
        Ok(ToSqlOutput::from(date_time_str))
    }
}

/// "YYYY-MM-DD HH:MM:SS"/"YYYY-MM-DD HH:MM:SS.SSS" => ISO 8601 combined date
/// and time without timezone. ("YYYY-MM-DDTHH:MM:SS"/"YYYY-MM-DDTHH:MM:SS.SSS"
/// also supported)
impl FromSql for PrimitiveDateTime {
    #[inline]
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        match value {
            ValueRef::Timestamp(tu, t) => {
                let (secs, nsecs) = match tu {
                    TimeUnit::Second => (t, 0),
                    TimeUnit::Millisecond => (t / 1000, (t % 1000) * 1_000_000),
                    TimeUnit::Microsecond => (t / 1_000_000, (t % 1_000_000) * 1000),
                    TimeUnit::Nanosecond => (t / 1_000_000_000, t % 1_000_000_000),
                };
                let timestamp =
                    OffsetDateTime::from_unix_timestamp(secs).map_err(|err| FromSqlError::Other(Box::new(err)))?;
                let timestamp = timestamp + time::Duration::nanoseconds(nsecs as i64);
                Ok(PrimitiveDateTime::new(timestamp.date(), timestamp.time()))
            }
            ValueRef::Date32(t) => {
                let timestamp = OffsetDateTime::from_unix_timestamp(t as i64 * 24 * 60 * 60)
                    .map_err(|err| FromSqlError::Other(Box::new(err)))?;
                Ok(PrimitiveDateTime::new(timestamp.date(), timestamp.time()))
            }
            ValueRef::Time64(TimeUnit::Microsecond, d) => {
                let seconds = d / 1_000_000;
                let nanos = ((d % 1_000_000) * 1_000) as u32;

                let timestamp = OffsetDateTime::from_unix_timestamp(seconds)
                    .map_err(|err| FromSqlError::Other(Box::new(err)))?
                    + time::Duration::nanoseconds(nanos as i64);

                Ok(PrimitiveDateTime::new(timestamp.date(), timestamp.time()))
            }
            ValueRef::Text(s) => {
                let mut s = std::str::from_utf8(s).unwrap();

                if let Ok(date) = Self::parse(s, &Iso8601::DEFAULT) {
                    return Ok(date);
                }

                let format = match s.len() {
                    //2016-02-23
                    10 => format_description!("[year]-[month]-[day]"),
                    //2016-02-23 23:56:04
                    19 => format_description!("[year]-[month]-[day] [hour]:[minute]:[second]"),
                    //2016-02-23 23:56:04.789
                    23 => format_description!("[year]-[month]-[day] [hour]:[minute]:[second].[subsecond]"),
                    //2016-02-23 23:56:04.789+00:00
                    29 => format_description!("[year]-[month]-[day] [hour]:[minute]:[second].[subsecond]"),
                    _ => {
                        if s.len() > 10 {
                            s = &s[..10];
                        }
                        format_description!("[year]-[month]-[day]")
                    }
                };

                let res = Self::parse(s, &format).map_err(|err| FromSqlError::Other(Box::new(err)));
                res
            }
            _ => Err(FromSqlError::InvalidType),
        }
    }
}

/// Date and time with time zone => UTC RFC3339 timestamp
/// ("YYYY-MM-DD HH:MM:SS.SSS+00:00").
impl ToSql for OffsetDateTime {
    #[inline]
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        let date_time_str = self
            .format(&Rfc3339)
            .map_err(|err| Error::ToSqlConversionFailure(err.into()))?;
        Ok(ToSqlOutput::from(date_time_str))
    }
}

/// RFC3339 ("YYYY-MM-DD HH:MM:SS.SSS[+-]HH:MM") into `DateTime<Utc>`.
impl FromSql for OffsetDateTime {
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        PrimitiveDateTime::column_result(value).map(|dt| dt.assume_utc())
    }
}

const DAYS_PER_MONTH: i128 = 30;
const SECONDS_PER_DAY: i128 = 24 * 3600;
const NANOS_PER_SECOND: i128 = 1_000_000_000;
const NANOS_PER_DAY: i128 = SECONDS_PER_DAY * NANOS_PER_SECOND;

impl ToSql for time::Duration {
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        let seconds = self.whole_seconds();
        let ns = self.subsec_nanoseconds();
        let nanos = seconds as i128 * NANOS_PER_SECOND + ns as i128;

        let (days, nanos) = nanos.div_mod_floor(&NANOS_PER_DAY);
        let (months, days) = days.div_mod_floor(&DAYS_PER_MONTH);

        Ok(ToSqlOutput::Owned(Value::Interval {
            months: months.try_into().unwrap(),
            days: days.try_into().unwrap(),
            nanos: nanos.try_into().unwrap(),
        }))
    }
}

impl FromSql for time::Duration {
    fn column_result(value: ValueRef<'_>) -> FromSqlResult<Self> {
        match value {
            ValueRef::Interval { months, days, nanos } => {
                let days = days + (months * 30);
                let seconds = i64::from(days) * 24 * 3600;

                match nanos.try_into() {
                    Ok(nanos) => Ok(time::Duration::new(seconds, nanos)),
                    Err(err) => Err(FromSqlError::Other(format!("Invalid duration: {err}").into())),
                }
            }
            _ => Err(FromSqlError::InvalidType),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Connection, Result};
    use time::macros::{date, datetime, time};
    use time::{Date, OffsetDateTime, PrimitiveDateTime, Time};

    fn checked_memory_handle() -> Result<Connection> {
        let db = Connection::open_in_memory()?;
        db.execute_batch("CREATE TABLE foo (d DATE, t Text, i INTEGER, f FLOAT, b TIMESTAMP, tt time)")?;
        Ok(db)
    }

    #[test]
    fn test_offset_date_time() -> Result<()> {
        let db = checked_memory_handle()?;

        let mut ts_vec = vec![];

        let make_datetime =
            |secs: i128, nanos: i128| OffsetDateTime::from_unix_timestamp_nanos(1_000_000_000 * secs + nanos).unwrap();

        ts_vec.push(make_datetime(10_000, 0)); //January 1, 1970 2:46:40 AM
        ts_vec.push(make_datetime(10_000, 1000)); //January 1, 1970 2:46:40 AM (and one microsecond)
        ts_vec.push(make_datetime(1_500_391_124, 1_000_000)); //July 18, 2017
        ts_vec.push(make_datetime(2_000_000_000, 2_000_000)); //May 18, 2033
        ts_vec.push(make_datetime(3_000_000_000, 999_999_999)); //January 24, 2065
        ts_vec.push(make_datetime(10_000_000_000, 0)); //November 20, 2286

        for ts in ts_vec {
            db.execute("INSERT INTO foo(t) VALUES (?1)", [ts])?;

            let from: OffsetDateTime = db.query_row("SELECT t FROM foo", [], |r| r.get(0))?;

            db.execute("DELETE FROM foo", [])?;

            assert_eq!(from, ts);
        }
        Ok(())
    }

    #[test]
    fn test_date() -> Result<()> {
        let db = checked_memory_handle()?;
        let date = date!(2016 - 02 - 23);
        db.execute("INSERT INTO foo (d) VALUES (?1)", [date])?;

        let s: String = db.query_row("SELECT d FROM foo", [], |r| r.get(0))?;
        assert_eq!("2016-02-23", s);
        let t: Date = db.query_row("SELECT d FROM foo", [], |r| r.get(0))?;
        assert_eq!(date, t);
        Ok(())
    }

    #[test]
    fn test_time() -> Result<()> {
        let db = checked_memory_handle()?;
        let time = time!(23:56:04);
        db.execute("INSERT INTO foo (t) VALUES (?1)", [time])?;

        let s: String = db.query_row("SELECT t FROM foo", [], |r| r.get(0))?;
        assert_eq!("23:56:04.0", s);
        let v: Time = db.query_row("SELECT t FROM foo", [], |r| r.get(0))?;
        assert_eq!(time, v);
        Ok(())
    }

    #[test]
    fn test_primitive_date_time() -> Result<()> {
        let db = checked_memory_handle()?;
        let dt = date!(2016 - 02 - 23).with_time(time!(23:56:04));

        db.execute("INSERT INTO foo (b) VALUES (?)", [dt])?;

        let s: String = db.query_row("SELECT b FROM foo", [], |r| r.get(0))?;
        assert_eq!("2016-02-23 23:56:04", s);

        let v: PrimitiveDateTime = db.query_row("SELECT b FROM foo", [], |r| r.get(0))?;
        assert_eq!(dt, v);

        db.execute(
            "UPDATE foo set b = strftime(cast(b as datetime), '%Y-%m-%d %H:%M:%S')",
            [],
        )?; // "YYYY-MM-DD HH:MM:SS"

        let hms: PrimitiveDateTime = db.query_row("SELECT b FROM foo", [], |r| r.get(0))?;
        assert_eq!(dt, hms);
        Ok(())
    }

    #[test]
    fn test_date_parsing() -> Result<()> {
        let db = checked_memory_handle()?;
        let result: Date = db.query_row("SELECT ?", ["2013-10-07"], |r| r.get(0))?;
        assert_eq!(result, date!(2013 - 10 - 07));
        Ok(())
    }

    #[test]
    fn test_time_parsing() -> Result<()> {
        let db = checked_memory_handle()?;
        let tests = vec![
            ("08:23", time!(08:23)),
            ("08:23:19", time!(08:23:19)),
            ("08:23:19.111", time!(08:23:19.111)),
        ];

        for (s, t) in tests {
            let result: Time = db.query_row("SELECT ?", [s], |r| r.get(0))?;
            assert_eq!(result, t);
        }
        Ok(())
    }

    #[test]
    fn test_primitive_date_time_parsing() -> Result<()> {
        let db = checked_memory_handle()?;

        let tests = vec![
            ("2013-10-07T08:23", datetime!(2013-10-07 8:23)),
            ("2013-10-07T08:23:19", datetime!(2013-10-07 8:23:19)),
            ("2013-10-07T08:23:19.111", datetime!(2013-10-07 8:23:19.111)),
            ("2013-10-07 08:23:19", datetime!(2013-10-07 8:23:19)),
            ("2013-10-07 08:23:19.111", datetime!(2013-10-07 8:23:19.111)),
        ];

        for (s, t) in tests {
            let result: PrimitiveDateTime = db.query_row("SELECT ?", [s], |r| r.get(0))?;
            assert_eq!(result, t);
        }
        Ok(())
    }

    #[test]
    fn test_duckdb_datetime_functions() -> Result<()> {
        let db = checked_memory_handle()?;

        db.query_row::<PrimitiveDateTime, _, _>("SELECT CURRENT_TIMESTAMP", [], |r| r.get(0))?;
        db.query_row::<OffsetDateTime, _, _>("SELECT CURRENT_TIMESTAMP", [], |r| r.get(0))?;
        db.query_row::<Time, _, _>("SELECT CURRENT_TIME", [], |r| r.get(0))?;
        db.query_row::<Date, _, _>("SELECT CURRENT_DATE", [], |r| r.get(0))?;

        Ok(())
    }

    #[test]
    fn test_time_param() -> Result<()> {
        let db = checked_memory_handle()?;
        let now = OffsetDateTime::now_utc().time();
        let result: Result<bool> = db.query_row(
            "SELECT 1 WHERE ?::time BETWEEN (?::time - INTERVAL '1 minute') AND (?::time + INTERVAL '1 minute')",
            [now, now, now],
            |r| r.get(0),
        );
        result.unwrap();
        Ok(())
    }

    #[test]
    fn test_date_param() -> Result<()> {
        let db = checked_memory_handle()?;
        let now = OffsetDateTime::now_utc().date();
        let result: Result<bool> = db.query_row(
            "SELECT 1 WHERE ? BETWEEN (now()::timestamp - INTERVAL '1 day') AND (now()::timestamp + INTERVAL '1 day')",
            [now],
            |r| r.get(0),
        );
        result.unwrap();
        Ok(())
    }

    #[test]
    fn test_primitive_date_time_param() -> Result<()> {
        let db = checked_memory_handle()?;
        let now = PrimitiveDateTime::new(OffsetDateTime::now_utc().date(), OffsetDateTime::now_utc().time());
        let result: Result<bool> = db.query_row(
            "SELECT 1 WHERE ? BETWEEN (now()::timestamp - INTERVAL '1 minute') AND (now()::timestamp + INTERVAL '1 minute')",
            [now],
            |r| r.get(0),
        );
        result.unwrap();
        Ok(())
    }

    #[test]
    fn test_offset_date_time_param() -> Result<()> {
        let db = checked_memory_handle()?;
        let result: Result<bool> = db.query_row(
            "SELECT 1 WHERE ? BETWEEN (now()::timestamp - INTERVAL '1 minute') AND (now()::timestamp + INTERVAL '1 minute')",
            [OffsetDateTime::now_utc()],
            |r| r.get(0),
        );
        result.unwrap();
        Ok(())
    }
}
