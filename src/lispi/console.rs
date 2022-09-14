use crossterm::cursor;
use crossterm::terminal;
use crossterm::ExecutableCommand;
use std::fmt::Display;
use std::io::{stdout, Write};

pub fn print<T>(text: &T) -> std::io::Result<()>
where
    T: Display + ?Sized,
{
    write!(stdout(), "{}", text)?;
    stdout().flush()?;
    Ok(())
}

pub fn printuw<T>(text: &T)
where
    T: Display + ?Sized,
{
    print(text).unwrap();
}

pub fn println<T>(text: &T) -> std::io::Result<()>
where
    T: Display + ?Sized,
{
    print(text)?;
    newline()?;
    Ok(())
}

pub fn printlnuw<T>(text: &T)
where
    T: Display + ?Sized,
{
    println(text).unwrap();
}

pub fn newline() -> std::io::Result<()> {
    stdout()
        .execute(cursor::MoveToNextLine(1))?
        .execute(terminal::ScrollUp(1))?;
    Ok(())
}

pub fn newlineuw() {
    newline().unwrap();
}
