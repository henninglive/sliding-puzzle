//! Slide Puzzle
//!
//! <https://www.cs.cmu.edu/~adamchik/15-121/labs/HW-7%20Slide%20Puzzle/lab.html>

#[macro_use]
extern crate quick_error;
extern crate pathfinding;

use pathfinding::astar::astar;
use std::str::FromStr;
use std::fmt::Write;
use std::fmt;
use std::char;

pub const SIZE: usize = 9;
pub const STRIDE: usize = 3;

quick_error! {
    #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Error {
        InvalidLength {
            description("Invalid board size.")
        }
        DuplicateCells {
            description("Contains duplicate cells numbers.")
        }
        UncontinuousCells {
            description("Cells numbers are not continuous.")
        }
        Unsolvable {
            description("Board is unsolvable.")
        }
        Parse {
            description("Failed to parse board from str.")
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Direction {
    Up,
    Down,
    Left,
    Right
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Board {
    grid: [u8; SIZE],
    zero: u8,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Node {
    board: Board,
    prev: Option<Direction>,
}

impl Direction {
    pub fn rev(&self) -> Direction {
        match *self {
            Direction::Up    => Direction::Down,
            Direction::Down  => Direction::Up,
            Direction::Left  => Direction::Right,
            Direction::Right => Direction::Left,
        }
    }

    pub fn from_char(c: char) -> Option<Direction> {
        match c {
            'U' | 'u' => Some(Direction::Up),
            'D' | 'd' => Some(Direction::Down),
            'L' | 'l' => Some(Direction::Left),
            'R' | 'r' => Some(Direction::Right),
            _ => None,
        }
    }
}

impl From<Direction> for char {
    fn from(dir: Direction) -> char {
        match dir {
            Direction::Up    => 'U',
            Direction::Down  => 'D',
            Direction::Left  => 'L',
            Direction::Right => 'R',
        }
    }
}

impl Board {
    pub fn new(board: &[u8]) -> Result<Board, Error> {
        if board.len() != SIZE {
            return Err(Error::InvalidLength);
        }

        let mut bitset = [0u8; <u8>::max_value() as usize / 8];
        for n in board {
            if bitset[(*n / 8) as usize] & (1 << (*n % 8)) != 0 {
                return Err(Error::DuplicateCells)
            }

            bitset[(*n / 8) as usize] |= 1 << (*n % 8);
        }

        for i in 0..SIZE {
            if bitset[(i / 8) as usize] & (1 << (i % 8)) == 0 {
                return Err(Error::UncontinuousCells)
            }
        }

        // Test solveble
        let mut inv_count = 0;
        for i in 0..(SIZE - 1) {
            for j in (i + 1)..SIZE {
                if (board[j] > 0) && (board[i] > 0) && (board[i] > board[j]) {
                    inv_count += 1;
                }
            }
        }

        if inv_count % 2 != 0 {
            return Err(Error::Unsolvable);
        }

        // find zero cell
        let zero = board.iter().position(|&i| i == 0).unwrap() as u8;
        let mut grid = [0; 9];
        grid.copy_from_slice(board);

        Ok(Board {
            grid: grid,
            zero: zero,
        })
    }

    pub fn manhattan(&self) -> usize {
        let xy = |i: isize| ((i % STRIDE as isize), (i / STRIDE as isize));
        self.grid.iter()
            .enumerate()
            .filter(|&(_, j)| *j != 0)
            .map(|(i, j)| {
                let a = xy(i as isize);
                let b = xy(*j as isize - 1);
                ((a.0 - b.0).abs() + (a.1 - b.1).abs()) as usize
            })
            .sum::<usize>()
    }

    pub fn play_move(&self, dir: Direction) -> Option<Board> {
        use Direction::*;

        let old = self.zero as usize;
        let new = match dir {
            Up    if old >= STRIDE               => old - STRIDE,
            Down  if old +  STRIDE <  SIZE       => old + STRIDE,
            Left  if old %  STRIDE != 0          => old - 1,
            Right if old %  STRIDE != STRIDE - 1 => old + 1,
            _ => return None,
        };

        let mut grid = self.grid;
        grid.swap(old, new);
        Some(Board {
            grid: grid,
            zero: new as u8,
        })
    }

    pub fn solve(&self) -> Vec<Direction> {
        use Direction::*;

        let path = astar(
            // Root,
            &Node {
                board: self.clone(),
                prev: None,
            },
            // Neighbors fn.
            |n| {
                let node = n.clone();
                [Up, Down, Left, Right]
                    .into_iter()
                    .filter_map(move |d| {
                        node.board
                        .play_move(*d)
                        .map(|b| (Node {
                            board: b,
                            prev: Some(*d),
                        }, 1))
                    })
            },
            // Heuristic fn.
            |n| n.board.manhattan(),
            // Success fn.
            |n| n.board.manhattan() == 0,
        );

        path
        .unwrap().0
        .into_iter()
        .filter_map(|n| n.prev)
        .collect()
    }
}

impl FromStr for Board {
    type Err = Error;
    fn from_str(s: &str) -> Result<Board, Error> {
        let mut v = Vec::new();
        for c in s.chars() {
            let n = c.to_digit(36).ok_or(Error::Parse)?;
            v.push(n as u8);
        }
        Board::new(&v[..])
    }
}

impl fmt::Display for Board {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (j, i) in self.grid.iter().enumerate() {
            let c = char::from_digit(*i as u32, 10).unwrap();
            f.write_char(c)?;
            if j % STRIDE == STRIDE - 1 {
                f.write_char('\n')?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ::*;
    use Direction::*;

    static TARGET: Board = Board {
        grid: [1, 2, 3, 4, 5, 6, 7, 8, 0],
        zero: 8,
    };

    static TEST_SOLUTIONS: [(&'static str, &'static[&'static str]); 15] = [
        ("123405786", &["RD"]),
        ("123745086", &["URRD"]),
        ("123480765", &["DLURD"]),
        ("413726580", &["LLUURDDR"]),
        ("162530478", &["LURDLLDRR"]),
        ("512630478", &["LLURRDLLDRR"]),
        ("126350478", &["ULDLDRRULURDD"]),
        ("356148072", &["RRUULLDRDRUULDRD"]),
        ("436871052", &["URRULDDRULDLUURDRD"]),
        ("302651478", &["DRULDLURRDLLDRRULURDD", "DLURDRULDLURDRULDLDRR"]),
        ("012345678", &["RDLDRRULLDRUURDDLLURRD", "DRRULLDDRUURDLLURRDLDR"]),
        ("503284671", &["LDDRRULLDRRULLDRUULDDRR"]),
        ("874320651", &["DLULURDRULDDLUURDRDLLURRD"]),
        ("876543021", &["UURDRDLLUURDRULDDRULDLUURDRD",
            "UURDLDRURDLLUURDRULDDLUURDDR"]),
        ("876543210", &["ULLURDDRUULDDLUURDDRUULDDLURRD",
            "ULULDDRUULDDRUURDDLUURDLULDRDR"]),
    ];

    static TEST_MOVES: [(&'static str, Direction, Option<&'static str>); 12] = [
        ("012345678", Up, None),
        ("123045678", Up, Some("023145678")),
        ("123456078", Up, Some("123056478")),
        ("012345678", Down, Some("312045678")),
        ("123045678", Down, Some("123645078")),
        ("123456078", Down, None),
        ("012345678", Left, None),
        ("102345678", Left, Some("012345678")),
        ("120345678", Left, Some("102345678")),
        ("012345678", Right, Some("102345678")),
        ("102345678", Right, Some("120345678")),
        ("120345678", Right, None),
    ];

    static TEST_MANHATTAN: [(&'static str, usize); 3] = [
        ("123456780", 0),
        ("213540678", 9),
        ("647850321", 21),
    ];

    static TEST_UNSOLVABLE: [&'static str; 1] = [
        "812043765",
    ];

    #[test]
    fn test_new() {
        assert_eq!(Board::new(&[]), Err(Error::InvalidLength));
        assert_eq!(Board::new(&[0u8; 20][..]), Err(Error::InvalidLength));

        assert_eq!(Board::new(&[0; SIZE]), Err(Error::DuplicateCells));
        assert_eq!(Board::new(&[0, 2, 4, 6, 8, 10, 12, 14, 16]),
            Err(Error::UncontinuousCells));

        Board::new(&[0, 1, 2, 3, 4, 5, 6, 7, 8]).unwrap();
        Board::new(&[7, 1, 4, 3, 2, 6, 5, 0, 8]).unwrap();
    }

    #[test]
    fn test_move() {
        for &(board, dir, res) in TEST_MOVES.iter() {
            let board = board.parse::<Board>().unwrap();
            let res = res.map(|res| res.parse::<Board>().unwrap());
            let next = board.play_move(dir);
            assert_eq!(next, res);
        }
    }

    #[test]
    fn test_manhattan() {
        for &(board, man) in TEST_MANHATTAN.iter() {
            let board = board.parse::<Board>().unwrap();
            assert_eq!(board.manhattan(), man);
        }
    }

    #[test]
    fn test_solutions() {
        for &(board, optimals) in TEST_SOLUTIONS.iter() {
            let puzzle = board.parse::<Board>().unwrap();

            let mut answer = puzzle;
            for dir in puzzle.solve() {
                answer = answer.play_move(dir).expect("invalid move");
            }

            assert_eq!(TARGET, answer);

            for optimal in optimals {
                let moves = optimal.chars()
                    .map(|c| Direction::from_char(c).unwrap())
                    .collect::<Vec<_>>();

                answer = puzzle;
                for dir in moves {
                    answer = answer.play_move(dir).expect("invalid move");
                }

                assert_eq!(TARGET, answer);
            }
        }
    }

    #[test]
    fn test_unsolvable() {
        for board in TEST_UNSOLVABLE.iter() {
            assert_eq!(board.parse::<Board>(), Err(Error::Unsolvable));
        }
    }
}
