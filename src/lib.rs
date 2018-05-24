//! Slide Puzzle
//!
//! <https://www.cs.cmu.edu/~adamchik/15-121/labs/HW-7%20Slide%20Puzzle/lab.html>

#[macro_use]
extern crate quick_error;
extern crate indexmap;

use indexmap::{IndexSet, Equivalent};
use std::collections::BinaryHeap;
use std::hash::{Hash, Hasher};
use std::cmp::Ordering;
use std::str::FromStr;

const SIZE: usize = 9;
const STRIDE: usize = 3;

quick_error! {
    #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Error {
        InvalidLength {
            description("Invalid board size")
        }
        DuplicateCells {
            description("Contains duplicate cells numbers")
        }
        UncontinuousCells {
            description("Cells numbers are not continuous")
        }
        Parse {
            description("Failed to parse board from str")
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

#[derive(Debug, Clone)]
struct SearchNode {
    board: Board,
    prev: Option<(Direction, usize)>,
}

#[derive(Debug)]
pub struct Solver {
    head: Option<(SearchNode, usize)>,
    seen: IndexSet<SearchNode>,
    queue: BinaryHeap<SearchNode>,
    best: Option<usize>,
    pub limit: usize,
    pub iters: usize,
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

impl PartialEq for SearchNode {
    fn eq(&self, other: &SearchNode) -> bool {
        self.board.eq(&other.board)
    }
}

impl Eq for SearchNode {}

impl Hash for SearchNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.board.hash(state);
    }
}

impl PartialOrd for SearchNode {
    fn partial_cmp(&self, other: &SearchNode) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SearchNode {
    fn cmp(&self, other: &SearchNode) -> Ordering {
        self.board.manhattan().cmp(&other.board.manhattan()).reverse()
    }
}

impl Equivalent<SearchNode> for Board {
    fn equivalent(&self, key: &SearchNode) -> bool {
        self.eq(&key.board)
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
}

impl Solver {
    pub fn new(start: Board, limit: usize) -> Solver {
        let head = SearchNode {
            board: start,
            prev: None,
        };

        let mut seen = IndexSet::new();
        seen.insert(head.clone());

        Solver {
            head: Some((head, 0)),
            seen: seen,
            queue: BinaryHeap::new(),
            best: None,
            limit: limit,
            iters: 0,
        }
    }

    fn depth(&self, mut idx: usize) -> usize {
        let mut depth = 0;
        loop {
            idx = match self.seen.get_index(idx).unwrap().prev {
                Some((_, ref prev_idx)) => *prev_idx,
                None => break,
            };
            depth += 1;
        }
        depth
    }

    pub fn solve(&mut self) -> bool {
        use Direction::*;

        while let Some((ref head, ref head_idx)) = self.head {
            let head_depth = match head.prev {
                Some((_, ref prev_idx)) => self.depth(*prev_idx) + 1,
                None => 0,
            };

            let rev = head.prev.as_ref().map(|p| p.0.rev());
            for dir in [Up, Down, Left, Right].iter() {
                if rev == Some(*dir) {
                    continue;
                }

                if let Some(next_board) = head.board.play_move(*dir) {
                    self.seen.get(&next_board)
                        .and_then(|s| s.prev)
                        .map(|(_, idx)| self.depth(idx));
                }
            }
        }

        /*
        for _ in 0..self.limit {
            let rev = self.head.prev.as_ref().map(|p| p.0.rev());
            for dir in [Up, Down, Left, Right].iter() {
                if rev == Some(*dir) {
                    continue;
                }

                if let Some(next_board) = self.head.board.play_move(*dir) {
                    self.iters += 1;

                    let next = Rc::new(SearchNode {
                        board: next_board,
                        depth: self.head.depth + 1,
                        prev: Some((*dir, self.head.clone())),
                    });

                    let (remove, insert) = if let Some(stored) = self.seen.get(&*next) {
                        if stored.depth > next.depth {
                            (true, true)
                        } else {
                            (false, false)
                        }
                    } else {
                        (false, true)
                    };

                    if remove {
                        self.seen.remove(&*next);
                    }

                    if insert {
                        self.seen.insert(next.clone());
                        self.queue.push(next);
                    }
                }
            }
            self.queue.pop()
        }
        */
        true
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

#[cfg(test)]
mod tests {
    use ::*;
    use Direction::*;

    const LIMIT: usize = 100_000;

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
        ("312045678", Up, Some("012345678")),
        ("812345670", Up, Some("812340675")),
        ("012345678", Down, Some("312045678")),
        ("312045678", Down, Some("312645078")),
        ("812345670", Down, None),
        ("012345678", Left, None),
        ("102345678", Left, Some("012345678")),
        ("210345678", Left, Some("201345678")),
        ("012345678", Right, Some("102345678")),
        ("102345678", Right, Some("120345678")),
        ("210345678", Right, None),
    ];

    static TEST_MANHATTAN: [(&'static str, usize); 3] = [
        ("123456780", 0),
        ("213540678", 9),
        ("647850321", 21),
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
            let mut solver = Solver::new(puzzle, LIMIT);

            let mut answer = puzzle;
            for dir in solver.solve().expect("no solution") {
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
}
