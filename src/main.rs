extern crate sliding_puzzle as sp;

/*
use sp::*;

const LIMIT: usize = 1_000_000;
const OPT_NUM: usize = 1_000;

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
*/

fn main() {
    /*
    for &(board, solutions) in TEST_SOLUTIONS.iter() {
        let puzzle = board.parse::<Board>().unwrap();
        let mut solver = Solver::new(puzzle, LIMIT);

        println!("{:?}", board);

        let d = (0..OPT_NUM)
            .map(|_| {
                print!("{:?} ", solver.len());
                solver.solve()
                    .expect(&format!("no solution {}", solver.iters))
                    .iter()
                    .map(|m| char::from(*m))
                    .collect::<String>()
            })
            .inspect(|v| println!("{:?}", v))
            .find(|s| solutions.contains(&s.as_str()));

        assert!(d.is_some());
    }
    */
}
