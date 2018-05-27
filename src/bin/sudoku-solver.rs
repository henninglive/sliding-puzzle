extern crate sliding_puzzle as ss;

fn main() {
    let data = std::env::args()
        .skip(1)
        .flat_map(|arg| arg.chars().collect::<Vec<_>>())
        .filter_map(|c| c.to_digit(10).map(|i| i as u8))
        .collect::<Vec<_>>();

    let cells = data.get(..ss::SIZE)
        .expect("Incomplete board");

    let mut board = ss::Board::new(cells)
        .expect("Invalid board");

    print!("Start board:\n{}\n", board);

    let moves = board.solve();
    println!("Solved in {} moves:\n{:?}", moves.len(), moves);

    for m in moves {
        board = board.play_move(m)
            .expect("Invalid move");
    }

    print!("\nEnd board:\n{}", board);
}
