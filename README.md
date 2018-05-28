# sliding-puzzle
Sliding puzzel solver written in rust. The solver applies an A* search algorithm with manhattan distance as a heuristic function.

### Example
```text
$ sliding-puzzle 012345678
Start board:
012
345
678

Solved in 22 moves:
[Right, Down, Left, Down, Right, Right, Up, Left, Left, Down, Right, Up, Up, Right, Down, Down, Left, Left, Up, Right, Right, Down]

End board:
123
456
780
```

### Usage
The CLI will read 3x3/9 numbers from the command line arguments and will ignore all other characters.
This means you can format the board anyway you want. Number 0 is the empty cell.
```text
$ sliding-puzzle 012 345 678

$ sliding-puzzle "012
                  345
                  678"
```

### Build and Run
1. Ensure you have current version of `cargo` and [Rust](https://www.rust-lang.org/) installed
2. Clone the project `$ git clone https://github.com/henninglive/sliding-puzzle/ && cd sliding-puzzle`
3. Build the project `$ cargo build --release` (NOTE: There is a large performance differnce when compiling without optimizations, so I recommend alwasy using `--release` to enable to them)
4. Once complete, the binary will be located at `target/release/sliding-puzzle`
5. Use `$ cargo run --release -- 012345678` to build and then run, in one step
