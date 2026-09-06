

## Usage

    luatrix <input> <out>

The command accepts exactly two positional arguments: the input Lua/Luau source file and the output path.

## Native pipeline

The single-file implementation in `src/luatrix.cpp` contains:

- Clyde-shaped lexer and recoverable source diagnostics
- Recursive expression/statement traversal with Luau type declarations preserved as opaque source
- Local-symbol rewriting that avoids keywords and member/property names
- Runtime XOR string reconstruction
- Opaque control-flow guards for supported conditional and loop forms
- Stack and register bytecode models used to build per-output dispatch metadata
- Fresh numeric opcode IDs and decoy handlers for every generated output
- RLE-compressed source reconstruction and a protected LTRIX bootstrap
- Anti-tamper and active-debug-hook checks

The output remains source-compatible by executing the reconstructed Lua/Luau chunk through the target runtime. The original Clyde TypeScript implementation under `vendor/clyde/src` remains the behavioral reference for future parity work.

## Randomized opcodes

Opcode IDs are shuffled for each output. The generated dispatcher emits a new mapping, code stream, and handler table each time, so a semantic operation does not have a stable public numeric identity.

## Watermark

Generated files begin with the LTRIX identity marker.

## Build

    g++ -std=c++17 -O2 -Wall -Wextra -pedantic src/luatrix.cpp -o luatrix
