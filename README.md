# Syntax, Semantics & Compiler for a Conceptual Language

### Developed for: Principles of Programming Languages - Year 2

## Task

Develop the syntax, semantics and a compiler for a conceptual programming language using Coq to prove its soundness.

## Description

The `Zeno_Final.v` file encapsulates the Syntax and Semantics part and includes:

- Data Types
*(built like the Result type in Rust - Wrapper including value and error)*
  - Basic Types
    - Natural Numbers
    - Boolean Values
    - Character Strings
  - Complex Data Types
    - Linked Lists
    - Arrays 
    *(built on lists)*
    - Enums
    - Structs 
- Collective Data Types
  - Unassigned
  - ResultTypes

- Expression Syntax
  - Arithmetics
  - Boolean Algebra
  - Comparisons
  
- Statement Syntax
  - Declaration
  - Assignment
  - Initialisation
  - List Operations
  - Array Operations
  - Control-Flow Statements
    - If-Then-Else
    - While, Do-While, For
    - Switch
    - Break, Continue
    
- Semantics

- Proofs of Soundness

The `Zeno_Compiler.v` file encompasses the compiler for the above, alongside proofs.

## How to Run

You need to install The Coq Proof Assistant, you can do that from [here](https://coq.inria.fr/download).

Then, just import the two files and run line by line or as a whole, browsing through the provided examples.

## Useful Links

[The Coq Proof Assistant Documentation](https://coq.inria.fr/documentation)
[The Principles of Programming Languages Course](https://profs.info.uaic.ro/~arusoaie.andrei/lectures/PLP/plp.html)
