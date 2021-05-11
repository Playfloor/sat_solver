# Boolean Satisfiability Solver
This is a simple boolean satisfiability solver built in the Jai Programming Language that uses the DPLL algorithm to solve the boolean satisfiability problem. Specifically, this solver uses Conflict-Driven Clause Learning to speed up DPLL.

# Implmentation
This program takes in a *.cnf file in the DIMACS format, and determines whether the boolean equation is satisfiable or not.

DIMACS file formats have the following format:
```
c This is a comment
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0
```
The `p cnf 5 3` indicates that there are 5 boolean values to solve and 3 clauses to solve for.

# Benchmarks
You can run the sat solver against sat problems encoded here: https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html

# Resources
Boolean Satisfiability Solver https://en.wikipedia.org/wiki/Boolean_satisfiability_problem

DPLL Algorithm: https://en.wikipedia.org/wiki/DPLL_algorithm

Conflict Driven Clause Learning: https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning

DIMACS format: http://www.satcompetition.org/2004/format-solvers2004.html
