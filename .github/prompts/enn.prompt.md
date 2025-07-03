---
mode: 'agent'
---

Have a look whether you can make the construction of the ennreal_arith tactic more error-proof, readable, maintainable, shorter, more idiomatic and simpler. 

Convert it from a macro into  a real tactic.

This tactic should work with more kinds of expressions, not just for a * (b / c) = d / e from a * b * e = d * c. Have a look how tactics like norm_num, field_simp and linarith work. You probably have to do something similar. Clear the denominators and then normalise multiplicative and additive expressions of both sides of the equality so that you can verify one of the assumptions or a combination of assumptions proves the goal


Use output of MCP server to correct errors along the way