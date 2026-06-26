module

public import HexGramSchmidt.Int.Core
public import HexGramSchmidt.Int.Canonical
public import HexGramSchmidt.Int.Combination

public section

/-!
Executable Gram-determinant and scaled-coefficient surface for
`hex-gram-schmidt`: Gram determinants of leading principal minors, their
vector packaging, and the integral scaled Gram-Schmidt coefficient matrix
used downstream by LLL, together with the canonical-coefficient correctness
machinery and the integer row-combination support. Split by subject across
`HexGramSchmidt/Int/*`; this module re-exports them.
-/
