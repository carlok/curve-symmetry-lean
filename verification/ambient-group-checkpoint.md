# Actual ambient-group checkpoint — 2026-09-14

The commit containing this report adds `lean/FamilyAmbientGroup.lean` and
integrates it into the aggregate and Lake roots. Its group consists of actual
sphere permutations in the Möbius action image preserving the spherical curve
in both directions. Scalar-equivalent matrices do not create extra elements.

For `m >= 2`, nonreal `alpha`, and `norm alpha = 1`, every element is either
a dilation with `c^(2*m) = 1` or an inversion with
`c^(2*m) = conjugate(alpha)^2`. Both families have unique parameters and are
disjoint. Their membership lemmas need only `m > 0`. Zero and infinity are
included in the permutation actions. No dihedral isomorphism or count is
asserted by this checkpoint.

Checks: new module and aggregate compiled incrementally with warnings as
errors, using installed dependencies. The complete namespace axiom audit
passed for 1,021 declarations, allowing only `propext`, `Classical.choice`,
and `Quot.sound`. Package preflight passed for 70 modules and nine pins;
all six package tests passed. This was not a clean Linux build, independent
replay, or Palomar dry run. No paper files were edited.

Next: construct the group isomorphism to `DihedralGroup (2*m)` and derive
order `4*m`, using these independently defined actual sphere transformations.
