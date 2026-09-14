# Package 4, first part — 2026-09-14

The introducing commit adds FamilyEuclidean and integrates it into Lake and
the aggregate. For m>=2 and normalized nonreal alpha, it proves that no
nondegenerate conjugate-affine map even sends the plane curve into itself.
This follows by extending the affine map to an actual sphere action and
applying the previously proved no-anti-Möbius theorem.

Consequences: no opposite Euclidean symmetries, including m=2; every actual
Euclidean self-isometry has the direct affine form. The older unnormalized
m>=3 theorem is retained, since its hypotheses differ.

The new module and aggregate compiled incrementally with warnings as errors.
Full namespace audit: 1,085 declarations, only propext, Classical.choice and
Quot.sound. Source preflight: 72 modules, nine pins. Six package tests passed.
TeX/PDF hashes are unchanged. Installed dependencies were reused, not modified.

The preceding package 3 commit 8d34a48 passed private Linux runs 34848016730
and 34848016706. This checkpoint needs its own CI result. No clean local build,
independent replay, or Palomar dry run is claimed.

Package 4 remains incomplete: eliminate the translation term, identify the
exact root rotations, and package the actual full Euclidean-group count.
