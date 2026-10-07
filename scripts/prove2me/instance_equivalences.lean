/-
Instance paths that differ between the original library and the merged definition
files (a merged file imports the Mathlib modules of all its source modules, so
instance search can take another, equal path). Each pair is proved equal here, at
reducible-and-instances transparency; the checks `type_diff.py` and `def_diff.py`
identify the pairs listed in `INSTANCE_EQUIV` only after this file compiles.
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.GroupTheory.GroupAction.Ring

example (R : Type*) [NonUnitalNonAssocSemiring R] :
    (instDistribSMul : DistribSMul R R) = NonUnitalNonAssocSemiring.toDistribSMul := by
  with_reducible_and_instances rfl
