import Mathlib.RingTheory.Length
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section Length

open Order

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [Ring S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable [Module R M] [IsScalarTower R S M]

namespace Module

/-- Lemma 10.52.5 (1), in the canonical library-facing scalar-tower form: if an `S`-module `M`
is also an `R`-module compatibly with `R → S`, then the length of `M` over `R` is at least its
length over `S`. Specializing to the induced `R`-module structure recovers the Stacks-project
statement for restriction of scalars along `R → S`. -/
-- Proof sketch: every chain of `S`-submodules of `M` is also a chain of `R`-submodules, so the
-- Krull dimension of `Submodule S M` is bounded above by that of `Submodule R M`.
@[stacks 00IX]
theorem length_le_restrictScalars : length S M ≤ length R M := by
  let e := Submodule.restrictScalarsEmbedding R S M
  simpa [length_eq_height] using height_le_height_apply_of_strictMono e e.strictMono ⊤

end Module

/- Lemma 10.52.5 (2), in the same scalar-tower form: if `algebraMap R S` is surjective, then the
length of `M` is unchanged when passing between the compatible `R`- and `S`-module structures.
Specializing to the induced `R`-module structure recovers the Stacks-project statement. This is
exactly the canonical theorem `Module.length_eq_of_surjective`. -/
#check (Module.length_eq_of_surjective :
  Function.Surjective (algebraMap R S) → Module.length R M = Module.length S M)

end Length
