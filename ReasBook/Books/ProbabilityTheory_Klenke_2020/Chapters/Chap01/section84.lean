import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_1_84 (from Items/Chap01) -/
open MeasureTheory

universe u

variable {Ω : Type u} [TopologicalSpace Ω]

/-- Corollary 1.84: For a subset `A` of a topological space `Ω`, the Borel `σ`-algebra of the
subspace topology on `A` is the trace of the ambient Borel `σ`-algebra along the subtype
inclusion. -/
theorem borel_subtype_eq_comap_subtype_val (A : Set Ω) :
    borel A = (borel Ω).comap (Subtype.val : A → Ω) :=
  borel_comap
