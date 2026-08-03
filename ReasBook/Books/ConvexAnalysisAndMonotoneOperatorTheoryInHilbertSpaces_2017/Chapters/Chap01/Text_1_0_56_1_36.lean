import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.56 (1.36): the limit inferior of an extended-real-valued function `f` at `x` is the
filter `liminf` of `f` along the neighborhood filter `nhds x`. -/
noncomputable abbrev liminfAt (f : X → EReal) (x : X) : EReal :=
  liminf f (nhds x)

/-- The textbook neighborhood formula for the pointwise limit inferior. -/
-- Proof sketch: unfold `liminfAt` and specialize the standard filter formula for `Filter.liminf`
-- to the neighborhood filter `nhds x`.
theorem liminfAt_eq_sSup_nhds_sInf (f : X → EReal) (x : X) :
    liminfAt f x = sSup ((fun V : Set X ↦ sInf (f '' V)) '' {V : Set X | V ∈ nhds x}) := by
  simpa [liminfAt] using (liminf_eq_sSup_sInf (nhds x) f)

end ERealFunction
