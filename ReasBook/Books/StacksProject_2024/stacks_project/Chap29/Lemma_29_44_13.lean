import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- `AlgebraicGeometry.IsFinite` is the canonical finiteness owner for scheme morphisms, and
-- `AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc` is the canonical coproduct bridge for
-- Zariski-local-at-source morphism properties.

section

variable {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)

/-- Lemma 29.44.13: if `X i ⟶ Y` is finite for every `i`, then the induced morphism from
the coproduct `∐ i, X i` to `Y` is finite. The source's finite-coproduct statement is the
special case where `ι` is finite. -/
theorem finite_sigma_desc [Finite ι] (hf : ∀ i, IsFinite (f i)) :
    IsFinite (Sigma.desc f) := by
  sorry

end

end AlgebraicGeometry
