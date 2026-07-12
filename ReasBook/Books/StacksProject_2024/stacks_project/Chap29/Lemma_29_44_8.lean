import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.JacobsonSpace

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-side owner
-- `IsIntegralHom`, while the canonical scheme-theoretic fibre API is owned by
-- `Mathlib.AlgebraicGeometry.Fiber` and closed points are the standard owner
-- `closedPoints`. This file uses that fibrewise closed-point surface rather than restating the
-- claim as a raw singleton-closedness predicate.

/-- Lemma 29.44.8: if `f : X ⟶ S` is an integral morphism, then every point of `X` is closed in
its fibre over `S`. -/
theorem asFiber_mem_closedPoints_of_isIntegralHom
    {X S : Scheme} {f : X ⟶ S} (hf : IsIntegralHom f) (x : X) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) := by
  sorry

end AlgebraicGeometry
