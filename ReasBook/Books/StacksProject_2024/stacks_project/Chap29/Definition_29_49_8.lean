import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

-- Semantic recall: mathlib already provides the canonical owner `Scheme.RationalMap.domain` and
-- the exact source-facing pointwise criterion `Scheme.RationalMap.mem_domain`. This file therefore
-- keeps the canonical owner primary and adds only the companion statement identifying the domain
-- as the set of points where some representative is defined.

variable {X Y : Scheme}

/- Definition 29.49.8 (1): a rational map `φ : X.RationalMap Y` is defined at a point `x : X`
exactly when some representative of `φ` has domain containing `x`. -/
#check RationalMap.mem_domain

/-- Definition 29.49.8 (2): the domain of definition of a rational map `φ : X.RationalMap Y` is
the set of points where `φ` is defined. -/
theorem rationalMap_domain_def (φ : X.RationalMap Y) :
    (φ.domain : Set X) = {x | ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = φ} := by
  ext x
  exact RationalMap.mem_domain

end AlgebraicGeometry.Scheme
