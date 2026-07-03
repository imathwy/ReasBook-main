import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: combine Lemma `20.49.5`, which characterizes perfect objects by
-- pseudo-coherence and local finite tor dimension, with Lemma `20.47.4 (1)` for the
-- pseudo-coherent part and Lemma `20.48.6 (1)` for the tor-amplitude part on each member of a
-- local open cover.
/-- Lemma 20.49.7 (1): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `K` and `L` are
perfect, then `M` is perfect. -/
theorem isPerfect_obj₃_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₂ : DerivedCategory.IsPerfect T.obj₂) :
    DerivedCategory.IsPerfect T.obj₃ := sorry

-- Proof sketch: use Lemma `20.49.5` to reduce perfectness to pseudo-coherence plus local finite
-- tor dimension; then apply Lemma `20.47.4 (2)` and Lemma `20.48.6 (2)` to the distinguished
-- triangle and reassemble the two conditions.
/-- Lemma 20.49.7 (2): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `K` and `M` are
perfect, then `L` is perfect. -/
theorem isPerfect_obj₂_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₂ := sorry

-- Proof sketch: again reduce via Lemma `20.49.5`, then use Lemma `20.47.4 (3)` for
-- pseudo-coherence and Lemma `20.48.6 (3)` for the local tor-amplitude bounds to propagate
-- perfectness to the first vertex.
/-- Lemma 20.49.7 (3): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `L` and `M` are
perfect, then `K` is perfect. -/
theorem isPerfect_obj₁_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : DerivedCategory.IsPerfect T.obj₂) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₁ := sorry

end AlgebraicGeometry.RingedSpace
