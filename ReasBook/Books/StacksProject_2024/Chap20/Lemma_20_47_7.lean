import Mathlib
import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

/-- A cochain complex of `\mathcal O_X`-modules is locally bounded above if every point has an
open neighborhood on which the restricted complex vanishes in all sufficiently high degrees. -/
def CochainComplex.IsLocallyBoundedAbove (K : CochainComplex (RingedSpace.Modules X) ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ b : ℤ, ((moduleComplexRestrictionToOpen X U).obj K).IsStrictlyLE b

-- Proof sketch: choose the top open `⊤` as a neighborhood of every point and reuse the same
-- global upper bound after restricting the complex to `⊤`.
/-- A bounded-above complex of `\mathcal O_X`-modules is locally bounded above. -/
theorem cochainComplex_isLocallyBoundedAbove_of_boundedAbove
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (hK : ∃ b : ℤ, K.IsStrictlyLE b) :
    CochainComplex.IsLocallyBoundedAbove K := sorry

-- Proof sketch: for each point, choose an open neighborhood on which `K` is bounded above. Apply
-- the truncation argument of Lemma `15.65.9` to the restricted complex on that neighborhood,
-- using Lemma `20.47.4` for the induction step on stupid truncation triangles. This gives local
-- derived `m`-pseudo-coherence of the restriction, and Lemma `20.47.2` converts the resulting
-- derived statement back to the restricted cochain complex, which is exactly the local data
-- required in Definition `20.47.1`.
/-- Lemma 20.47.7: a locally bounded-above cochain complex of `\mathcal O_X`-modules whose term
in degree `i` is `(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
theorem cochainComplex_isMPseudoCoherent_of_locallyBoundedAbove_of_termwise
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ)
    (hbounded : CochainComplex.IsLocallyBoundedAbove K)
    (hterm : ∀ i : ℤ, IsMPseudoCoherent ((single0).obj (K.X i)) (m - i)) :
    CochainComplex.IsMPseudoCoherent K m := sorry

end AlgebraicGeometry.RingedSpace
