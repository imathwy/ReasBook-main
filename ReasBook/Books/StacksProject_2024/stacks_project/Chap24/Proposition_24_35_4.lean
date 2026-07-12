import Mathlib
import StacksProject_2024.Chap15.Lemma_15_93_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe uR uQ vQ uK vK

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

-- Semantic recall note: `lean_leansearch` returned only generic derived-category hits here, so
-- the owner/API choice was checked against the local Chapter 15 derived-complete owner
-- `DerivedCategory.derivedCompleteObjectProperty` and the Chapter 24 equivalence criteria
-- `Lemma_24_30_1` and `Lemma_24_34_2`.

section

variable {R : Type uR} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

local notation "DComp" =>
  ObjectProperty.FullSubcategory (derivedCompleteObjectProperty (A := R) I)

/-- Proposition 24.35.4 (1): for a Noetherian ring `R` and an ideal `I ⊆ R`, let
`\mathcal A` be the sheaf of `R`-algebras on `\mathbf N` coming from the quotient tower
`A_n = R / I^n`. If the chosen functor from the full subcategory `D_{comp}(R, I)` of
`I`-derived-complete objects of `D(R)` to `QC(\mathcal A)` has a chosen right adjoint whose
kernel is zero and whose adjunction unit is an isomorphism on every derived-complete object, then
this functor is an equivalence. This is the source-facing `QC(\mathcal A) ≃ D_{comp}(R, I)`
clause of the proposition. -/
@[stacks 0GZK]
theorem derivedCompleteToQuotientTowerQC_isEquivalence
    {QCA : Type uQ} [Category.{vQ} QCA]
    (quotientTowerPullback : DComp ⥤ QCA)
    (quotientTowerPushforward : QCA ⥤ DComp)
    (adj : quotientTowerPullback ⊣ quotientTowerPushforward)
    (hunit : ∀ K : DComp, IsIso (adj.unit.app K))
    (hkernel : quotientTowerPushforward.kernel ≤ CategoryTheory.Limits.IsZero) :
    Functor.IsEquivalence quotientTowerPullback := sorry

/-- Proposition 24.35.4 (2): for a Noetherian ring `R`, an ideal `I ⊆ R`, and generators
`f_1, \ldots, f_r` of `I`, let `\mathcal B` be the sheaf of differential graded `R`-algebras on
`\mathbf N` given by the powered Koszul tower on `f_1^n, \ldots, f_r^n`. If the chosen functor
from `D_{comp}(R, I)` to `QC(\mathcal B)` has a chosen right adjoint whose kernel is zero and
whose adjunction unit is an isomorphism on every derived-complete object, then this functor is an
equivalence. This is the source-facing `QC(\mathcal B) ≃ D_{comp}(R, I)` clause of the
proposition. -/
@[stacks 0GZK]
theorem derivedCompleteToKoszulTowerQC_isEquivalence
    {QCB : Type uK} [Category.{vK} QCB]
    {r : ℕ} (f : Fin r → R) (hf : Ideal.span (Set.range f) = I)
    (koszulTowerPullback : DComp ⥤ QCB)
    (koszulTowerPushforward : QCB ⥤ DComp)
    (adj : koszulTowerPullback ⊣ koszulTowerPushforward)
    (hunit : ∀ K : DComp, IsIso (adj.unit.app K))
    (hkernel : koszulTowerPushforward.kernel ≤ CategoryTheory.Limits.IsZero) :
    Functor.IsEquivalence koszulTowerPullback := sorry

end

end CategoryTheory.DerivedCategory
