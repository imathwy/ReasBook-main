import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The object property on `TopCat` selecting Hausdorff weakly locally compact spaces. -/
abbrev HausdorffWeaklyLocallyCompactObject : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ WeaklyLocallyCompactSpace X

/-- The category of Hausdorff locally quasi-compact spaces used for `LC_{qc}`. -/
abbrev LCCat : Type (u + 1) :=
  HausdorffWeaklyLocallyCompactObject.FullSubcategory

namespace CategoryTheory.GrothendieckTopology

section

variable (ZarSheaf QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (ZarSheaf X)]
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, Abelian (ZarSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (ZarSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasInjectiveResolutions (QcSheaf X)]

variable (piInverseAb :
  ∀ X : LCCat.{u}, TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤ ZarSheaf X)
variable (aInverseAb :
  ∀ X : LCCat.{u}, TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤ QcSheaf X)
variable (epsilonPushforwardAb : ∀ X : LCCat.{u}, QcSheaf X ⥤ ZarSheaf X)
variable [∀ X : LCCat.{u}, Functor.Additive (epsilonPushforwardAb X)]

variable (piInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (ZarSheaf X))
variable (aInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (QcSheaf X))
variable (rEpsilonPushforward :
  ∀ X : LCCat.{u}, DerivedCategory (QcSheaf X) ⥤ DerivedCategory (ZarSheaf X))
variable (smallPushforwardDerived :
  ∀ {X Y : LCCat.{u}} (_ : X ⟶ Y),
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} Y.obj))
variable (qcPushforwardDerived :
  ∀ {X Y : LCCat.{u}} (_ : X ⟶ Y),
    DerivedCategory (QcSheaf X) ⥤ DerivedCategory (QcSheaf Y))

/-- The bounded-below condition on the derived category of small abelian sheaves on an `LC`
object. -/
private def smallAbDerivedBoundedBelow (X : LCCat.{u}) :
    ObjectProperty (DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)) :=
  fun K ↦
    ∃ n : ℤ, ∀ i : ℤ, i < n →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor
          (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) i).obj K)

-- Proof sketch: this is the underived comparison statement obtained by pushing forward the
-- canonical qc pullback `a_X^{-1}\mathcal F` along `\epsilon_X` and identifying the result with
-- the big-Zariski pullback `π_X^{-1}\mathcal F`.
/-- Lemma 21.31.10 (1): for `X ∈ LC_{qc}` and an abelian sheaf `\mathcal F` on `X`, the chosen
comparison pushforward formalizing `\epsilon_{X,*}` sends `a_X^{-1}\mathcal F` to
`π_X^{-1}\mathcal F`. -/
theorem comparisonPushforward_aInverseAb_isomorphic_piInverseAb
    (X : LCCat.{u})
    (ℱ : TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) :
    IsIsomorphic
      ((epsilonPushforwardAb X).obj ((aInverseAb X).obj ℱ))
      ((piInverseAb X).obj ℱ) := sorry

-- Proof sketch: compute the higher right derived functors of the comparison pushforward on the
-- qc pullback `a_X^{-1}\mathcal F`; the comparison situation forces the positive-degree terms to
-- vanish.
/-- Lemma 21.31.10 (2): for `X ∈ LC_{qc}` and an abelian sheaf `\mathcal F` on `X`, the higher
derived direct images `R^i \epsilon_{X,*}(a_X^{-1}\mathcal F)` vanish for `i > 0`. -/
theorem higherComparisonPushforward_aInverseAb_isZero
    (X : LCCat.{u})
    (ℱ : TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero
      (((epsilonPushforwardAb X).rightDerived i).obj ((aInverseAb X).obj ℱ)) := sorry

-- Proof sketch: apply the derived comparison theorem to the bounded-below object `K`. The chosen
-- derived pullbacks formalizing `π_X^{-1}` and `a_X^{-1}` identify the resulting comparison with
-- `π_X^{-1}K \to R\epsilon_{X,*}(a_X^{-1}K)`.
/-- Lemma 21.31.10 (3): for `X ∈ LC_{qc}` and a bounded-below derived abelian sheaf `K` on `X`,
the canonical map `π_X^{-1}K \to R \epsilon_{X,*}(a_X^{-1}K)` is an isomorphism. -/
theorem piInverseDerived_isomorphic_rComparisonPushforward_aInverseDerived
    (X : LCCat.{u})
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIsomorphic
      ((piInverseDerived X).obj K)
      ((rEpsilonPushforward X).obj ((aInverseDerived X).obj K)) := sorry

-- Proof sketch: combine proper base change on the small Zariski site with the derived comparison
-- for `\epsilon_Y`. The chosen derived direct images formalizing `Rf_*` and `R f_{qc,*}` then
-- identify `a_Y^{-1}(Rf_* K)` with `R f_{qc,*}(a_X^{-1}K)`.
/-- Lemma 21.31.10 (4): for a proper morphism `f : X \to Y` in `LC_{qc}` and a bounded-below
derived abelian sheaf `K` on `X`, the inverse image `a_Y^{-1}(Rf_* K)` is canonically
isomorphic to `R f_{qc,*}(a_X^{-1}K)`. -/
theorem proper_aInverseDerived_smallPushforward_isomorphic_qcPushforwardDerived
    {X Y : LCCat.{u}}
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIsomorphic
      ((aInverseDerived Y).obj ((smallPushforwardDerived f).obj K))
      ((qcPushforwardDerived f).obj ((aInverseDerived X).obj K)) := sorry

end

end CategoryTheory.GrothendieckTopology
