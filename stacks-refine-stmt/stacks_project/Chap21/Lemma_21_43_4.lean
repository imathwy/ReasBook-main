import Mathlib
import stacks_project.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable (X : C)

/-- The derived category `D(\mathcal O(X))` of modules over the ring of sections at the chosen
object `X`. -/
abbrev terminalSectionsDerived :=
  DerivedCategory (ModuleCat (𝒪.obj (op X)))

/-- The restriction of the derived pushforward `Rf_*` for the obvious morphism
`(\mathcal C,\mathcal O) \to (pt,\mathcal O(X))` to the quasi-coherent full subcategory. In this
formalization it is the evaluation functor `R\Gamma(X,-)` on objects satisfying the defining
comparison isomorphisms. -/
abbrev rightDerivedPushforwardFromQC :
    QC 𝒪 RGamma derivedRestrict comparison ⥤ terminalSectionsDerived 𝒪 X :=
  (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).ι ⋙ RGamma X

/-- The restriction of a candidate derived pullback `Lf^* : D(\mathcal O(X)) \to D(\mathcal O)`
to the quasi-coherent full subcategory, assuming its essential image is quasi-coherent. -/
abbrev leftDerivedPullbackToQC
    (Lf : terminalSectionsDerived 𝒪 X ⥤ D)
    (hLf_mem : ∀ K : terminalSectionsDerived 𝒪 X,
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ((Lf).obj K)) :
    terminalSectionsDerived 𝒪 X ⥤ QC 𝒪 RGamma derivedRestrict comparison :=
  ObjectProperty.lift
    (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison)
    Lf
    hLf_mem

-- Proof sketch: for the terminal object `X`, identify `Rf_*` with `R\Gamma(X,-)`, restrict it to
-- `QC(\mathcal O)`, and restrict `Lf^*` along the defining object property. The given unit and
-- counit isomorphism hypotheses are exactly the data needed to show that the restricted `Lf^*`
-- is an equivalence with quasi-inverse the restricted `Rf_*`.
/-- Lemma 21.43.4: if `X` is a final object of `\mathcal C`, set `R = \mathcal O(X)` and let
`f : (\mathcal C,\mathcal O) \to (pt,R)` be the obvious morphism of ringed sites. Then
`QC(\mathcal O)` is equivalent to `D(R)`, with quasi-inverse functors given by the derived
pullback `Lf^*` and the derived pushforward `Rf_* = R\Gamma(X,-)`. -/
theorem leftDerivedPullbackToQC_isEquivalence
    (hX : Limits.IsTerminal X)
    (Lf : terminalSectionsDerived 𝒪 X ⥤ D)
    (hLf_mem : ∀ K : terminalSectionsDerived 𝒪 X,
      isQuasiCoherent 𝒪 RGamma derivedRestrict comparison ((Lf).obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : terminalSectionsDerived 𝒪 X, IsIso (adj.unit.app K))
    (hcounit : ∀ K : QC 𝒪 RGamma derivedRestrict comparison,
      IsIso (adj.counit.app K.obj)) :
    Functor.IsEquivalence
      (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem) := sorry

end

end CategoryTheory.ModulesOnCategory
