import Mathlib
import StacksProject_2024.Chap12.Lemma_12_14_3
import StacksProject_2024.Chap12.Lemma_12_14_4
import StacksProject_2024.Chap12.Lemma_12_14_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable (S : ShortComplex (ChainComplex 𝒜 ℤ))
variable (σ σ' : ∀ n : ℤ, (ChainComplex.degreewiseShortComplex S n).Splitting)
variable
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

/-
Domain-style sampling for degreewise-split connecting morphisms:
- primary domain: homotopies between connecting morphisms attached to degreewise split short
  complexes.
- owner declarations inspected:
  `CochainComplex.homOfDegreewiseSplit` and `CochainComplex.homOfDegreewiseSplit_f` from mathlib,
  `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference` and its degreewise
  companion theorem from `Lemma_12_14_12`,
  `chainToCochainHomotopyEquiv` from `Lemma_12_14_3`,
  `ChainComplex.homOfDegreewiseSplit` and `chainToCochain` from `Lemma_12_14_4` and
  `Definition_12_14_1`.
- best owner abstraction: the cochain-side homotopy theorem, transported through the chapter
  owner functor `chainToCochain 𝒜`.
- primitive data here: the correction family `h n : C_n ⟶ A_n` and the section-difference
  identity `hs_eq`.
- derived API here: the transported chain homotopy and its degreewise component formula.
-/

noncomputable section

private abbrev transportedShortComplex :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  (chainToCochain 𝒜).mapShortComplex.obj S

private abbrev transportedSplitting
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting) :
    ∀ n : ℤ, ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting :=
  fun n ↦ show ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting from σ (-n)

private abbrev transportedCorrection :
    ∀ n : ℤ, ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₃ ⟶
      ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₁ :=
  fun n ↦ show ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₃ ⟶
      ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).X₁ from -h (-n)

private def shiftMinusOneComparison :
    (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
      (chainToCochain 𝒜).obj (S.X₁⟦(-1 : ℤ)⟧) :=
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj ((chainToCochain 𝒜).obj S.X₁) :=
    rfl
  eqToHom hEq ≫ (((chainToCochain 𝒜).commShiftIso (-1 : ℤ)).app S.X₁).symm.hom

private theorem transportedSectionDifference
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    : CochainComplex.sectionDifference
        (transportedShortComplex S)
        (transportedSplitting S σ')
        (transportedSplitting S σ)
        (transportedCorrection S h) := by
  sorry

-- Proof sketch: write the difference of the two connecting morphisms using the identities
-- `(σ' n).s = (σ n).s + h_n ≫ i_n` and `(σ' n).r = (σ n).r - q_n ≫ h_n`. After expanding
-- degreewise, the cross-term vanishes
-- because `S.f ≫ S.g = 0`, and the remaining terms are exactly the null-homotopic expression
-- determined by the family `h_n : C_n ⟶ A_n`, viewed as maps into the canonical shift `A⟦-1⟧`.
/- Source/core/bridge triage:
- core/canonical owner in this chapter: `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference`
  from `Lemma_12_14_12`
- target item here: a `bridge/view`, transporting that owner statement along
  `cochainComplexEquivalence 𝒜`. -/
/-- Lemma 12.14.6: if a second degreewise splitting differs from the first by maps
`h_n : C_n ⟶ A_n`, then these maps, viewed as morphisms `C_n ⟶ A[-1]_{n + 1}`, give a chain
homotopy between the associated connecting morphisms. -/
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f) :
    Homotopy
      (homOfDegreewiseSplit S σ)
      (homOfDegreewiseSplit S σ') := by
  let T := transportedShortComplex S
  let τ := transportedSplitting S σ
  let τ' := transportedSplitting S σ'
  let e := shiftMinusOneComparison S
  let hs : CochainComplex.sectionDifference T τ' τ (transportedCorrection S h) :=
    transportedSectionDifference S σ σ' h hs_eq
  let H :
      Homotopy
        (CochainComplex.homOfDegreewiseSplit T τ)
        (CochainComplex.homOfDegreewiseSplit T τ') :=
    CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference
      T τ' τ (transportedCorrection S h) hs
  have H' :
      Homotopy
        ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ))
        ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ')) := by
    simpa [e, homOfDegreewiseSplit, T, τ, τ'] using H.compRight e
  exact
    (chainToCochainHomotopyEquiv :
      Homotopy (homOfDegreewiseSplit S σ) (homOfDegreewiseSplit S σ') ≃
        Homotopy
          ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ))
          ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit S σ'))).symm H'

private theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom_comp_shiftMinusOneXIso
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (S.X₁.shiftMinusOneXIso (n + 1)).hom =
      (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
        simpa using h n) := by
  sorry

private theorem correction_comp_shiftIndexIso (n : ℤ) :
    (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
      simpa using h n) ≫
        (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom =
      h n := by
  have e : n + 1 - 1 = n := by omega
  change
    cast (congrArg (fun W : 𝒜 ↦ S.X₃.X n ⟶ W) (congrArg (fun i ↦ S.X₁.X i) e).symm) (h n) ≫
        eqToHom (congrArg (fun i ↦ S.X₁.X i) e) =
      h n
  have hcast := congrArg_cast_hom_right (h n) (congrArg (fun i ↦ S.X₁.X i) e)
  have hpost := congrArg (fun k ↦ k ≫ eqToHom (congrArg (fun i ↦ S.X₁.X i) e)) hcast
  simpa [Category.assoc] using hpost

/-- The homotopy of Lemma 12.14.6 has degree-`n` component given by the correction map
`h_n : C_n ⟶ A_n`, viewed in the shifted target `A[-1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (shiftMinusOneSuccXIso S.X₁ n).hom =
      h n := by
  have hcomp :=
    congrArg
      (fun k ↦ k ≫ (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom)
      (homOfDegreewiseSplit_homotopy_of_splitting_difference_hom_comp_shiftMinusOneXIso
        S σ σ' h hs_eq n)
  calc
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (shiftMinusOneSuccXIso S.X₁ n).hom =
      (show S.X₃.X n ⟶ S.X₁.X (n + 1 - 1) by
        simpa using h n) ≫
          (S.X₁.XIsoOfEq (show n + 1 - 1 = n by omega)).hom := by
        simpa [shiftMinusOneSuccXIso, Category.assoc] using hcomp
    _ = h n := correction_comp_shiftIndexIso S h n

end

end ChainComplex
