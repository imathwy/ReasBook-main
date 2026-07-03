import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape HomologicalComplex

universe u v

namespace CategoryTheory
namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (S : ShortComplex (CochainComplex V ℤ))

/- Domain-style sampling:
- primary domain: degreewise split short complexes of cochain complexes and the homotopies
  comparing the owner connecting morphisms `CochainComplex.homOfDegreewiseSplit`.
- inspected owner declarations: `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit_f`,
  `CochainComplex.shiftFunctorObjXIso`,
  `ChainComplex.degreewiseShortComplex` from `Lemma_12_14_4`.
- best owner abstraction: `CochainComplex.homOfDegreewiseSplit`.
- primitive data in this file: the degreewise short complex, two degreewise splittings, and the
  section-difference family `h`.
- derived API in this file: the induced homotopy between the two owner connecting morphisms and
  its degreewise component formula. -/

/-- The short complex obtained by evaluating a short complex of cochain complexes in degree `n`.
-/
abbrev degreewiseShortComplex (S : ShortComplex (CochainComplex V ℤ)) (n : ℤ) :=
  S.map (HomologicalComplex.eval V (up ℤ) n)

variable
  (spl spl' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

/-- The second degreewise splitting differs from the first by the section corrections `h^n`. -/
abbrev sectionDifference : Prop :=
  ∀ n : ℤ, (spl' n).s = (spl n).s + h n ≫ (degreewiseShortComplex S n).f

private theorem retraction_eq_sub_section_correction
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (spl' n).r = (spl n).r - (degreewiseShortComplex S n).g ≫ h n := by
  sorry

-- Proof sketch: use that each degreewise splitting satisfies `r ≫ s = 0`. Expanding
-- `(spl' n).r = (spl n).r + g^n ≫ q^n` and the derived formula
-- `(spl' n).r = (spl n).r - q^n ≫ h^n` coming from `ShortComplex.Splitting.ext_s`, then precompose
-- with `(spl n).s`. The identities `(spl n).s ≫ (spl n).r = 0` and `(spl n).s ≫ q^n = 𝟙`
-- leave exactly `g^n + h^n = 0`.
/-- Lemma 12.14.12 (1): if a second degreewise splitting differs from the first one by correction
maps `h^n` on the section side and `g^n` on the retraction side, then these corrections satisfy
`g^n = -h^n` in every degree. -/
theorem retraction_correction_eq_neg_section_correction
    (k : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)
    (hs : sectionDifference S spl spl' h)
    (hr' : ∀ n : ℤ,
      (spl' n).r = (spl n).r + (degreewiseShortComplex S n).g ≫ k n)
    (n : ℤ) :
    k n = -h n := by
  sorry

-- Proof sketch: the retraction correction is canonically `-h^n`, so these maps, viewed in the
-- shifted target `A^•[1]`, form the degreewise components of a homotopy from the connecting
-- morphism attached to `spl'` to the one attached to `spl`. The homotopy relation is exactly the
-- standard textbook identity for the two connecting morphisms.
/- Source/core/bridge triage:
- source-facing: correction maps comparing two degreewise splittings of the same short complex.
- core/canonical owner: `homOfDegreewiseSplit`.
- target item here: a bridge/view giving the induced homotopy between the two owner maps. -/
/-- Lemma 12.14.12: the correction maps between two degreewise splittings define a homotopy from
the connecting morphism attached to `spl'` to the one attached to `spl`. -/
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs : sectionDifference S spl spl' h) :
    Homotopy
      (CochainComplex.homOfDegreewiseSplit S spl')
      (CochainComplex.homOfDegreewiseSplit S spl) where
  hom i j :=
    if hij : (up ℤ).Rel j i then
      (-h i) ≫
        (S.X₁.shiftFunctorObjXIso 1 (i - 1) i (Int.sub_add_cancel i 1).symm).inv ≫
          ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (by
            have hij' : j + 1 = i := by simpa [up_Rel] using hij
            omega)).hom
    else
      0
  zero i j hij := by
    dsimp
    split_ifs with hrel
    · exact (hij hrel).elim
    · rfl
  comm n := by
    sorry

/-- The degree-`n` component of the homotopy from Lemma 12.14.12 is the correction map
`-h^n : C^n ⟶ A^n`, viewed inside the shifted target `A^•[1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference S spl spl' h hs).hom n (n - 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).hom =
      -h n := by
  sorry

end

end CochainComplex
end CategoryTheory
