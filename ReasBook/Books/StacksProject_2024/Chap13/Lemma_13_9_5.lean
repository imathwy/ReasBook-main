import Mathlib
import StacksProject_2024.Chap13.Definition_13_9_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {A B C D : CochainComplex V ℤ}
variable {f : A ⟶ B} {a : A ⟶ C} {b : B ⟶ D} {g : C ⟶ D}

local notation "Q" => quotient V (up ℤ)

/- Domain-style sampling for Lemma 13.9.5:
- primary domain: homotopy-commutative squares of cochain-complex morphisms together with
  termwise split mono/epi hypotheses on one side of the square;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `HomotopyCategory.quotient`,
  `HomotopyCategory.homotopyOfEq`,
  `CategoryTheory.IsSplitMono`,
  `CategoryTheory.IsSplitEpi`;
- best owner abstraction: the source-facing compatibility datum is a homotopy
  `Homotopy (f ≫ b) (a ≫ g)` between the two composites; the canonical core/view of that datum is
  the square `CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g)` in the homotopy category,
  while the termwise splitting assumptions remain the direct componentwise owners from
  `Definition_13_9_4`;
- primitive data: the four maps `f`, `a`, `b`, `g`, together with the componentwise split
  structure on `f.f n` or `g.f n`, and the chosen homotopy witnessing up-to-homotopy
  commutativity;
- derived API: the quotient-square reformulation of “commutes up to homotopy” via
  `HomotopyCategory.homotopyOfEq`, and equality of quotient classes of a replacement map via
  `HomotopyCategory.eq_of_homotopy`.

Source/core/bridge triage:
- `source-facing`: the two strictification existence lemmas below, phrased as existence of a
  homotopic strictifying replacement with a chosen homotopy
  `Homotopy (f ≫ b) (a ≫ g)`;
- `core/canonical`: `CommSq` for square-shaped compatibility in the homotopy category and the
  per-component owners `IsSplitMono` / `IsSplitEpi`;
- `bridge/view`: the `CommSq` above, formed using the canonical quotient functor `Q`, as the
  homotopy-category reformulation of the source hypothesis, and
  equality of quotient classes via `eq_of_homotopy`.
-/

-- Proof sketch: choose degreewise retractions of the split monomorphism `f`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those retractions to obtain a
-- correction term on `B`. Subtracting the associated null-homotopic map from `b` gives a map
-- homotopic to `b` whose composite with `f` is exactly `a ≫ g`.
/-- Lemma 13.9.5 (1): if a square of morphisms of cochain complexes commutes up to homotopy and
the top map is termwise split monic, then the right map is homotopic to a morphism making the
square commute strictly. -/
theorem exists_homotopic_rightMap_of_termwiseSplitMono
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ (b' : B ⟶ D) (hbb' : Homotopy b b'), CommSq f a b' g := sorry

/-- Bridge/view form of Lemma 13.9.5 (1): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `b` there. -/
theorem exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ b' : B ⟶ D, (Q).map b = (Q).map b' ∧ CommSq f a b' g := by
  obtain ⟨b', hbb', hsq⟩ :=
    exists_homotopic_rightMap_of_termwiseSplitMono
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitMono
  exact ⟨b', eq_of_homotopy _ _ hbb', hsq⟩

-- Proof sketch: choose degreewise sections of the split epimorphism `g`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those sections to obtain a
-- correction term on `A`. Adding the associated null-homotopic map to `a` gives a map homotopic
-- to `a` whose composite with `g` is exactly `f ≫ b`.
/-- Lemma 13.9.5 (2): if a square of morphisms of cochain complexes commutes up to homotopy and
the bottom map is termwise split epi, then the left map is homotopic to a morphism making the
square commute strictly. -/
theorem exists_homotopic_leftMap_of_termwiseSplitEpi
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ (a' : A ⟶ C) (haa' : Homotopy a a'), CommSq f a' b g := sorry

/-- Bridge/view form of Lemma 13.9.5 (2): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `a` there. -/
theorem exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ a' : A ⟶ C, (Q).map a = (Q).map a' ∧ CommSq f a' b g := by
  obtain ⟨a', haa', hsq⟩ :=
    exists_homotopic_leftMap_of_termwiseSplitEpi
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitEpi
  exact ⟨a', eq_of_homotopy _ _ haa', hsq⟩

end CochainComplex
