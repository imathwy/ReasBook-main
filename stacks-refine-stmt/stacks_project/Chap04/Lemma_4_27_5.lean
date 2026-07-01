import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

open CategoryTheory
open MorphismProperty

universe u v w w'

namespace CategoryTheory
namespace Localization

variable {C : Type u} {D : Type w'} [Category.{v} C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasLeftCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.5:
- primary domain: localization by a left calculus of fractions;
- inspected owner declarations:
  `Localization.exists_leftFraction`,
  `MorphismProperty.RightFraction.leftFraction`,
  `MorphismProperty.RightFraction.leftFraction_fac`,
  `MorphismProperty.LeftFraction.map_eq_iff`,
  `Localization.exists_leftFraction₂`;
- best owner abstraction: `MorphismProperty.LeftFraction` as the canonical representation of a
  localized morphism by a roof;
- primitive data: a finite family `g i : L.obj (X i) ⟶ L.obj Y`;
- derived API: existence of representatives with one common denominator.

Source/core/bridge triage:
- `source-facing`: `exists_leftFraction_finite`;
- `core/canonical`: the owner-level left-fraction localization API above;
- `bridge/view`: the operational `Finset`-indexed common-denominator statement
  used internally to derive the finite theorem. -/

/-- Operational `Finset` form of Lemma 4.27.5: for a finite subfamily of morphisms in a
localization with common target, one can choose left-fraction representatives with a single common
denominator in `W`. -/
private theorem exists_leftFraction_finset {ι : Type w} {X : ι → C} (s : Finset ι) {Z : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Z) :
    ∃ (Z' : C) (t : Z ⟶ Z') (ht : W t) (f : ∀ i, i ∈ s → (X i ⟶ Z')),
      ∀ i (hi : i ∈ s), g i = (LeftFraction.mk (f i hi) t ht).map L (inverts L W) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨Z, 𝟙 Z, W.id_mem Z, fun i hi ↦ False.elim <| Finset.notMem_empty i hi, ?_⟩
      intro i hi
      exact False.elim <| Finset.notMem_empty i hi
  | @insert a s ha ih =>
      obtain ⟨Z₁, s₁, hs₁, f₁, hf₁⟩ := ih
      obtain ⟨φ₀, hφ₀⟩ := exists_leftFraction L W (g a)
      let α : W.LeftFraction φ₀.Y' Z₁ := (RightFraction.mk φ₀.s φ₀.hs s₁).leftFraction
      have hα : φ₀.s ≫ α.f = s₁ ≫ α.s := by
        simpa [α] using
          (RightFraction.leftFraction_fac (RightFraction.mk φ₀.s φ₀.hs s₁)).symm
      let t : Z ⟶ α.Y' := s₁ ≫ α.s
      have ht : W t := W.comp_mem _ _ hs₁ α.hs
      let f : ∀ i, i ∈ insert a s → (X i ⟶ α.Y') := fun i hi ↦
        if h : i = a then by
          subst h
          exact φ₀.f ≫ α.f
        else
          f₁ i ((Finset.mem_insert.1 hi).resolve_left h) ≫ α.s
      refine ⟨α.Y', t, ht, f, ?_⟩
      intro i hi
      by_cases h : i = a
      · subst h
        rw [hφ₀]
        exact (LeftFraction.map_eq_iff L W _ _).2 <| by
          refine ⟨α.Y', α.f, 𝟙 α.Y', ?_, ?_, ?_⟩
          · simpa [t] using hα
          · simp [f, α]
          · rw [hα]
            simpa [t] using ht
      · have hi' : i ∈ s := (Finset.mem_insert.1 hi).resolve_left h
        rw [hf₁ i hi']
        exact (LeftFraction.map_eq_iff L W _ _).2 <| by
          refine ⟨α.Y', α.s, 𝟙 α.Y', ?_, ?_, ht⟩
          · simp [t]
          · simp [f, h, α]

-- Proof sketch: choose a left-fraction representative for each `g i`. Then induct on the finite
-- index type, using the left Ore condition to replace two denominators by a common refinement in
-- `W`, and compose the previously chosen numerators with the comparison maps into that refinement.
/-- Lemma 4.27.5: a finite family of morphisms in a localization with common target admits
representatives by left fractions with a single common denominator in `W`. -/
theorem exists_leftFraction_finite {ι : Type w} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = (LeftFraction.mk (f i) s hs).map L (inverts L W) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨Y', s, hs, f, hf⟩ := exists_leftFraction_finset L W Finset.univ g
  refine ⟨Y', s, hs, fun i ↦ f i (by simp), ?_⟩
  intro i
  exact hf i (by simp)

end Localization
end CategoryTheory
