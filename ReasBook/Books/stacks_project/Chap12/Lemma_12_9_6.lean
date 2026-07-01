import Mathlib
import stacks_project.Chap12.Aux_12_20_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Subobject

variable {A : C}

/- Domain triage:
- primary domain: Jordan-Hölder theory for the subobject lattice of an object in an abelian
  category;
- sampled owner API:
  `JordanHolderLattice`,
  `CompositionSeries.jordan_holder`,
  `JordanHolderModule.instJordanHolderLattice`,
  `subobjectSubquotient`;
- `core/canonical`: the ambient owner is `JordanHolderLattice (Subobject A)`;
- `bridge/view`: `iso_iff_nonempty_subobjectSubquotient_iso` and `CompositionSeries.factor`
  translate the generic Jordan-Hölder owner back to canonical subquotients `Y / X`.
-/

-- Proof sketch: a cover `X ⋖ Y` means the interval `[X, Y]` has exactly two points, and in an
-- abelian category the subobjects of the canonical subquotient `Y / X` correspond to this
-- interval. Hence the quotient is simple.
private theorem simple_subobjectSubquotient_of_covBy {X Y : Subobject A} (h : X ⋖ Y) :
    Simple (subobjectSubquotient (CovBy.le h)) := sorry

-- Proof sketch: this is the second isomorphism theorem for subquotients in an abelian category.
private theorem subquotient_sup_iso_subquotient_inf (X Y : Subobject A) :
    Nonempty (subobjectSubquotient (show X ≤ X ⊔ Y from _root_.le_sup_left) ≅
      subobjectSubquotient (show X ⊓ Y ≤ Y from _root_.inf_le_right)) := sorry

open scoped Classical in
/-- The Jordan-Hölder lattice structure on the subobject lattice of an object in an abelian
category, with factors given by canonical subquotients. -/
instance : JordanHolderLattice (Subobject A) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := by
    intro X Y hX hY
    sorry
  Iso X Y := Nonempty
    (subobjectSubquotient (show X.1 ⊓ X.2 ≤ X.2 from _root_.inf_le_right) ≅
      subobjectSubquotient (show Y.1 ⊓ Y.2 ≤ Y.2 from _root_.inf_le_right))
  iso_symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
  iso_trans := fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩
  second_iso := by
    intro X Y h
    simpa [inf_eq_left.2 (_root_.le_sup_left : X ≤ X ⊔ Y), inf_assoc] using
      subquotient_sup_iso_subquotient_inf X Y

/-- For comparable pairs of subobjects, the `Iso` relation in the Jordan-Hölder lattice structure
is exactly isomorphism of the canonical subquotients. -/
theorem iso_iff_nonempty_subobjectSubquotient_iso {X₁ X₂ Y₁ Y₂ : Subobject A}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) :
    JordanHolderLattice.Iso (X₁, X₂) (Y₁, Y₂) ↔
      Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY) := by
  change Nonempty
      (subobjectSubquotient (show X₁ ⊓ X₂ ≤ X₂ from _root_.inf_le_right) ≅
        subobjectSubquotient (show Y₁ ⊓ Y₂ ≤ Y₂ from _root_.inf_le_right)) ↔
    Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY)
  simp [inf_eq_left.2 hX, inf_eq_left.2 hY]

end Subobject

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- The `i`-th successive canonical subquotient in a composition series of subobjects. -/
noncomputable abbrev factor (s : CompositionSeries (Subobject A)) (i : Fin s.length) :=
  subobjectSubquotient (s.step i).le

-- Proof sketch: apply `Subobject.simple_subobjectSubquotient_of_covBy` to the `i`-th cover
-- relation.
/-- Each successive canonical subquotient `s (i + 1) / s i` of a composition series in
`Subobject A` is simple. -/
theorem factor_simple (s : CompositionSeries (Subobject A)) (i : Fin s.length) :
    Simple (s.factor i) := by
  simpa using Subobject.simple_subobjectSubquotient_of_covBy (s.step i)

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- This is the exact order-theoretic owner construction used for finite-length modules, applied to
-- the well-founded subobject lattice of an Artinian and Noetherian object.
/-- If an object in an abelian category is Artinian and Noetherian, then its subobject lattice
admits a composition series from `0` to the whole object. -/
theorem exists_compositionSeries_of_isArtinianObject_isNoetherianObject (A : C)
    [IsArtinianObject A] [IsNoetherianObject A] :
    ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Subobject A)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

-- Proof sketch: if `A` is Artinian and Noetherian, refine a maximal strict chain in `Subobject A`
-- from `⊥` to `⊤` into a composition series. Conversely, such a composition series bounds strict
-- ascending and descending chains of subobjects.
/-- Lemma 12.9.6: an object of an abelian category is Artinian and Noetherian if and only if it
admits a composition series of subobjects from `0` to itself. -/
lemma isArtinianObject_and_isNoetherianObject_iff_exists_compositionSeries (A : C) :
    (IsArtinianObject A ∧ IsNoetherianObject A) ↔
      ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := by
  constructor
  · rintro ⟨hArtinian, hNoetherian⟩
    letI : IsArtinianObject A := hArtinian
    letI : IsNoetherianObject A := hNoetherian
    exact exists_compositionSeries_of_isArtinianObject_isNoetherianObject A
  · sorry

end CategoryTheory
