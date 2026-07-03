import Mathlib
import stacks_project.Chap13.Definition_13_36_3
import stacks_project.Chap13.Definition_13_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Definition 13.37.5:
- primary domain: compact generation of triangulated categories via compact objects and generating
  families;
- sampled owner declarations:
  `IsCompactObject`,
  `D_c(D)`,
  `IsWeakGenerator`,
  `IsGeneratingFamily`,
  `ObjectProperty.ofObj`,
  `ObjectProperty.shiftClosure`,
  `isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero`;
- best upstream owner abstractions:
  `IsCompactObject` for the compactness predicate on each generator and
  `IsGeneratingFamily E` for the family-level generation statement;
- source-facing reformulation for this item: the coproduct weak-generator statement
  `IsWeakGenerator (∐ E)`;
- primitive data: a family `E : I → D` together with the compactness owner
  `∀ i, IsCompactObject (E i)` and the source coproduct-generation condition
  `IsWeakGenerator (∐ E)`;
- derived API: the canonical generation-family bridge
  `isCompactlyGenerated_iff_exists_compact_generatingFamily`, obtained from
  `isWeakGenerator_coproduct_iff_isGeneratingFamily`, and the bundled compact-subcategory bridge
  `isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily`;
- source/core/bridge triage:
  `source-facing`: `IsCompactlyGenerated D`;
  `core/canonical`: `IsCompactObject` and `IsGeneratingFamily E`;
  `bridge/view`: the equivalences
  `IsWeakGenerator (∐ E) ↔ IsGeneratingFamily E` via the singleton shift-closure owner for
  `∐ E`, the family shift-closure owner for `E`, and the coproduct/shift comparison
  `Limits.PreservesCoproduct.iso (shiftFunctor D n) E`, together with the equivalent
  `D_c(D)`-family packaging of the compactness data.

The source notion is not a new owner parallel to `IsCompactObject` or `IsGeneratingFamily`; it is
the existential compact-generation wrapper built directly from those owners, with the
canonical generation-family reformulation and compact-subcategory packaging retained as bridge
views. -/

section

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]

omit [HasZeroMorphisms D] in
private theorem hasCoproduct_shift {I : Type w} (E : I → D) [HasCoproduct E] (n : ℤ) :
    HasCoproduct (fun i ↦ (shiftFunctor D n).obj (E i)) := by
  change HasColimit (Discrete.functor fun i ↦ (shiftFunctor D n).obj (E i))
  letI : HasColimit (Discrete.functor E ⋙ shiftFunctor D n) := inferInstance
  let e :
      Discrete.functor (fun i ↦ (shiftFunctor D n).obj (E i)) ≅
        Discrete.functor E ⋙ shiftFunctor D n :=
    Discrete.natIso fun i ↦ Iso.refl _
  exact hasColimit_of_iso e

omit [HasZeroMorphisms D] in
private def coproductShiftIso {I : Type w} (E : I → D) [HasCoproduct E] (n : ℤ)
    [HasCoproduct (fun i ↦ (shiftFunctor D n).obj (E i))] :
    (∐ fun i ↦ E i⟦n⟧) ≅ (∐ E)⟦n⟧ :=
  (PreservesCoproduct.iso (shiftFunctor D n) E).symm

/-- A family generates exactly when its coproduct is a weak generator. -/
theorem isWeakGenerator_coproduct_iff_isGeneratingFamily {I : Type w} (E : I → D)
    [HasCoproduct E] :
    IsWeakGenerator (∐ E) ↔ IsGeneratingFamily E := by
  rw [isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero, IsGeneratingFamily]
  suffices
      ((singleton (∐ E)).shiftClosure ℤ).rightOrthogonal =
        ((ofObj E).shiftClosure ℤ).rightOrthogonal by
    rw [this]
  ext K
  constructor
  · intro hK X f hX
    rcases hX with ⟨Y, n, eX, hY⟩
    rcases hY with ⟨i⟩
    letI : HasCoproduct (fun j ↦ (shiftFunctor D n).obj (E j)) := hasCoproduct_shift E n
    let e := coproductShiftIso E n
    classical
    let g : (j : I) → E j⟦n⟧ ⟶ K := fun j ↦ by
      by_cases h : j = i
      · subst h
        exact eX.inv ≫ f
      · exact 0
    let φ : (∐ fun j ↦ E j⟦n⟧) ⟶ K := Limits.Sigma.desc g
    have hφ : e.inv ≫ φ = 0 := hK (e.inv ≫ φ) ⟨∐ E, n, Iso.refl _, by simp⟩
    have hφ' : φ = 0 := by
      simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hφ
    have hι : Limits.Sigma.ι (fun j ↦ E j⟦n⟧) i ≫ φ = eX.inv ≫ f := by
      rw [show φ = Limits.Sigma.desc g by rfl, Limits.Sigma.ι_desc]
      simp [g]
    calc
      f = eX.hom ≫ (eX.inv ≫ f) := by simp
      _ = eX.hom ≫ (Limits.Sigma.ι (fun j ↦ E j⟦n⟧) i ≫ φ) := by
            simpa using congrArg (eX.hom ≫ ·) hι.symm
      _ = 0 := by simp [hφ']
  · intro hK X f hX
    rcases hX with ⟨Y, n, eX, hY⟩
    rw [singleton_iff] at hY
    subst Y
    letI : HasCoproduct (fun j ↦ (shiftFunctor D n).obj (E j)) := hasCoproduct_shift E n
    let e := coproductShiftIso E n
    have hg : e.hom ≫ eX.inv ≫ f = 0 := by
      apply Limits.Sigma.hom_ext
      intro j
      simpa using hK (Limits.Sigma.ι (fun j ↦ E j⟦n⟧) j ≫ e.hom ≫ eX.inv ≫ f)
        ⟨E j, n, Iso.refl _, ofObj_apply E j⟩
    calc
      f = eX.hom ≫ (e.inv ≫ (e.hom ≫ eX.inv ≫ f)) := by simp
      _ = 0 := by simp [hg]

end

section

variable (D : Type u) [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [HasCoproducts.{max u v} D]

/-- Definition 13.37.5: in the source triangulated setting, compact generation is the existence of
a family of compact objects whose coproduct is a weak generator. The canonical family-level
reformulation is `isCompactlyGenerated_iff_exists_compact_generatingFamily`, and the compact
subcategory packaging is
`isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily`. -/
def IsCompactlyGenerated : Prop :=
  ∃ (I : Type (max u v)) (E : I → D), (∀ i, IsCompactObject (E i)) ∧ IsWeakGenerator (∐ E)

/-- Canonical bridge: compact generation is equivalently the existence of a compact generating
family. -/
theorem isCompactlyGenerated_iff_exists_compact_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type (max u v)) (E : I → D), (∀ i, IsCompactObject (E i)) ∧ IsGeneratingFamily E := by
  constructor
  · rintro ⟨I, E, hcompact, hweak⟩
    exact ⟨I, E, hcompact, (isWeakGenerator_coproduct_iff_isGeneratingFamily E).1 hweak⟩
  · rintro ⟨I, E, hcompact, hgenerate⟩
    exact ⟨I, E, hcompact, (isWeakGenerator_coproduct_iff_isGeneratingFamily E).2 hgenerate⟩

/-- Compact generation is equivalently the existence of a generating family valued in the compact
subcategory `D_c(D)`. This is the thin bridge from the canonical generation-family reformulation
to the full-subcategory view. -/
theorem isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type (max u v)) (E : I → D_c(D)), IsGeneratingFamily (fun i ↦ (E i).obj) := by
  rw [isCompactlyGenerated_iff_exists_compact_generatingFamily]
  constructor
  · rintro ⟨I, E, hcompact, hE⟩
    exact ⟨I, fun i ↦ ⟨E i, hcompact i⟩, hE⟩
  · rintro ⟨I, E, hE⟩
    exact ⟨I, fun i ↦ (E i).obj, fun i ↦ (E i).property, hE⟩

end

end CategoryTheory
