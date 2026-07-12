import StacksProject_2024.Chap04.Lemma_4_19_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]

/- Domain-style sampling for Lemma 4.19.7:
- source-facing input: the chapter owner `HasSpanCocones`
- core/canonical owners in this domain: `Functor.PreservesMonomorphisms`,
  `NatTrans.mono_iff_mono_app`, `mono_iff_injective`,
  `Types.FilteredColimit.Rel`, and the stronger mathlib owner
  `MorphismProperty.IsStableUnderFilteredColimits (monomorphisms (Type _))`
- best owner abstraction here: the local instance
  `(colim : (I ⥤ Type _) ⥤ Type _).PreservesMonomorphisms` under `[HasSpanCocones I]`;
  the filtered-colimit owner is only a background comparison because it would strengthen the
  source hypothesis to filteredness
- target layer here: keep the monomorphism-preservation instance as the owner-level statement,
  and derive the source-facing injectivity formulations as thin bridge theorems
-/

private theorem rel_of_eqvGen_colimitTypeRel
    [HasSpanCocones I] {F : I ⥤ Type (max uI vI)}
    {p q : Σ i, F.obj i} (h : Relation.EqvGen F.ColimitTypeRel p q) :
    Types.FilteredColimit.Rel F p q := by
  induction h with
  | rel p q hpq =>
      exact Types.FilteredColimit.rel_of_colimitTypeRel F p q hpq
  | refl p =>
      exact ⟨p.1, 𝟙 p.1, 𝟙 p.1, rfl⟩
  | symm _ _ _ ih =>
      rcases ih with ⟨k, f, g, hfg⟩
      exact ⟨k, g, f, hfg.symm⟩
  | trans p q r _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨k₁, f₁, g₁, h₁⟩
      rcases ih₂ with ⟨k₂, f₂, g₂, h₂⟩
      obtain ⟨k, h₁₂, h₂₁, hh⟩ := HasSpanCocones.span g₁ f₂
      refine ⟨k, f₁ ≫ h₁₂, g₂ ≫ h₂₁, ?_⟩
      calc
        F.map (f₁ ≫ h₁₂) p.2 = F.map h₁₂ (F.map f₁ p.2) := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map h₁₂ (F.map g₁ q.2) := by rw [h₁]
        _ = F.map (g₁ ≫ h₁₂) q.2 := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map (f₂ ≫ h₂₁) q.2 := by rw [hh]
        _ = F.map h₂₁ (F.map f₂ q.2) := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map h₂₁ (F.map g₂ r.2) := by rw [h₂]
        _ = F.map (g₂ ≫ h₂₁) r.2 := by
          rw [FunctorToTypes.map_comp_apply]

/-
Source/core/bridge triage for Lemma 4.19.7:
- `source-facing`: the full textbook payload, namely the injectivity statement for `Type`-valued
  colimits together with the assertion that the analogous statement fails for
  `AddCommGrpCat`.
- `core/canonical`: `(colim : (I ⥤ Type _) ⥤ Type _).PreservesMonomorphisms`.
- `bridge/view`: the injectivity reformulation obtained from `mono_iff_injective` together with
  the explicit `AddCommGrpCat` counterexample theorem.
-/

/-- Lemma 4.19.7, core/canonical form: if every span in `I` admits a cocone, then the colimit
functor on `Type`-valued diagrams preserves monomorphisms. -/
instance colim_preservesMonomorphisms_of_hasSpanCocones [HasSpanCocones I] :
    (colim : (I ⥤ Type (max uI vI)) ⥤ Type (max uI vI)).PreservesMonomorphisms where
  preserves := by
    intro M N α hα
    letI : Mono α := hα
    rw [mono_iff_injective]
    intro x y hxy
    obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' y
    simp only [Types.Colimit.ι_map_apply] at hxy
    have hrel :
        Types.FilteredColimit.Rel N ⟨i, α.app i x⟩ ⟨j, α.app j y⟩ :=
      rel_of_eqvGen_colimitTypeRel (Types.colimit_eq hxy)
    rcases hrel with ⟨k, f, g, hfg⟩
    have hxy' : M.map f x = M.map g y := by
      apply (mono_iff_injective (α.app k)).1 inferInstance
      calc
        α.app k (M.map f x) = N.map f (α.app i x) := by
          simpa using congrFun (α.naturality f) x
        _ = N.map g (α.app j y) := hfg
        _ = α.app k (M.map g y) := by
          simpa using (congrFun (α.naturality g) y).symm
    exact Types.colimit_sound' f g hxy'

-- Proof sketch: use a one-object category attached to the group of order two and the standard
-- injective equivariant map whose induced map on coinvariants is zero.
private theorem addCommGrpCat_counterexample_to_colimMap_mono :
    ∃ (J : Type) (_ : Category J) (_ : HasSpanCocones J)
      (M N : J ⥤ AddCommGrpCat) (α : M ⟶ N),
      Mono α ∧ ¬ Mono (colim.map α) := by
  sorry

/-- Lemma 4.19.7, bridge/view form for `Type`: objectwise injective natural transformations induce
injective maps on colimits whenever every span in `I` admits a cocone. -/
theorem colimit_map_injective_of_app_injective [HasSpanCocones I]
    {M N : I ⥤ Type (max uI vI)} (α : M ⟶ N)
    (hα : ∀ i : I, Function.Injective (α.app i)) :
    Function.Injective (colim.map α) := by
  letI : Mono α := (NatTrans.mono_iff_mono_app α).2 fun i ↦ (mono_iff_injective _).2 (hα i)
  exact (mono_iff_injective _).1 (colim.map_mono α)

/-- Lemma 4.19.7, source-facing negative half: the analogous injectivity statement for colimits is
false in general for `AddCommGrpCat`-valued diagrams, even when every span admits a cocone. -/
theorem addCommGrpCat_counterexample_to_colimit_map_injective :
    ∃ (J : Type) (_ : Category J) (_ : HasSpanCocones J)
      (M N : J ⥤ AddCommGrpCat) (α : M ⟶ N),
      (∀ j : J, Function.Injective (α.app j)) ∧
        ¬ Function.Injective (colim.map α) := by
  obtain ⟨J, hJ, hSpan, M, N, α, hMono, hcolim⟩ := addCommGrpCat_counterexample_to_colimMap_mono
  letI : Category J := hJ
  letI : HasSpanCocones J := hSpan
  have hMonoApp := (NatTrans.mono_iff_mono_app α).1 hMono
  refine ⟨J, hJ, hSpan, M, N, α, ?_, ?_⟩
  · intro j
    exact (AddCommGrpCat.mono_iff_injective _).1 (hMonoApp j)
  · simpa [AddCommGrpCat.mono_iff_injective] using hcolim

end CategoryTheory.Limits
