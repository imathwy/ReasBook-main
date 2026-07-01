import Mathlib
import stacks_project.Chap13.Definition_13_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.40.2:
- primary domain: orthogonality in a pretriangulated category, detected by the long exact
  covariant Hom sequence of a distinguished triangle;
- sampled core/canonical declarations:
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.rightOrthogonal_iff`,
  `ObjectProperty.isColocal`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.coyoneda_exact₁`,
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`;
- best owner abstraction: the bridge between the canonical right orthogonal object property `A^⊥`
  and the canonical morphism property `A.isColocal`;
- primitive data: an object property `A`, a distinguished triangle `T`, and shift-stability of `A`;
- derived API: the proof-level unfolding of `A.isColocal T.mor₁` to the postcomposition
  bijectivity criterion, with no separate parallel owner-level theorem;
- source/core/bridge triage:
  `source-facing`: the stated equivalence for one distinguished triangle;
  `core/canonical`: `A^⊥`, `A.isColocal`, and the distinguished-triangle exactness lemmas;
  `bridge/view`: the internal `Function.Bijective` expansion of `A.isColocal T.mor₁`.

This item is therefore a bridge theorem: it should reuse the orthogonal owner and the canonical
exactness API directly, and it should route the postcomposition condition through the existing
owner `A.isColocal` rather than a parallel local expansion of that notion.
-/

-- Proof sketch: apply the long exact sequence for the homological functor `Hom(B, -)` to the
-- distinguished triangle `T`. If `T.obj₃` is right-orthogonal to `A`, then the outer terms vanish
-- for every `B ∈ A`, so postcomposition with `T.mor₁` is bijective. Conversely, apply the same exact
-- sequence to `B` and to `B⟦-1⟧`; shift-stability of `A` makes the neighboring terms bijective as
-- well, forcing `Hom(B, T.obj₃) = 0` for every `B ∈ A`.
/-- Lemma 13.40.2: for a distinguished triangle `T` in a shift-stable full subcategory setting,
the third object `T.obj₃` lies in the right orthogonal `A^⊥` if and only if
the first morphism `T.mor₁` is `A`-colocal. -/
theorem rightOrthogonal_obj₃_iff_isColocal_mor₁
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    A^⊥ T.obj₃ ↔ A.isColocal T.mor₁ := by
  change A^⊥ T.obj₃ ↔
    ∀ ⦃B : D⦄ (_ : A B), Function.Bijective (fun f : B ⟶ T.obj₁ ↦ f ≫ T.mor₁)
  rw [A.rightOrthogonal_iff]
  constructor
  · intro h₃ B hB
    constructor
    · intro f₁ f₂ h
      apply sub_eq_zero.mp
      have hsub : (f₁ - f₂) ≫ T.mor₁ = 0 := by
        rw [Preadditive.sub_comp]
        exact sub_eq_zero.mpr h
      have hshift :
          (f₁ - f₂)⟦(1 : ℤ)⟧' ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
        simpa only [Functor.map_sub, Functor.map_zero, Functor.map_comp] using
          congrArg (Functor.map (shiftFunctor D (1 : ℤ))) hsub
      obtain ⟨g, hg⟩ := T.coyoneda_exact₁ hT ((f₁ - f₂)⟦(1 : ℤ)⟧') hshift
      have hg_zero : g = 0 := h₃ g (A.le_shift 1 _ hB)
      have hmap_zero : (f₁ - f₂)⟦(1 : ℤ)⟧' = 0 := by simpa [hg_zero] using hg
      exact (shiftFunctor D (1 : ℤ)).map_injective <| by simpa using hmap_zero
    · intro g
      obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT g (h₃ (g ≫ T.mor₂) hB)
      exact ⟨f, hf.symm⟩
  · intro hbij B f hB
    have hinjShift :
        Function.Injective (fun h : B ⟶ T.obj₁⟦(1 : ℤ)⟧ ↦ h ≫ T.mor₁⟦(1 : ℤ)⟧') := by
      intro h₁ h₂ hh
      let adj := (shiftEquiv D (1 : ℤ)).symm.toAdjunction
      let e₁ := adj.homEquiv B T.obj₁
      let e₂ := adj.homEquiv B T.obj₂
      obtain ⟨g₁, rfl⟩ :=
        e₁.surjective h₁
      obtain ⟨g₂, rfl⟩ :=
        e₁.surjective h₂
      have hg :
          g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ := by
        apply e₂.injective
        change e₂ (g₁ ≫ T.mor₁) = e₂ (g₂ ≫ T.mor₁)
        rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
        exact hh
      have hg' : g₁ = g₂ := (hbij (A.le_shift (-1) _ hB)).1 hg
      change e₁ g₁ = e₁ g₂
      exact congrArg e₁ hg'
    have hf_zero : f ≫ T.mor₃ = 0 := by
      apply hinjShift
      simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₃₁ T hT)
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hf_zero
    obtain ⟨k, hk⟩ := (hbij hB).2 g
    rw [hg, ← hk, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT]
    simp

end CategoryTheory.ObjectProperty
