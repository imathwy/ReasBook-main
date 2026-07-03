import Mathlib
import StacksProject_2024.Chap13.Definition_13_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.40.3:
- primary domain: orthogonality in a pretriangulated category, detected by the long exact
  contravariant Hom sequence of a distinguished triangle;
- sampled core/canonical declarations:
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.leftOrthogonal_iff`,
  `ObjectProperty.isLocal`,
  `Triangle.yoneda_exact₂`,
  `Triangle.yoneda_exact₃`,
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`;
- best owner abstraction: the bridge between the canonical left orthogonal object property `^⊥A`
  and the canonical morphism property `A.isLocal`;
- primitive data: an object property `A`, a distinguished triangle `T`, and shift-stability of `A`;
- derived API: the proof-level unfolding of `A.isLocal T.mor₂` to the precomposition
  bijectivity criterion, with no parallel owner-level theorem for that condition;
- source/core/bridge triage:
  `source-facing`: the stated equivalence for one distinguished triangle;
  `core/canonical`: `^⊥A`, `A.isLocal`, and the distinguished-triangle exactness lemmas;
  `bridge/view`: the internal `Function.Bijective` expansion of `A.isLocal T.mor₂`.

This item is therefore a bridge theorem: it should reuse the orthogonal owner and the canonical
exactness API directly, and it should route the precomposition condition through the existing
owner `A.isLocal` rather than a parallel local expansion of that notion.
-/

-- Proof sketch: apply the long exact sequence for the cohomological functor `Hom(-, B)` to the
-- distinguished triangle `T`. If `T.obj₁` is left-orthogonal to `A`, then the neighboring terms
-- vanish for every `B ∈ A`, so precomposition with `T.mor₂` is bijective. Conversely, apply the
-- same exactness statement to `B` and to `B⟦1⟧`; shift-stability of `A` makes the adjacent terms
-- bijective as well, forcing `Hom(T.obj₁, B) = 0` for every `B ∈ A`.
/-- Lemma 13.40.3: for a distinguished triangle `T` in a shift-stable full subcategory setting,
the first object `T.obj₁` lies in the left orthogonal `^⊥A` if and only if the second morphism
`T.mor₂` is `A`-local. -/
theorem leftOrthogonal_obj₁_iff_isLocal_mor₂
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    ^⊥A T.obj₁ ↔ A.isLocal T.mor₂ := by
  change ^⊥A T.obj₁ ↔
    ∀ ⦃B : D⦄ (_ : A B), Function.Bijective (fun f : T.obj₃ ⟶ B ↦ T.mor₂ ≫ f)
  rw [A.leftOrthogonal_iff]
  let S := shiftFunctor D (1 : ℤ)
  constructor
  · intro h₁ B hB
    let _ : ((shiftEquiv D (1 : ℤ)).functor).Additive := by
      change (shiftFunctor D (1 : ℤ)).Additive
      infer_instance
    let e := (shiftEquiv D (1 : ℤ)).toAdjunction.homAddEquiv T.obj₁ B
    constructor
    · intro f₁ f₂ h
      have hzero : T.mor₂ ≫ (f₁ - f₂) = 0 := by
        rw [Preadditive.comp_sub, sub_eq_zero]
        exact h
      obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT (f₁ - f₂) hzero
      have hEg : e g = 0 := by
        simpa [e] using h₁ (e g) (A.le_shift (-1) _ hB)
      have hg_zero : g = 0 := by
        simpa [e] using e.map_eq_zero_iff.mp hEg
      have hsub : f₁ - f₂ = 0 := by
        simpa [hg_zero] using hg
      exact sub_eq_zero.mp hsub
    · intro g
      obtain ⟨f, hf⟩ := T.yoneda_exact₂ hT g (h₁ (T.mor₁ ≫ g) hB)
      exact ⟨f, hf.symm⟩
  · intro hbij B f hB
    have hmor₃ : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0 := by
      refine (hbij (A.le_shift 1 _ hB)).1 ?_
      calc
        T.mor₂ ≫ (T.mor₃ ≫ S.map f) = (T.mor₂ ≫ T.mor₃) ≫ S.map f := by
          rw [← Category.assoc]
        _ = 0 := by
          rw [comp_distTriang_mor_zero₂₃ _ hT, zero_comp]
        _ = T.mor₂ ≫ 0 := by
          simp
    have hmor₃' : T.mor₃ ≫ (-S.map f) = 0 := by
      rw [Preadditive.comp_neg, hmor₃, neg_zero]
    obtain ⟨gShift, hgShift⟩ := (T.rotate.rotate).yoneda_exact₂
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) (-S.map f) hmor₃'
    obtain ⟨g, rfl⟩ := S.map_surjective gShift
    have hf_factor : f = T.mor₁ ≫ g := by
      apply S.map_injective
      simpa [S, Functor.map_comp] using hgShift
    obtain ⟨k, hk⟩ := (hbij hB).2 g
    rw [hf_factor, ← hk, ← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]

end CategoryTheory.ObjectProperty
