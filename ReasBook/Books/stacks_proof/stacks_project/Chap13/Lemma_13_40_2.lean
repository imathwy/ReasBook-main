import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_40_1

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
/-- Helper for Lemma 13.40.2: if `T.obj₃` is right-orthogonal to `A`, then the first map in the
triangle is injective on morphisms out of any object of `A`. -/
lemma coyoneda_mor₁_injective_of_rightOrthogonal_obj₃
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (h₃ : A^⊥ T.obj₃) :
    Function.Injective (fun f : B ⟶ T.obj₁ ↦ f ≫ T.mor₁) := by
  -- Proof comment: rewrite orthogonality as Hom-vanishing, then apply exactness one step to the
  -- left after shifting the kernel element.
  rw [A.rightOrthogonal_iff] at h₃
  intro f₁ f₂ h
  apply sub_eq_zero.mp
  have hsub : (f₁ - f₂) ≫ T.mor₁ = 0 := by
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr h
  -- The source proof kills the left outer term by shifting `B` once inside `A`.
  have hshift :
      (f₁ - f₂)⟦(1 : ℤ)⟧' ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
    simpa only [Functor.map_sub, Functor.map_zero, Functor.map_comp] using
      congrArg (Functor.map (shiftFunctor D (1 : ℤ))) hsub
  obtain ⟨g, hg⟩ := T.coyoneda_exact₁ hT ((f₁ - f₂)⟦(1 : ℤ)⟧') hshift
  have hg_zero : g = 0 := h₃ g (A.le_shift 1 _ hB)
  have hmap_zero : (f₁ - f₂)⟦(1 : ℤ)⟧' = 0 := by
    simpa [hg_zero] using hg
  exact (shiftFunctor D (1 : ℤ)).map_injective <| by simpa using hmap_zero

/-- Helper for Lemma 13.40.2: if `T.obj₃` is right-orthogonal to `A`, then the first map in the
triangle is surjective on morphisms out of any object of `A`. -/
lemma coyoneda_mor₁_surjective_of_rightOrthogonal_obj₃
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (h₃ : A^⊥ T.obj₃) :
    Function.Surjective (fun f : B ⟶ T.obj₁ ↦ f ≫ T.mor₁) := by
  -- Proof comment: exactness at `Hom(B, T.obj₂)` turns vanishing of `Hom(B, T.obj₃)` into
  -- surjectivity of postcomposition with `T.mor₁`.
  rw [A.rightOrthogonal_iff] at h₃
  intro g
  obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT g (h₃ (g ≫ T.mor₂) hB)
  exact ⟨f, hf.symm⟩

/-- Helper for Lemma 13.40.2: colocality of `T.mor₁` propagates to injectivity after shifting the
source object by `-1`. -/
lemma shifted_coyoneda_mor₁_injective_of_isColocal
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) {B : D} (hB : A B) (hcol : A.isColocal T.mor₁) :
    Function.Injective (fun h : B ⟶ T.obj₁⟦(1 : ℤ)⟧ ↦ h ≫ T.mor₁⟦(1 : ℤ)⟧') := by
  -- Route correction: instead of unfolding shifts directly, transport equality through the shift
  -- adjunction and use colocality on `B⟦-1⟧`, exactly as in the source proof.
  intro h₁ h₂ hh
  let adj := (shiftEquiv D (1 : ℤ)).symm.toAdjunction
  let e₁ := adj.homEquiv B T.obj₁
  let e₂ := adj.homEquiv B T.obj₂
  obtain ⟨g₁, rfl⟩ := e₁.surjective h₁
  obtain ⟨g₂, rfl⟩ := e₁.surjective h₂
  -- Proof comment: naturality on the right identifies equality after shifting with equality after
  -- postcomposition by `T.mor₁` before transport.
  have hg : g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ := by
    apply e₂.injective
    change e₂ (g₁ ≫ T.mor₁) = e₂ (g₂ ≫ T.mor₁)
    rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
    exact hh
  have hg' : g₁ = g₂ := (hcol _ (A.le_shift (-1) _ hB)).1 hg
  change e₁ g₁ = e₁ g₂
  exact congrArg e₁ hg'

/-- Helper for Lemma 13.40.2: colocality of `T.mor₁` forces every map from an object of `A` to
`T.obj₃` to vanish. -/
lemma hom_to_obj₃_zero_of_isColocal
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (hcol : A.isColocal T.mor₁) (f : B ⟶ T.obj₃) :
    f = 0 := by
  -- Proof comment: kill the connecting morphism via shifted injectivity, factor through `T.mor₂`,
  -- and then use surjectivity for `T.mor₁` to reduce to the zero composite relation.
  have hf_zero : f ≫ T.mor₃ = 0 := by
    apply shifted_coyoneda_mor₁_injective_of_isColocal (A := A) (T := T) hB hcol
    simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₃₁ T hT)
  obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hf_zero
  obtain ⟨k, hk⟩ := (hcol _ hB).2 g
  rw [hg, ← hk, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT]
  simp

/-- Lemma 13.40.2: for a distinguished triangle `T` in a shift-stable full subcategory setting,
the third object `T.obj₃` lies in the right orthogonal `A^⊥` if and only if
the first morphism `T.mor₁` is `A`-colocal. -/
@[stacks 0CQQ]
theorem rightOrthogonal_obj₃_iff_isColocal_mor₁
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    A^⊥ T.obj₃ ↔ A.isColocal T.mor₁ := by
  constructor
  · intro h₃
    -- Proof comment: exactness with vanishing outer terms gives bijectivity for every `B ∈ A`.
    intro B hB
    exact ⟨coyoneda_mor₁_injective_of_rightOrthogonal_obj₃ (A := A) (T := T) hT hB h₃,
      coyoneda_mor₁_surjective_of_rightOrthogonal_obj₃ (A := A) (T := T) hT hB h₃⟩
  · intro hcol
    -- Proof comment: the converse packages the exactness argument as pointwise Hom-vanishing.
    rw [A.rightOrthogonal_iff]
    intro B f hB
    exact hom_to_obj₃_zero_of_isColocal (A := A) (T := T) hT hB hcol f

end CategoryTheory.ObjectProperty
