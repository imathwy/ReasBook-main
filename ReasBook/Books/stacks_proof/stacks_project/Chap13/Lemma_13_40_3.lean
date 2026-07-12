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
/-- Helper for Lemma 13.40.3: if `T.obj₁` is left-orthogonal to `A`, then the second map in the
triangle is injective on morphisms into any object of `A`. -/
lemma yoneda_mor₂_injective_of_leftOrthogonal_obj₁
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (h₁ : ^⊥A T.obj₁) :
    Function.Injective (fun f : T.obj₃ ⟶ B ↦ T.mor₂ ≫ f) := by
  rw [A.leftOrthogonal_iff] at h₁
  intro f₁ f₂ h
  -- Proof comment: exactness at `Hom(T.obj₃, B)` turns a kernel element for `T.mor₂` into a map
  -- out of `T.obj₁⟦1⟧`, and shift-stability propagates left orthogonality to that shift.
  have hsub : T.mor₂ ≫ (f₁ - f₂) = 0 := by
    rw [Preadditive.comp_sub, sub_eq_zero]
    exact h
  obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT (f₁ - f₂) hsub
  have hg_zero : g = 0 := by
    exact ((^⊥A).le_shift 1 _ h₁) g hB
  have hsub_zero : f₁ - f₂ = 0 := by
    simpa [hg_zero] using hg
  exact sub_eq_zero.mp hsub_zero

/-- Helper for Lemma 13.40.3: if `T.obj₁` is left-orthogonal to `A`, then the second map in the
triangle is surjective on morphisms into any object of `A`. -/
lemma yoneda_mor₂_surjective_of_leftOrthogonal_obj₁
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (h₁ : ^⊥A T.obj₁) :
    Function.Surjective (fun f : T.obj₃ ⟶ B ↦ T.mor₂ ≫ f) := by
  rw [A.leftOrthogonal_iff] at h₁
  intro g
  -- Proof comment: exactness at `Hom(T.obj₂, B)` produces a lift as soon as the incoming map
  -- from `T.obj₁` vanishes, and left orthogonality gives exactly that vanishing.
  obtain ⟨f, hf⟩ := T.yoneda_exact₂ hT g (h₁ (T.mor₁ ≫ g) hB)
  exact ⟨f, hf.symm⟩

/-- Helper for Lemma 13.40.3: locality of `T.mor₂` forces the shifted connecting morphism of any
map `T.obj₁ ⟶ B` to vanish. -/
lemma mor₃_comp_shift_zero_of_isLocal
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (hloc : A.isLocal T.mor₂) (f : T.obj₁ ⟶ B) :
    T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0 := by
  -- Proof comment: apply injectivity of the precomposition map for `B⟦1⟧` and compare the
  -- composite through `T.mor₂` with the distinguished-triangle zero relation.
  refine (hloc _ (A.le_shift 1 _ hB)).1 ?_
  calc
    T.mor₂ ≫ (T.mor₃ ≫ f⟦(1 : ℤ)⟧') = (T.mor₂ ≫ T.mor₃) ≫ f⟦(1 : ℤ)⟧' := by
      rw [← Category.assoc]
    _ = 0 := by
      rw [comp_distTriang_mor_zero₂₃ _ hT, zero_comp]
    _ = T.mor₂ ≫ 0 := by
      simp

/-- Helper for Lemma 13.40.3: locality of `T.mor₂` forces every map from `T.obj₁` into an object
of `A` to vanish. -/
lemma hom_from_obj₁_zero_of_isLocal
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    {B : D} (hB : A B) (hloc : A.isLocal T.mor₂) (f : T.obj₁ ⟶ B) :
    f = 0 := by
  let S := shiftFunctor D (1 : ℤ)
  -- Proof comment: the shifted connecting morphism vanishes by locality, so the double rotation
  -- exact sequence factors `-f⟦1⟧'` through the shift of `T.mor₁`.
  have hmor₃ : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0 := by
    exact mor₃_comp_shift_zero_of_isLocal (A := A) (T := T) hT hB hloc f
  have hmor₃' : T.mor₃ ≫ (-S.map f) = 0 := by
    rw [Preadditive.comp_neg, hmor₃, neg_zero]
  obtain ⟨gShift, hgShift⟩ := (T.rotate.rotate).yoneda_exact₂
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) (-S.map f) hmor₃'
  obtain ⟨g, rfl⟩ := S.map_surjective gShift
  -- Proof comment: unshift the factorization and then use locality again to write the factor
  -- through `T.obj₂` as a composite with `T.mor₂`.
  have hf_factor : f = T.mor₁ ≫ g := by
    apply S.map_injective
    simpa [S, Functor.map_comp] using hgShift
  obtain ⟨k, hk⟩ := (hloc _ hB).2 g
  rw [hf_factor, ← hk, ← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]

/-- Lemma 13.40.3: for a distinguished triangle `T` in a shift-stable full subcategory setting,
the first object `T.obj₁` lies in the left orthogonal `^⊥A` if and only if the second morphism
`T.mor₂` is `A`-local. -/
@[stacks 0H0M]
theorem leftOrthogonal_obj₁_iff_isLocal_mor₂
    (A : ObjectProperty D) [A.IsStableUnderShift ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D) :
    ^⊥A T.obj₁ ↔ A.isLocal T.mor₂ := by
  -- Proof comment: unfold both sides to the pointwise vanishing and bijectivity conditions used
  -- in the source proof, then prove each direction through the long exact sequence.
  change ^⊥A T.obj₁ ↔
    ∀ ⦃B : D⦄ (_ : A B), Function.Bijective (fun f : T.obj₃ ⟶ B ↦ T.mor₂ ≫ f)
  rw [A.leftOrthogonal_iff]
  constructor
  · intro h₁ B hB
    -- Proof comment: vanishing of the outer Hom groups makes precomposition with `T.mor₂`
    -- bijective on every target object of `A`.
    exact ⟨yoneda_mor₂_injective_of_leftOrthogonal_obj₁ (A := A) (T := T) hT hB h₁,
      yoneda_mor₂_surjective_of_leftOrthogonal_obj₁ (A := A) (T := T) hT hB h₁⟩
  · intro hbij B f hB
    -- Proof comment: the converse direction reduces every map out of `T.obj₁` to zero by a
    -- shifted exactness argument and a final factorization through `T.mor₂`.
    exact hom_from_obj₁_zero_of_isLocal (A := A) (T := T) hT hB hbij f

end CategoryTheory.ObjectProperty
