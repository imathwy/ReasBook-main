import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_40_1 (from Chap13) -/
universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Definition 13.40.1:
- primary domain: orthogonals of object properties in categories with zero morphisms;
- sampled core/canonical declarations:
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.rightOrthogonal_iff`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.leftOrthogonal_iff`;
- best owner abstraction: the owner object properties `A.rightOrthogonal` and `A.leftOrthogonal`;
- primitive data: only the object property `A : ObjectProperty D`;
- derived API: the full-subcategory realizations `A.rightOrthogonal.FullSubcategory` and
  `A.leftOrthogonal.FullSubcategory`, together with the pointwise membership lemmas
  `A.rightOrthogonal_iff` and `A.leftOrthogonal_iff`;
- source/core/bridge triage:
  `source-facing`: the right and left orthogonal subcategories attached to `A`;
  `core/canonical`: `ObjectProperty.rightOrthogonal` and `ObjectProperty.leftOrthogonal`;
  `bridge/view`: the corresponding full subcategories and pointwise characterization lemmas;
- source-facing notation: `A^⊥` for the right orthogonal and `^⊥A` for the left orthogonal.

No parallel local wrapper is needed: the source notion is already owned canonically by the
mathlib orthogonal API on `ObjectProperty`. -/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroMorphisms D]

/- Source-facing notation for Definition 13.40.1: `A^⊥` and `^⊥A` are the right and left
orthogonals of the object property `A`, while the owner declarations remain
`A.rightOrthogonal` and `A.leftOrthogonal`. -/
postfix:max "^⊥" => rightOrthogonal
prefix:max "^⊥" => leftOrthogonal

/- Definition 13.40.1 (1): for a full subcategory of `D` encoded by an object property `A`, its
right orthogonal `A^⊥` is the canonical owner object property `A.rightOrthogonal`; the
corresponding full subcategory is recalled below. -/
recall rightOrthogonal

/- Definition 13.40.1 (2): for the same full subcategory `A`, its left orthogonal `^⊥A` is the
canonical owner object property `A.leftOrthogonal`; the corresponding full subcategory is recalled
below. -/
recall leftOrthogonal

section

variable (A : ObjectProperty D)

/- Companion recall: the right orthogonal subcategory is the canonical full subcategory
`(A^⊥).FullSubcategory`. -/
#check (A^⊥).FullSubcategory

/- Companion recall: membership in the right orthogonal means that every morphism from an object
satisfying `A` is zero. -/
#check A.rightOrthogonal_iff

/- Companion recall: the left orthogonal subcategory is the canonical full subcategory
`(^⊥A).FullSubcategory`. -/
#check (^⊥A).FullSubcategory

/- Companion recall: membership in the left orthogonal means that every morphism to an object
satisfying `A` is zero. -/
#check A.leftOrthogonal_iff

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_40_2 (from Chap13) -/
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

/-! ### Lemma_13_40_3 (from Chap13) -/
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

/-! ### Lemma_13_40_4 (from Chap13) -/
open CategoryTheory Limits

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.4:
- primary domain: orthogonals of object properties and their induced full subcategories in
  categories with zero morphisms and, later, triangulated structure;
- sampled core/canonical declarations:
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the source-facing owners are the orthogonal object properties `A^⊥` and
  `^⊥A`; retract stability and triangulatedity are derived owner instances on those object
  properties, while the full-subcategory realizations are bridge/view consequences;
- primitive data: only the object property `A : ObjectProperty D`;
- derived API: the retract-stability instances below, strict-fullness from canonical
  isomorphism-closure instances, and the induced full-subcategory triangulated structures coming
  from the owner-level orthogonal `IsTriangulated` instances.

Source/core/bridge triage:
- `source-facing`: the saturation statements for the right and left orthogonals;
- `core/canonical`: the owner object properties `A^⊥`, `^⊥A`, and the generic predicates
  `ObjectProperty.IsStableUnderRetracts` and `CategoryTheory.IsTriangulated`;
- `bridge/view`: the full-subcategory realizations of the orthogonals.

There is no extra local wrapper to keep here: the file should prove retract stability directly for
the canonical orthogonal owners and otherwise reuse the upstream instance machinery verbatim. -/

section Saturated

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
variable (A : ObjectProperty D)

-- Proof sketch: if `X` is a retract of `Y` and `Y` lies in `A^⊥`, then any map
-- `B ⟶ X` with `A B` factors through the retract inclusion `X ⟶ Y`; applying the retract
-- projection `Y ⟶ X` to the resulting zero morphism shows the original map is zero.
/-- Lemma 13.40.4 (1): the right orthogonal `A^⊥` is stable under retracts, hence
is saturated; in the triangulated setting recalled below, it is also a triangulated object
property, so its canonical full subcategory carries the induced triangulated structure. -/
instance :
    A^⊥.IsStableUnderRetracts where
  of_retract h hY := by
    intro B f hB
    have hf : f ≫ h.i = 0 := hY (f ≫ h.i) hB
    calc
      f = (f ≫ h.i) ≫ h.r := by
        rw [Category.assoc, h.retract, Category.comp_id]
      _ = 0 := by rw [hf, zero_comp]

-- Proof sketch: dually, if `X` is a retract of `Y` and `Y` lies in `^⊥A`, then any
-- map `X ⟶ B` with `A B` factors through the retract projection `Y ⟶ X`, so it vanishes because
-- every map out of `Y` into an object of `A` is zero.
/-- Lemma 13.40.4 (2): the left orthogonal `^⊥A` is stable under retracts, hence is
saturated; in the triangulated setting recalled below, it is also a triangulated object property,
so its canonical full subcategory carries the induced triangulated structure. -/
instance :
    (^⊥A).IsStableUnderRetracts where
  of_retract h hY := by
    intro B f hB
    have hf : h.r ≫ f = 0 := hY (h.r ≫ f) hB
    calc
      f = h.i ≫ (h.r ≫ f) := by
        rw [← Category.assoc, h.retract, Category.id_comp]
      _ = 0 := by rw [hf, comp_zero]

/- Companion recall: orthogonals are strictly full because they are canonically closed under
isomorphisms. -/
#check (inferInstance : A^⊥.IsClosedUnderIsomorphisms)

/- Companion recall: the same strict-fullness statement holds for the left orthogonal. -/
#check (inferInstance : (^⊥A).IsClosedUnderIsomorphisms)

end Saturated

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsStableUnderShift ℤ]

/- Companion recall: in the triangulated-subcategory sense, the right orthogonal is itself a
canonical triangulated object property. -/
#check (inferInstance : (A^⊥).IsTriangulated)

/- Companion recall: the left orthogonal is likewise a canonical triangulated object property. -/
#check (inferInstance : (^⊥A).IsTriangulated)

end Triangulated

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_40_5 (from Chap13) -/
open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.5:
- primary domain: triangulated closure of extension products of object properties in a
  triangulated category;
- sampled core/canonical declarations:
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderBinaryProducts`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`;
- best owner abstraction: the source-facing object property `A ⋆ A^⊥`, owned canonically by
  `ObjectProperty.extensionProduct`, whose three triangle-closure clauses are organized by the
  owner predicate `.IsTriangulated`, while direct-sum closure is the generic
  `ObjectProperty.IsClosedUnderBinaryCoproducts` owner consequence of a triangulated object
  property in the preadditive ambient category;
- primitive data: the object property `A`, its canonical right orthogonal `A^⊥`, and their
  canonical extension product `A ⋆ A^⊥`;
- derived API: the clausewise closure predicates
  `(A ⋆ A^⊥).IsTriangulatedClosed₁`,
  `(A ⋆ A^⊥).IsTriangulatedClosed₂`, and
  `(A ⋆ A^⊥).IsTriangulatedClosed₃`;
  clause `(4)` is the direct binary-coproduct closure of this same owner, obtained from its
  triangulated/product closure and the canonical biproduct bridge in a preadditive category.

Source/core/bridge triage:
- `source-facing`: Lemma `13.40.5` asserts that `A ⋆ A^⊥` is closed under the three distinguished
  triangle clauses and under binary direct sums;
- `core/canonical`: the owner declarations `extensionProduct`, `rightOrthogonal`, and
  `IsTriangulated`;
- `bridge/view`: the clausewise `IsTriangulatedClosed₁/₂/₃` consequences obtained by inference from
  the main triangulated owner instance, together with the generic binary-coproduct closure owner
  instance reused for clause `(4)`.

The file should therefore keep the owner-level triangulated instance as the main declaration and
demote the individual closure clauses to companion recalls, rather than storing all three as
primitive parallel instances. -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: the owner-level mathematical content of clauses `(1)`–`(3)` is that the
-- canonical extension product `A ⋆ A^⊥` is triangulated. Its `Closed₁` and
-- `Closed₃` clauses are then derived automatically from the canonical owner instance.
/-- Lemma 13.40.5 (1)–(3): the canonical extension product `A ⋆ A^⊥` is a
triangulated subcategory. Equivalently, it satisfies all three distinguished-triangle closure
clauses from the source statement. -/
instance extensionProduct_rightOrthogonal_isTriangulated :
    (A ⋆ A^⊥).IsTriangulated where
  toContainsZero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_left (A^⊥) Z hA⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := sorry

/- Companion recall for clause `(1)`: this is the canonical `Closed₁` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₁)

/- Companion recall for clause `(2)`: this is the `Closed₂` field of the triangulated owner
instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₂)

/- Companion recall for clause `(3)`: this is the canonical `Closed₃` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₃)

/- Companion recall for clause `(4)`: binary direct-sum closure is the generic owner consequence
of the triangulated instance above together with the canonical isomorphism-closure of
`extensionProduct`. -/
#check (inferInstance : (A ⋆ A^⊥).IsClosedUnderBinaryCoproducts)

end Triangulated

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_40_6 (from Chap13) -/
open CategoryTheory Limits ZeroObject
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.6:
- primary domain: triangulated closure of extension products of object properties in a
  triangulated category;
- sampled core/canonical declarations:
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`;
- best owner abstraction: the source-facing object property `(^⊥A) ⋆ A`, owned canonically by
  `ObjectProperty.extensionProduct`, whose three distinguished-triangle closure clauses are
  organized by the owner predicate `.IsTriangulated`, while clause `(4)` is the generic
  `ObjectProperty.IsClosedUnderBinaryCoproducts` consequence of a triangulated object property in a
  preadditive ambient category;
- primitive data: the object property `A`, its canonical left orthogonal `^⊥A`, and their
  canonical extension product `(^⊥A) ⋆ A`;
- derived API: the clausewise closure predicates
  `((^⊥A) ⋆ A).IsTriangulatedClosed₁`,
  `((^⊥A) ⋆ A).IsTriangulatedClosed₂`, and
  `((^⊥A) ⋆ A).IsTriangulatedClosed₃`;
  clause `(4)` is the derived binary-coproduct closure of the same owner.

Source/core/bridge triage:
- `source-facing`: Lemma `13.40.6` asserts that `(^⊥A) ⋆ A` is closed under the three
  distinguished-triangle clauses and under binary direct sums;
- `core/canonical`: the owner declarations `extensionProduct`, `leftOrthogonal`, and
  `IsTriangulated`;
- `bridge/view`: the clausewise `IsTriangulatedClosed₁/₂/₃` consequences obtained by inference
  from the main triangulated owner instance, together with the generic binary-coproduct closure
  instance reused for clause `(4)`.

This file should therefore keep the owner-level triangulated instance as the main declaration and
demote the individual closure clauses to companion recalls, mirroring Lemma `13.40.5` on the dual
side. -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: the owner-level mathematical content of clauses `(1)`–`(3)` is that the
-- canonical extension product `(^⊥A) ⋆ A` is triangulated. Clause `(2)` is the primitive
-- triangulated-closure field; clauses `(1)` and `(3)` are then derived automatically.
/-- Lemma 13.40.6 (1)–(3): the canonical extension product `(^⊥A) ⋆ A` is a
triangulated subcategory. Equivalently, it satisfies all three distinguished-triangle closure
clauses from the source statement. -/
instance leftOrthogonal_extensionProduct_isTriangulated :
    ((^⊥A) ⋆ A).IsTriangulated where
  toContainsZero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_right (^⊥A) Z hA⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := sorry

/- Companion recall for clause `(1)`: this is the canonical `Closed₁` consequence of the
triangulated owner instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₁)

/- Companion recall for clause `(2)`: this is the `Closed₂` field of the triangulated owner
instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₂)

/- Companion recall for clause `(3)`: this is the canonical `Closed₃` consequence of the
triangulated owner instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₃)

/- Companion recall for clause `(4)`: binary direct-sum closure is the generic owner consequence
of the triangulated instance above together with the canonical isomorphism-closure of
`extensionProduct`. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsClosedUnderBinaryCoproducts)

end Triangulated

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_40_7 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/- Domain-style sampling for Lemma 13.40.7:
- primary domain: admissibility and semi-orthogonal decompositions of triangulated subcategories;
- sampled core/canonical declarations:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`,
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`;
- best owner abstraction: the inclusion functor owner `A.ι.rightAdjointObjIsDefined`, whose
  equality with `⊤` is the canonical adjoint-existence criterion for `A.ι`;
- primitive data: the triangulated object property `A` and its inclusion functor `A.ι`;
- derived API: the source-facing extension-product description `A ⋆ A^⊥ = ⊤`, retract stability,
  and the orthogonal-equality corollary under strict fullness;
- source/core/bridge triage:
  `source-facing`: the semi-orthogonal decomposition criterion `A ⋆ A^⊥ = ⊤`;
  `core/canonical`: `A.ι.rightAdjointObjIsDefined` together with
    `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`;
  `bridge/view`: the identification of `A.ι.rightAdjointObjIsDefined` with
    `A ⋆ A^⊥`.

Primitive data should stay with the inclusion-functor owner. The extension-product condition is a
source-facing bridge theorem, not a second owner for adjointability. -/

-- Proof sketch: for `X : D`, the representability criterion defining
-- `A.ι.rightAdjointObjIsDefined X` is equivalent to the existence of a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`, via Lemma `13.40.2` applied to the universal map
-- representing `Hom_D(A.ι.obj -, X)`.
/-- Bridge theorem for Lemma 13.40.7: the canonical partial-right-adjoint domain of the inclusion
`A.ι` is exactly the extension product `A ⋆ A^⊥`. -/
theorem rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal :
    A.ι.rightAdjointObjIsDefined = A ⋆ A^⊥ := by
  sorry

-- Proof sketch: for `(→)`, let `v` be a chosen right adjoint to the inclusion `A.ι`; for each
-- `X`, complete the counit map `A.ι.obj ((Functor.leftAdjoint A.ι).obj X) ⟶ X` to a distinguished
-- triangle and use Lemma `13.40.2` to identify the cone with an object of `A^⊥`.
-- For `(←)`, use the chosen distinguished triangle for each `X` to define the object part of a
-- right adjoint and use the same bijectivity criterion from Lemma `13.40.2` to define the action
-- on morphisms and prove the adjunction.
/-- Lemma 13.40.7: for a triangulated subcategory `A` of a pretriangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` has a right adjoint if and only if every object of
`D` belongs to the extension product of `A` with its right orthogonal `A^⊥`. -/
theorem isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top :
    A.ι.IsLeftAdjoint ↔ A ⋆ A^⊥ = ⊤ := by
  simpa [A.rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal] using
    A.ι.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: by the main equivalence, the hypothesis gives `A ⋆ A^⊥ = ⊤`. Lemma `13.40.5`
-- shows this extension product is triangulated, and Lemma
-- `13.40.4` shows `A^⊥` is stable under retracts; then the textbook argument implies
-- that `A` itself is stable under retracts.
/-- If the inclusion of `A` into `D` admits a right adjoint, then `A` is saturated, i.e. stable
under retracts. -/
theorem isStableUnderRetracts_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A.IsStableUnderRetracts := sorry

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`. If `X` lies in the left orthogonal
-- of `A^⊥`, then the map `X ⟶ B` is zero, so Lemma `13.4.11` splits the triangle and
-- saturation from `hA` gives strict fullness of `A`, forcing `X` to lie in `A`. The reverse
-- inclusion is immediate from the
-- definition of the right orthogonal.
/-- If the inclusion of `A` into `D` has a right adjoint, then `A` equals the left orthogonal of
its right orthogonal. -/
theorem eq_rightOrthogonal_leftOrthogonal_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A = ^⊥(A^⊥) := sorry

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_40_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/-
Domain-style sampling for Lemma 13.40.8:
- primary domain: admissibility and semi-orthogonal decompositions of triangulated subcategories;
- sampled core/canonical declarations:
  `Functor.leftAdjointObjIsDefined`,
  `Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top`,
  `ObjectProperty.extensionProduct`;
- best owner abstraction: the inclusion functor owner `A.ι.leftAdjointObjIsDefined`, whose
  equality with `⊤` is the canonical adjoint-existence criterion for `A.ι`;
- primitive data: the triangulated object property `A` and its inclusion functor `A.ι`;
- derived API: in this weaker section, the source-facing extension-product description
  `(^⊥A) ⋆ A = ⊤`; the later stronger section adds retract stability and the
  orthogonal-equality corollary under strict fullness;
- source/core/bridge triage:
  `source-facing`: the semi-orthogonal decomposition criterion `(^⊥A) ⋆ A = ⊤`;
  `core/canonical`: `A.ι.leftAdjointObjIsDefined` together with
    `Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top`;
  `bridge/view`: the identification of `A.ι.leftAdjointObjIsDefined` with
    `(^⊥A) ⋆ A`.

Primitive data should stay with the inclusion-functor owner. The extension-product condition is a
source-facing bridge theorem, not a second owner for adjointability. -/

-- Proof sketch: for `X : D`, the corepresentability criterion defining
-- `A.ι.leftAdjointObjIsDefined X` is equivalent to the existence of a distinguished triangle
-- `B ⟶ X ⟶ A' ⟶ B⟦1⟧` with `^⊥A B` and `A A'`, via Lemma `13.40.3` applied to the universal map
-- corepresenting `Hom_D(X, A.ι.obj -)`.
/-- Bridge theorem for Lemma 13.40.8: the canonical partial-left-adjoint domain of the inclusion
`A.ι` is exactly the extension product `(^⊥A) ⋆ A`. -/
theorem leftAdjointObjIsDefined_eq_leftOrthogonal_extensionProduct :
    A.ι.leftAdjointObjIsDefined = (^⊥A) ⋆ A := by
  sorry

-- Proof sketch: this is dual to Lemma `13.40.7`. For `(→)`, let `u` be a chosen left adjoint to
-- the inclusion `A.ι`; for each `X`, complete the unit map `X ⟶ A.ι.obj ((Functor.rightAdjoint
-- A.ι).obj X)` to a distinguished triangle and use Lemma `13.40.3` to identify the first term
-- with an object of `^⊥A`. For `(←)`, choose such a triangle for each `X` and use
-- the bijectivity criterion of Lemma `13.40.3` to define the object and morphism parts of a left
-- adjoint to the inclusion.
/-- Lemma 13.40.8: for a triangulated subcategory `A` of a pretriangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` is a right adjoint, equivalently admits a left
adjoint, if and only if every object of `D` belongs to the extension product of its left
orthogonal `^⊥A` with `A`. -/
theorem isRightAdjoint_iff_leftOrthogonal_extensionProduct_eq_top :
    A.ι.IsRightAdjoint ↔ (^⊥A) ⋆ A = ⊤ := by
  simpa [A.leftAdjointObjIsDefined_eq_leftOrthogonal_extensionProduct] using
    A.ι.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: by the main equivalence, the hypothesis gives `(^⊥A) ⋆ A = ⊤`. Lemma `13.40.6`
-- shows this extension product is triangulated, and Lemma `13.40.4`
-- shows `^⊥A` is stable under retracts; then the textbook argument implies that `A`
-- itself is stable under retracts.
/-- If the inclusion of `A` into `D` admits a left adjoint, then `A` is saturated, i.e. stable
under retracts. -/
theorem isStableUnderRetracts_of_inclusion_isRightAdjoint
    (hA : A.ι.IsRightAdjoint) :
    A.IsStableUnderRetracts := sorry

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `B ⟶ X ⟶ A' ⟶ B⟦1⟧` with `^⊥A B` and `A A'`. If `X` lies in the right orthogonal
-- of `^⊥A`, then the map `B ⟶ X` is zero, so Lemma `13.4.11` splits the triangle and
-- `A.isStableUnderRetracts_of_inclusion_isRightAdjoint hA` gives strict fullness of `A`,
-- forcing `X` to lie in `A`. The reverse inclusion is immediate from the definition of the left
-- orthogonal.
/-- If the inclusion of `A` into `D` has a left adjoint, then `A` equals the right orthogonal of
its left orthogonal. -/
theorem eq_leftOrthogonal_rightOrthogonal_of_inclusion_isRightAdjoint
    (hA : A.ι.IsRightAdjoint) :
    A = (^⊥A)^⊥ := sorry

end

end CategoryTheory.ObjectProperty

/-! ### Definition_13_40_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Definition 13.40.9:
- primary domain: admissible full triangulated subcategories of a triangulated category;
- sampled owner API:
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `Functor.IsRightAdjoint`,
  `Functor.IsLeftAdjoint`;
- best owner abstraction: the object property `A : ObjectProperty D` together with the canonical
  inclusion functor `A.ι : A.FullSubcategory ⥤ D`;
- primitive data:
  `A.IsTriangulated`,
  `A.IsClosedUnderIsomorphisms`,
  and the adjointness of the owner inclusion functor;
- ambient layer: only the pretriangulated structure on `D` is primitive here; the ambient
  hypothesis `[IsTriangulated D]` is not needed for the owner declarations themselves;
- derived API: the induced instances `A.ι.IsRightAdjoint` and `A.ι.IsLeftAdjoint`, and the
  one-sided admissibility instances recovered from two-sided admissibility;
- source/core/bridge triage:
  `source-facing`: right admissibility, left admissibility, and admissibility of a triangulated
    subcategory;
  `core/canonical`: the existing owners `ObjectProperty.IsTriangulated`,
    `ObjectProperty.IsClosedUnderIsomorphisms`, `Functor.IsRightAdjoint`, and
    `Functor.IsLeftAdjoint`;
  `bridge/view`: the inclusion functor `A.ι`, whose adjointness is the canonical functor-level
    view of admissibility.

No higher object replaces the source notion here: admissibility is intrinsically a property of the
owner object property `A`, and the only non-primitive data is the adjointness of `A.ι`. -/

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A right admissible subcategory is a strictly full triangulated subcategory satisfying the
equivalent conditions of Lemma `13.40.7`; here this is packaged by requiring the inclusion functor
to be a left adjoint, equivalently to admit a right adjoint. -/
class IsRightAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint

/-- A left admissible subcategory is a strictly full triangulated subcategory satisfying the
equivalent conditions of Lemma `13.40.8`; here this is packaged by requiring the inclusion functor
to be a right adjoint, equivalently to admit a left adjoint. -/
class IsLeftAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsRightAdjoint

/-- Definition 13.40.9: a two-sided admissible subcategory is a strictly full triangulated
subcategory that is both right admissible and left admissible. -/
class IsAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint, A.ι.IsRightAdjoint

instance instIsRightAdmissibleOfIsAdmissible (A : ObjectProperty D) [hA : IsAdmissible A] :
    IsRightAdmissible A where
  toIsTriangulated := hA.toIsTriangulated
  toIsClosedUnderIsomorphisms := hA.toIsClosedUnderIsomorphisms
  toIsLeftAdjoint := hA.toIsLeftAdjoint

instance instIsLeftAdmissibleOfIsAdmissible (A : ObjectProperty D) [hA : IsAdmissible A] :
    IsLeftAdmissible A where
  toIsTriangulated := hA.toIsTriangulated
  toIsClosedUnderIsomorphisms := hA.toIsClosedUnderIsomorphisms
  toIsRightAdjoint := hA.toIsRightAdjoint

end

end CategoryTheory.ObjectProperty

/-! ### Proposition_13_40_10 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem inverseImage_trW_rightOrthogonal_le_isomorphisms
    (A B : ObjectProperty D) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hB : B ≤ A^⊥) :
    (B.trW).inverseImage A.ι ≤ isomorphisms A.FullSubcategory := by
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff] at hf
  obtain ⟨Z, g, h, hT, hBZ⟩ := hf
  have hAZ : A Z :=
    A.ext_of_isTriangulatedClosed₃ (Triangle.mk (A.ι.map f) g h) hT X.2 Y.2
  have hZorth : (A^⊥) Z := hB _ hBZ
  have hZzero : IsZero Z := by
    refine (IsZero.iff_id_eq_zero Z).2 ?_
    exact hZorth (𝟙 Z) hAZ
  haveI : IsIso (A.ι.map f) := ((Triangle.mk (A.ι.map f) g h).isZero₃_iff_isIso₁ hT).1 hZzero
  letI : A.ι.ReflectsIsomorphisms := Functor.FullyFaithful.reflectsIsomorphisms A.fullyFaithfulι
  exact Functor.ReflectsIsomorphisms.reflects A.ι f

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A B : ObjectProperty D)

/- Domain-style sampling for Proposition 13.40.10:
- primary domain: semi-orthogonal decompositions and admissible triangulated subcategories;
- sampled owner declarations:
  `IsRightAdmissible`,
  `IsLeftAdmissible`,
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.extensionProduct`,
  `P.trW.Q : D ⥤ D / P`,
  `Functor.rightAdjoint`,
  `Functor.leftAdjoint`,
  `Localization.uniq`;
- best owner abstractions:
  the source-facing TFAE statement stays at the admissibility/orthogonal-extension-product layer,
  while the comparison functors to Verdier quotients should be expressed directly through the
  canonical orthogonal owners `A^⊥` and `^⊥B`, and the adjoint-description statements should use
  the chosen inclusion adjoints together with the inverse functors of the canonical quotient
  equivalences;
- primitive data: object properties `A`, `B` and the admissibility hypotheses;
- derived API: the orthogonal equalities, the extension-product condition, and the quotient
  comparison equivalences, plus the resulting identifications of the inclusion adjoints as
  composites through those quotient equivalences;
- source/core/bridge triage:
  `source-facing`: the TFAE theorem for admissibility and semi-orthogonal decomposition;
  `core/canonical`: orthogonals, extension product, and the quotient owner `D / P`;
  `bridge/view`: the comparison functors from admissible subcategories to the corresponding
    Verdier quotients, together with the description of the inclusion adjoints via quasi-inverses
    to those comparison functors.

The comparison theorems below should therefore target the canonical quotients by `A^⊥` and `^⊥B`
rather than an arbitrary equal copy, and the adjoint-description theorems should be stated as
functor isomorphisms rather than wrapper definitions. -/

-- Proof sketch: combine Lemma `13.40.7` for `A` with Lemma `13.40.8` for `B`. The condition
-- `B = A^⊥` identifies the right-admissible and left-admissible descriptions, while
-- the triangle condition is exactly the extension-product statement `A ⋆ B = ⊤`
-- together with the orthogonality inclusion `B ≤ A^⊥`, under the source-facing hypotheses that
-- `A` and `B` are strictly full triangulated subcategories.
/-- Proposition 13.40.10: the following are equivalent for subcategories `A, B` of a triangulated
category `D`: `A` is right admissible with `B = A^⊥`, `B` is left admissible with
`A = ^⊥B`, and `A` and `B` are strictly full triangulated subcategories such that `B` is
right-orthogonal to `A` and every object of `D` fits into a distinguished triangle
`A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A' ∈ A` and `B' ∈ B`. -/
theorem tfae_rightAdmissible_leftAdmissible_orthogonal_triangleDecomposition :
    List.TFAE
      [ IsRightAdmissible A ∧ B = A^⊥
      , IsLeftAdmissible B ∧ A = ^⊥B
      , A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧
          B.IsTriangulated ∧ B.IsClosedUnderIsomorphisms ∧
          B ≤ A^⊥ ∧ A ⋆ B = ⊤ ] := sorry

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D)

private instance : ((A^⊥).trW.Q : D ⥤ D / (A^⊥)).IsLocalization (A^⊥).trW :=
  Functor.q_isLocalization (A^⊥).trW

-- Proof sketch: under `hA`, every object of `D` admits a triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧`
-- with `A' ∈ A` and `B' ∈ A^⊥`. The first morphism becomes an isomorphism in `D / (A^⊥)` because
-- its cone lies in `A^⊥`, so the quotient of `X` is represented by an object of `A`.
-- Full faithfulness follows from the orthogonality relation and the universal property of
-- the Verdier quotient.
/-- If `A` is right admissible, then the canonical comparison functor
`A ⥤ D / (A^⊥)` is an equivalence. Under the additional ambient hypothesis
`[IsTriangulated D]`, the canonical exactness instances upgrade this to the triangulated
equivalence appearing in Proposition 13.40.10. -/
theorem rightAdmissibleComparisonFunctor_isEquivalence
    [IsRightAdmissible A] :
    Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q) := sorry

private instance [IsRightAdmissible A] : Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q) :=
  rightAdmissibleComparisonFunctor_isEquivalence A

-- Proof sketch: an object lies in the kernel of the chosen right adjoint exactly when every map
-- from an object of `A` to it vanishes. The forward direction is immediate from the adjunction.
-- Conversely, if `X ∈ A^⊥`, then the counit `A.ι.obj (A.ι.rightAdjoint.obj X) ⟶ X` is zero, so
-- the identity of `A.ι.rightAdjoint.obj X` is zero by adjunction, hence `A.ι.rightAdjoint.obj X`
-- is a zero object.
/-- Under right admissibility, the kernel of the chosen right adjoint to the inclusion `A ⥤ D`
is exactly the right orthogonal `A^⊥`. -/
theorem rightAdmissible_rightAdjoint_kernel_eq_rightOrthogonal
    [IsRightAdmissible A] :
    Functor.kernel A.ι.rightAdjoint = A^⊥ := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  ext X
  constructor
  · intro hX
    rw [A.rightOrthogonal_iff]
    intro Y f hY
    exact (adj.homEquiv ⟨Y, hY⟩ X).injective (hX.eq_of_tgt _ _)
  · intro hX
    rw [A.rightOrthogonal_iff] at hX
    have hzero : adj.counit.app X = 0 :=
      hX (adj.counit.app X) (A.ι.rightAdjoint.obj X).2
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply (adj.homEquiv (A.ι.rightAdjoint.obj X) X).symm.injective
    rw [Adjunction.homEquiv_symm_id]
    rw [hzero]
    rw [Adjunction.homEquiv_counit]
    simp
    rfl

-- Proof sketch: the chosen right adjoint is exact by the triangulated-adjunction API. The
-- Bousfield-localization description of a right adjoint to a fully faithful inclusion identifies
-- the morphisms it inverts with the inverse image of isomorphisms; the exact-functor kernel owner
-- rewrites that morphism property as `(Functor.kernel A.ι.rightAdjoint).trW`, and the previous
-- theorem identifies this kernel with `A^⊥`.
/-- Under right admissibility, the chosen right adjoint to the
inclusion `A ⥤ D` is a localization functor for the Verdier morphism property `(A^⊥).trW`. -/
theorem rightAdmissible_rightAdjoint_isLocalization
    [IsRightAdmissible A] :
    A.ι.rightAdjoint.IsLocalization (A^⊥).trW := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI : A.ι.rightAdjoint.IsTriangulated := adj.isTriangulated_rightAdjoint
  rw [← rightAdmissible_rightAdjoint_kernel_eq_rightOrthogonal A]
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor A.ι.rightAdjoint]
  rw [← ObjectProperty.isColocal_eq_inverseImage_isomorphisms adj]
  exact ObjectProperty.isLocalization_isColocal adj

-- Proof sketch: both `A.ι.rightAdjoint` and the Verdier quotient functor `(A^⊥).trW.Q` localize
-- at `(A^⊥).trW`, so `Localization.compUniqInverse` identifies `A.ι.rightAdjoint` with
-- `(A^⊥).trW.Q` composed with the inverse functor of the canonical localization equivalence. The
-- left adjoint `A.ι` is fully faithful, so its unit is an isomorphism; this identifies that
-- canonical localization equivalence with the comparison equivalence
-- `A.ι ⋙ (A^⊥).trW.Q`. Uniqueness of right adjoints for a fixed left adjoint
-- then transports the inverse functor accordingly.
/-- Under right admissibility, the chosen right adjoint to the inclusion `A ⥤ D` is canonically
isomorphic to the composite `D ⥤ D / (A^⊥) ⥤ A`, where the second functor is a quasi-inverse to
the comparison equivalence `A.ι ⋙ (A^⊥).trW.Q : A ⥤ D / (A^⊥)`. This is the
adjoint-description part of Proposition 13.40.10. -/
noncomputable def rightAdmissible_rightAdjointIso_quotientCompInverse
    [IsRightAdmissible A] :
    A.ι.rightAdjoint ≅
      (A^⊥).trW.Q ⋙ (A.ι ⋙ (A^⊥).trW.Q).asEquivalence.inverse :=
  letI : A.ι.rightAdjoint.IsLocalization (A^⊥).trW :=
    rightAdmissible_rightAdjoint_isLocalization A
  let quotientFunctor : D ⥤ D / (A^⊥) := (A^⊥).trW.Q
  letI : quotientFunctor.IsLocalization (A^⊥).trW := by
    change ((A^⊥).trW.Q : D ⥤ D / (A^⊥)).IsLocalization (A^⊥).trW
    infer_instance
  let comparisonFunctor : A.FullSubcategory ⥤ D / (A^⊥) := A.ι ⋙ quotientFunctor
  letI : comparisonFunctor.IsEquivalence := by
    change Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q)
    infer_instance
  let e : A.FullSubcategory ≌ D / (A^⊥) :=
    Localization.uniq A.ι.rightAdjoint quotientFunctor (A^⊥).trW
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  let i : e.functor ≅ comparisonFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.unit) e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.rightAdjoint quotientFunctor (A^⊥).trW)
  let j : e.inverse ≅ comparisonFunctor.asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      comparisonFunctor.asEquivalence.toAdjunction
  (Localization.compUniqInverse A.ι.rightAdjoint quotientFunctor (A^⊥).trW).symm ≪≫
    Functor.isoWhiskerLeft quotientFunctor j

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (B : ObjectProperty D)

private instance : ((^⊥B).trW.Q : D ⥤ D / (^⊥B)).IsLocalization (^⊥B).trW :=
  Functor.q_isLocalization (^⊥B).trW

-- Proof sketch: this is the dual quotient argument. Under `hB`, every object of `D`
-- admits a triangle `B' ⟶ X ⟶ A' ⟶ B'⟦1⟧` with `B' ∈ B` and `A' ∈ ^⊥B`, so the quotient by
-- `^⊥B` is represented by an object of `B`. Orthogonality gives full faithfulness in the quotient.
/-- If `B` is left admissible, then the canonical comparison functor
`B ⥤ D / (^⊥B)` is an equivalence. Under the additional ambient hypothesis
`[IsTriangulated D]`, the canonical exactness instances upgrade this to the second triangulated
equivalence appearing in Proposition 13.40.10. -/
theorem leftAdmissibleComparisonFunctor_isEquivalence
    [IsLeftAdmissible B] :
    Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q) := sorry

private instance [IsLeftAdmissible B] : Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q) :=
  leftAdmissibleComparisonFunctor_isEquivalence B

-- Proof sketch: this is the dual kernel computation. If `B.ι.leftAdjoint.obj X` is zero, then
-- every morphism `X ⟶ Y` with `Y ∈ B` vanishes by adjunction. Conversely, if `X ∈ ^⊥B`, then the
-- unit `X ⟶ B.ι.obj (B.ι.leftAdjoint.obj X)` is zero, so the identity of
-- `B.ι.leftAdjoint.obj X` is zero by adjunction.
/-- Under left admissibility, the kernel of the chosen left adjoint to the inclusion `B ⥤ D`
is exactly the left orthogonal `^⊥B`. -/
theorem leftAdmissible_leftAdjoint_kernel_eq_leftOrthogonal
    [IsLeftAdmissible B] :
    Functor.kernel B.ι.leftAdjoint = ^⊥B := by
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  ext X
  constructor
  · intro hX
    rw [B.leftOrthogonal_iff]
    intro Y f hY
    exact (adj.homEquiv X ⟨Y, hY⟩).symm.injective (hX.eq_of_src _ _)
  · intro hX
    rw [B.leftOrthogonal_iff] at hX
    have hzero : adj.unit.app X = 0 :=
      hX (adj.unit.app X) (B.ι.leftAdjoint.obj X).2
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply (adj.homEquiv X (B.ι.leftAdjoint.obj X)).injective
    rw [Adjunction.homEquiv_id]
    rw [hzero]
    rw [Adjunction.homEquiv_unit]
    simp
    rfl

-- Proof sketch: dually, the chosen left adjoint is exact by the triangulated-adjunction API. The
-- Bousfield-localization description of a left adjoint to a fully faithful right adjoint rewrites
-- the inverted morphisms as the inverse image of isomorphisms, hence as the `trW` owner of its
-- kernel; the previous theorem identifies that kernel with `^⊥B`.
/-- Under left admissibility, the chosen left adjoint to the inclusion
`B ⥤ D` is a localization functor for the Verdier morphism property `(^⊥B).trW`. -/
theorem leftAdmissible_leftAdjoint_isLocalization
    [IsLeftAdmissible B] :
    B.ι.leftAdjoint.IsLocalization (^⊥B).trW := by
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  letI := adj.leftAdjointCommShift ℤ
  letI := adj.commShift_of_rightAdjoint ℤ
  letI : B.ι.leftAdjoint.IsTriangulated := adj.isTriangulated_leftAdjoint
  rw [← leftAdmissible_leftAdjoint_kernel_eq_leftOrthogonal B]
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor B.ι.leftAdjoint]
  rw [← ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]
  exact ObjectProperty.isLocalization_isLocal adj

-- Proof sketch: both `B.ι.leftAdjoint` and the Verdier quotient functor `(^⊥B).trW.Q` localize
-- at `(^⊥B).trW`, so `Localization.compUniqInverse` identifies `B.ι.leftAdjoint` with
-- `(^⊥B).trW.Q` composed with the inverse functor of the canonical localization equivalence.
-- Since `B.ι` is fully faithful, the counit of `B.ι.leftAdjoint ⊣ B.ι` is an isomorphism, which
-- identifies that canonical localization equivalence with the comparison equivalence
-- `B.ι ⋙ (^⊥B).trW.Q`.
-- Uniqueness of right adjoints then transports the inverse functor.
/-- Under left admissibility, the chosen left adjoint to the inclusion `B ⥤ D` is canonically
isomorphic to the composite `D ⥤ D / (^⊥B) ⥤ B`, where the second functor is a quasi-inverse to
the comparison equivalence `B.ι ⋙ (^⊥B).trW.Q : B ⥤ D / (^⊥B)`. This is the dual
adjoint-description part of Proposition 13.40.10. -/
noncomputable def leftAdmissible_leftAdjointIso_quotientCompInverse
    [IsLeftAdmissible B] :
    B.ι.leftAdjoint ≅
      (^⊥B).trW.Q ⋙ (B.ι ⋙ (^⊥B).trW.Q).asEquivalence.inverse :=
  letI : B.ι.leftAdjoint.IsLocalization (^⊥B).trW :=
    leftAdmissible_leftAdjoint_isLocalization B
  let quotientFunctor : D ⥤ D / (^⊥B) := (^⊥B).trW.Q
  letI : quotientFunctor.IsLocalization (^⊥B).trW := by
    change ((^⊥B).trW.Q : D ⥤ D / (^⊥B)).IsLocalization (^⊥B).trW
    infer_instance
  let comparisonFunctor : B.FullSubcategory ⥤ D / (^⊥B) := B.ι ⋙ quotientFunctor
  letI : comparisonFunctor.IsEquivalence := by
    change Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q)
    infer_instance
  let e : B.FullSubcategory ≌ D / (^⊥B) :=
    Localization.uniq B.ι.leftAdjoint quotientFunctor (^⊥B).trW
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  let i : e.functor ≅ comparisonFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft B.ι
        (Localization.compUniqFunctor B.ι.leftAdjoint quotientFunctor (^⊥B).trW)
  let j : e.inverse ≅ comparisonFunctor.asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      comparisonFunctor.asEquivalence.toAdjunction
  (Localization.compUniqInverse B.ι.leftAdjoint quotientFunctor (^⊥B).trW).symm ≪≫
    Functor.isoWhiskerLeft quotientFunctor j

end

end CategoryTheory.ObjectProperty
