import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_40_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_40_3

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Lemma 13.40.8: the partial-left-adjoint domain is equivalent to the existence of a
universal morphism from `X` to an object of `A`. -/
lemma leftAdjointObjIsDefined_iff_exists_local_morphism (X : D) :
    A.ι.leftAdjointObjIsDefined X ↔ ∃ (Z : A.FullSubcategory) (u : X ⟶ Z.obj), A.isLocal u := by
  -- Proof comment: unpack corepresentability to the universal element `X ⟶ Z`, and conversely
  -- package a local morphism back into a corepresenting object.
  rw [Functor.leftAdjointObjIsDefined_iff]
  constructor
  · intro h
    rcases h.has_corepresentation with ⟨Z, ⟨e⟩⟩
    let u : X ⟶ Z.obj := e.homEquiv (𝟙 Z)
    refine ⟨Z, u, ?_⟩
    intro Y hY
    let Y' : A.FullSubcategory := ⟨Y, hY⟩
    let eY : (Z ⟶ Y') ≃ (X ⟶ Y) := e.homEquiv
    constructor
    · intro g₁ g₂ hg
      have hg₁ : eY (homMk g₁ : Z ⟶ Y') = u ≫ g₁ := by
        simpa [u, eY, Y'] using
          (Functor.CorepresentableBy.homEquiv_eq e (homMk g₁ : Z ⟶ Y'))
      have hg₂ : eY (homMk g₂ : Z ⟶ Y') = u ≫ g₂ := by
        simpa [u, eY, Y'] using
          (Functor.CorepresentableBy.homEquiv_eq e (homMk g₂ : Z ⟶ Y'))
      have hg' : eY (homMk g₁ : Z ⟶ Y') = eY (homMk g₂ : Z ⟶ Y') := by
        rw [hg₁, hg₂]
        exact hg
      have hhom : (homMk g₁ : Z ⟶ Y') = homMk g₂ := eY.injective hg'
      simpa using congrArg (fun f : Z ⟶ Y' => f.hom) hhom
    · intro k
      obtain ⟨g, hg⟩ := eY.surjective k
      have hg' : u ≫ g.hom = k := by
        exact (Functor.CorepresentableBy.homEquiv_eq e g).symm.trans hg
      exact ⟨g.hom, hg'⟩
  · rintro ⟨Z, u, hu⟩
    refine ⟨Z, ⟨?_⟩⟩
    -- Proof comment: the locality bijection is the required corepresenting Hom-equivalence.
    refine
      { homEquiv := ?_
        homEquiv_comp := ?_ }
    · intro Y
      let e := ObjectProperty.isLocal.homEquiv hu Y.obj Y.property
      refine
        { toFun := fun f ↦ u ≫ f.hom
          invFun := fun g ↦ homMk (e.symm g)
          left_inv := ?_
          right_inv := ?_ }
      · intro f
        apply hom_ext
        have hcomp : e (e.symm (u ≫ f.hom)) = e f.hom := by
          rw [e.apply_symm_apply]
          rfl
        exact e.injective hcomp
      · intro g
        exact e.apply_symm_apply g
    · intro Y Y' g f
      change (fun f' : Z ⟶ Y' => u ≫ f'.hom) (f ≫ g) =
        (A.ι ⋙ coyoneda.obj (Opposite.op X)).map g ((fun f' : Z ⟶ Y => u ≫ f'.hom) f)
      simp [Category.assoc]

/-- Helper for Lemma 13.40.8: membership in `(^⊥A) ⋆ A` is equivalent to the existence of a local
morphism from `X` into an object of `A`. -/
lemma leftOrthogonal_extensionProduct_iff_exists_local_morphism (X : D) :
    ((^⊥A) ⋆ A) X ↔ ∃ (Z : A.FullSubcategory) (u : X ⟶ Z.obj), A.isLocal u := by
  constructor
  · intro hX
    rw [extensionProduct_iff] at hX
    rcases hX with ⟨K, Z, f, u, h, hT, hK, hZ⟩
    -- Proof comment: the triangle witnessing extension-product membership already carries the
    -- desired local morphism by Lemma 13.40.3.
    refine ⟨⟨Z, hZ⟩, u, ?_⟩
    exact (leftOrthogonal_obj₁_iff_isLocal_mor₂ A (Triangle.mk f u h) hT).1 hK
  · rintro ⟨Z, u, hu⟩
    -- Proof comment: complete the local morphism to a distinguished triangle and recover the
    -- left-orthogonal first term from the same bridge theorem.
    obtain ⟨K, f, h, hT⟩ := distinguished_cocone_triangle₁ u
    refine ⟨K, Z.obj, f, u, h, hT, ?_, Z.property⟩
    exact (leftOrthogonal_obj₁_iff_isLocal_mor₂ A (Triangle.mk f u h) hT).2 hu

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
  ext X
  -- Proof comment: both owner predicates normalize to the same universal-morphism condition.
  rw [A.leftAdjointObjIsDefined_iff_exists_local_morphism,
    A.leftOrthogonal_extensionProduct_iff_exists_local_morphism]

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

/-- Helper for Lemma 13.40.8: if `X` retracts onto an object of `A`, then any `A`-local morphism
`X ⟶ Z` with `Z ∈ A` exhibits `X` as a retract of `Z`. -/
lemma retract_of_isLocal_of_retract_into_A {X Y : D} {Z : A.FullSubcategory}
    (u : X ⟶ Z.obj) (hu : A.isLocal u) (r : Retract X Y) (hY : A Y) :
    Nonempty (Retract X Z.obj) := by
  -- Proof comment: factor the retract inclusion `X ⟶ Y` uniquely through the local morphism,
  -- then postcompose with the given retraction `Y ⟶ X`.
  let g : Z.obj ⟶ Y := (ObjectProperty.isLocal.homEquiv hu Y hY).symm r.i
  have hg : u ≫ g = r.i :=
    (ObjectProperty.isLocal.homEquiv hu Y hY).apply_symm_apply r.i
  refine ⟨
    { i := u
      r := g ≫ r.r
      retract := by
        calc
          u ≫ (g ≫ r.r) = (u ≫ g) ≫ r.r := by rw [Category.assoc]
          _ = r.i ≫ r.r := by rw [hg]
          _ = 𝟙 X := r.retract }⟩

/-- Helper for Lemma 13.40.8: an object in the left orthogonal that retracts into an object of
`A` must be zero. -/
lemma isZero_of_leftOrthogonal_retract_into_A {K Y : D}
    (hK : ^⊥A K) (r : Retract K Y) (hY : A Y) :
    IsZero K := by
  -- Proof comment: the retract inclusion `K ⟶ Y` vanishes by left orthogonality, so the
  -- idempotent `𝟙_K = r.i ≫ r.r` is zero.
  refine (IsZero.iff_id_eq_zero K).2 ?_
  calc
    𝟙 K = r.i ≫ r.r := by symm; exact r.retract
    _ = 0 := by rw [hK r.i hY, zero_comp]

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
