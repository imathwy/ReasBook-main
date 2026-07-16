import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_33_10
import stacks_proof.stacks_project.Chap04.Lemma_4_33_11
import stacks_proof.stacks_project.Chap04.Lemma_4_32_5
import stacks_proof.stacks_project.Chap04.Lemma_4_39_6
import stacks_proof.stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories
import stacks_proof.stacks_project.Chap08.Definition_8_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 8.2.5:
- primary domain: the source `2`-fibre product
  `S ×_{S × S, (x, y)} C/U`, whose objects over `a : V ⟶ U` are
  `(a, z, α : z ≅ a^*x, β : z ≅ a^*y)`;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `explicitTwoFibreProductLeftProjection`,
  `Functor.fiberIsoClassPresheaf`,
  `fiberIsomorphismSubfunctor`;
- correction from the previous refinement: the raw product
  `C/U ×_S C/U` only fixes the left slice object and lets the right slice object vary over the
  same base.  The source lemma fixes the same slice object `a` on both sides.  The corrected
  statement below therefore uses the diagonal fibre subcategory cut out by equality of the right
  projection with the fixed left slice object;
- primitive data: the fibred category `X`, an object `U : C`, and fiber objects
  `x y : X.p.Fiber U`;
- derived API: the auxiliary off-diagonal projection, its right projection, the diagonal fibre
  subcategory, and the source-facing equivalence with `Isom(x, y)`.

Source/core/bridge triage:
- `source-facing`: `fiberObjectDiagonalFiberCategory` and
  `fiberIsomorphismSubfunctor_toFunctor_equiv_diagonalFiberIsoClasses`;
- `core/canonical`: `fiberIsomorphismSubfunctor`, `isomorphismClasses`, and the explicit
  `2`-fibre-product projections;
- `bridge/view`: the old global equality with `fiberIsoClassPresheaf` is intentionally not stated,
  because it is false for the off-diagonal projection. -/

open Opposite

universe u v uS

namespace CategoryTheory

open CategoryOver
open Functor
open Functor.IsHomLift

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/-- The pullback-model `2`-Yoneda morphism `C/U ⟶ X` corresponding to an object of the fibre
`X_U`. -/
private noncomputable def fiberObjectYonedaBasedFunctor
    (X : FibredCategoryOver C) {U : C} (x : X.p.Fiber U) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
  ((X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x).toHom

/-- Auxiliary off-diagonal slice `2`-fibre-product projection.  Its fibre over `f : V ⟶ U`
allows the right slice object to vary over the same base `V`; Lemma 8.2.5 uses the diagonal
subcategory where the right slice object is also `f`. -/
noncomputable def fiberObjectSliceProjection
    (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U) :
    (explicitTwoFibreProduct
      (fiberObjectYonedaBasedFunctor X x)
      (fiberObjectYonedaBasedFunctor X y)).obj ⥤ Over U :=
  (explicitTwoFibreProductLeftProjection
    (fiberObjectYonedaBasedFunctor X x)
    (fiberObjectYonedaBasedFunctor X y)).toFunctor

/-- The right projection from the same auxiliary off-diagonal `2`-fibre product. -/
noncomputable def fiberObjectSliceRightProjection
    (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U) :
    (explicitTwoFibreProduct
      (fiberObjectYonedaBasedFunctor X x)
      (fiberObjectYonedaBasedFunctor X y)).obj ⥤ Over U :=
  (explicitTwoFibreProductRightProjection
    (fiberObjectYonedaBasedFunctor X x)
    (fiberObjectYonedaBasedFunctor X y)).toFunctor

section

variable (X : FibredCategoryOver C) {U : C} (x y : X.p.Fiber U)

/-- Helper for Chap08 Lemma 8 2 5: each fibre of the slice forgetful functor is thin. -/
private theorem overForget_fiber_isThin
    (U V : C) :
    Quiver.IsThin ((Over.forget U).Fiber V) := by
  intro A B
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Both fibre morphisms lift the same transported identity on the fixed base `V`.
  let base : A.1.left ⟶ B.1.left :=
    eqToHom A.2 ≫ 𝟙 V ≫ eqToHom B.2.symm
  letI : (Over.forget U).IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map φ) := by
    simpa using φ.2
  letI : (Over.forget U).IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map ψ) := by
    simpa using ψ.2
  have hφ : (Functor.Fiber.fiberInclusion.map φ).left = base := by
    simpa [Over.forget, base] using
      IsHomLift.fac' (Over.forget U) (𝟙 V) (Functor.Fiber.fiberInclusion.map φ)
  have hψ : (Functor.Fiber.fiberInclusion.map ψ).left = base := by
    simpa [Over.forget, base] using
      IsHomLift.fac' (Over.forget U) (𝟙 V) (Functor.Fiber.fiberInclusion.map ψ)
  -- Equality in the fibre is detected after forgetting to the slice category.
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  rw [hφ, hψ]

/-- Helper for Chap08 Lemma 8 2 5: an object of the slice fibre whose underlying slice object is
the fixed slice object is equal to the standard representative of that fibre. -/
private theorem overForget_fiber_eq_of_obj_eq
    (f : Over U) (a : (Over.forget U).Fiber f.left) (ha : a.1 = f) :
    a = Functor.Fiber.mk (p := Over.forget U) rfl := by
  apply Subtype.ext
  exact ha

-- Proof sketch: over an object `f : V ⟶ U` of the slice category, Lemma `4.42.1` identifies the
-- corresponding fibre with a structured-arrow category whose source fibre in `C/U` is thin. Hence
-- any two morphisms in that fibre agree.
/-- Every standard fibre of the auxiliary off-diagonal slice projection is a setoid `1`-category.
-/
private theorem fiberObjectSliceProjection_fiber_isThin
    (f : Over U) :
    Quiver.IsThin ((X.fiberObjectSliceProjection x y).Fiber f) := by
  intro P Q
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Normalize the fixed left projection, then compare the two explicit product components.
  match P, Q, φ, ψ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      φ, ψ =>
        apply Functor.Fiber.hom_ext
        apply ExplicitTwoFibreProductHom.ext
        · letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) φ.1 := by
            simpa using φ.2
          letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) ψ.1 := by
            simpa using ψ.2
          have hφa : (Functor.Fiber.fiberInclusion.map φ).a = 𝟙 f := by
            simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
              explicitTwoFibreProduct] using
                IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) φ.1
          have hψa : (Functor.Fiber.fiberInclusion.map ψ).a = 𝟙 f := by
            simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
              explicitTwoFibreProduct] using
                IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) ψ.1
          rw [hφa, hψa]
        · letI : (Over.forget U).IsHomLift (𝟙 f.left) φ.1.b := by
            letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
              simpa using φ.1.a_over
            letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) φ.1 := by
              simpa using φ.2
            have hφa : φ.1.a = 𝟙 f := by
              simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
                explicitTwoFibreProduct] using
                  IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) φ.1
            have hbase : φ.1.base = 𝟙 f.left := by
              simpa [hφa] using IsHomLift.fac (Over.forget U) φ.1.base φ.1.a
            simpa [hbase] using φ.1.b_over
          letI : (Over.forget U).IsHomLift (𝟙 f.left) ψ.1.b := by
            letI : (Over.forget U).IsHomLift ψ.1.base ψ.1.a := by
              simpa using ψ.1.a_over
            letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) ψ.1 := by
              simpa using ψ.2
            have hψa : ψ.1.a = 𝟙 f := by
              simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
                explicitTwoFibreProduct] using
                  IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) ψ.1
            have hbase : ψ.1.base = 𝟙 f.left := by
              simpa [hψa] using IsHomLift.fac (Over.forget U) ψ.1.base ψ.1.a
            simpa [hbase] using ψ.1.b_over
          change (Functor.Fiber.fiberInclusion.map φ).b =
            (Functor.Fiber.fiberInclusion.map ψ).b
          let φright :=
            Functor.Fiber.homMk (Over.forget U) f.left φ.1.b
          let ψright :=
            Functor.Fiber.homMk (Over.forget U) f.left ψ.1.b
          letI : Quiver.IsThin ((Over.forget U).Fiber f.left) :=
            overForget_fiber_isThin U f.left
          have hright : φright = ψright := Subsingleton.elim φright ψright
          simpa [φright, ψright] using congrArg (fun η ↦ η.1) hright

/-- Helper for Chap08 Lemma 8 2 5: every morphism in a fibre of the auxiliary off-diagonal
slice projection is an isomorphism. -/
private theorem fiberObjectSliceProjection_fiber_hom_isIso
    (f : Over U) {P Q : (X.fiberObjectSliceProjection x y).Fiber f}
    (φ : P ⟶ Q) : IsIso φ := by
  -- Normalize the fixed left projection and build the inverse from the two slice-fibre inverses.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, sndP, isoP⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, sndQ, isoQ⟩⟩, rfl⟩,
      φ =>
        have hφa_lift : (Over.forget U).IsHomLift (𝟙 f.left) φ.1.a := by
          letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
            simpa using φ.1.a_over
          letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) φ.1 := by
            simpa using φ.2
          have hφa : φ.1.a = 𝟙 f := by
            simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
              explicitTwoFibreProduct] using
                IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) φ.1
          have hbase : φ.1.base = 𝟙 f.left := by
            simpa [hφa] using IsHomLift.fac (Over.forget U) φ.1.base φ.1.a
          simpa [hbase] using φ.1.a_over
        have hφb_lift : (Over.forget U).IsHomLift (𝟙 f.left) φ.1.b := by
          letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
            simpa using φ.1.a_over
          letI : (Over.forget U).IsHomLift φ.1.base φ.1.b := by
            simpa using φ.1.b_over
          letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) φ.1 := by
            simpa using φ.2
          have hφa : φ.1.a = 𝟙 f := by
            simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
              explicitTwoFibreProduct] using
                IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) φ.1
          have hbase : φ.1.base = 𝟙 f.left := by
            simpa [hφa] using IsHomLift.fac (Over.forget U) φ.1.base φ.1.a
          simpa [hbase] using φ.1.b_over
        let fFiber : (Over.forget U).Fiber f.left :=
          Functor.Fiber.mk (p := Over.forget U) rfl
        let φleft : fFiber ⟶ fFiber :=
          ⟨φ.1.a, hφa_lift⟩
        let φright : sndP ⟶ sndQ :=
          ⟨φ.1.b, by simpa using hφb_lift⟩
        let ψleft := inv φleft
        letI : Quiver.IsThin ((Over.forget U).Fiber f.left) :=
          overForget_fiber_isThin U f.left
        let fwdBase : sndP.1.left ⟶ sndQ.1.left :=
          eqToHom sndP.2 ≫ eqToHom sndQ.2.symm
        let invBase : sndQ.1.left ⟶ sndP.1.left :=
          eqToHom sndQ.2 ≫ eqToHom sndP.2.symm
        have hφright_left : φ.1.b.left = fwdBase := by
          letI : (Over.forget U).IsHomLift (𝟙 f.left) φ.1.b := hφb_lift
          simpa [Over.forget, fwdBase] using
            IsHomLift.fac' (Over.forget U) (𝟙 f.left) φ.1.b
        have hforward : fwdBase ≫ sndQ.1.hom = sndP.1.hom := by
          rw [← hφright_left]
          simpa using φ.1.b.w
        have hinvBase : invBase ≫ sndP.1.hom = sndQ.1.hom := by
          rw [← hforward]
          simp [invBase, fwdBase]
        let ψright0 : sndQ.1 ⟶ sndP.1 :=
          Over.homMk invBase hinvBase
        have ψright0_over : (Over.forget U).IsHomLift (𝟙 f.left) ψright0 := by
          refine IsHomLift.of_fac' (Over.forget U) (𝟙 f.left) ψright0 sndQ.2 sndP.2 ?_
          simp [Over.forget, ψright0, invBase]
        let ψright : sndQ ⟶ sndP :=
          ⟨ψright0, ψright0_over⟩
        have hψleft : ψleft.1 = 𝟙 f := by
          have hψ : ψleft = 𝟙 fFiber :=
            Subsingleton.elim ψleft (𝟙 fFiber)
          simpa [ψleft] using congrArg (fun η ↦ η.1) hψ
        let eA : _ ≅ _ :=
          { hom := φleft.1
            inv := ψleft.1
            hom_inv_id := by
              exact congrArg (fun η ↦ η.1) (Iso.hom_inv_id (asIso φleft))
            inv_hom_id := by
              exact congrArg (fun η ↦ η.1) (Iso.inv_hom_id (asIso φleft)) }
        let eB : _ ≅ _ :=
          { hom := φright.1
            inv := ψright.1
            hom_inv_id := by
              have h : φright ≫ ψright = 𝟙 sndP :=
                (overForget_fiber_isThin U f.left sndP sndP).elim
                  (φright ≫ ψright) (𝟙 sndP)
              exact congrArg (fun η ↦ η.1) h
            inv_hom_id := by
              have h : ψright ≫ φright = 𝟙 sndQ :=
                (overForget_fiber_isThin U f.left sndQ sndQ).elim
                  (ψright ≫ φright) (𝟙 sndQ)
              exact congrArg (fun η ↦ η.1) h }
        let eFA :=
          Functor.mapIso (fiberObjectYonedaBasedFunctor X x).toFunctor eA
        let eGB :=
          Functor.mapIso (fiberObjectYonedaBasedFunctor X y).toFunctor eB
        have hcomm :
            CommSq ((fiberObjectYonedaBasedFunctor X x).toFunctor.map ψleft.1)
              isoQ.hom.1 isoP.hom.1
              ((fiberObjectYonedaBasedFunctor X y).toFunctor.map ψright.1) := by
          simpa [eFA, eGB, eA, eB] using
            (CommSq.horiz_inv (f := eFA) (i := eGB) φ.1.comm)
        let ψ0 :
            ({ U := f.left, obj := { fst := fFiber, snd := sndQ, iso := isoQ } } :
              (explicitTwoFibreProduct
                (fiberObjectYonedaBasedFunctor X x)
                (fiberObjectYonedaBasedFunctor X y)).obj) ⟶
              ({ U := f.left, obj := { fst := fFiber, snd := sndP, iso := isoP } } :
                (explicitTwoFibreProduct
                  (fiberObjectYonedaBasedFunctor X x)
                  (fiberObjectYonedaBasedFunctor X y)).obj) :=
          { base := 𝟙 f.left
            a := ψleft.1
            a_over := ψleft.2
            b := ψright.1
            b_over := ψright.2
            comm := hcomm }
        have hψ0 : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) ψ0 := by
          refine IsHomLift.of_fac' (X.fiberObjectSliceProjection x y) (𝟙 f) ψ0 rfl rfl ?_
          have hid : (𝟙 f : f ⟶ f) = 𝟙 (fFiber.1) := by
            rfl
          simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
            explicitTwoFibreProduct, ψ0, fFiber, hψleft] using hid
        let ψ : _ ⟶ _ :=
          Functor.Fiber.homMk (X.fiberObjectSliceProjection x y) f ψ0
        letI : Quiver.IsThin ((X.fiberObjectSliceProjection x y).Fiber f) :=
          fiberObjectSliceProjection_fiber_isThin X x y f
        refine ⟨⟨ψ, ?_, ?_⟩⟩
        · exact Subsingleton.elim _ _
        · exact Subsingleton.elim _ _

/-- Helper for Chap08 Lemma 8 2 5: every fibre of the auxiliary off-diagonal slice projection is
a groupoid. -/
private theorem fiberObjectSliceProjection_fiber_isGroupoid
    (f : Over U) :
    IsGroupoid ((X.fiberObjectSliceProjection x y).Fiber f) where
  all_isIso φ := fiberObjectSliceProjection_fiber_hom_isIso X x y f φ

/-- Helper for Chap08 Lemma 8 2 5: a morphism of fibred categories preserves strong
cartesianness over the same displayed base arrow. -/
private theorem fiberObject_map_stronglyCartesian_over_base
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} {a b : Y.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : Y.p.IsStronglyCartesian f φ) :
    Z.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map φ) := by
  have hφ' : Y.p.IsStronglyCartesian (Y.p.map φ) φ := by
    letI : Y.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift Y.p f φ
    simpa using hφ
  have hmap :
      Z.p.IsStronglyCartesian (Z.p.map ((FibredCategoryMor.toFunctor F).map φ))
        ((FibredCategoryMor.toFunctor F).map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  have hLift : Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := by
    letI : Y.p.IsHomLift f φ := hφ.toIsHomLift
    change Z.p.IsHomLift f ((FibredCategoryMor.toBasedFunctor F).map φ)
    exact BasedFunctor.preserves_isHomLift (FibredCategoryMor.toBasedFunctor F) f φ
  letI : Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := hLift
  subst_hom_lift Z.p f ((FibredCategoryMor.toFunctor F).map φ)
  simpa using hmap

/-- Auxiliary fact: the off-diagonal slice projection is fibred in setoids.  This is useful
infrastructure, but it is not the source statement of Lemma 8.2.5; the source statement is the
fixed-diagonal fibre comparison below. -/
theorem fiberObjectSliceProjection_isFibredInSetoids :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) := by
  let p := X.fiberObjectSliceProjection x y
  letI : ∀ f : Over U, Quiver.IsThin (p.Fiber f) :=
    fiberObjectSliceProjection_fiber_isThin X x y
  change IsFibredInSetoids p
  have hpcomp : (p ⋙ Over.forget U).IsFibered := by
    have hpbase' :
        (explicitTwoFibreProduct
          (fiberObjectYonedaBasedFunctor X x)
          (fiberObjectYonedaBasedFunctor X y)).p.IsFibered := by
      let Fx : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X :=
        (X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x
      let Fy : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X :=
        (X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y
      change (explicitTwoFibreProduct
        (FibredCategoryMor.toBasedFunctor Fx)
        (FibredCategoryMor.toBasedFunctor Fy)).p.IsFibered
      change (FibredCategoryOver.twoFibreProduct Fx Fy).p.IsFibered
      exact FibredCategoryOver.isFibred (FibredCategoryOver.twoFibreProduct Fx Fy)
    have hp_eq :
        p ⋙ Over.forget U =
          (explicitTwoFibreProduct
            (fiberObjectYonedaBasedFunctor X x)
            (fiberObjectYonedaBasedFunctor X y)).p := by
      change (explicitTwoFibreProductLeftProjection
          (fiberObjectYonedaBasedFunctor X x)
          (fiberObjectYonedaBasedFunctor X y)).toFunctor ⋙ Over.forget U =
        (explicitTwoFibreProduct
          (fiberObjectYonedaBasedFunctor X x)
          (fiberObjectYonedaBasedFunctor X y)).p
      exact (explicitTwoFibreProductLeftProjection
        (fiberObjectYonedaBasedFunctor X x)
        (fiberObjectYonedaBasedFunctor X y)).w
    rw [hp_eq]
    exact hpbase'
  letI : (p ⋙ Over.forget U).IsFibered := hpcomp
  letI : p.IsFibered := Functor.isFibered_of_comp_over_forget p
  letI : IsFibredInGroupoids p := by
    exact CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      p inferInstance (fiberObjectSliceProjection_fiber_isGroupoid X x y)
  infer_instance

instance :
    IsFibredInSetoids (X.fiberObjectSliceProjection x y) :=
  fiberObjectSliceProjection_isFibredInSetoids X x y

/-- For a fixed slice object `f : V ⟶ U`, the diagonal fibre subcategory of the auxiliary product:
objects are those in the fibre of the left projection over `f` whose right projection is also
`f`.  This is the fibrewise version of the source `2`-fibre product
`S ×_{S × S, (x, y)} C/U` from Lemma 8.2.5. -/
abbrev fiberObjectDiagonalFiberCategory (f : Over U) :=
  ObjectProperty.FullSubcategory
    ((fun P : (X.fiberObjectSliceProjection x y).Fiber f =>
      (X.fiberObjectSliceRightProjection x y).obj P.1 = f) :
        ObjectProperty ((X.fiberObjectSliceProjection x y).Fiber f))

/-- Helper for Chap08 Lemma 8 2 5: the Yoneda-based functor attached to a fibre object and the
canonical pullback construction have canonically isomorphic values over a slice object. -/
private noncomputable def fiberObjectYonedaComparisonIso
    (f : Over U) :
    ((fiberObjectYonedaBasedFunctor X x).fiberFunctor f.left).obj
        (Functor.Fiber.mk (p := Over.forget U) rfl) ≅
      (f.hom ^*[canonicalPullbackChoice X.p] x) := by
  let Fx : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X :=
    (X.yonedaEvaluationFunctor U).asEquivalence.inverse.obj x
  let fFiber : (Over.forget U).Fiber f.left :=
    Functor.Fiber.mk (p := Over.forget U) rfl
  let idU : Over U := Over.mk (𝟙 U)
  let toId : f ⟶ idU := Over.homMk f.hom (by simp [idU])
  let φF : (FibredCategoryMor.toFunctor Fx).obj f ⟶
      (FibredCategoryMor.toFunctor Fx).obj idU :=
    (FibredCategoryMor.toFunctor Fx).map toId
  have htoId_lift : (Over.forget U).IsHomLift f.hom toId := by
    refine IsHomLift.of_fac' (Over.forget U) f.hom toId rfl rfl ?_
    simp [toId, idU, Over.forget]
  have htoId_strong :
      (Over.forget U).IsStronglyCartesian f.hom toId := by
    have hraw :
        (Over.forget U).IsStronglyCartesian ((Over.forget U).map toId) toId :=
      (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map toId
    simpa [toId, idU, Over.forget] using hraw
  have hφF_lift : X.p.IsHomLift f.hom φF := by
    letI : (FibredCategoryOver.ofFunctor (Over.forget U)).p.IsHomLift f.hom toId := by
      simpa [FibredCategoryOver.p, BasedCategory.ofFunctor] using htoId_lift
    change X.p.IsHomLift f.hom ((FibredCategoryMor.toBasedFunctor Fx).map toId)
    exact BasedFunctor.preserves_isHomLift (FibredCategoryMor.toBasedFunctor Fx) f.hom toId
  have hφF_strong : X.p.IsStronglyCartesian f.hom φF := by
    exact fiberObject_map_stronglyCartesian_over_base Fx htoId_strong
  let ε : (X.yonedaEvaluationFunctor U).obj Fx ≅ x :=
    (X.yonedaEvaluationFunctor U).asEquivalence.counitIso.app x
  have hε_lift : X.p.IsHomLift (𝟙 U) ε.hom.1 := ε.hom.2
  let εTotal : (FibredCategoryMor.toFunctor Fx).obj idU ≅ x.1 :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).mapIso ε
  let can : (f.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶ x.1 :=
    (canonicalPullbackChoice X.p).map f.hom x
  have hcan_strong : X.p.IsStronglyCartesian f.hom can :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f.hom x
  have hεTotal_inv_lift : X.p.IsHomLift (𝟙 U) εTotal.inv := by
    change X.p.IsHomLift (𝟙 U) ε.inv.1
    exact ε.inv.2
  let canToF : (f.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶
      (FibredCategoryMor.toFunctor Fx).obj idU :=
    can ≫ εTotal.inv
  have hcanToF_cart : X.p.IsCartesian f.hom canToF := by
    letI : X.p.IsStronglyCartesian f.hom can := hcan_strong
    letI : X.p.IsCartesian f.hom can := by infer_instance
    letI : X.p.IsHomLift (𝟙 ((fromPUnit U).obj f.right)) εTotal.symm.hom := by
      change X.p.IsHomLift (𝟙 U) εTotal.symm.hom
      exact hεTotal_inv_lift
    simpa [canToF] using
      (Functor.IsCartesian.of_comp_iso X.p f.hom can εTotal.symm)
  have hφF_cart : X.p.IsCartesian f.hom φF := by
    letI : X.p.IsStronglyCartesian f.hom φF := hφF_strong
    infer_instance
  let eTotal :
      (FibredCategoryMor.toFunctor Fx).obj f ≅
        (f.hom ^*[canonicalPullbackChoice X.p] x).1 :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ X.p _ _ _ _ f.hom
      canToF hcanToF_cart _ φF hφF_cart
  have heTotal_hom_lift : X.p.IsHomLift (𝟙 f.left) eTotal.hom := by
    simpa [eTotal] using
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
        X.p _ _ _ _ f.hom canToF hcanToF_cart _ φF hφF_cart)
  have heTotal_inv_lift : X.p.IsHomLift (𝟙 f.left) eTotal.inv := by
    simpa [eTotal] using
      (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
        X.p _ _ _ _ f.hom canToF hcanToF_cart _ φF hφF_cart)
  let eFiber :
      ((fiberObjectYonedaBasedFunctor X x).fiberFunctor f.left).obj fFiber ≅
        (f.hom ^*[canonicalPullbackChoice X.p] x) :=
    { hom := ⟨eTotal.hom, heTotal_hom_lift⟩
      inv := ⟨eTotal.inv, heTotal_inv_lift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact eTotal.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact eTotal.inv_hom_id }
  simpa [fiberObjectYonedaBasedFunctor, Fx, fFiber] using eFiber

/-- Helper for Chap08 Lemma 8 2 5: a section of the isomorphism subfunctor as a bundled
isomorphism between the two canonical pullbacks over a slice object. -/
private noncomputable def isomorphismSectionAsIso
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    (f.hom ^*[canonicalPullbackChoice X.p] x) ≅
      (f.hom ^*[canonicalPullbackChoice X.p] y) :=
  @asIso _ _ _ _ δ.1
    ((mem_fiberIsomorphismSubfunctor_obj_iff X.p x y δ.1).1 δ.2)

/-- Helper for Chap08 Lemma 8 2 5: the explicit product object attached to an isomorphism
section over `f`. -/
private noncomputable def isomorphismSectionProductObject
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    (explicitTwoFibreProduct
      (fiberObjectYonedaBasedFunctor X x)
      (fiberObjectYonedaBasedFunctor X y)).obj :=
  { U := f.left
    obj :=
      { fst := Functor.Fiber.mk (p := Over.forget U) rfl
        snd := Functor.Fiber.mk (p := Over.forget U) rfl
        iso := fiberObjectYonedaComparisonIso X x f ≪≫ isomorphismSectionAsIso X x y f δ ≪≫
          (fiberObjectYonedaComparisonIso X y f).symm } }

/-- Helper for Chap08 Lemma 8 2 5: the left slice projection of the object attached to a section
is the original slice object. -/
private theorem isomorphismSectionProductObject_left_projection
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    (X.fiberObjectSliceProjection x y).obj
      (isomorphismSectionProductObject X x y f δ) = f := by
  rfl

/-- Helper for Chap08 Lemma 8 2 5: the right slice projection of the object attached to a section
is the original slice object. -/
private theorem isomorphismSectionProductObject_right_projection
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    (X.fiberObjectSliceRightProjection x y).obj
      (isomorphismSectionProductObject X x y f δ) = f := by
  rfl

/-- Helper for Chap08 Lemma 8 2 5: an isomorphism section over `f` determines an object of the
diagonal fibre category. -/
private noncomputable def isomorphismSectionToDiagonalFiberObject
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    fiberObjectDiagonalFiberCategory X x y f :=
  { obj :=
      ⟨isomorphismSectionProductObject X x y f δ,
        isomorphismSectionProductObject_left_projection X x y f δ⟩
    property := isomorphismSectionProductObject_right_projection X x y f δ }

/-- Helper for Chap08 Lemma 8 2 5: an object of the diagonal fibre category gives the induced
isomorphism section over `f`. -/
private noncomputable def diagonalFiberObjectToIsomorphismSection
    (f : Over U)
    (P : fiberObjectDiagonalFiberCategory X x y f) :
    ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f) := by
  classical
  rcases P with ⟨⟨⟨W, ⟨fst, snd, iso⟩⟩, hleft⟩, hright⟩
  dsimp [fiberObjectSliceProjection, fiberObjectSliceRightProjection,
    explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection,
    explicitTwoFibreProduct] at hleft hright
  have hW : W = f.left := by
    simpa [Over.forget, hleft] using fst.2.symm
  subst W
  let fFiber : (Over.forget U).Fiber f.left :=
    Functor.Fiber.mk (p := Over.forget U) rfl
  have hfst : fst = fFiber :=
    overForget_fiber_eq_of_obj_eq f fst hleft
  subst fst
  have hsnd : snd = fFiber :=
    overForget_fiber_eq_of_obj_eq f snd hright
  subst snd
  let δIso := (fiberObjectYonedaComparisonIso X x f).symm ≪≫ iso ≪≫
    fiberObjectYonedaComparisonIso X y f
  refine ⟨δIso.hom, ?_⟩
  exact (mem_fiberIsomorphismSubfunctor_obj_iff X.p x y δIso.hom).2 inferInstance

/-- Helper for Chap08 Lemma 8 2 5: extracting the section from the diagonal object associated
to that section recovers the original section. -/
private theorem diagonalFiberObjectToIsomorphismSection_toDiagonal
    (f : Over U)
    (δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)) :
    diagonalFiberObjectToIsomorphismSection X x y f
      (isomorphismSectionToDiagonalFiberObject X x y f δ) = δ := by
  apply Subtype.ext
  dsimp [diagonalFiberObjectToIsomorphismSection, isomorphismSectionToDiagonalFiberObject,
    isomorphismSectionProductObject, isomorphismSectionAsIso]
  letI : IsIso δ.1 := (mem_fiberIsomorphismSubfunctor_obj_iff X.p x y δ.1).1 δ.2
  simp

/-- Helper for Chap08 Lemma 8 2 5: every diagonal fibre object is isomorphic to the object
reconstructed from its extracted isomorphism section. -/
private noncomputable def diagonalFiberObject_iso_toDiagonal_from
    (f : Over U)
    (P : fiberObjectDiagonalFiberCategory X x y f) :
    P ≅ isomorphismSectionToDiagonalFiberObject X x y f
      (diagonalFiberObjectToIsomorphismSection X x y f P) := by
  classical
  rcases P with ⟨⟨⟨W, ⟨fst, snd, iso⟩⟩, hleft⟩, hright⟩
  dsimp [fiberObjectSliceProjection, fiberObjectSliceRightProjection,
    explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection,
    explicitTwoFibreProduct] at hleft hright
  have hW : W = f.left := by
    simpa [Over.forget, hleft] using fst.2.symm
  subst W
  let fFiber : (Over.forget U).Fiber f.left :=
    Functor.Fiber.mk (p := Over.forget U) rfl
  have hfst : fst = fFiber :=
    overForget_fiber_eq_of_obj_eq f fst hleft
  subst fst
  have hsnd : snd = fFiber :=
    overForget_fiber_eq_of_obj_eq f snd hright
  subst snd
  cases hleft
  cases hright
  let P0 : fiberObjectDiagonalFiberCategory X x y f :=
    { obj :=
        ⟨({ U := f.left, obj := { fst := fFiber, snd := fFiber, iso := iso } } :
          (explicitTwoFibreProduct
            (fiberObjectYonedaBasedFunctor X x)
            (fiberObjectYonedaBasedFunctor X y)).obj), rfl⟩
      property := rfl }
  let δIso := (fiberObjectYonedaComparisonIso X x f).symm ≪≫ iso ≪≫
    fiberObjectYonedaComparisonIso X y f
  let δ : ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f) :=
    ⟨δIso.hom,
      (mem_fiberIsomorphismSubfunctor_obj_iff X.p x y δIso.hom).2 inferInstance⟩
  have hδ : diagonalFiberObjectToIsomorphismSection X x y f P0 = δ := by
    apply Subtype.ext
    dsimp [P0, δ, δIso, diagonalFiberObjectToIsomorphismSection]
  change P0 ≅ isomorphismSectionToDiagonalFiberObject X x y f
    (diagonalFiberObjectToIsomorphismSection X x y f P0)
  rw [hδ]
  apply eqToIso
  apply ObjectProperty.FullSubcategory.ext
  apply Subtype.ext
  dsimp [P0, δ, δIso, isomorphismSectionToDiagonalFiberObject,
    isomorphismSectionProductObject, isomorphismSectionAsIso]
  congr
  apply Iso.ext
  simp [Category.assoc]

/-- Helper for Chap08 Lemma 8 2 5: isomorphic objects of the diagonal fibre category determine
the same isomorphism section. -/
private theorem diagonalFiberObjectToIsomorphismSection_eq_of_iso
    (f : Over U) {P Q : fiberObjectDiagonalFiberCategory X x y f}
    (e : P ≅ Q) :
    diagonalFiberObjectToIsomorphismSection X x y f P =
      diagonalFiberObjectToIsomorphismSection X x y f Q := by
  classical
  rcases P with ⟨⟨⟨WP, ⟨fstP, sndP, isoP⟩⟩, hleftP⟩, hrightP⟩
  rcases Q with ⟨⟨⟨WQ, ⟨fstQ, sndQ, isoQ⟩⟩, hleftQ⟩, hrightQ⟩
  dsimp [fiberObjectSliceProjection, fiberObjectSliceRightProjection,
    explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection,
    explicitTwoFibreProduct] at hleftP hrightP hleftQ hrightQ
  have hWP : WP = f.left := by
    simpa [Over.forget, hleftP] using fstP.2.symm
  subst WP
  have hWQ : WQ = f.left := by
    simpa [Over.forget, hleftQ] using fstQ.2.symm
  subst WQ
  let fFiber : (Over.forget U).Fiber f.left :=
    Functor.Fiber.mk (p := Over.forget U) rfl
  have hfstP : fstP = fFiber :=
    overForget_fiber_eq_of_obj_eq f fstP hleftP
  subst fstP
  have hsndP : sndP = fFiber :=
    overForget_fiber_eq_of_obj_eq f sndP hrightP
  subst sndP
  have hfstQ : fstQ = fFiber :=
    overForget_fiber_eq_of_obj_eq f fstQ hleftQ
  subst fstQ
  have hsndQ : sndQ = fFiber :=
    overForget_fiber_eq_of_obj_eq f sndQ hrightQ
  subst sndQ
  cases hleftP
  cases hrightP
  cases hleftQ
  cases hrightQ
  have ha : e.hom.hom.1.a = 𝟙 f := by
    letI : (X.fiberObjectSliceProjection x y).IsHomLift (𝟙 f) e.hom.hom.1 :=
      e.hom.hom.2
    simpa [fiberObjectSliceProjection, explicitTwoFibreProductLeftProjection,
      explicitTwoFibreProduct] using
        IsHomLift.fac' (X.fiberObjectSliceProjection x y) (𝟙 f) e.hom.hom.1
  have hb_lift : (Over.forget U).IsHomLift (𝟙 f.left) e.hom.hom.1.b := by
    letI : (Over.forget U).IsHomLift e.hom.hom.1.base e.hom.hom.1.a :=
      e.hom.hom.1.a_over
    have hbase : e.hom.hom.1.base = 𝟙 f.left := by
      have hbase_map :
          e.hom.hom.1.base = (Over.forget U).map e.hom.hom.1.a :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget U) _ _
          e.hom.hom.1.base e.hom.hom.1.a e.hom.hom.1.a_over
      simpa [ha, Over.forget] using
        hbase_map
    simpa [hbase] using e.hom.hom.1.b_over
  have hb : e.hom.hom.1.b = 𝟙 f := by
    let β : fFiber ⟶ fFiber :=
      ⟨e.hom.hom.1.b, hb_lift⟩
    letI : Quiver.IsThin ((Over.forget U).Fiber f.left) :=
      overForget_fiber_isThin U f.left
    have hβ : β = 𝟙 fFiber := Subsingleton.elim β (𝟙 fFiber)
    simpa [β, fFiber] using congrArg (fun η ↦ η.1) hβ
  have hiso : isoP.hom = isoQ.hom := by
    have hcomm := e.hom.hom.1.comm.w
    rw [ha, hb] at hcomm
    have hxmap' :
        (fiberObjectYonedaBasedFunctor X x).map (𝟙 f) =
          𝟙 ((((fiberObjectYonedaBasedFunctor X x).fiberFunctor f.left).obj fFiber).1) := by
      exact Functor.map_id ((fiberObjectYonedaBasedFunctor X x).toFunctor) f
    have hymap' :
        (fiberObjectYonedaBasedFunctor X y).map (𝟙 f) =
          𝟙 ((((fiberObjectYonedaBasedFunctor X y).fiberFunctor f.left).obj fFiber).1) := by
      exact Functor.map_id ((fiberObjectYonedaBasedFunctor X y).toFunctor) f
    have hxobj :
        (((fiberObjectYonedaBasedFunctor X x).fiberFunctor f.left).obj fFiber).1 =
          (fiberObjectYonedaBasedFunctor X x).obj f := by
      rfl
    have hyobj :
        (((fiberObjectYonedaBasedFunctor X y).fiberFunctor f.left).obj fFiber).1 =
          (fiberObjectYonedaBasedFunctor X y).obj f := by
      rfl
    cases hxobj
    cases hyobj
    have htot :
        Functor.Fiber.fiberInclusion.map isoP.hom =
          Functor.Fiber.fiberInclusion.map isoQ.hom := by
      have h := hcomm.symm
      erw [Functor.map_id ((fiberObjectYonedaBasedFunctor X y).toFunctor) f] at h
      erw [Functor.map_id ((fiberObjectYonedaBasedFunctor X x).toFunctor) f] at h
      convert h using 1
      · erw [Category.comp_id]
        rfl
      · erw [Category.id_comp]
        rfl
    exact Functor.Fiber.hom_ext htot
  apply Subtype.ext
  change (fiberObjectYonedaComparisonIso X x f).inv ≫ isoP.hom ≫
      (fiberObjectYonedaComparisonIso X y f).hom =
    (fiberObjectYonedaComparisonIso X x f).inv ≫ isoQ.hom ≫
      (fiberObjectYonedaComparisonIso X y f).hom
  simp [hiso]

/-- Lemma 8.2.5 (corrected fibrewise form): for each `f : V ⟶ U`, `Isom(x, y)(f)` is the set of
isomorphism classes of the diagonal fibre category.  Under the source description, an object
`(f, z, α, β)` is sent to the isomorphism `β ≫ α⁻¹` between the two pullbacks over `V`. -/
@[stacks 04SI]
theorem fiberIsomorphismSubfunctor_toFunctor_equiv_diagonalFiberIsoClasses
    (f : Over U) :
    Nonempty
      (((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f) ≃
        isomorphismClasses.obj (Cat.of (fiberObjectDiagonalFiberCategory X x y f))) := by
  classical
  let A := ((fiberIsomorphismSubfunctor X.p x y).toFunctor).obj (op f)
  let D := fiberObjectDiagonalFiberCategory X x y f
  let toObj : A → D :=
    fun δ ↦ isomorphismSectionToDiagonalFiberObject X x y f δ
  let toClass : A →
      isomorphismClasses.obj (Cat.of (fiberObjectDiagonalFiberCategory X x y f)) :=
    fun δ ↦ Quotient.mk'' (toObj δ)
  refine ⟨{ toFun := toClass, invFun := ?_, left_inv := ?_, right_inv := ?_ }⟩
  · intro q
    refine Quotient.liftOn q
      (fun P : D ↦ diagonalFiberObjectToIsomorphismSection X x y f P) ?_
    intro P Q hPQ
    exact diagonalFiberObjectToIsomorphismSection_eq_of_iso X x y f
      (Classical.choice hPQ)
  · intro δ
    exact diagonalFiberObjectToIsomorphismSection_toDiagonal X x y f δ
  · intro q
    refine Quotient.inductionOn q ?_
    intro P
    exact _root_.Quotient.sound
      ⟨(diagonalFiberObject_iso_toDiagonal_from X x y f P).symm⟩

end

end FibredCategoryOver

end CategoryTheory
