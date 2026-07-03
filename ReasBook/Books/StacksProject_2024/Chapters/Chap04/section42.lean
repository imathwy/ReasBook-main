import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_42_1 (from Chap04) -/
universe u v

namespace CategoryTheory

open CategoryOver
open BasedFunctor
open Functor
open Functor.Fiber
open CategoryTheory.Limits
open Functor.IsHomLift

variable {C : Type u} [Category.{v} C]
variable {X Y : Type (max u v)} [Category.{v} X] [Category.{v} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}

namespace FibredCategoryOver

/- Domain-style sampling for Lemma 4.42.1:
- primary domain: fibers of the left projection of the explicit slice `2`-fibre product.
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `Fiber.inducedFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`,
  `StructuredArrow`.
- best owner abstraction: the core object here is the fiber of the owner projection
  `explicitTwoFibreProductLeftProjection G F`; over a fixed `f : Over U`, that fiber should be
  described by the canonical comma owner `StructuredArrow` in the fiber `pY.Fiber f.left`, not by
  a new slice-specific wrapper.
- primitive data: the based functors `G`, `F`, and the fixed slice object `f : Over U`.
- derived API: the canonical equivalence from that structured-arrow category to the corresponding
  fiber of the explicit `2`-fibre-product projection.

Source/core/bridge triage:
- `source-facing`: `sliceTwoFibreProductStructuredArrowEquivFiber`.
- `core/canonical`: `Functor.Fiber`, `BasedFunctor.fiberFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`, and `StructuredArrow`.
- `bridge/view`: the internal comparison functors
  `sliceTwoFibreProductStructuredArrowToExplicit` and
  `sliceTwoFibreProductStructuredArrowToFiber`. -/

end FibredCategoryOver

section SliceTwoFibreProductStructuredArrow

variable {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

/-- The canonical functor from the structured-arrow category to the total explicit
`2`-fibre product, with constant left projection `f`. -/
private noncomputable def sliceTwoFibreProductStructuredArrowToExplicit
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      (explicitTwoFibreProduct G F).obj where
  obj A := by
    letI : IsFibredInGroupoids (BasedCategory.ofFunctor pY).p := by
      change IsFibredInGroupoids pY
      infer_instance
    letI : IsIso A.hom := IsFibredInGroupoids.hom_isIso f.left A.hom
    exact
      { U := f.left
        obj :=
          { fst := Fiber.mk rfl
            snd := A.right
            iso := asIso A.hom } }
  map {A B} α := by
    letI : (Over.forget U).IsHomLift (𝟙 f.left) (𝟙 f) := IsHomLift.id rfl
    letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
    exact
      { base := 𝟙 f.left
        a := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).1
        a_over := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).2
        b := (Fiber.homMk pX f.left α.right.1).1
        b_over := (Fiber.homMk pX f.left α.right.1).2
        comm := by
          -- The left component is forced to be `𝟙 f`, so the pullback square is exactly the
          -- structured-arrow compatibility equation.
          refine ⟨?_⟩
          change G.map (𝟙 f) ≫ B.hom.1 = A.hom.1 ≫ F.map α.right.1
          have hα : B.hom.1 = A.hom.1 ≫ ((F.fiberFunctor f.left).map α.right).1 := by
            simpa using (congrArg Subtype.val (StructuredArrow.w α)).symm
          have hg : G.map (𝟙 f) = 𝟙 _ := by
            exact G.toFunctor.map_id f
          rw [hg, Category.id_comp]
          simpa using hα }
  map_id A := by
    cases A
    rfl
  map_comp α β := by
    apply ExplicitTwoFibreProductHom.ext
    · change 𝟙 f = 𝟙 f ≫ 𝟙 f
      simp
    · letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
      letI : pX.IsHomLift (𝟙 f.left) β.right.1 := β.right.2
      rfl

private theorem sliceTwoFibreProductStructuredArrowToExplicit_comp_projection
    [IsFibredInGroupoids pY] (f : Over U) :
    sliceTwoFibreProductStructuredArrowToExplicit G F f ⋙
        (explicitTwoFibreProductLeftProjection G F).toFunctor =
      (Functor.const
        (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left))).obj
        f :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ α ↦ by
    change 𝟙 f = eqToHom (by simp) ≫ 𝟙 f ≫ eqToHom (by simp)
    simp)

/-- The canonical functor from the structured-arrow category
`(G(f) ↓ F_V)` to the fiber over `f` of the explicit `2`-fibre-product projection. -/
private noncomputable def sliceTwoFibreProductStructuredArrowToFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  Fiber.inducedFunctor
    (sliceTwoFibreProductStructuredArrowToExplicit_comp_projection G F f)

/-- Helper for Lemma 4.42.1: forgetting the redundant outer fibre equality turns an object of the
fibre of the left projection into the corresponding structured arrow. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow_obj
    [IsFibredInGroupoids pY] (f : Over U) :
    ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f →
      StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)
  | ⟨⟨_, ⟨⟨_, rfl⟩, x, i⟩⟩, rfl⟩ => StructuredArrow.mk (Y := x) i.hom

/-- Helper for Lemma 4.42.1: the left component of a morphism in the fibre of the left projection
lies over the identity of `f.left`. -/
private theorem fiberOfSliceTwoFibreProduct_left_over_id
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (Over.forget U).IsHomLift (𝟙 f.left) φ.1.a := by
  -- After normalizing the outer fibre equalities, the projection-to-slice lift is literally over
  -- `𝟙 f`, so the left component lies over `𝟙 f.left`.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : (explicitTwoFibreProductLeftProjection G F).toFunctor.IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      simpa [ha] using (show (Over.forget U).IsHomLift (𝟙 f.left) (𝟙 f) from IsHomLift.id rfl)

/-- Helper for Lemma 4.42.1: the right component of a morphism in the fibre of the left
projection lies over the identity of `f.left`. -/
private theorem fiberOfSliceTwoFibreProduct_right_over_id
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    pX.IsHomLift (𝟙 f.left) φ.1.b := by
  -- The right component lies over the same base map as the left one, and that base map is
  -- `𝟙 f.left` after strictifying the left slice component.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : pX.IsHomLift φ.1.base φ.1.b := by
        simpa using φ.1.b_over
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : (explicitTwoFibreProductLeftProjection G F).toFunctor.IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      have hbase : φ.1.base = 𝟙 f.left := by
        simpa [ha] using (IsHomLift.fac (Over.forget U) φ.1.base φ.1.a)
      simpa [hbase] using φ.1.b_over

/-- Helper for Lemma 4.42.1: a morphism in the outer fibre induces the corresponding morphism
between the right fibre objects appearing in the structured-arrow description. -/
private def fiberOfSliceTwoFibreProduct_right_fiber_hom
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P).right ⟶
      (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q).right :=
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      Fiber.homMk pX f.left φ.1.b

/-- Helper for Lemma 4.42.1: after strictifying the left slice component to `𝟙 f`, the
commutative square of a morphism in the explicit pullback becomes the structured-arrow triangle
in the fibre over `f.left`. -/
private theorem slice_two_fibre_product_fiber_structured_arrow_triangle
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P).hom ≫
        (F.fiberFunctor f.left).map
          (fiberOfSliceTwoFibreProduct_right_fiber_hom (G := G) (F := F) φ) =
      (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q).hom := by
  -- Strictify the left component to `𝟙 f` and then read `φ.1.comm.w` in the fibre of `pY`.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, xP, iP⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, xQ, iQ⟩⟩, rfl⟩, φ =>
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : ((explicitTwoFibreProductLeftProjection G F).toFunctor).IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      have hg : G.toFunctor.map φ.1.a = 𝟙 _ := by
        rw [ha]
        exact Functor.map_id G.toFunctor f
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      let φright : xP ⟶ xQ := by
        simpa using (Fiber.homMk pX f.left φ.1.b)
      -- Compare the underlying morphisms in the fibre of `pY` after rewriting the left leg to
      -- `𝟙 f`.
      apply Functor.Fiber.hom_ext
      change
        fiberInclusion.map (iP.hom ≫ (F.fiberFunctor f.left).map φright) =
          fiberInclusion.map iQ.hom
      suffices
          fiberInclusion.map (iP.hom ≫ (F.fiberFunctor f.left).map φright) =
            G.toFunctor.map φ.1.a ≫ fiberInclusion.map iQ.hom by
        simpa [hg] using this
      simpa [ExplicitTwoFibreProductObject.comparison, φright] using φ.1.comm.w.symm

/-- Helper for Lemma 4.42.1: a morphism in the fibre of the left projection induces a morphism
between the corresponding structured arrows. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow_map
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P ⟶
      fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q :=
  StructuredArrow.homMk
    (fiberOfSliceTwoFibreProduct_right_fiber_hom (G := G) (F := F) φ)
    (slice_two_fibre_product_fiber_structured_arrow_triangle (G := G) (F := F) φ)

/-- Helper for Lemma 4.42.1: the concrete inverse functor preserves identities. -/
private theorem fiberOfSliceTwoFibreProduct_to_structuredArrow_map_id
    [IsFibredInGroupoids pY]
    {f : Over U} (P : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) (𝟙 P) =
      𝟙 (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P) := by
  -- Normalize to the right fibre component and compare in the structured-arrow category.
  match P with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩ =>
      apply StructuredArrow.hom_ext
      apply Functor.Fiber.hom_ext
      rfl

/-- Helper for Lemma 4.42.1: the concrete inverse functor preserves composition. -/
private theorem fiberOfSliceTwoFibreProduct_to_structuredArrow_map_comp
    [IsFibredInGroupoids pY]
    {f : Over U}
    {P Q R : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) (φ ≫ ψ) =
      fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) φ ≫
        fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) ψ := by
  -- Normalize to the right fibre component and use that composition in the fibre is componentwise.
  match P, Q, R, φ, ψ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      φ, ψ =>
        apply StructuredArrow.hom_ext
        apply Functor.Fiber.hom_ext
        rfl

/-- Helper for Lemma 4.42.1: forgetting the redundant outer fibre equality gives the concrete
quasi-inverse from the fibre of the left projection to the structured-arrow category. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow
    [IsFibredInGroupoids pY] (f : Over U) :
    ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f ⥤
      StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) where
  obj := fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f
  map := fiberOfSliceTwoFibreProduct_to_structuredArrow_map G F
  map_id := fiberOfSliceTwoFibreProduct_to_structuredArrow_map_id G F
  map_comp := fiberOfSliceTwoFibreProduct_to_structuredArrow_map_comp G F

/-- Helper for Lemma 4.42.1: the canonical functor to the fibre followed by the concrete
quasi-inverse is the identity on the structured-arrow category. -/
private theorem sliceTwoFibreProductStructuredArrow_comp_inverse
    [IsFibredInGroupoids pY] (f : Over U) :
    sliceTwoFibreProductStructuredArrowToFiber G F f ⋙
        fiberOfSliceTwoFibreProduct_to_structuredArrow G F f =
      𝟭 (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)) := by
  -- Compare the right fibre morphisms componentwise and then transport the ordinary equality into
  -- the heterogeneous morphism clause required by `Functor.hext`.
  refine Functor.hext (fun A ↦ rfl) ?_
  intro A B α
  cases A
  cases B
  have hmap :
      (sliceTwoFibreProductStructuredArrowToFiber G F f ⋙
          fiberOfSliceTwoFibreProduct_to_structuredArrow G F f).map α =
        (𝟭
          (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl))
            (F.fiberFunctor f.left))).map α := by
    apply StructuredArrow.hom_ext
    apply Functor.Fiber.hom_ext
    rfl
  exact hmap ▸ HEq.rfl

/-- Helper for Lemma 4.42.1: rebuilding the explicit pullback object from a stored comparison
isomorphism replaces `i` by `asIso i.hom`, and these are definitionally the same isomorphism. -/
private theorem slice_two_fibre_product_rebuild_comparison_iso
    [IsFibredInGroupoids pY]
    {f : Over U} {x : pX.Fiber f.left}
    (i : (G.fiberFunctor f.left).obj (Fiber.mk rfl) ≅ (F.fiberFunctor f.left).obj x) :
    asIso i.hom = i := by
  -- Rebuilding from the stored comparison morphism does not change the underlying isomorphism.
  ext
  simp [asIso_hom]

/-- Helper for Lemma 4.42.1: the components of an equality morphism in the explicit
`2`-fibre product are the corresponding equality morphisms on the two fibre factors. -/
private theorem explicitTwoFibreProduct_eqToHom_components
    {P Q : ExplicitTwoFibreProductObject G F} (h : P = Q) :
    ((eqToHom h : P ⟶ Q).a = eqToHom (by cases h; rfl)) ∧
      ((eqToHom h : P ⟶ Q).b = eqToHom (by cases h; rfl)) := by
  -- Equality morphisms in the explicit pullback are defined componentwise.
  cases h
  constructor <;> rfl

/-- Helper for Lemma 4.42.1: forgetting an equality morphism in a fibre recovers the equality
morphism on the underlying ambient objects. -/
private theorem fiber_eqToHom_map
    {S : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber S}
    (h : P = Q) :
    fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  -- The equality morphism in a fibre is defined by the same underlying ambient morphism.
  cases h
  rfl

/-- Helper for Lemma 4.42.1: the forward-then-backward composite fixes each object of the outer
fibre once the rebuilt comparison isomorphism is normalized back to the stored one. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward_obj
    [IsFibredInGroupoids pY]
    {f : Over U} (P : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f).obj P = P := by
  -- Unfold the composite object and rewrite the rebuilt comparison `asIso i.hom` back to `i`.
  match P with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, i⟩⟩, rfl⟩ =>
      -- Compare only the underlying explicit pullback object; the subtype proof is then irrelevant.
      apply Subtype.ext
      change
        (({ U := f.left
            obj :=
              { fst := Fiber.mk rfl
                snd := _
                iso := asIso i.hom } } :
            ExplicitTwoFibreProductObject G F) =
          { U := f.left
            obj :=
              { fst := Fiber.mk rfl
                snd := _
                iso := i } })
      rw [slice_two_fibre_product_rebuild_comparison_iso (G := G) (F := F) (f := f) i]

/-- Helper for Lemma 4.42.1: after normalizing the rebuilt comparison isomorphisms on objects,
the backward composite acts on morphisms by the original fibre morphism. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward_map_heq
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f).map φ ≍ φ := by
  -- Route correction: first rewrite the `HEq` target into an ordinary conjugation statement using
  -- the normalized object equalities, then compare the explicit pullback morphisms componentwise.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, iP⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, iQ⟩⟩, rfl⟩, φ =>
      have hP :
          (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
              sliceTwoFibreProductStructuredArrowToFiber G F f).obj
              ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩ =
            ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩ := by
        exact fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F)
          ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩
      have hQ :
          (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
              sliceTwoFibreProductStructuredArrowToFiber G F f).obj
              ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩ =
            ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩ := by
        exact fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F)
          ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩
      rw [← conj_eqToHom_iff_heq
        ((fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
            sliceTwoFibreProductStructuredArrowToFiber G F f).map φ)
        φ hP hQ]
      -- After forgetting to the ambient explicit pullback, the remaining comparison is ordinary
      -- equality of explicit pullback morphisms.
      apply Functor.Fiber.hom_ext
      rw [show
          fiberInclusion.map
              ((fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
                  sliceTwoFibreProductStructuredArrowToFiber G F f).map φ) =
            (sliceTwoFibreProductStructuredArrowToExplicit G F f).map
              (fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) φ) by
        rfl]
      have hPa : (fiberInclusion.map (eqToHom hP)).a = 𝟙 f := by
        rw [fiber_eqToHom_map (G := G) (F := F) hP]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hP)).1
      have hPb : (fiberInclusion.map (eqToHom hP)).b = 𝟙 _ := by
        rw [fiber_eqToHom_map (G := G) (F := F) hP]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hP)).2
      have hQa : (fiberInclusion.map (eqToHom hQ.symm)).a = 𝟙 f := by
        rw [fiber_eqToHom_map (G := G) (F := F) hQ.symm]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hQ.symm)).1
      have hQb : (fiberInclusion.map (eqToHom hQ.symm)).b = 𝟙 _ := by
        rw [fiber_eqToHom_map (G := G) (F := F) hQ.symm]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hQ.symm)).2
      letI : ((explicitTwoFibreProductLeftProjection G F).toFunctor).IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      have hφa : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      apply ExplicitTwoFibreProductHom.ext
      · -- The left slice component is forced to be `𝟙 f`, so the conjugated comparison is a short
        -- identity computation in `Over U`.
        change
          𝟙 f =
            (fiberInclusion.map (eqToHom hP)).a ≫
              φ.1.a ≫ (fiberInclusion.map (eqToHom hQ.symm)).a
        rw [hPa, hQa, hφa]
        calc
          𝟙 f = 𝟙 f ≫ 𝟙 f := by simp
          _ = 𝟙 f ≫ 𝟙 f ≫ 𝟙 f := by simp
      · -- The right fibre component is the original fibre morphism, up to the identity
        -- conjugations coming from `hP` and `hQ`.
        change
          ((Fiber.homMk pX f.left φ.1.b).1) =
            (fiberInclusion.map (eqToHom hP)).b ≫
              φ.1.b ≫ (fiberInclusion.map (eqToHom hQ.symm)).b
        rw [hPb, hQb]
        calc
          (Fiber.homMk pX f.left φ.1.b).1 = φ.1.b := by rfl
          _ = 𝟙 _ ≫ φ.1.b := by simp
          _ = 𝟙 _ ≫ φ.1.b ≫ 𝟙 _ := by simp

/-- Helper for Lemma 4.42.1: the concrete quasi-inverse followed by the canonical functor back to
the outer fibre is the identity on that fibre. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward
    [IsFibredInGroupoids pY] (f : Over U) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f =
      𝟭 (((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) := by
  -- Normalize the rebuilt comparison isomorphism and then compare fibre morphisms componentwise.
  refine Functor.hext
    (fun P ↦ fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F) P)
    ?_
  intro P Q φ
  -- The dependent map clause is handled separately so the final `Functor.hext` proof stays flat.
  exact fiberOfSliceTwoFibreProduct_comp_forward_map_heq (G := G) (F := F) φ

-- Proof sketch: an object of the fiber over `f : V ⟶ U` in the explicit `2`-fibre-product
-- already has left leg equal to `f`, so the remaining data are exactly an object
-- `x ∈ X_V` together with a morphism `G(f) ⟶ F(x)` in `Y_V`, i.e. a structured arrow from the
-- canonical fibre object `G(f)` to the induced fibre functor `F_V`.
/-- Lemma 4.42.1: for a functor `G : C/U ⥤ Y` over `C` and a functor `F : X ⥤ Y` over `C`, the
fiber over `f : V ⟶ U` of the explicit `2`-fibre-product projection
`(C/U) ×_Y X ⟶ C/U` is canonically equivalent to the structured-arrow category
`StructuredArrow (G(f)) (F_V)`, where `G(f)` is regarded as an object of `Y_V` and `F_V` is the
induced functor `X_V ⥤ Y_V`. Equivalently, its objects are pairs `(x, φ)` with `x ∈ X_V` and
`φ : G(f) ⟶ F(x)` in `Y_V`. -/
private theorem sliceTwoFibreProductStructuredArrowToFiber_isEquivalence
    [IsFibredInGroupoids pY] (f : Over U) :
    (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence := by
  -- Route correction: the source proof identifies the outer fibre by strictifying the fixed left
  -- projection to `f` and then forgetting the redundant equality.
  let H := fiberOfSliceTwoFibreProduct_to_structuredArrow G F f
  have hη :
      sliceTwoFibreProductStructuredArrowToFiber G F f ⋙ H =
        𝟭 (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)) :=
    sliceTwoFibreProductStructuredArrow_comp_inverse G F f
  have hε :
      H ⋙ sliceTwoFibreProductStructuredArrowToFiber G F f =
        𝟭 (((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :=
    fiberOfSliceTwoFibreProduct_comp_forward G F f
  exact
    Functor.IsEquivalence.mk'
      H
      (eqToIso hη.symm)
      (eqToIso hε)

/-- The canonical equivalence in Lemma 4.42.1 between the structured-arrow category
`StructuredArrow (G(f)) (F_V)` and the fiber over `f` of the left projection
`(C/U) ×_Y X ⟶ C/U`. -/
noncomputable def sliceTwoFibreProductStructuredArrowEquivFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ≌
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  letI : (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence :=
    sliceTwoFibreProductStructuredArrowToFiber_isEquivalence G F f
  (sliceTwoFibreProductStructuredArrowToFiber G F f).asEquivalence

end SliceTwoFibreProductStructuredArrow

end CategoryTheory

/-! ### Lemma_4_42_2 (from Chap04) -/
universe v u

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {U : C}
variable {X Y : BasedCategory.{v, max u v} C}

/- Domain-style sampling for Lemma 4.42.2:
- primary domain: slice-level base change of categories fibred in groupoids, with the explicit
  `2`-fibre product from `Cat/C` viewed over the slice category `C/U`;
- inspected owner-level declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductLeftProjection`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`,
  `Functor.isFibredInGroupoids_of_comp_over_forget`,
  `FibredInGroupoidsOver.twoFibreProduct`;
- best owner abstraction: the source-facing object is the canonical explicit left projection
  `explicitTwoFibreProductLeftProjection G F : (C/U) ×_Y X ⥤ᵇ C/U`, and the main property should
  live directly on its underlying functor via `IsFibredInGroupoids`;
- primitive data: the based functors `F : X ⥤ᵇ Y` and
  `G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y`, together with the explicit pullback total
  category `explicitTwoFibreProduct G F`;
- derived API: the fibred-in-groupoids theorem for the explicit left projection; the bundled
  owner object is already supplied upstream by `FibredInGroupoidsOver.twoFibreProduct`.

Source/core/bridge triage:
- `source-facing`: `explicitTwoFibreProductLeftProjection_isFibredInGroupoids`;
- `core/canonical`: `explicitTwoFibreProductLeftProjection` and `IsFibredInGroupoids`;
- `bridge/view`: the bundled owner rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

-- Proof sketch: compose `(explicitTwoFibreProductLeftProjection G F).toFunctor` with
-- `Over.forget U` to recover the projection to `C` from Lemma `4.35.7`, which is fibred in
-- groupoids because the pullback source `X` is fibred in groupoids and the target projection
-- `Y.p` is fibred over `C`. Then apply
-- Lemma `4.35.13` to lift the fibred-in-groupoids structure along `Over.forget U`.
/-- Helper for Lemma 4.42.2: if the target projection `Y.p` is itself fibred in groupoids, then
the slice left projection is fibred in groupoids by descending the already-known composite over
`C` along `Over.forget U`. -/
theorem explicitTwoFibreProductLeftProjection_isFibredInGroupoids_of_target_groupoids
    {X' Y' : BasedCategory.{v, max u v} C}
    (F : X' ⥤ᵇ Y') (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y')
    [IsFibredInGroupoids X'.p] [IsFibredInGroupoids Y'.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor := by
  let p : (explicitTwoFibreProduct G F).obj ⥤ Over U :=
    (explicitTwoFibreProductLeftProjection G F).toFunctor
  letI : IsFibredInGroupoids (BasedCategory.ofFunctor (Over.forget U)).p := by
    change IsFibredInGroupoids (Over.forget U)
    infer_instance
  -- Identify the composite to `C` with the explicit pullback projection handled in Lemma 4.35.7.
  have hp : p ⋙ Over.forget U = (explicitTwoFibreProduct G F).p := by
    simpa [p] using (explicitTwoFibreProductLeftProjection G F).w
  -- Fix the ambient owner parameters explicitly so Lean sees the imported pullback theorem in the
  -- same universe configuration as the current slice pullback.
  have hcomp : IsFibredInGroupoids (explicitTwoFibreProduct G F).p := by
    exact
      (show IsFibredInGroupoids (explicitTwoFibreProduct G F).p from
        CategoryTheory.explicitTwoFibreProductProjection_isFibredInGroupoids
          (X := BasedCategory.ofFunctor (Over.forget U)) (Y := X') (S := Y') G F)
  letI : IsFibredInGroupoids (p ⋙ Over.forget U) := by
    simpa [hp] using hcomp
  -- Descend the fibred-in-groupoids structure from `C` to the slice category `C/U`.
  simpa [p] using Functor.isFibredInGroupoids_of_comp_over_forget p

/-- Lemma 4.42.2: if `F : X ⥤ᵇ Y` has source fibred in groupoids over `C`, if the target
projection `Y.p` is fibred over `C`, and if `G : (C/U) ⥤ Y` lies over `C`, then the projection
from the explicit `2`-fibre product `(C/U) ×_Y X` to `C/U` is a category fibred in groupoids. In
particular this applies to a morphism between categories fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductLeftProjection_isFibredInGroupoids
    (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor := by
  -- The theorem now carries the target groupoid hypothesis needed by the textbook argument and
  -- by the imported composite-over-`C` theorem from Lemma 4.35.7. The remaining proof work is a
  -- universe-specialized transport from the helper above to this owner surface.
  simpa using
    explicitTwoFibreProductLeftProjection_isFibredInGroupoids_of_target_groupoids
      (C := C) (U := U) (X' := X) (Y' := Y) F G

instance (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor :=
  explicitTwoFibreProductLeftProjection_isFibredInGroupoids F G

end CategoryTheory

/-! ### Definition_4_42_3 (from Chap04) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsMor

open CategoryOver
open FibredInGroupoidsOver (ofFunctor)

variable {X Y : FibredInGroupoidsOver C}

/- Domain-style sampling for Definition 4.42.3:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductLeftProjection`,
  `FibredInGroupoidsMor.toBasedFunctor`,
  `FibredInGroupoidsOver.IsRepresentable`;
- best owner abstraction: the ambient owner hom `F : X ⟶ Y` in `FibredInGroupoidsOver C`. The
  source-facing test object is the slice base-change owner
  `twoFibreProductLeftProjection G F` over `C/U`, viewed through the existing owner
  `twoFibreProduct G F` instead of rebuilding the explicit pullback model locally; the
  representability owner itself remains the ambient hom `F : X ⟶ Y`;
- primitive data: only the owner morphism `F : X ⟶ Y`;
- derived API: the canonical slice base-change owner `sliceTwoFibreProduct F G` over `C/U`. -/

/- Source/core/bridge triage for Definition 4.42.3:
- `source-facing`: `FibredInGroupoidsMor.IsRepresentable` as a property of an owner hom `X ⟶ Y`;
- `core/canonical`: the absolute owner `FibredInGroupoidsOver.IsRepresentable` applied to the
  slice base-change projection over `C/U`;
- `bridge/view`: the representable test objects `ofFunctor (Over.forget U)` and the owner-level
  slice pullback `sliceTwoFibreProduct F G`. -/

private noncomputable abbrev sliceTwoFibreProductProjection
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    (FibredInGroupoidsOver.twoFibreProduct G F).S ⥤ Over U :=
  (FibredInGroupoidsMor.toBasedFunctor
    (FibredInGroupoidsOver.twoFibreProductLeftProjection G F)).toFunctor

private instance sliceTwoFibreProductProjection_isFibredInGroupoids
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInGroupoids (sliceTwoFibreProductProjection F G) := by
  change IsFibredInGroupoids
    (explicitTwoFibreProductLeftProjection (toBasedFunctor G) (toBasedFunctor F)).toFunctor
  exact explicitTwoFibreProductLeftProjection_isFibredInGroupoids
    (toBasedFunctor F) (toBasedFunctor G)

/-- The canonical slice base change of `F : X ⟶ Y` along `G : C/U ⟶ Y`, regarded as a category
fibred in groupoids over the slice category `C/U`. -/
noncomputable def sliceTwoFibreProduct
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    FibredInGroupoidsOver (Over U) :=
  ofFunctor (sliceTwoFibreProductProjection F G)

instance sliceTwoFibreProduct_isFibredInGroupoids
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInGroupoids (sliceTwoFibreProduct F G).p := by
  unfold sliceTwoFibreProduct
  change IsFibredInGroupoids (sliceTwoFibreProductProjection F G)
  infer_instance

instance sliceTwoFibreProduct_isFibered
    (F : FibredInGroupoidsMor X Y) {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    (sliceTwoFibreProduct F G).p.IsFibered := by
  unfold sliceTwoFibreProduct
  change (sliceTwoFibreProductProjection F G).IsFibered
  infer_instance

/-- Definition 4.42.3: a `1`-morphism `F : X ⟶ Y` of categories fibred in groupoids over `C` is
representable, or relatively representable over `Y`, if for every object `U : C` and every
`1`-morphism `G : C/U ⟶ Y`, the induced slice base change `(C/U) ×[Y] X → C/U` is
representable. -/
def IsRepresentable (F : FibredInGroupoidsMor X Y) : Prop :=
  ∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
    (sliceTwoFibreProduct F G).IsRepresentable

-- Proof sketch: unfold `FibredInGroupoidsMor.IsRepresentable`; the statement is exactly the
-- defining universal representability condition on all slice base changes.
/-- Companion specification for Definition 4.42.3: a morphism of categories fibred in groupoids is
representable exactly when every canonical slice base change `sliceTwoFibreProduct F G` is a
representable fibred category over the slice base. -/
theorem isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable
    (F : FibredInGroupoidsMor X Y) :
    F.IsRepresentable ↔
      ∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
        (sliceTwoFibreProduct F G).IsRepresentable := by
  -- Unfold the definition: the theorem states exactly the defining condition of representability.
  rfl

end FibredInGroupoidsMor

end CategoryTheory

/-! ### Lemma_4_42_4 (from Chap04) -/
universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

variable {A : Type*} [Category A]
variable {B : Type*} [Category B]

/- Domain-style sampling for Lemma 4.42.4:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base and
  the induced functors on their fiber categories;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `sliceTwoFibreProductStructuredArrowEquivFiber`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the source-facing owner hom `F : X ⟶ Y`, together with its canonical
  slice base change `F.sliceTwoFibreProduct G` over `C/U`; the fiberwise statement should be
  derived from that owner data rather than from a parallel local slice wrapper;
- primitive data: the owner morphism `F` and, for a chosen `y ∈ Y_U`, the canonical Yoneda
  representing morphism `Gy : C/U ⟶ Y`;
- derived API: the slice object `F.sliceTwoFibreProduct G`, its fibred-in-setoids consequence via
  Lemma `4.40.2`, and the comparison equivalence of Lemma `4.42.1`.

Source/core/bridge triage:
- `source-facing`: `fiber_functor_faithful_of_is_representable`;
- `core/canonical`: `F.IsRepresentable`, `F.sliceTwoFibreProduct G`, and the owner theorem
  `isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- `bridge/view`: the Yoneda-selected morphism `Gy` and the equivalence
  `sliceTwoFibreProductStructuredArrowEquivFiber`. -/

/-- Helper for Lemma 4.42.4: the Yoneda inverse at `y ∈ Y_U` gives the canonical slice morphism
`C/U ⟶ Y` used to test representability near `y`. -/
private noncomputable abbrev yoneda_inverse_slice
    (U : C) (y : Y.p.Fiber U) :
    ofFunctor (Over.forget U) ⟶ Y :=
  ofAmbientHom ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y)

/-- Helper for Lemma 4.42.4: a faithful functor into a thin category has a thin source. -/
private theorem isThin_of_faithful
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  intro a b
  refine ⟨?_⟩
  intro f g
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 4.42.4: the identity arrow `id_U : U/U` viewed as an object of the slice
fiber over `U`. -/
private abbrev id_slice_fiber_obj (U : C) : (Over.forget U).Fiber U :=
  ⟨Over.mk (𝟙 U), rfl⟩

/-- Helper for Lemma 4.42.4: evaluating the Yoneda-selected slice morphism at `id_U`
recovers the chosen object `y ∈ Y_U`. -/
private noncomputable def yoneda_inverse_fiber_iso
    (U : C) (y : Y.p.Fiber U) :
    ((fiberFunctor (yoneda_inverse_slice (Y := Y) U y) U).obj
      (id_slice_fiber_obj U)) ≅ y := by
  -- The Yoneda counit identifies evaluation of the inverse object at `id_U` with `y`.
  simpa [yoneda_inverse_slice, FibredInGroupoidsMor.fiberFunctor] using
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y

/-- Helper for Lemma 4.42.4: representability of `F` forces every comma category
`((F_U x) ↓ F_U)` to be thin. -/
private theorem fiber_functor_image_structuredArrow_thin_of_is_representable
    (F : FibredInGroupoidsMor X Y)
    (hF : F.IsRepresentable)
    (U : C)
    (x : X.p.Fiber U) :
    Quiver.IsThin (StructuredArrow ((fiberFunctor F U).obj x) (fiberFunctor F U)) := by
  let y : Y.p.Fiber U := (fiberFunctor F U).obj x
  let Gy : ofFunctor (Over.forget U) ⟶ Y := yoneda_inverse_slice (Y := Y) U y
  let E :
      StructuredArrow ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U) ≌
        ((F.sliceTwoFibreProduct Gy).p).Fiber (Over.mk (𝟙 U)) :=
    sliceTwoFibreProductStructuredArrowEquivFiber
      (G := FibredInGroupoidsMor.toBasedFunctor Gy)
      (F := FibredInGroupoidsMor.toBasedFunctor F)
      (f := Over.mk (𝟙 U))
  -- Representability of the chosen slice base change gives a thin fiber over `id_U`.
  letI :
      IsFibredInSetoids (F.sliceTwoFibreProduct Gy).p :=
    (FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
      (F.sliceTwoFibreProduct Gy)).mp (hF Gy) |>.1
  have hThinSource :
      Quiver.IsThin (StructuredArrow
        ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U)) := by
    -- Lemma `4.42.1` identifies that fiber with the relevant structured-arrow category.
    letI : Quiver.IsThin (((F.sliceTwoFibreProduct Gy).p).Fiber (Over.mk (𝟙 U))) :=
      inferInstance
    letI : E.functor.Faithful := by
      infer_instance
    exact isThin_of_faithful E.functor
  let E' :
      StructuredArrow ((fiberFunctor Gy U).obj (id_slice_fiber_obj U)) (fiberFunctor F U) ≌
        StructuredArrow ((fiberFunctor F U).obj x) (fiberFunctor F U) :=
    StructuredArrow.mapIso
      (yoneda_inverse_fiber_iso (Y := Y) U ((fiberFunctor F U).obj x))
  -- Transport thinness across the Yoneda comparison of the source object.
  letI :
      Quiver.IsThin (StructuredArrow
        ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U)) :=
    hThinSource
  letI : E'.symm.functor.Faithful := by
    infer_instance
  exact isThin_of_faithful E'.symm.functor

/-- Helper for Lemma 4.42.4: if every structured-arrow category over an image object is thin,
then the functor is faithful. -/
private theorem faithful_of_image_structuredArrow_thin
    (G : A ⥤ B)
    (hThin : ∀ x : A, Quiver.IsThin (StructuredArrow (G.obj x) G)) :
    G.Faithful := by
  refine ⟨?_⟩
  intro a b f g hfg
  letI : Quiver.IsThin (StructuredArrow (G.obj a) G) := hThin a
  let source : StructuredArrow (G.obj a) G := StructuredArrow.mk (𝟙 (G.obj a))
  let target : StructuredArrow (G.obj a) G := StructuredArrow.mk (G.map f)
  let α : source ⟶ target := StructuredArrow.homMk f (by simp [source, target])
  let β : source ⟶ target := StructuredArrow.homMk g (by simpa [source, target] using hfg.symm)
  -- Thinness makes the two structured-arrow lifts coincide, hence their right components agree.
  have hαβ : α = β := Subsingleton.elim _ _
  simpa [α, β] using congrArg CommaMorphism.right hαβ

-- Proof sketch: for a fixed object `U : C`, Lemma `4.42.1` identifies the fiber over `𝟙 U` of
-- the representable base change `(C/U) ×_Y X → C/U` with the comma-style fiber category attached
-- to `F_U`. By Lemma `4.40.2`, a representable fibred category in groupoids is fibred in setoids,
-- so this fiber category is a setoid; that is exactly the faithfulness of `F_U`.
/-- Lemma 4.42.4: if a `1`-morphism `F : X ⟶ Y` of categories fibred in groupoids over `C` is
representable, then for every object `U : C` the induced functor `F_U : X_U ⥤ Y_U` between fiber
categories is faithful. -/
theorem fiber_functor_faithful_of_is_representable
    (F : FibredInGroupoidsMor X Y)
    (hF : F.IsRepresentable)
    (U : C) :
    (fiberFunctor F U).Faithful := by
  -- For each `x ∈ X_U`, representability makes the comma category `((F_U x) ↓ F_U)` thin.
  refine faithful_of_image_structuredArrow_thin (fiberFunctor F U) ?_
  intro x
  exact fiber_functor_image_structuredArrow_thin_of_is_representable F hF U x

end FibredInGroupoidsMor

end CategoryTheory

/-! ### Lemma_4_42_5 (from Chap04) -/
open Opposite
open Functor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

variable {X Y : FibredInGroupoidsOver C}
variable {A : Type*} [Category A]
variable {B : Type*} [Category B]

/- Domain-style sampling for Lemma 4.42.5:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the owner hom `F : X ⟶ Y` together with the canonical slice base-change
  object `F.sliceTwoFibreProduct G` attached to an actual slice morphism `G : C/U ⟶ Y`; the
  source-facing fibre-object formulation is recovered through Yoneda equivalence only as internal
  bridge data, not as a second public owner;
- primitive data: the owner morphism `F`, faithfulness of `F.toBasedFunctor`, and for each slice
  morphism `G : C/U ⟶ Y` representability of the canonical iso-class presheaf of
  `F.sliceTwoFibreProduct G`;
- derived API: the representability criterion from Lemma `4.40.2`, and the internal Yoneda bridge
  from a fiber object `y ∈ Y_U` to a slice morphism `G : C/U ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: Lemma 4.42.5;
- `core/canonical`: `F.IsRepresentable`;
- `bridge/view`: the internal Yoneda-selected morphism `C/U ⟶ Y` attached to a fiber object
  `y ∈ Y_U`. -/

/-- Helper for Lemma 4.42.5: a faithful functor into a thin category has a thin source. -/
private theorem isThin_of_faithful
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  intro a b
  refine ⟨?_⟩
  intro f g
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 4.42.5: in a groupoid-valued faithful functor, every structured-arrow
category is thin because the target commutativity relation determines the lifted arrow uniquely. -/
private theorem structuredArrow_thin_of_faithful
    (b : B) (G : A ⥤ B) [G.Faithful] [IsGroupoid B] :
    Quiver.IsThin (StructuredArrow b G) := by
  intro X Y
  refine ⟨?_⟩
  intro f g
  apply StructuredArrow.hom_ext
  apply G.map_injective
  have hf :
      inv X.hom ≫ Y.hom = G.map f.right := by
    -- Precompose the commutativity relation with the inverse of `X.hom`.
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) f.w
  have hg :
      inv X.hom ≫ Y.hom = G.map g.right := by
    -- The same normalization applies to any competing lift.
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) g.w
  exact hf.symm.trans hg

/-- Helper for Lemma 4.42.5: fiberwise faithfulness forces every slice base change of `F` to be
fibred in setoids. -/
private theorem sliceTwoFibreProduct_isFibredInSetoids_of_fiberwise_faithful
    (F : FibredInGroupoidsMor X Y)
    (hFiber : ∀ V : C, (fiberFunctor F V).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInSetoids (F.sliceTwoFibreProduct G).p := by
  refine { fiber_isThin := ?_ }
  intro f
  let E :
      StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl)) (fiberFunctor F f.left) ≌
        ((F.sliceTwoFibreProduct G).p).Fiber f := by
    -- Lemma `4.42.1` identifies the slice fiber with the structured-arrow category in the fiber.
    simpa [FibredInGroupoidsMor.sliceTwoFibreProduct] using
      (sliceTwoFibreProductStructuredArrowEquivFiber
        (G := FibredInGroupoidsMor.toBasedFunctor G)
        (F := FibredInGroupoidsMor.toBasedFunctor F)
        (f := f))
  letI : (fiberFunctor F f.left).Faithful := hFiber f.left
  letI :
      Quiver.IsThin
        (StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
          (fiberFunctor F f.left)) :=
    structuredArrow_thin_of_faithful
      ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
      (fiberFunctor F f.left)
  -- Transport the thin structured-arrow description across the equivalence from Lemma `4.42.1`.
  exact isThin_of_faithful E.symm.functor

/-- Helper for Lemma 4.42.5: once the slice base change is fibred in setoids, Lemma `4.40.2`
turns representability of its iso-class presheaf into representability of the slice itself. -/
private theorem sliceTwoFibreProduct_isRepresentable_of_faithful
    (F : FibredInGroupoidsMor X Y)
    (hFiber : ∀ V : C, (fiberFunctor F V).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ Y)
    (hG : ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf).IsRepresentable) :
    (F.sliceTwoFibreProduct G).IsRepresentable := by
  -- Lemma `4.40.2` reduces representability to the setoid condition plus the given presheaf.
  exact
    (FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
      (F.sliceTwoFibreProduct G)).2
      ⟨sliceTwoFibreProduct_isFibredInSetoids_of_fiberwise_faithful F hFiber G, hG⟩

-- Proof sketch: fix `U : C` and `G : C/U ⟶ Y`. The category `F.sliceTwoFibreProduct G` is the
-- canonical slice base change of `F` along `G`, and its iso-class presheaf is exactly the owner
-- presheaf `fiberIsoClassPresheaf (F.sliceTwoFibreProduct G).p`. Under Yoneda, taking `G`
-- corresponding to `y ∈ Y_U` recovers the source presheaf of pairs
-- `(x, \phi : f^* y ⟶ F(x))`. Faithfulness of `F.toBasedFunctor` forces each such slice
-- projection to be fibred in setoids, and Lemma `4.40.2` upgrades representability of every
-- slice iso-class presheaf to representability of every slice base change, hence of `F`.
/-- Lemma 4.42.5: let `F : X ⟶ Y` be a morphism of categories fibred in groupoids over `C`.
Assume that the underlying based functor `F.toBasedFunctor` is faithful and that for every object
`U : C` and every slice morphism `G : C/U ⟶ Y`, the canonical presheaf of isomorphism classes of
objects in the slice base change `F.sliceTwoFibreProduct G` is representable. Via the Yoneda
equivalence for `Y_U`, this is exactly the source presheaf of isomorphism classes of pairs
`(x, \phi : f^* y ⟶ F(x))`. Then `F` is representable. -/
theorem isRepresentable_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isRepresentable
    (F : FibredInGroupoidsMor X Y)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hRepresentable :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ Y),
        ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf).IsRepresentable) :
    F.IsRepresentable := by
  -- Route correction: follow the source proof through slice fibers and Lemma `4.40.2`,
  -- rather than re-expressing representability through a separate Yoneda detour.
  rw [isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable]
  have hFiber : ∀ U : C, (fiberFunctor F U).Faithful :=
    (faithful_iff_fiberwise (F := F)).1 hFaithful
  intro U G
  -- Each slice base change is representable once its fibers are setoids and its iso-class
  -- presheaf is representable by hypothesis.
  exact sliceTwoFibreProduct_isRepresentable_of_faithful F hFiber G (hRepresentable G)

end FibredInGroupoidsMor

end CategoryTheory

/-! ### Lemma_4_42_6 (from Chap04) -/
universe v u

namespace CategoryTheory

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]

/- The owner-level scaffolding for Lemma 4.42.6 — the canonical diagonal owner
`FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection`, the equivalence-transport of
representability, and the product-slice / diagonal base-change comparison — lives in
`Lemma_4_42_6/Core.lean`. The two directions of the equivalence are proved in
`Lemma_4_42_6/Direction1.lean` (`(1) → (2)`) and `Lemma_4_42_6/Direction2.lean` (`(2) → (1)`),
both built on the absolutization bridge `Lemma_4_42_6/SliceRepresentable.lean`. -/

-- Proof sketch: for `(1) → (2)`, fix `U` and `G : C/U ⥤ S`. To test representability of `G`,
-- pull back the diagonal along `(G, G') : C/U × C/V ⥤ S × S` for arbitrary `V` and `G'`,
-- using binary products in `C` and Lemma `4.31.11` together with Remark `4.35.8` to identify the
-- resulting representable pullback with `C/U ×_S C/V`. For `(2) → (1)`, start from a pair
-- `(G, G') : C/V ⥤ S × S`, apply representability to the first projection of
-- `C/V ×_{G, S, G'} C/V`, and then use Lemma `4.31.12` and Remark `4.35.8` to recover the
-- pullback of the diagonal.

/-- Lemma 4.42.6: for a category fibred in groupoids `X` over `C`, representability of its
canonical diagonal morphism is equivalent to representability of every morphism
`G : C/U ⟶ X` from a slice category. The left-hand side uses the canonical owner
`FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection` directly, rather than the wrapper alias
`FibredInGroupoidsOver.baseProjectionDiagonalMor X`. -/
theorem representable_diagonal_iff_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C] (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ↔
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G := by
  exact ⟨
    fun hDiagonal U G =>
      all_slice_morphisms_representable_of_representable_diagonal X hDiagonal G,
    fun hAll =>
      representable_diagonal_of_all_slice_morphisms_representable X hAll⟩

end CategoryTheory
