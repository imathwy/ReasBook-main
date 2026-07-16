import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_6_6.Index
import StacksProject_2024.stacks_project.Chap15.Situation_15_6_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u v

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

/-- Helper for Lemma 15.6.6: when the two composite scalar maps into `A` agree, the corresponding
restricted-scalar module structures are identified by the identity map on the underlying carrier. -/
private def restrictScalars_comm_hom
    (f : S.Bprime →+* B) (g : S.Bprime →+* A')
    (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (M : ModuleCat A) :
    (ModuleCat.restrictScalars (S.toA.comp f)).obj M ⟶
      (ModuleCat.restrictScalars (S.fromAprime.comp g)).obj M :=
  (eqToIso (congrArg
    (fun h ↦ (ModuleCat.restrictScalars h).obj M)
    hcomm)).hom

/-- Helper for Lemma 15.6.6: the transport map between equal restricted-scalar structures acts by
the identity on the underlying carrier. -/
private theorem restrictScalars_eqToIso_hom_apply
    {u v : S.Bprime →+* A} (h : u = v) (M : ModuleCat A)
    (m : (ModuleCat.restrictScalars u).obj M) :
    ((eqToIso (congrArg (fun w ↦ (ModuleCat.restrictScalars w).obj M) h)).hom) m = m := by
  -- Reduce to the reflexive ring-map equality so the transport becomes definitionally trivial.
  cases h
  rfl

/-- Helper for Lemma 15.6.6: the transport map between equal restricted-scalar structures acts by
the identity on the underlying carrier. -/
private theorem restrictScalars_comm_hom_apply
    (f : S.Bprime →+* B) (g : S.Bprime →+* A')
    (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (M : ModuleCat A)
    (m : (ModuleCat.restrictScalars (S.toA.comp f)).obj M) :
    restrictScalars_comm_hom (S := S) f g hcomm M m = m := by
  -- Rewrite the custom transport into the canonical `eqToIso` transport and evaluate it pointwise.
  simpa [restrictScalars_comm_hom] using
    restrictScalars_eqToIso_hom_apply (S := S) hcomm M m

/-- Helper for Lemma 15.6.6: the left comparison map from the restricted `B`-module to the common
base-changed target. -/
abbrev module_tensor_pullback_left_map
    (f : S.Bprime →+* B) (g : S.Bprime →+* A')
    (hcomm : S.toA.comp f = S.fromAprime.comp g) (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶
      (ModuleCat.restrictScalars (S.fromAprime.comp g)).obj
        ((ModuleCat.extendScalars S.fromAprime).obj X.snd) :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj S.toA).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f S.toA).inv.app ((ModuleCat.extendScalars S.toA).obj X.fst) ≫
    (ModuleCat.restrictScalars (S.toA.comp f)).map X.iso.hom ≫
    restrictScalars_comm_hom (S := S) f g hcomm
      ((ModuleCat.extendScalars S.fromAprime).obj X.snd)

/-- Helper for Lemma 15.6.6: the right comparison map from the restricted `A'`-module to the same
common base-changed target. -/
abbrev module_tensor_pullback_right_map
    (g : S.Bprime →+* A') (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶
      (ModuleCat.restrictScalars (S.fromAprime.comp g)).obj
        ((ModuleCat.extendScalars S.fromAprime).obj X.snd) :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj S.fromAprime).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g S.fromAprime).inv.app
      ((ModuleCat.extendScalars S.fromAprime).obj X.snd)

/-- Helper for Lemma 15.6.6: the left comparison map sends `n` to the standard generator in the
base-changed module, then applies the pullback isomorphism. -/
private theorem module_tensor_pullback_left_map_apply
    (f : S.Bprime →+* B) (g : S.Bprime →+* A')
    (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (X : PullbackModuleCat) (x : X.fst) :
    module_tensor_pullback_left_map (S := S) f g hcomm X x =
      restrictScalars_comm_hom (S := S) f g hcomm
        ((ModuleCat.extendScalars S.fromAprime).obj X.snd)
        (X.iso.hom ((1 : A) ⊗ₜ[B] x)) := by
  let _ : Algebra B A := S.toA.toAlgebra
  -- Unfold the left comparison map and observe that the unit sends `x` to the generator `1 ⊗ x`.
  change
    restrictScalars_comm_hom (S := S) f g hcomm
      ((ModuleCat.extendScalars S.fromAprime).obj X.snd)
      (X.iso.hom (((ModuleCat.extendRestrictScalarsAdj S.toA).unit.app X.fst) x)) =
    restrictScalars_comm_hom (S := S) f g hcomm
      ((ModuleCat.extendScalars S.fromAprime).obj X.snd)
      (X.iso.hom ((1 : A) ⊗ₜ[B] x))
  rfl

/-- Helper for Lemma 15.6.6: the right comparison map sends `m'` to the standard generator
`1 ⊗ m'`. -/
private theorem module_tensor_pullback_right_map_apply
    (g : S.Bprime →+* A') (X : PullbackModuleCat) (x : X.snd) :
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    module_tensor_pullback_right_map (S := S) g X x =
      (1 : A) ⊗ₜ[A'] x := by
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  rfl

/-- Helper for Lemma 15.6.6: the left comparison map is natural with respect to morphisms in the
pullback category. -/
private theorem module_tensor_pullback_left_map_natural
    (f : S.Bprime →+* B) (g : S.Bprime →+* A')
    (hcomm : S.toA.comp f = S.fromAprime.comp g)
    {X Y : PullbackModuleCat}
    (φ : X ⟶ Y)
    (x : (ModuleCat.restrictScalars f).obj X.fst) :
    ((ModuleCat.extendScalars S.fromAprime).map φ.snd).hom
        (module_tensor_pullback_left_map (S := S) f g hcomm X x) =
      module_tensor_pullback_left_map (S := S) f g hcomm Y
        (((ModuleCat.restrictScalars f).map φ.fst) x) := by
  let _ : Algebra B A := S.toA.toAlgebra
  -- Evaluate the pullback compatibility `φ.w` on the generator `1 ⊗ x`.
  have hx := congrArg
    (fun k ↦ ModuleCat.Hom.hom k ((1 : A) ⊗ₜ[B] x))
    φ.w
  rw [module_tensor_pullback_left_map_apply, module_tensor_pullback_left_map_apply,
    restrictScalars_comm_hom_apply, restrictScalars_comm_hom_apply]
  exact hx.symm.trans rfl

/-- Helper for Lemma 15.6.6: the right comparison map is natural with respect to morphisms in the
pullback category. -/
private theorem module_tensor_pullback_right_map_natural
    (g : S.Bprime →+* A')
    {X Y : PullbackModuleCat}
    (φ : X ⟶ Y)
    (x : (ModuleCat.restrictScalars g).obj X.snd) :
    ((ModuleCat.extendScalars S.fromAprime).map φ.snd).hom
        (module_tensor_pullback_right_map (S := S) g X x) =
      module_tensor_pullback_right_map (S := S) g Y (φ.snd x) := by
  -- The right comparison map is definitionally the map `m' ↦ 1 ⊗ m'`.
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  rw [module_tensor_pullback_right_map_apply, module_tensor_pullback_right_map_apply]
  rfl

/- Domain-style sampling for 15.6.6:
- primary domain: morphisms in the pullback category
  `Mod_B ×[Mod_A] Mod_{A'}`
  attached to Situation `15.6.1`, together with the induced map on the fibre-product module from
  `15.6.4`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `CategoricalPullback`,
  `module_tensor_pullback_right_adjoint`,
  `Functor.map`;
- best owner abstraction: the primitive source-facing data are an object
  `X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)`
  and a morphism `f : X ⟶ Y`; the induced map on fibre-product modules is the derived canonical
  morphism `((module_tensor_pullback_right_adjoint
    S.bprimeToB
    S.bprimeToAprime
    S.comm).map f)`;
- primitive data: `S`, `X`, `Y`, and `f`;
- derived API: the component maps `f.fst`, `f.snd`, and the induced map on the fibre-product
  module.

Source/core/bridge triage:
- `source-facing`: `surjectiveRingPullbackModuleFiberProduct_map_surjective`;
- `core/canonical`: the functor
  `module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm`;
- `bridge/view`: the explicit kernel model of the fibre-product module coming from
  `module_tensor_pullback_right_adjoint`. -/

-- Proof sketch: view `X` and `Y` as triples `(N₁, M'₁, φ₁)` and `(N₂, M'₂, φ₂)` in the canonical
-- pullback category of `15.6.4`. The morphism `f` provides the compatible pair of maps
-- `f.fst : N₁ → N₂` and `f.snd : M'₁ → M'₂`; surjectivity of these components is exactly the
-- hypothesis of the textbook argument, which then gives surjectivity on the induced map between
-- the fibre-product modules.

/-- Helper for Lemma 15.6.6: the ambient product module whose kernel realizes the fibre product.
-/
private abbrev rightAdjointSourceObj
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (X : PullbackModuleCat) :
    ModuleCat S.Bprime :=
  Limits.prod ((ModuleCat.restrictScalars f).obj X.fst) ((ModuleCat.restrictScalars g).obj X.snd)

/-- Helper for Lemma 15.6.6: the common target of the two comparison maps. -/
private abbrev rightAdjointTargetObj
    (g : S.Bprime →+* A') (X : PullbackModuleCat) :
    ModuleCat S.Bprime :=
  (ModuleCat.restrictScalars (S.fromAprime.comp g)).obj
    ((ModuleCat.extendScalars S.fromAprime).obj X.snd)

/-- Helper for Lemma 15.6.6: the left comparison map from the ambient product module. -/
private abbrev rightAdjointLeftMap
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (X : PullbackModuleCat) :
    rightAdjointSourceObj (S := S) f g X ⟶ rightAdjointTargetObj (S := S) g X :=
  Limits.prod.fst ≫ module_tensor_pullback_left_map (S := S) f g hcomm X

/-- Helper for Lemma 15.6.6: the right comparison map from the ambient product module. -/
private abbrev rightAdjointRightMap
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (X : PullbackModuleCat) :
    rightAdjointSourceObj (S := S) f g X ⟶ rightAdjointTargetObj (S := S) g X :=
  Limits.prod.snd ≫ module_tensor_pullback_right_map (S := S) g X

/-- Helper for Lemma 15.6.6: the defining difference map whose kernel is the fibre-product module.
-/
private abbrev rightAdjointDifference
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (X : PullbackModuleCat) :
    rightAdjointSourceObj (S := S) f g X ⟶ rightAdjointTargetObj (S := S) g X :=
  rightAdjointLeftMap (S := S) f g hcomm X - rightAdjointRightMap (S := S) f g X

/-- Helper for Lemma 15.6.6: expand the defining fibre-product difference map into its left and
right ambient comparison maps. -/
private theorem rightAdjointDifference_def
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    (X : PullbackModuleCat) :
    rightAdjointDifference (S := S) f g hcomm X =
      rightAdjointLeftMap (S := S) f g hcomm X - rightAdjointRightMap (S := S) f g X := rfl

/-- Helper for Lemma 15.6.6: the ambient product modules assemble functorially over the pullback
category. -/
private def rightAdjointSourceFunctor
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') : PullbackModuleCat ⥤ ModuleCat S.Bprime where
  obj X := rightAdjointSourceObj (S := S) f g X
  map φ := Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
    ((ModuleCat.restrictScalars g).map φ.snd)
  map_id X := by
    ext <;> simp
  map_comp φ ψ := by
    ext <;> simp

/-- Helper for Lemma 15.6.6: the common targets of the comparison maps assemble functorially. -/
private def rightAdjointTargetFunctor
    (g : S.Bprime →+* A') : PullbackModuleCat ⥤ ModuleCat S.Bprime where
  obj X := rightAdjointTargetObj (S := S) g X
  map φ := (ModuleCat.restrictScalars (S.fromAprime.comp g)).map
    ((ModuleCat.extendScalars S.fromAprime).map φ.snd)
  map_id X := by
    simp
  map_comp φ ψ := by
    simp

/-- Helper for Lemma 15.6.6: the defining difference maps are natural in the pullback-module
variable. -/
private theorem rightAdjointDifference_naturality
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    {X Y : PullbackModuleCat}
    (φ : X ⟶ Y) :
    (rightAdjointSourceFunctor (S := S) f g).map φ ≫
      rightAdjointDifference (S := S) f g hcomm Y =
      rightAdjointDifference (S := S) f g hcomm X ≫
      (rightAdjointTargetFunctor (S := S) g).map φ := by
  -- Split the difference map into its left and right pieces and verify each piece separately.
  have hleft :
      (rightAdjointSourceFunctor (S := S) f g).map φ ≫
          rightAdjointLeftMap (S := S) f g hcomm Y =
        rightAdjointLeftMap (S := S) f g hcomm X ≫
          (rightAdjointTargetFunctor (S := S) g).map φ := by
    ext z
    simpa [rightAdjointLeftMap, rightAdjointSourceFunctor, rightAdjointTargetFunctor] using
      (module_tensor_pullback_left_map_natural (S := S) f g hcomm φ
        ((Limits.prod.fst : rightAdjointSourceObj (S := S) f g X ⟶
          (ModuleCat.restrictScalars f).obj X.fst) z)).symm
  have hright :
      (rightAdjointSourceFunctor (S := S) f g).map φ ≫
          rightAdjointRightMap (S := S) f g Y =
        rightAdjointRightMap (S := S) f g X ≫
          (rightAdjointTargetFunctor (S := S) g).map φ := by
    ext z
    simpa [rightAdjointRightMap, rightAdjointSourceFunctor, rightAdjointTargetFunctor] using
      (module_tensor_pullback_right_map_natural (S := S) g φ
        ((Limits.prod.snd : rightAdjointSourceObj (S := S) f g X ⟶
          (ModuleCat.restrictScalars g).obj X.snd) z)).symm
  calc
    (rightAdjointSourceFunctor (S := S) f g).map φ ≫
        rightAdjointDifference (S := S) f g hcomm Y =
      (rightAdjointSourceFunctor (S := S) f g).map φ ≫
        (rightAdjointLeftMap (S := S) f g hcomm Y -
          rightAdjointRightMap (S := S) f g Y) := by
            rw [rightAdjointDifference_def]
    _ = (rightAdjointSourceFunctor (S := S) f g).map φ ≫
          rightAdjointLeftMap (S := S) f g hcomm Y -
        (rightAdjointSourceFunctor (S := S) f g).map φ ≫
          rightAdjointRightMap (S := S) f g Y := by
            exact Preadditive.comp_sub _ _ _
    _ = rightAdjointLeftMap (S := S) f g hcomm X ≫
          (rightAdjointTargetFunctor (S := S) g).map φ -
        rightAdjointRightMap (S := S) f g X ≫
          (rightAdjointTargetFunctor (S := S) g).map φ := by
            rw [hleft, hright]
            rfl
    _ = (rightAdjointLeftMap (S := S) f g hcomm X -
          rightAdjointRightMap (S := S) f g X) ≫
        (rightAdjointTargetFunctor (S := S) g).map φ := by
            symm
            exact Preadditive.sub_comp _ _ _
    _ = rightAdjointDifference (S := S) f g hcomm X ≫
          (rightAdjointTargetFunctor (S := S) g).map φ := by
            rfl

/-- Helper for Lemma 15.6.6: the difference maps form a natural transformation. -/
private def rightAdjointDifferenceNatTrans
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g) :
    rightAdjointSourceFunctor (S := S) f g ⟶ rightAdjointTargetFunctor (S := S) g :=
  let T : PullbackModuleCat ⥤ ModuleCat S.Bprime := rightAdjointTargetFunctor (S := S) g
  show rightAdjointSourceFunctor (S := S) f g ⟶ T from
    { app := fun X ↦ rightAdjointDifference (S := S) f g hcomm X
      naturality := by
        intro X Y φ
        exact rightAdjointDifference_naturality (S := S) f g hcomm φ }

/-- Helper for Lemma 15.6.6: package the ambient product and difference map as an arrow-valued
functor so that pointwise kernels recover the fibre-product modules. -/
private def rightAdjointArrow
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g) :
    PullbackModuleCat ⥤ Arrow (ModuleCat S.Bprime) where
  obj X := Arrow.mk ((rightAdjointDifferenceNatTrans (S := S) f g hcomm).app X)
  map {X Y} φ :=
    Arrow.homMk'
      ((rightAdjointSourceFunctor (S := S) f g).map φ)
      ((rightAdjointTargetFunctor (S := S) g).map φ)
      ((rightAdjointDifferenceNatTrans (S := S) f g hcomm).naturality φ)

/-- Helper for Lemma 15.6.6: the fibre-product module functor is the pointwise kernel of the
defining difference map. -/
abbrev module_tensor_pullback_right_adjoint
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g) :
    PullbackModuleCat ⥤ ModuleCat S.Bprime :=
  rightAdjointArrow (S := S) f g hcomm ⋙ Limits.ker (ModuleCat S.Bprime)

/-- Helper for Lemma 15.6.6: a compatible pair of maps into the two pullback components
equalizes the defining difference map. -/
private theorem rightAdjointLift_condition
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    {L : ModuleCat S.Bprime}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map (S := S) f g hcomm X)
      (module_tensor_pullback_right_map (S := S) g X)) :
    Limits.prod.lift u v ≫ rightAdjointDifference (S := S) f g hcomm X = 0 := by
  -- The compatibility square says the two components agree after mapping to the common target.
  rw [rightAdjointDifference, Preadditive.comp_sub, sub_eq_zero]
  calc
    Limits.prod.lift u v ≫ rightAdjointLeftMap (S := S) f g hcomm X =
        u ≫ module_tensor_pullback_left_map (S := S) f g hcomm X := by
          rw [rightAdjointLeftMap, ← Category.assoc, Limits.prod.lift_fst]
    _ = v ≫ module_tensor_pullback_right_map (S := S) g X := by
          simpa using hcompat.w
    _ = Limits.prod.lift u v ≫ rightAdjointRightMap (S := S) f g X := by
          symm
          rw [rightAdjointRightMap, ← Category.assoc, Limits.prod.lift_snd]

/-- Helper for Lemma 15.6.6: the universal map from a compatible pair into the fibre-product
kernel object. -/
abbrev module_tensor_pullback_right_adjoint_lift
    (f : S.Bprime →+* B) (g : S.Bprime →+* A') (hcomm : S.toA.comp f = S.fromAprime.comp g)
    {L : ModuleCat S.Bprime}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map (S := S) f g hcomm X)
      (module_tensor_pullback_right_map (S := S) g X)) :
    L ⟶ Limits.kernel (rightAdjointDifference (S := S) f g hcomm X) :=
  kernel.lift
    (rightAdjointDifference (S := S) f g hcomm X)
    (Limits.prod.lift u v)
    (rightAdjointLift_condition (S := S) f g hcomm u v hcompat)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint (S := S) S.bprimeToB S.bprimeToAprime S.comm

/-- Helper for Lemma 15.6.6: the ambient product module containing the fibre-product kernel model.
-/
abbrev fiber_product_ambient_product
    (X : PullbackModuleCat) : ModuleCat S.Bprime :=
  Limits.prod ((ModuleCat.restrictScalars S.bprimeToB).obj X.fst)
    ((ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd)

/-- Helper for Lemma 15.6.6: the first projection from the ambient product module. -/
abbrev fiber_product_ambient_fst
    (X : PullbackModuleCat) :
    fiber_product_ambient_product (S := S) X ⟶
      (ModuleCat.restrictScalars S.bprimeToB).obj X.fst :=
  Limits.prod.fst

/-- Helper for Lemma 15.6.6: the second projection from the ambient product module. -/
abbrev fiber_product_ambient_snd
    (X : PullbackModuleCat) :
    fiber_product_ambient_product (S := S) X ⟶
      (ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd :=
  Limits.prod.snd

/-- Helper for Lemma 15.6.6: the explicit difference map whose kernel is the fibre-product module.
-/
abbrev fiber_product_ambient_difference
    (X : PullbackModuleCat) :
    fiber_product_ambient_product (S := S) X ⟶
      (ModuleCat.restrictScalars (S.fromAprime.comp S.bprimeToAprime)).obj
        ((ModuleCat.extendScalars S.fromAprime).obj X.snd) :=
  fiber_product_ambient_fst (S := S) X ≫
      module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X -
    fiber_product_ambient_snd (S := S) X ≫
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X

/-- Helper for Lemma 15.6.6: the public fibre-product object embeds into the ambient product by
the kernel inclusion. -/
abbrev fiber_product_kernel_iota
    (X : PullbackModuleCat) :
    Limits.kernel (fiber_product_ambient_difference (S := S) X) ⟶
      fiber_product_ambient_product (S := S) X :=
  kernel.ι (fiber_product_ambient_difference (S := S) X)

/-- Helper for Lemma 15.6.6: a morphism in the pullback category induces the obvious map on the
ambient product modules. -/
abbrev fiber_product_ambient_map
    {X Y : PullbackModuleCat} (f : X ⟶ Y) :
    fiber_product_ambient_product (S := S) X ⟶
      fiber_product_ambient_product (S := S) Y :=
  Limits.prod.map ((ModuleCat.restrictScalars S.bprimeToB).map f.fst)
    ((ModuleCat.restrictScalars S.bprimeToAprime).map f.snd)

/-- Helper for Lemma 15.6.6: evaluating the ambient difference map amounts to subtracting the two
comparison maps on the two ambient coordinates. -/
lemma fiber_product_ambient_difference_apply
    (X : PullbackModuleCat)
    (z : fiber_product_ambient_product (S := S) X) :
    fiber_product_ambient_difference (S := S) X z =
      module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X
          ((fiber_product_ambient_fst (S := S) X) z) -
        module_tensor_pullback_right_map (S := S) S.bprimeToAprime X
          ((fiber_product_ambient_snd (S := S) X) z) := by
  rfl

/-- Helper for Lemma 15.6.6: a compatible pair of maps into the two pullback components yields a
map into the kernel model of the fibre-product module. -/
abbrev fiber_product_lift
    {L : ModuleCat S.Bprime}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars S.bprimeToB).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd)
    (hcompat : CommSq u v
      (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X)
      (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X)) :
    L ⟶ Limits.kernel (fiber_product_ambient_difference (S := S) X) :=
  module_tensor_pullback_right_adjoint_lift (S := S) S.bprimeToB S.bprimeToAprime S.comm u v hcompat

/-- Helper for Lemma 15.6.6: after composing the universal lift with the kernel inclusion, one
recovers the ambient product map. -/
lemma module_tensor_pullback_right_adjoint_lift_comp_kernel_iota
    {L : ModuleCat S.Bprime}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars S.bprimeToB).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd)
    (hcompat : CommSq u v
      (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X)
      (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X)) :
    fiber_product_lift (S := S) u v hcompat ≫
      fiber_product_kernel_iota (S := S) X =
      Limits.prod.lift u v := by
  -- Composing a kernel lift with the kernel inclusion recovers the ambient product map.
  simpa [fiber_product_lift, module_tensor_pullback_right_adjoint_lift, fiber_product_kernel_iota]
    using
      kernel.lift_ι
        (rightAdjointDifference (S := S) S.bprimeToB S.bprimeToAprime S.comm X)
        (Limits.prod.lift u v)
        (rightAdjointLift_condition
          (S := S) S.bprimeToB S.bprimeToAprime S.comm u v hcompat)

/-- Helper for Lemma 15.6.6: after composing with the kernel inclusion, the map on fibre-product
modules is the evident map on the ambient products. -/
private theorem module_tensor_pullback_right_adjoint_map_comp_kernel_iota
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y) :
    (fiberProductFunctor).map f ≫ fiber_product_kernel_iota (S := S) Y =
      fiber_product_kernel_iota (S := S) X ≫ fiber_product_ambient_map (S := S) f := by
  -- Route correction: unfold the kernel functor map once so the claim reduces to
  -- `kernel.lift_ι`, avoiding repeated `whnf` on the ambient difference map.
  dsimp [module_tensor_pullback_right_adjoint, rightAdjointArrow, rightAdjointDifferenceNatTrans,
    fiber_product_kernel_iota, fiber_product_ambient_map, fiber_product_ambient_difference,
    fiber_product_ambient_fst, fiber_product_ambient_snd, rightAdjointDifference,
    rightAdjointLeftMap, rightAdjointRightMap, kernel.map]
  exact kernel.lift_ι _ _ _

/-- Helper for Lemma 15.6.6: the left comparison map is natural with respect to morphisms in the
pullback category. -/
lemma extend_scalars_snd_map_left_map
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (x : X.fst) :
    ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
        (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X x) =
      module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm Y (f.fst x) := by
  simpa using
    module_tensor_pullback_left_map_natural (S := S) S.bprimeToB S.bprimeToAprime S.comm f x

/-- Helper for Lemma 15.6.6: the right comparison map is natural with respect to the second
component map. -/
lemma extend_scalars_snd_map_right_map
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (x : X.snd) :
    ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
        (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x) =
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime Y (f.snd x) := by
  simpa using module_tensor_pullback_right_map_natural (S := S) S.bprimeToAprime f x

/-- Helper for Lemma 15.6.6: after lifting the two ambient coordinates of a target fibre-product
element, the resulting compatibility defect is killed by the base-changed second component map. -/
lemma ambient_defect_mem_kernel_extend_scalars_snd
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (y : (fiberProductFunctor).obj Y)
    {n1 : X.fst}
    {m1 : X.snd}
    (hn1 : f.fst n1 =
      (fiber_product_ambient_fst (S := S) Y).hom
        ((fiber_product_kernel_iota (S := S) Y).hom y))
    (hm1 : f.snd m1 =
      (fiber_product_ambient_snd (S := S) Y).hom
        ((fiber_product_kernel_iota (S := S) Y).hom y)) :
    ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
        (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1 -
          module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1) = 0 := by
  -- Push the defect forward, rewrite both summands by naturality, and then use that `y` lies in
  -- the kernel of the ambient difference map on `Y`.
  rw [show ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
      (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1 -
        module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1) =
      ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
          (module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1) -
        ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
          (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1) by
      exact map_sub _ _ _]
  rw [extend_scalars_snd_map_left_map, extend_scalars_snd_map_right_map]
  rw [hn1, hm1]
  have hy :
      fiber_product_ambient_difference (S := S) Y
          (((fiber_product_kernel_iota (S := S) Y).hom) y) = 0 := by
    -- Evaluating the kernel equation on `y` says exactly that the ambient defect vanishes.
    exact congrArg (fun k ↦ k y)
      (kernel.condition (fiber_product_ambient_difference (S := S) Y))
  simpa [fiber_product_ambient_difference_apply] using hy

/-- Helper for Lemma 15.6.6: a surjective linear map sends `ker(S.fromAprime) M` onto
`ker(S.fromAprime) N`. -/
lemma map_smul_top_eq_of_surjective
    {M N : Type*} [AddCommGroup M] [Module A' M] [AddCommGroup N] [Module A' N]
    (ψ : M →ₗ[A'] N) (hψ : Function.Surjective ψ) :
    Submodule.map ψ ((RingHom.ker S.fromAprime) • (⊤ : Submodule A' M)) =
      (RingHom.ker S.fromAprime) • (⊤ : Submodule A' N) := by
  -- The source proof uses only the canonical image formula for scalar multiples under a
  -- surjective map, so keep this step at the submodule level and avoid an element chase.
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hψ]

/-- Helper for Lemma 15.6.6: a defect killed by the base-changed second component comes from a
kernel vector of `f.snd` after applying the canonical map `m' ↦ 1 ⊗ m'`. -/
lemma right_map_surjective_on_kernel_of_snd
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (hsnd : Function.Surjective f.snd)
    (δ : ((ModuleCat.extendScalars S.fromAprime).obj X.snd))
    (hδ : ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom δ = 0) :
    ∃ k : LinearMap.ker (ModuleCat.Hom.hom f.snd),
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X k.1 = δ := by
  -- Route correction: the remaining source-faithful route is to transport the scalar-extension
  -- object to the quotient model from `Lemma_15_6_6/QuotientBridge.lean`, turn `hδ` into a
  -- quotient-map vanishing statement, and then correct a lift by an element of `ker f.snd`.
  let I : Ideal A' := RingHom.ker S.fromAprime
  let q : fromAprime_quotient_obj (S := S) X.snd :=
    (fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).hom δ
  obtain ⟨x, hxq⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A' X.snd)) q
  have hδ_repr :
      ((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
          ((I • (⊤ : Submodule A' X.snd)).mkQ x) = δ := by
    -- The chosen quotient representative of `δ` becomes `δ` again after applying the inverse
    -- quotient-model isomorphism.
    rw [hxq]
    change
      ((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
          ((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).hom δ) = δ
    exact (fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).hom_inv_id_apply δ
  have hmap_mkQ :
      ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
          (((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
            ((I • (⊤ : Submodule A' X.snd)).mkQ x)) =
        (((fromAprime_extendScalars_obj_iso_quotient (S := S) Y.snd).inv).hom
          ((I • (⊤ : Submodule A' Y.snd)).mkQ (f.snd x))) := by
    -- Rewrite both source and target terms to the standard tensors `1 ⊗ x` and `1 ⊗ f.snd x`.
    have htarget :
        ((1 : A) ⊗ₜ[A'] f.snd x : (ModuleCat.extendScalars S.fromAprime).obj Y.snd) =
          (((fromAprime_extendScalars_obj_iso_quotient (S := S) Y.snd).inv).hom
            ((I • (⊤ : Submodule A' Y.snd)).mkQ (f.snd x))) := by
      simpa using
        (fromAprime_extendScalars_obj_iso_quotient_inv_mkQ
          (S := S) Y.snd (f.snd x)).symm
    rw [fromAprime_extendScalars_obj_iso_quotient_inv_mkQ (S := S) X.snd x]
    rw [show ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
        ((1 : A) ⊗ₜ[A'] x) =
      ((1 : A) ⊗ₜ[A'] f.snd x : (ModuleCat.extendScalars S.fromAprime).obj Y.snd) by
        rfl]
    exact htarget
  have hmkQ_zero :
      ((I • (⊤ : Submodule A' Y.snd)).mkQ (f.snd x)) = 0 := by
    -- Applying the quotient-model isomorphism to the base-changed defect shows that the quotient
    -- class of `f.snd x` vanishes.
    have hzero_tensor :
        ((fromAprime_extendScalars_obj_iso_quotient (S := S) Y.snd).inv).hom
            ((I • (⊤ : Submodule A' Y.snd)).mkQ (f.snd x)) = 0 := by
      calc
        ((fromAprime_extendScalars_obj_iso_quotient (S := S) Y.snd).inv).hom
            ((I • (⊤ : Submodule A' Y.snd)).mkQ (f.snd x)) =
            ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom
              (((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
                ((I • (⊤ : Submodule A' X.snd)).mkQ x)) := by
                symm
                exact hmap_mkQ
        _ = ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom δ := by
              rw [hδ_repr]
        _ = 0 := hδ
    have hzero_apply := congrArg
      (ModuleCat.Hom.hom (fromAprime_extendScalars_obj_iso_quotient (S := S) Y.snd).hom)
      hzero_tensor
    simpa using hzero_apply
  have hfx_mem :
      f.snd x ∈ I • (⊤ : Submodule A' Y.snd) := by
    -- Vanishing of the quotient class is equivalent to membership in `I • ⊤`.
    exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A' Y.snd))).1 hmkQ_zero
  have hmap_smul :
      Submodule.map (ModuleCat.Hom.hom f.snd) (I • (⊤ : Submodule A' X.snd)) =
        I • (⊤ : Submodule A' Y.snd) :=
    map_smul_top_eq_of_surjective (S := S) (ModuleCat.Hom.hom f.snd) hsnd
  have hfx_mem_map :
      f.snd x ∈ Submodule.map (ModuleCat.Hom.hom f.snd) (I • (⊤ : Submodule A' X.snd)) := by
    simpa [hmap_smul] using hfx_mem
  rw [Submodule.mem_map] at hfx_mem_map
  rcases hfx_mem_map with ⟨xI, hxI_mem, hxI_eq⟩
  have hxI_mkQ_zero :
      ((I • (⊤ : Submodule A' X.snd)).mkQ xI) = 0 := by
    -- The correction term already lies in `I • ⊤`, so its quotient class is trivial.
    exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A' X.snd))).2 hxI_mem
  have hright_x :
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x = δ := by
    -- The chosen representative `x` maps back to the original defect element `δ`.
    calc
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x =
          ((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
            ((I • (⊤ : Submodule A' X.snd)).mkQ x) := by
            rw [module_tensor_pullback_right_map_apply]
            exact
              (fromAprime_extendScalars_obj_iso_quotient_inv_mkQ (S := S) X.snd x).symm
      _ = δ := hδ_repr
  have hright_xI :
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X xI = 0 := by
    -- The `I`-multiple correction term dies after extending scalars to `A`.
    calc
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X xI =
          ((fromAprime_extendScalars_obj_iso_quotient (S := S) X.snd).inv).hom
            ((I • (⊤ : Submodule A' X.snd)).mkQ xI) := by
            rw [module_tensor_pullback_right_map_apply]
            exact
              (fromAprime_extendScalars_obj_iso_quotient_inv_mkQ (S := S) X.snd xI).symm
      _ = 0 := by
            rw [hxI_mkQ_zero]
            simp
  have hk_mem :
      x - xI ∈ LinearMap.ker (ModuleCat.Hom.hom f.snd) := by
    -- Subtracting the lifted `I`-multiple removes the image under `f.snd`.
    change f.snd (x - xI) = 0
    simp [hxI_eq]
  let k : LinearMap.ker (ModuleCat.Hom.hom f.snd) := ⟨x - xI, hk_mem⟩
  refine ⟨k, ?_⟩
  -- The correction term maps to zero after scalar extension, so the right comparison sends
  -- `x - xI` back to the original defect `δ`.
  calc
    module_tensor_pullback_right_map (S := S) S.bprimeToAprime X k.1 =
        module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x -
          module_tensor_pullback_right_map (S := S) S.bprimeToAprime X xI := by
            change
              module_tensor_pullback_right_map (S := S) S.bprimeToAprime X (x - xI) =
                module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x -
                  module_tensor_pullback_right_map (S := S) S.bprimeToAprime X xI
            exact map_sub (ModuleCat.Hom.hom
              (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X)) x xI
    _ = module_tensor_pullback_right_map (S := S) S.bprimeToAprime X x := by
          rw [hright_xI, sub_zero]
    _ = δ := hright_x
set_option maxHeartbeats 5000000 in
section

/-- Helper for Lemma 15.6.6: the canonical kernel-model map induced by a morphism in the pullback
module category is surjective when the two component maps are surjective. -/
private theorem canonical_pullback_module_map_surjective
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (hfst : Function.Surjective f.fst)
    (hsnd : Function.Surjective f.snd) :
    Function.Surjective
      ((module_tensor_pullback_right_adjoint
        (S := S) S.bprimeToB S.bprimeToAprime S.comm).map f) := by
  intro y
  let y₀ : fiber_product_ambient_product (S := S) Y :=
    (fiber_product_kernel_iota (S := S) Y).hom y
  obtain ⟨n1, hn1⟩ := hfst ((fiber_product_ambient_fst (S := S) Y).hom y₀)
  obtain ⟨m1, hm1⟩ := hsnd ((fiber_product_ambient_snd (S := S) Y).hom y₀)
  let δ :=
    module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1 -
      module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1
  have hδ :
      ((ModuleCat.extendScalars S.fromAprime).map f.snd).hom δ = 0 := by
    -- The textbook defect becomes zero after applying the target compatibility relation.
    have hδ₀ :=
      ambient_defect_mem_kernel_extend_scalars_snd
        (S := S) (X := X) (Y := Y) (f := f) (y := y) (n1 := n1) (m1 := m1) hn1 hm1
    simpa [δ, y₀] using hδ₀
  obtain ⟨k, hk⟩ :=
    right_map_surjective_on_kernel_of_snd (S := S) f hsnd δ hδ
  have hcompat₀ :
      module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1 =
        module_tensor_pullback_right_map (S := S) S.bprimeToAprime X (m1 + k.1) := by
    -- Route correction: use the corrected right lift `m1 + k` from the source proof, so the
    -- ambient defect vanishes before forming the kernel lift.
    calc
      module_tensor_pullback_left_map (S := S) S.bprimeToB S.bprimeToAprime S.comm X n1 =
          δ + module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1 := by
            dsimp [δ]
            abel
      _ = module_tensor_pullback_right_map (S := S) S.bprimeToAprime X k.1 +
            module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1 := by
              rw [hk]
      _ = module_tensor_pullback_right_map (S := S) S.bprimeToAprime X m1 +
            module_tensor_pullback_right_map (S := S) S.bprimeToAprime X k.1 := by
              simp [add_comm]
      _ = module_tensor_pullback_right_map (S := S) S.bprimeToAprime X (m1 + k.1) := by
            symm
            exact map_add
              (ModuleCat.Hom.hom
                (module_tensor_pullback_right_map (S := S) S.bprimeToAprime X))
              m1 k.1
  let z : fiber_product_ambient_product (S := S) X := PProd.mk n1 (m1 + k.1)
  have hz :
      fiber_product_ambient_difference (S := S) X z = 0 := by
    -- The corrected ambient pair already satisfies the defining kernel equation.
    simpa [fiber_product_ambient_difference_apply, z] using sub_eq_zero.2 hcompat₀
  have hz_mem :
      z ∈ LinearMap.ker (ModuleCat.Hom.hom (fiber_product_ambient_difference (S := S) X)) := by
    simpa [LinearMap.mem_ker] using hz
  let x₀ :
      LinearMap.ker (ModuleCat.Hom.hom (fiber_product_ambient_difference (S := S) X)) :=
    ⟨z, hz_mem⟩
  let x : (fiberProductFunctor).obj X :=
    ((ModuleCat.kernelIsoKer (fiber_product_ambient_difference (S := S) X)).inv).hom x₀
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective (fiber_product_kernel_iota (S := S) Y)).1 inferInstance
  have hx_ambient :
      (fiber_product_kernel_iota (S := S) X).hom x =
        z := by
    -- The kernel object is canonically the subtype of ambient vectors satisfying the defect
    -- equation, and `x` is the image of the corrected ambient pair under this identification.
    have hx₀ :
        ((ModuleCat.kernelIsoKer (fiber_product_ambient_difference (S := S) X)).hom) x = x₀ := by
      let e := ModuleCat.kernelIsoKer (fiber_product_ambient_difference (S := S) X)
      have h :=
        congrArg
          (fun q :
            ModuleCat.of S.Bprime
                ↥(ModuleCat.Hom.hom (fiber_product_ambient_difference (S := S) X)).ker ⟶
              ModuleCat.of S.Bprime
                ↥(ModuleCat.Hom.hom (fiber_product_ambient_difference (S := S) X)).ker ↦ q x₀)
          e.inv_hom_id
      simpa [x, e] using h
    have hι := congrArg
      (fun q : (fiberProductFunctor).obj X ⟶ fiber_product_ambient_product (S := S) X ↦ q x)
      (ModuleCat.kernelIsoKer_hom_ker_subtype
        (f := fiber_product_ambient_difference (S := S) X))
    calc
      (fiber_product_kernel_iota (S := S) X).hom x =
          (ModuleCat.ofHom
            (ModuleCat.Hom.hom (fiber_product_ambient_difference (S := S) X)).ker.subtype)
            (((ModuleCat.kernelIsoKer (fiber_product_ambient_difference (S := S) X)).hom) x) := by
              exact hι.symm
      _ = x₀.1 := by
            rw [hx₀]
            rfl
      _ = z := rfl
  have hmap_ambient :
      (fiber_product_kernel_iota (S := S) Y).hom (((fiberProductFunctor).map f).hom x) =
        (fiber_product_ambient_map (S := S) f).hom
          ((fiber_product_kernel_iota (S := S) X).hom x) := by
    -- The map on kernels is the evident map on ambient products after postcomposing with `ι`.
    exact congrArg
      (fun q : (fiberProductFunctor).obj X ⟶ fiber_product_ambient_product (S := S) Y ↦ q x)
      (module_tensor_pullback_right_adjoint_map_comp_kernel_iota (S := S) f)
  have hy_ambient :
      (fiber_product_ambient_map (S := S) f).hom
          z = y₀ := by
    -- Compare the two ambient elements by their two product projections.
    apply PProd.ext
    · change f.fst n1 = (fiber_product_ambient_fst (S := S) Y).hom y₀
      simpa [fiber_product_ambient_map, fiber_product_ambient_fst, z] using hn1
    · change f.snd (m1 + k.1) = (fiber_product_ambient_snd (S := S) Y).hom y₀
      simp [fiber_product_ambient_map, fiber_product_ambient_snd, z, hm1, k.2]
  calc
    (fiber_product_kernel_iota (S := S) Y).hom (((fiberProductFunctor).map f).hom x) =
        (fiber_product_ambient_map (S := S) f).hom
          ((fiber_product_kernel_iota (S := S) X).hom x) := hmap_ambient
    _ = (fiber_product_ambient_map (S := S) f).hom
          z := by
            rw [hx_ambient]
    _ = y₀ := hy_ambient
    _ = (fiber_product_kernel_iota (S := S) Y).hom y := by
          rfl

 
/-- Lemma 15.6.6: in Situation `15.6.1`, a morphism in
`Mod_B ×[Mod_A] Mod_{A'}`
whose `B`-component and `A'`-component are surjective induces a surjective map on the associated
fibre-product modules over `B' = B ×_A A'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_map_surjective
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (hfst : Function.Surjective f.fst)
    (hsnd : Function.Surjective f.snd) :
    Function.Surjective
      ((fiberProductFunctor).map f) := by
  simpa using canonical_pullback_module_map_surjective (S := S) f hfst hsnd

end

end
