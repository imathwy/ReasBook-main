import Mathlib
import StacksProject_2024.Chap15.«15_6_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

section

variable {R R' B B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable {s : B →+* R} {t : R' →+* R} (f : B' →+* B) (g : B' →+* R')
variable (hcomm : s.comp f = t.comp g)

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars s) (ModuleCat.extendScalars t)

/- Domain-style sampling for Lemma 15.5.4:
- primary domain: categorical base change for module categories over a commutative square of
  commutative rings, together with the kernel model of the fibre-product module;
- sampled owner declarations:
  `CategoricalPullback.CatCommSqOver`,
  `CategoricalPullback.π₂`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `CategoryTheory.CommSq`,
  `Limits.ker`;
- best owner abstraction: the source-facing right adjoint is the kernel of the canonical
  `Arrow (ModuleCat B')`-valued functor attached to the defining difference morphism;
- primitive data: the product source functor, the common target functor, and the defining
  difference natural transformation between them;
- derived API: the induced `Arrow`-valued functor, the kernel-valued right adjoint, the universal
  lift into that kernel, and the adjunction with base change.

Source/core/bridge triage:
- `source-facing`: `module_tensor_pullback_right_adjoint`,
  `module_tensor_pullback_right_adjoint_lift`,
  `module_tensor_pullback_adjunction`;
- `core/canonical`: `Arrow (ModuleCat B')`, `Limits.ker`, and the chapter owner
  `moduleCatBaseChangeToCategoricalPullback`;
- `bridge/view`: the explicit difference morphism whose kernel realizes the fibre-product module. -/

private abbrev rightAdjointSourceObj
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) : ModuleCat B' :=
  Limits.prod ((ModuleCat.restrictScalars f).obj X.fst) ((ModuleCat.restrictScalars g).obj X.snd)

private abbrev rightAdjointTargetObj
    (g : B' →+* R') (X : PullbackModuleCat) : ModuleCat B' :=
  (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd)

/-- Helper for Lemma 15.5.4: when the two composite scalar maps into `R` agree, the corresponding
restricted-scalar structures are identified by the identity map on the underlying carrier. -/
private def restrictScalars_comm_hom
    (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g)
    (M : ModuleCat R) :
    (ModuleCat.restrictScalars (s.comp f)).obj M ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj M :=
  (eqToIso (congrArg
    (fun h ↦ (ModuleCat.restrictScalars h).obj M)
    hcomm)).hom

/-- The left comparison map from the first component to the common target, obtained from the unit of
extension-restriction of scalars and the structural isomorphism in the categorical pullback. -/
abbrev module_tensor_pullback_left_map
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj s).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f s).inv.app ((ModuleCat.extendScalars s).obj X.fst) ≫
    (ModuleCat.restrictScalars (s.comp f)).map X.iso.hom ≫
    restrictScalars_comm_hom (s := s) (t := t) f g hcomm
      ((ModuleCat.extendScalars t).obj X.snd)

/-- The right comparison map from the second component to the common target, corresponding to the
element `m' ↦ 1 ⊗ m'`. -/
abbrev module_tensor_pullback_right_map
    (g : B' →+* R') (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj t).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g t).inv.app ((ModuleCat.extendScalars t).obj X.snd)

/-- Helper for Lemma 15.5.4: the `eqToIso` transport between equal restricted-scalar structures
acts as the identity on elements. -/
private theorem restrictScalars_eqToIso_hom_apply
    {u v : B' →+* R} (h : u = v) (M : ModuleCat R)
    (x : (ModuleCat.restrictScalars u).obj M) :
    ((eqToIso (congrArg (fun w ↦ (ModuleCat.restrictScalars w).obj M) h)).hom) x = x := by
  -- Reduce to the reflexive ring-map equality so the transport is definitionally the identity.
  cases h
  rfl

/-- Helper for Lemma 15.5.4: the restricted-scalar transport induced by the commuting square acts
as the identity on elements. -/
private theorem restrictScalars_comm_hom_apply
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (M : ModuleCat R)
    (x : (ModuleCat.restrictScalars (s.comp f)).obj M) :
    restrictScalars_comm_hom (s := s) (t := t) f g hcomm M x = x := by
  -- Rewrite the custom transport into the canonical `eqToIso` transport and evaluate it pointwise.
  simpa [restrictScalars_comm_hom] using
    restrictScalars_eqToIso_hom_apply (h := hcomm) M x

/-- Helper for Lemma 15.5.4: the inverse adjunction transpose evaluates on the standard tensor
generator by recovering the original restricted-scalar map. -/
private theorem extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul
    {A S : Type u} [CommRing A] [CommRing S] (q : A →+* S)
    (M : ModuleCat A) (N : ModuleCat S)
    (u : M ⟶ (ModuleCat.restrictScalars q).obj N) (x : M) :
    let _ : Algebra A S := q.toAlgebra
    (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) ((1 : S) ⊗ₜ[A] x) = u x := by
  let _ : Algebra A S := q.toAlgebra
  -- Apply the forward computation rule to the adjoint transpose and cancel the equivalence.
  have hu :
      ((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N)
          (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) = u := by
    exact Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N) u
  -- Evaluating the equality of morphisms at `x` exposes the desired generator formula.
  have hx := congrArg (fun k ↦ k x) hu
  exact
    (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
      (f := q)
      (M := M)
      (N := N)
      (φ := (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u))
      x).symm.trans hx

/-- Helper for Lemma 15.5.4: the left comparison map is the canonical generator map followed by the
structural isomorphism of the pullback object. -/
private theorem module_tensor_pullback_left_map_apply
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (X : PullbackModuleCat) (x : X.fst) :
    module_tensor_pullback_left_map f g hcomm X x =
      X.iso.hom ((1 : R) ⊗ₜ[B] x) := by
  let _ : Algebra B R := s.toAlgebra
  -- Unfold the left comparison map and collapse the commuting-square transport on elements.
  change
    restrictScalars_comm_hom (s := s) (t := t) f g hcomm
        ((ModuleCat.extendScalars t).obj X.snd)
        (X.iso.hom (((ModuleCat.extendRestrictScalarsAdj s).unit.app X.fst) x)) =
      X.iso.hom ((1 : R) ⊗ₜ[B] x)
  rw [restrictScalars_comm_hom_apply]
  rfl

/-- Helper for Lemma 15.5.4: the right comparison map sends `m'` to the generator `1 ⊗ m'`. -/
private theorem module_tensor_pullback_right_map_apply
    (g : B' →+* R') (X : PullbackModuleCat) (x : X.snd) :
    let _ : Algebra R' R := t.toAlgebra
    module_tensor_pullback_right_map g X x =
      (1 : R) ⊗ₜ[R'] x := by
  -- The right comparison map is definitionally the unit `m' ↦ 1 ⊗ m'`.
  let _ : Algebra R' R := t.toAlgebra
  rfl

/-- Helper for Lemma 15.5.4: the inverse comparison for iterated extension of scalars collapses a
pure tensor `r ⊗ (b ⊗ x)` to the corresponding tensor for the composite ring map. -/
private theorem extendScalarsComp_inv_app_tmul_tmul
    (f : B' →+* B) (s : B →+* R) (L' : ModuleCat B') (r : R) (b : B) (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R := (s.comp f).toAlgebra
    (ModuleCat.extendScalarsComp f s).inv.app L'
        (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) =
      (r * s b) ⊗ₜ[B'] x := by
  let _ : Algebra B R := s.toAlgebra
  let _ : Algebra B' B := f.toAlgebra
  let _ : Algebra B' R := (s.comp f).toAlgebra
  -- Compare after applying the forward comparison, whose action on pure tensors is the standard
  -- generator inclusion for iterated extension of scalars.
  apply (ModuleCat.mono_iff_injective ((ModuleCat.extendScalarsComp f s).hom.app L')).1
  infer_instance
  calc
    ((ModuleCat.extendScalarsComp f s).hom.app L')
        (((ModuleCat.extendScalarsComp f s).inv.app L') (r ⊗ₜ[B] (b ⊗ₜ[B'] x))) =
      r ⊗ₜ[B] (b ⊗ₜ[B'] x) := by
        simp
    _ = ((ModuleCat.extendScalarsComp f s).hom.app L') ((r * s b) ⊗ₜ[B'] x) := by
      -- Normalize the right-hand side through the tensor relation `r ⊗ (b • y) = (r * s b) ⊗ y`.
      change r ⊗ₜ[B] (b • ((1 : B) ⊗ₜ[B'] x)) =
        ((ModuleCat.extendScalarsComp f s).hom.app L') ((r * s b) ⊗ₜ[B'] x)
      rw [show b • ((1 : B) ⊗ₜ[B'] x) = b ⊗ₜ[B'] x by simp]
      rfl

/-- Helper for Lemma 15.5.4: the inverse of the extension-of-scalars comparison sends the nested
generator back to the single generator for the composite ring map. -/
private theorem extendScalarsComp_inv_app_nested_one_tmul
    (f : B' →+* B) (s : B →+* R) (L' : ModuleCat B') (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R := (s.comp f).toAlgebra
    (ModuleCat.extendScalarsComp f s).inv.app L'
        ((1 : R) ⊗ₜ[B] ((1 : B) ⊗ₜ[B'] x)) =
      (1 : R) ⊗ₜ[B'] x := by
  -- Specialize the pure-tensor normalization to the standard generator.
  simpa using extendScalarsComp_inv_app_tmul_tmul (f := f) (s := s) L' (1 : R) (1 : B) x

/-- Helper for Lemma 15.5.4: the structural isomorphism of the base-change object identifies the
two iterated generators coming from the commuting square of rings. -/
private theorem moduleCatBaseChangeSquare_iso_hom_app_tmul_tmul
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (r : R) (b : B) (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra R' R := t.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R' := g.toAlgebra
    ((moduleCatBaseChangeSquare s t f g hcomm).iso.hom.app L')
        (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) =
      (r * s b) • ((1 : R) ⊗ₜ[R'] ((1 : R') ⊗ₜ[B'] x)) := by
  let _ : Algebra B R := s.toAlgebra
  let _ : Algebra R' R := t.toAlgebra
  let _ : Algebra B' B := f.toAlgebra
  let _ : Algebra B' R' := g.toAlgebra
  let _ : Algebra B' R := (s.comp f).toAlgebra
  -- Route correction: unfold the owner square once so the computation runs through the two
  -- standard comparison isomorphisms and the commuting-square transport.
  dsimp [moduleCatBaseChangeSquare]
  calc
    ((ModuleCat.extendScalarsComp f s).inv.app L') (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) = (r * s b) ⊗ₜ[B'] x := by
      simpa using extendScalarsComp_inv_app_tmul_tmul (f := f) (s := s) L' r b x
    _ = (r * s b) • ((1 : R') ⊗ₜ[B'] x) := by
      simp [TensorProduct.smul_tmul']
    _ = (r * s b) •
          (((eqToIso (congrArg (fun u ↦ ModuleCat.extendScalars u) hcomm)).hom.app L')
            ((1 : R') ⊗ₜ[B'] x)) := by
          cases hcomm
          rfl
    _ = (r * s b) • ((1 : R) ⊗ₜ[R'] ((1 : R') ⊗ₜ[B'] x)) := by
          rfl

/-- Helper for Lemma 15.5.4: the structural isomorphism of the base-change object identifies the
two iterated generators coming from the commuting square of rings. -/
private theorem moduleCatBaseChangeSquare_iso_hom_app_nested_one_tmul
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra R' R := t.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R' := g.toAlgebra
    ((moduleCatBaseChangeSquare s t f g hcomm).iso.hom.app L')
        ((1 : R) ⊗ₜ[B] ((1 : B) ⊗ₜ[B'] x)) =
      (1 : R) ⊗ₜ[R'] ((1 : R') ⊗ₜ[B'] x) := by
  -- Specialize the owner-level pure-tensor computation to the standard generator.
  simpa using
    moduleCatBaseChangeSquare_iso_hom_app_tmul_tmul
      (s := s) (t := t) f g hcomm L' (1 : R) (1 : B) x

/-- Helper for Lemma 15.5.4: the structural isomorphism of the base-change object identifies the
two iterated generators coming from the commuting square of rings. -/
private theorem baseChange_iso_hom_app_nested_one_tmul
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra R' R := t.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R' := g.toAlgebra
    ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L').iso.hom
        ((1 : R) ⊗ₜ[B] ((1 : B) ⊗ₜ[B'] x)) =
      (1 : R) ⊗ₜ[R'] ((1 : R') ⊗ₜ[B'] x) := by
  -- The pullback-object structural isomorphism is the owner-square component.
  simpa [moduleCatBaseChangeToCategoricalPullback, moduleCatBaseChangeSquare] using
    moduleCatBaseChangeSquare_iso_hom_app_nested_one_tmul
      (s := s) (t := t) f g hcomm L' x

/-- Helper for Lemma 15.5.4: the base-change structural isomorphism sends a general generator
`r ⊗ (b ⊗ x)` to the normalized pure tensor `r • b • (1 ⊗ (1 ⊗ x))`. -/
private theorem baseChange_iso_hom_app_pure_tensor_normalized
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (r : R) (b : B) (x : L') :
    let _ : Algebra B R := s.toAlgebra
    let _ : Algebra R' R := t.toAlgebra
    let _ : Algebra B' B := f.toAlgebra
    let _ : Algebra B' R' := g.toAlgebra
    ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L').iso.hom
        (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) =
      (r * s b) • ((1 : R) ⊗ₜ[R'] ((1 : R') ⊗ₜ[B'] x)) := by
  -- Reuse the owner-level formula directly on the corresponding pullback object.
  simpa [moduleCatBaseChangeToCategoricalPullback, moduleCatBaseChangeSquare] using
    moduleCatBaseChangeSquare_iso_hom_app_tmul_tmul
      (s := s) (t := t) f g hcomm L' r b x

/-- Helper for Lemma 15.5.4: transposing a morphism from the base-change object along the two
extension-restriction adjunctions yields a compatible pair for the fibre-product kernel. -/
private theorem rightAdjoint_hom_equiv_to_commSq
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat)
    (a : (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L' ⟶ X) :
    CommSq
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
      (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
      (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X) := by
  let _ : Algebra B R := s.toAlgebra
  let _ : Algebra R' R := t.toAlgebra
  let _ : Algebra B' B := f.toAlgebra
  let _ : Algebra B' R' := g.toAlgebra
  -- Evaluate the pullback compatibility equation on the standard nested generator and then
  -- rewrite each component into the textbook pair of comparison maps.
  refine CommSq.mk ?_
  ext x
  have hx := congrArg
    (fun k ↦ k ((1 : R) ⊗ₜ[B] ((1 : B) ⊗ₜ[B'] x)))
    a.w
  simpa [Category.assoc, ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.ExtendScalars.map_tmul, module_tensor_pullback_left_map_apply,
    module_tensor_pullback_right_map_apply, baseChange_iso_hom_app_nested_one_tmul] using hx

/-- Helper for Lemma 15.5.4: the left comparison map is natural in the pullback-module variable. -/
private theorem module_tensor_pullback_left_map_natural
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {X Y : PullbackModuleCat} (φ : X ⟶ Y)
    (x : (ModuleCat.restrictScalars f).obj X.fst) :
    ((ModuleCat.extendScalars t).map φ.snd).hom
        (module_tensor_pullback_left_map f g hcomm X x) =
      module_tensor_pullback_left_map f g hcomm Y
        (((ModuleCat.restrictScalars f).map φ.fst) x) := by
  -- Evaluate the pullback compatibility `φ.w` on the generator `1 ⊗ x`.
  let _ : Algebra B R := s.toAlgebra
  let _ : Algebra R' R := t.toAlgebra
  have hx := congrArg
    (fun k ↦ ModuleCat.Hom.hom k ((1 : R) ⊗ₜ[B] x))
    φ.w
  rw [module_tensor_pullback_left_map_apply, module_tensor_pullback_left_map_apply]
  exact hx.symm.trans rfl

/-- Helper for Lemma 15.5.4: the right comparison map is natural in the pullback-module variable. -/
private theorem module_tensor_pullback_right_map_natural
    (g : B' →+* R') {X Y : PullbackModuleCat} (φ : X ⟶ Y)
    (x : (ModuleCat.restrictScalars g).obj X.snd) :
    ((ModuleCat.extendScalars t).map φ.snd).hom
        (module_tensor_pullback_right_map g X x) =
      module_tensor_pullback_right_map g Y
        (((ModuleCat.restrictScalars g).map φ.snd) x) := by
  -- After rewriting to tensor generators, naturality is definitional.
  let _ : Algebra R' R := t.toAlgebra
  rw [module_tensor_pullback_right_map_apply, module_tensor_pullback_right_map_apply]
  rfl

private abbrev rightAdjointLeftMap
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.fst ≫ module_tensor_pullback_left_map f g hcomm X

private abbrev rightAdjointRightMap
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.snd ≫ module_tensor_pullback_right_map g X

/-- Helper for Lemma 15.5.4: composing the ambient product lift with the left comparison map
recovers the left component followed by the left comparison. -/
private theorem rightAdjointLeftMap_comp_prod_lift
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'} {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd) :
    Limits.prod.lift u v ≫ rightAdjointLeftMap f g hcomm X =
      u ≫ module_tensor_pullback_left_map f g hcomm X := by
  -- The left projection of the ambient product lift is definitionally `u`.
  rw [rightAdjointLeftMap, ← Category.assoc, Limits.prod.lift_fst]

/-- Helper for Lemma 15.5.4: composing the ambient product lift with the right comparison map
recovers the right component followed by the right comparison. -/
private theorem rightAdjointRightMap_comp_prod_lift
    (f : B' →+* B) (g : B' →+* R')
    {L : ModuleCat B'} {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd) :
    Limits.prod.lift u v ≫ rightAdjointRightMap f g X =
      v ≫ module_tensor_pullback_right_map g X := by
  -- The right projection of the ambient product lift is definitionally `v`.
  rw [rightAdjointRightMap, ← Category.assoc, Limits.prod.lift_snd]

/-- The difference of the two comparison maps whose kernel is the fibre product module
`N ×_φ M'`. -/
private abbrev rightAdjointDifference
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  rightAdjointLeftMap f g hcomm X - rightAdjointRightMap f g X

/-- Helper for Lemma 15.5.4: expand the fibre-product difference map into its two ambient
comparison maps. -/
private theorem rightAdjointDifference_def
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointDifference f g hcomm X =
      rightAdjointLeftMap f g hcomm X - rightAdjointRightMap f g X := rfl

/-- Helper for Lemma 15.5.4: the ambient product objects assemble functorially over the pullback
module category. -/
private theorem rightAdjointSourceFunctor_map_id
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) :
    Limits.prod.map
        ((ModuleCat.restrictScalars f).map (𝟙 X.fst))
        ((ModuleCat.restrictScalars g).map (𝟙 X.snd)) =
      𝟙 (rightAdjointSourceObj f g X) := by
  -- The product map of identity morphisms is the identity on the ambient product.
  ext <;> simp

/-- Helper for Lemma 15.5.4: the ambient product functor preserves composition. -/
private theorem rightAdjointSourceFunctor_map_comp
    (f : B' →+* B) (g : B' →+* R')
    {X Y Z : PullbackModuleCat} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Limits.prod.map
        ((ModuleCat.restrictScalars f).map (φ.fst ≫ ψ.fst))
        ((ModuleCat.restrictScalars g).map (φ.snd ≫ ψ.snd)) =
      Limits.prod.map
          ((ModuleCat.restrictScalars f).map φ.fst)
          ((ModuleCat.restrictScalars g).map φ.snd) ≫
        Limits.prod.map
          ((ModuleCat.restrictScalars f).map ψ.fst)
          ((ModuleCat.restrictScalars g).map ψ.snd) := by
  -- Check equality after both product projections.
  ext <;> simp

/-- Helper for Lemma 15.5.4: the ambient product objects form a functor. -/
private def rightAdjointSourceFunctor
    (f : B' →+* B) (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B' where
  obj X := rightAdjointSourceObj f g X
  map φ := Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
    ((ModuleCat.restrictScalars g).map φ.snd)
  map_id X := rightAdjointSourceFunctor_map_id f g X
  map_comp φ ψ := rightAdjointSourceFunctor_map_comp f g φ ψ

/-- Helper for Lemma 15.5.4: the common targets of the comparison maps assemble functorially. -/
private theorem rightAdjointTargetFunctor_map_id
    (g : B' →+* R') (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars (t.comp g)).map
        ((ModuleCat.extendScalars t).map (𝟙 X.snd)) =
      𝟙 (rightAdjointTargetObj g X) := by
  -- Restriction of scalars preserves the identity morphism.
  simp

/-- Helper for Lemma 15.5.4: the common target functor preserves composition. -/
private theorem rightAdjointTargetFunctor_map_comp
    (g : B' →+* R') {X Y Z : PullbackModuleCat} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (ModuleCat.restrictScalars (t.comp g)).map
        ((ModuleCat.extendScalars t).map (φ.snd ≫ ψ.snd)) =
      (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map φ.snd) ≫
        (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map ψ.snd) := by
  -- This is functoriality of the composite restriction-then-extension map.
  simp

/-- Helper for Lemma 15.5.4: the common targets form a functor. -/
private def rightAdjointTargetFunctor
    (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B' where
  obj X := rightAdjointTargetObj g X
  map φ := (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map φ.snd)
  map_id X := rightAdjointTargetFunctor_map_id g X
  map_comp φ ψ := rightAdjointTargetFunctor_map_comp g φ ψ

/-- Helper for Lemma 15.5.4: the defining difference maps are natural in the pullback-module
variable. -/
private theorem rightAdjointDifference_naturality
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {X Y : PullbackModuleCat} (φ : X ⟶ Y) :
    (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointDifference f g hcomm Y =
      rightAdjointDifference f g hcomm X ≫ (rightAdjointTargetFunctor g).map φ := by
  have hleft :
      (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointLeftMap f g hcomm Y =
        rightAdjointLeftMap f g hcomm X ≫ (rightAdjointTargetFunctor g).map φ := by
    ext z
    simpa [rightAdjointLeftMap, rightAdjointSourceFunctor, rightAdjointTargetFunctor] using
      (module_tensor_pullback_left_map_natural (s := s) (t := t) f g hcomm φ
        ((Limits.prod.fst : rightAdjointSourceObj f g X ⟶
          (ModuleCat.restrictScalars f).obj X.fst) z)).symm
  have hright :
      (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointRightMap f g Y =
        rightAdjointRightMap f g X ≫ (rightAdjointTargetFunctor g).map φ := by
    ext z
    simpa [rightAdjointRightMap, rightAdjointSourceFunctor, rightAdjointTargetFunctor] using
      (module_tensor_pullback_right_map_natural (t := t) g φ
        ((Limits.prod.snd : rightAdjointSourceObj f g X ⟶
          (ModuleCat.restrictScalars g).obj X.snd) z)).symm
  -- Compare the left and right components separately before subtracting them.
  calc
    (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointDifference f g hcomm Y =
      (rightAdjointSourceFunctor f g).map φ ≫
        (rightAdjointLeftMap f g hcomm Y - rightAdjointRightMap f g Y) := by
          rw [rightAdjointDifference_def]
    _ =
        (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointLeftMap f g hcomm Y -
          (rightAdjointSourceFunctor f g).map φ ≫ rightAdjointRightMap f g Y := by
            exact Preadditive.comp_sub _ _ _
    _ =
        rightAdjointLeftMap f g hcomm X ≫ (rightAdjointTargetFunctor g).map φ -
          rightAdjointRightMap f g X ≫ (rightAdjointTargetFunctor g).map φ := by
            rw [hleft, hright]
    _ =
        (rightAdjointLeftMap f g hcomm X - rightAdjointRightMap f g X) ≫
          (rightAdjointTargetFunctor g).map φ := by
            symm
            exact Preadditive.sub_comp _ _ _
    _ = rightAdjointDifference f g hcomm X ≫ (rightAdjointTargetFunctor g).map φ := by
          rfl

/-- Helper for Lemma 15.5.4: the difference maps form a natural transformation. -/
private def rightAdjointDifferenceNatTrans
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    rightAdjointSourceFunctor f g ⟶ rightAdjointTargetFunctor g :=
  { app := fun X ↦ rightAdjointDifference f g hcomm X
    naturality := fun {X Y} φ ↦ rightAdjointDifference_naturality (s := s) (t := t) f g hcomm φ }

/-- Helper for Lemma 15.5.4: package the ambient product and difference map as an arrow-valued
functor so that pointwise kernels recover the fibre-product modules. -/
private def rightAdjointArrow
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    PullbackModuleCat ⥤ Arrow (ModuleCat B') where
  obj X := Arrow.mk ((rightAdjointDifferenceNatTrans f g hcomm).app X)
  map {X Y} φ :=
    Arrow.homMk'
      ((rightAdjointSourceFunctor f g).map φ)
      ((rightAdjointTargetFunctor g).map φ)
      ((rightAdjointDifferenceNatTrans f g hcomm).naturality φ)

/-- The explicit right adjoint to the module tensor pullback functor, sending a pullback object
`(N, M', φ)` to the fibre product module `N ×_φ M'`. -/
abbrev module_tensor_pullback_right_adjoint
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    PullbackModuleCat ⥤ ModuleCat B' :=
  rightAdjointArrow f g hcomm ⋙ Limits.ker (ModuleCat B')

/-- Helper for Lemma 15.5.4: a compatible pair of maps into the two pullback components equalizes
the defining difference map. -/
private theorem rightAdjointLift_condition
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'} {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    Limits.prod.lift u v ≫ rightAdjointDifference f g hcomm X = 0 := by
  -- The compatibility square says that the two components agree in the common target.
  rw [rightAdjointDifference, Preadditive.comp_sub, sub_eq_zero]
  calc
    Limits.prod.lift u v ≫ rightAdjointLeftMap f g hcomm X =
        u ≫ module_tensor_pullback_left_map f g hcomm X := by
          exact rightAdjointLeftMap_comp_prod_lift f g hcomm u v
    _ = v ≫ module_tensor_pullback_right_map g X := by
          simpa using hcompat.w
    _ = Limits.prod.lift u v ≫ rightAdjointRightMap f g X := by
          symm
          exact rightAdjointRightMap_comp_prod_lift f g u v

/-- The universal morphism into the fibre-product module `N ×_φ M'` attached to a compatible pair
of maps into `N` and `M'`. -/
abbrev module_tensor_pullback_right_adjoint_lift
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    L ⟶ kernel (rightAdjointDifference f g hcomm X) :=
  kernel.lift
    (rightAdjointDifference f g hcomm X)
    (Limits.prod.lift u v)
    (rightAdjointLift_condition f g hcomm u v hcompat)

/-- Helper for Lemma 15.5.4: a morphism into the kernel model yields a compatible pair of maps to
the two pullback components. -/
private theorem kernel_hom_to_commSq
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'} {X : PullbackModuleCat}
    (k : L ⟶ kernel (rightAdjointDifference f g hcomm X)) :
    CommSq
      (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst)
      (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd)
      (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X) := by
  -- Compose the kernel equation with `k` and split the difference map into its two projections.
  refine CommSq.mk ?_
  have hk :
      k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫
        rightAdjointDifference f g hcomm X = 0 := by
    simpa [Category.assoc] using
      congrArg
        (fun m ↦ k ≫ m)
        (kernel.condition (rightAdjointDifference f g hcomm X))
  rw [rightAdjointDifference, Category.assoc, Preadditive.comp_sub, sub_eq_zero] at hk
  simpa [rightAdjointLeftMap, rightAdjointRightMap, Category.assoc] using hk

/-- Helper for Lemma 15.5.4: the inverse adjunction transpose sends a pure tensor `a ⊗ x` to the
scalar multiple `a • u x`. -/
private theorem extendRestrictScalarsAdj_homEquiv_symm_apply_tmul
    {A S : Type u} [CommRing A] [CommRing S] (q : A →+* S)
    (M : ModuleCat A) (N : ModuleCat S)
    (u : M ⟶ (ModuleCat.restrictScalars q).obj N) (a : S) (x : M) :
    let _ : Algebra A S := q.toAlgebra
    (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) (a ⊗ₜ[A] x) = a • u x := by
  let _ : Algebra A S := q.toAlgebra
  -- Rewrite the pure tensor as a scalar multiple of the standard generator `1 ⊗ x`.
  calc
    (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) (a ⊗ₜ[A] x) =
      (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) (a • ((1 : S) ⊗ₜ[A] x)) := by
        simp [TensorProduct.smul_tmul', one_smul]
    _ = a • (((ModuleCat.extendRestrictScalarsAdj q).homEquiv M N).symm u) ((1 : S) ⊗ₜ[A] x) := by
        rw [map_smul]
    _ = a • u x := by
        rw [extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul]

/-- Helper for Lemma 15.5.4: the counit of extension-restriction of scalars sends a pure tensor
`a ⊗ x` to the scalar multiple `a • x`. -/
private theorem extendRestrictScalarsAdj_counit_app_apply_tmul
    {A S : Type u} [CommRing A] [CommRing S] (q : A →+* S)
    (N : ModuleCat S) (a : S) (x : N) :
    let _ : Algebra A S := q.toAlgebra
    ((ModuleCat.extendRestrictScalarsAdj q).counit.app N) (a ⊗ₜ[A] x) = a • x := by
  let _ : Algebra A S := q.toAlgebra
  -- The counit is the adjoint transpose of the identity map on the `S`-module `N`.
  simpa using
    (extendRestrictScalarsAdj_homEquiv_symm_apply_tmul (q := q)
      ((ModuleCat.restrictScalars q).obj N) N (𝟙 _) a x)

/-- Helper for Lemma 15.5.4: transposing a compatible pair across the two extension-restriction
adjunctions satisfies the pullback compatibility square. -/
private theorem compatible_pair_to_pullback_hom_w
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L' : ModuleCat B'} {X : PullbackModuleCat}
    (u : L' ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L' ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    (ModuleCat.extendScalars s).map (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm u) ≫
        X.iso.hom =
      ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L').iso.hom ≫
        (ModuleCat.extendScalars t).map (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm v) := by
  let _ : Algebra B R := s.toAlgebra
  let _ : Algebra R' R := t.toAlgebra
  let _ : Algebra B' B := f.toAlgebra
  let _ : Algebra B' R' := g.toAlgebra
  let u' := (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm u)
  let v' := (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm v)
  -- Compare the two maps on tensor generators `r ⊗ (b ⊗ x)`.
  ext r
  intro y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · -- Both maps are linear, so they vanish on the zero generator.
    simp [u', v']
  · -- Additivity in the inner tensor factor is automatic from linearity.
    intro y₁ y₂ hy₁ hy₂
    simp [hy₁, hy₂, u', v']
  · -- The pure inner tensor case is exactly the textbook compatibility rewritten on generators.
    intro b x
    have hx : X.iso.hom ((1 : R) ⊗ₜ[B] (u x)) = (1 : R) ⊗ₜ[R'] (v x) := by
      -- Evaluate the original compatibility square on `x`.
      have hx0 := congrArg (fun k ↦ k x) hcompat.w
      simpa [module_tensor_pullback_left_map_apply, module_tensor_pullback_right_map_apply] using hx0
    calc
      (((ModuleCat.extendScalars s).map u') ≫ X.iso.hom) (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) =
        X.iso.hom (r ⊗ₜ[B] (b • u x)) := by
          rw [ModuleCat.ExtendScalars.map_tmul, extendRestrictScalarsAdj_homEquiv_symm_apply_tmul]
      _ = r • X.iso.hom ((1 : R) ⊗ₜ[B] (b • u x)) := by
          rw [show r ⊗ₜ[B] (b • u x) = r • ((1 : R) ⊗ₜ[B] (b • u x)) by
            simp [TensorProduct.smul_tmul', one_smul]]
          rw [map_smul]
      _ = r • ((s b) • X.iso.hom ((1 : R) ⊗ₜ[B] (u x))) := by
          rw [show (1 : R) ⊗ₜ[B] (b • u x) = (s b) • ((1 : R) ⊗ₜ[B] (u x)) by
            simp [TensorProduct.tmul_smul]]
          rw [map_smul]
      _ = (r * s b) • ((1 : R) ⊗ₜ[R'] (v x)) := by
          rw [hx]
          simp [smul_smul, mul_assoc]
      _ = ((((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L').iso.hom) ≫
            (ModuleCat.extendScalars t).map v') (r ⊗ₜ[B] (b ⊗ₜ[B'] x)) := by
          rw [baseChange_iso_hom_app_pure_tensor_normalized, map_smul,
            ModuleCat.ExtendScalars.map_tmul, extendRestrictScalarsAdj_homEquiv_symm_apply_tmul]

/-- Helper for Lemma 15.5.4: a compatible pair of restricted-scalar maps defines a morphism from
the base-change object to the pullback object. -/
private abbrev compatible_pair_to_pullback_hom
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L' : ModuleCat B'} {X : PullbackModuleCat}
    (u : L' ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L' ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L' ⟶ X :=
  CategoricalPullback.Hom.mk
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm u)
    (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm v)
    (compatible_pair_to_pullback_hom_w (s := s) (t := t) f g hcomm u v hcompat)

/-- Helper for Lemma 15.5.4: composing the universal kernel lift with the kernel inclusion
recovers the ambient product map `Limits.prod.lift u v`. -/
private theorem module_tensor_pullback_right_adjoint_lift_ι
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'} {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    module_tensor_pullback_right_adjoint_lift f g hcomm u v hcompat ≫
        kernel.ι (rightAdjointDifference f g hcomm X) =
      Limits.prod.lift u v := by
  -- This is the defining equation of `kernel.lift`.
  simpa [module_tensor_pullback_right_adjoint_lift] using
    kernel.lift_ι
      (rightAdjointDifference f g hcomm X)
      (Limits.prod.lift u v)
      (rightAdjointLift_condition (s := s) (t := t) f g hcomm u v hcompat)

/-- Helper for Lemma 15.5.4: after composing the right-adjoint map with the kernel inclusion, one
recovers the evident map on the ambient product modules. -/
private theorem module_tensor_pullback_right_adjoint_map_comp_kernel_iota
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {X Y : PullbackModuleCat} (φ : X ⟶ Y) :
    (module_tensor_pullback_right_adjoint f g hcomm).map φ ≫
        kernel.ι (rightAdjointDifference f g hcomm Y) =
      kernel.ι (rightAdjointDifference f g hcomm X) ≫
        (rightAdjointSourceFunctor f g).map φ := by
  -- Route correction: unfold the kernel functor map once so the goal reduces to `kernel.lift_ι`.
  dsimp [module_tensor_pullback_right_adjoint, rightAdjointArrow, rightAdjointDifferenceNatTrans,
    rightAdjointDifference, rightAdjointLeftMap, rightAdjointRightMap, kernel.map]
  exact kernel.lift_ι _ _ _

/-- Helper for Lemma 15.5.4: the forward direction of the Hom equivalence sends a pullback
morphism to the kernel lift of its compatible pair of components. -/
private abbrev module_tensor_pullback_homEquiv_toFun
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat) :
    (((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L') ⟶ X) →
      (L' ⟶ kernel (rightAdjointDifference f g hcomm X)) :=
  fun a ↦
    module_tensor_pullback_right_adjoint_lift f g hcomm
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
      (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
      (rightAdjoint_hom_equiv_to_commSq (s := s) (t := t) f g hcomm L' X a)

/-- Helper for Lemma 15.5.4: the inverse direction of the Hom equivalence reconstructs a pullback
morphism from the compatible pair extracted from the kernel model. -/
private abbrev module_tensor_pullback_homEquiv_invFun
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat) :
    (L' ⟶ kernel (rightAdjointDifference f g hcomm X)) →
      (((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L') ⟶ X) :=
  fun k ↦
    compatible_pair_to_pullback_hom (s := s) (t := t) f g hcomm
      (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst)
      (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd)
      (kernel_hom_to_commSq (s := s) (t := t) f g hcomm k)

/-- Helper for Lemma 15.5.4: reconstructing a pullback morphism from the kernel lift of its
components returns the original morphism. -/
private theorem module_tensor_pullback_homEquiv_left_inv
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat)
    (a : ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L') ⟶ X) :
    module_tensor_pullback_homEquiv_invFun (s := s) (t := t) f g hcomm L' X
        (module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X a) =
      a := by
  -- Compare the two pullback morphisms on the two structural components.
  apply CategoricalPullback.Hom.ext
  · apply (Equiv.injective ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _))
    rw [Equiv.apply_symm_apply]
    calc
      module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X a ≫
          kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst =
        Limits.prod.lift
            (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
            (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd) ≫
          Limits.prod.fst := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦ m ≫ Limits.prod.fst)
                (module_tensor_pullback_right_adjoint_lift_ι (s := s) (t := t) f g hcomm
                  (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
                  (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
                  (rightAdjoint_hom_equiv_to_commSq (s := s) (t := t) f g hcomm L' X a))
      _ = ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst := by
            rw [Limits.prod.lift_fst]
  · apply (Equiv.injective ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _))
    rw [Equiv.apply_symm_apply]
    calc
      module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X a ≫
          kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd =
        Limits.prod.lift
            (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
            (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd) ≫
          Limits.prod.snd := by
            simpa [Category.assoc] using
              congrArg
                (fun m ↦ m ≫ Limits.prod.snd)
                (module_tensor_pullback_right_adjoint_lift_ι (s := s) (t := t) f g hcomm
                  (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
                  (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
                  (rightAdjoint_hom_equiv_to_commSq (s := s) (t := t) f g hcomm L' X a))
      _ = ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd := by
            rw [Limits.prod.lift_snd]

/-- Helper for Lemma 15.5.4: taking the kernel lift of the compatible pair extracted from a kernel
morphism returns that original kernel morphism. -/
private theorem module_tensor_pullback_homEquiv_right_inv
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat)
    (k : L' ⟶ kernel (rightAdjointDifference f g hcomm X)) :
    module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X
        (module_tensor_pullback_homEquiv_invFun (s := s) (t := t) f g hcomm L' X k) =
      k := by
  -- Postcompose with the kernel inclusion and compare the two induced ambient product maps.
  apply (cancel_mono (kernel.ι (rightAdjointDifference f g hcomm X))).1
  calc
    module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X
        (module_tensor_pullback_homEquiv_invFun (s := s) (t := t) f g hcomm L' X k) ≫
          kernel.ι (rightAdjointDifference f g hcomm X) =
      Limits.prod.lift
          (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst)
          (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd) := by
            rw [module_tensor_pullback_right_adjoint_lift_ι (s := s) (t := t) f g hcomm]
    _ = k ≫ kernel.ι (rightAdjointDifference f g hcomm X) := by
          apply Limits.prod.hom_ext
          · simp [Category.assoc]
          · simp [Category.assoc]

/-- Helper for Lemma 15.5.4: the textbook bijection between pullback morphisms and morphisms into
the kernel model of the fibre-product module. -/
private abbrev module_tensor_pullback_homEquiv
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat) :
    (((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L') ⟶ X) ≃
      (L' ⟶ kernel (rightAdjointDifference f g hcomm X)) :=
  { toFun := module_tensor_pullback_homEquiv_toFun (s := s) (t := t) f g hcomm L' X
    invFun := module_tensor_pullback_homEquiv_invFun (s := s) (t := t) f g hcomm L' X
    left_inv := module_tensor_pullback_homEquiv_left_inv (s := s) (t := t) f g hcomm L' X
    right_inv := module_tensor_pullback_homEquiv_right_inv (s := s) (t := t) f g hcomm L' X }

/-- Helper for Lemma 15.5.4: the inverse direction of the Hom equivalence is natural in the
module variable on the left. -/
private theorem module_tensor_pullback_homEquiv_naturality_left_symm
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L₁ L₂ : ModuleCat B'} {X : PullbackModuleCat}
    (α : L₁ ⟶ L₂)
    (k : L₂ ⟶ kernel (rightAdjointDifference f g hcomm X)) :
    (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L₁ X).symm (α ≫ k) =
      (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).map α ≫
        (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L₂ X).symm k := by
  -- Compare the two pullback morphisms on their `B`- and `R'`-components.
  apply CategoricalPullback.Hom.ext
  · -- The first component is exactly left naturality for `extendRestrictScalarsAdj f`.
    simpa [module_tensor_pullback_homEquiv_invFun, compatible_pair_to_pullback_hom,
      Category.assoc] using
      (Adjunction.homEquiv_naturality_left_symm (ModuleCat.extendRestrictScalarsAdj f) α
        (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst))
  · -- The second component is the same argument for `extendRestrictScalarsAdj g`.
    simpa [module_tensor_pullback_homEquiv_invFun, compatible_pair_to_pullback_hom,
      Category.assoc] using
      (Adjunction.homEquiv_naturality_left_symm (ModuleCat.extendRestrictScalarsAdj g) α
        (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd))

/-- Helper for Lemma 15.5.4: the inverse direction of the Hom equivalence is natural in the
pullback-object variable on the right. -/
private theorem module_tensor_pullback_homEquiv_naturality_right_symm
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L' : ModuleCat B'} {X Y : PullbackModuleCat}
    (k : L' ⟶ kernel (rightAdjointDifference f g hcomm X))
    (β : X ⟶ Y) :
    (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' Y).symm
        (k ≫ (module_tensor_pullback_right_adjoint f g hcomm).map β) =
      (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' X).symm k ≫ β := by
  -- Route correction: rewrite the kernel morphism immediately so each component becomes a standard
  -- right naturality statement for one extension/restriction adjunction.
  apply CategoricalPullback.Hom.ext
  · -- The `B`-component reduces to `homEquiv_naturality_right_symm` for `f`.
    rw [module_tensor_pullback_right_adjoint_map_comp_kernel_iota (s := s) (t := t) f g hcomm β]
    simp only [module_tensor_pullback_homEquiv_invFun, compatible_pair_to_pullback_hom,
      rightAdjointSourceFunctor, Category.assoc]
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_right_symm (ModuleCat.extendRestrictScalarsAdj f)
        (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.fst) β.fst)
  · -- The `R'`-component is the analogous naturality statement for `g`.
    rw [module_tensor_pullback_right_adjoint_map_comp_kernel_iota (s := s) (t := t) f g hcomm β]
    simp only [module_tensor_pullback_homEquiv_invFun, compatible_pair_to_pullback_hom,
      rightAdjointSourceFunctor, Category.assoc]
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_right_symm (ModuleCat.extendRestrictScalarsAdj g)
        (k ≫ kernel.ι (rightAdjointDifference f g hcomm X) ≫ Limits.prod.snd) β.snd)

/-- Helper for Lemma 15.5.4: the forward direction of the Hom equivalence is natural in the
pullback-object variable on the right. -/
private theorem module_tensor_pullback_homEquiv_naturality_right
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L' : ModuleCat B'} {X Y : PullbackModuleCat}
    (ψ : ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L') ⟶ X)
    (β : X ⟶ Y) :
    (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' Y) (ψ ≫ β) =
      (module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' X) ψ ≫
        (module_tensor_pullback_right_adjoint f g hcomm).map β := by
  -- Apply the inverse equivalence at `Y` so the statement becomes the symmetric naturality
  -- statement already proved above.
  apply ((module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' Y).symm).injective
  rw [Equiv.symm_apply_apply]
  rw [module_tensor_pullback_homEquiv_naturality_right_symm (s := s) (t := t) f g hcomm
    ((module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm L' X) ψ) β]
  rw [Equiv.symm_apply_apply]

/-- Lemma 15.5.4: the base-change functor
`Mod_{B'} → Mod_B ×[Mod_R] Mod_{R'}`
is left adjoint to the fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. -/
@[stacks 0D2F]
def module_tensor_pullback_adjunction
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    moduleCatBaseChangeToCategoricalPullback s t f g hcomm ⊣
      module_tensor_pullback_right_adjoint f g hcomm :=
  Adjunction.mkOfHomEquiv
    { homEquiv := module_tensor_pullback_homEquiv (s := s) (t := t) f g hcomm
      homEquiv_naturality_left_symm :=
        module_tensor_pullback_homEquiv_naturality_left_symm (s := s) (t := t) f g hcomm
      homEquiv_naturality_right :=
        module_tensor_pullback_homEquiv_naturality_right (s := s) (t := t) f g hcomm }

instance : (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).IsLeftAdjoint :=
  (module_tensor_pullback_adjunction (s := s) (t := t) f g hcomm).isLeftAdjoint

instance : (module_tensor_pullback_right_adjoint f g hcomm).IsRightAdjoint :=
  (module_tensor_pullback_adjunction (s := s) (t := t) f g hcomm).isRightAdjoint

end
