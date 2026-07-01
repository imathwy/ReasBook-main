import Mathlib
import stacks_project.Chap15.«15_6_3_1»

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

/-- The left comparison map from the first component to the common target, obtained from the unit of
extension-restriction of scalars and the structural isomorphism in the categorical pullback. -/
abbrev module_tensor_pullback_left_map
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj s).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f s).inv.app ((ModuleCat.extendScalars s).obj X.fst) ≫
    (ModuleCat.restrictScalars (s.comp f)).map X.iso.hom ≫
    (eqToIso (congrArg
      (fun u ↦ (ModuleCat.restrictScalars u).obj ((ModuleCat.extendScalars t).obj X.snd))
      hcomm)).hom

/-- The right comparison map from the second component to the common target, corresponding to the
element `m' ↦ 1 ⊗ m'`. -/
abbrev module_tensor_pullback_right_map
    (g : B' →+* R') (X : PullbackModuleCat) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd) :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj t).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g t).inv.app ((ModuleCat.extendScalars t).obj X.snd)

private abbrev rightAdjointLeftMap
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.fst ≫ module_tensor_pullback_left_map f g hcomm X

private abbrev rightAdjointRightMap
    (f : B' →+* B) (g : B' →+* R') (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  Limits.prod.snd ≫ module_tensor_pullback_right_map g X

/-- The difference of the two comparison maps whose kernel is the fibre product module
`N ×_φ M'`. -/
private abbrev rightAdjointDifference
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) (X : PullbackModuleCat) :
    rightAdjointSourceObj f g X ⟶ rightAdjointTargetObj g X :=
  rightAdjointLeftMap f g hcomm X - rightAdjointRightMap f g X

/-- The ambient product modules assemble functorially over the categorical pullback. -/
private def rightAdjointSourceFunctor
    (f : B' →+* B) (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B'
    where
  obj X := rightAdjointSourceObj f g X
  map φ := Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
    ((ModuleCat.restrictScalars g).map φ.snd)
  map_id X := by
    ext <;> simp
  map_comp φ ψ := by
    ext <;> simp

/-- The common targets assemble functorially over the categorical pullback. -/
private def rightAdjointTargetFunctor
    (g : B' →+* R') : PullbackModuleCat ⥤ ModuleCat B'
    where
  obj X := rightAdjointTargetObj g X
  map φ := (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map φ.snd)
  map_id X := by
    simp
  map_comp φ ψ := by
    simp

-- Proof sketch: expand the two comparison morphisms on both sides. Naturality of the adjunction
-- unit, of `restrictScalarsComp`, and of the structural morphism `φ.w` in the categorical pullback
-- gives commutativity for the left and right comparison maps separately; subtract the two resulting
-- identities.
/-- Compatibility of the defining difference morphism with morphisms in the categorical pullback of
module categories. -/
private theorem rightAdjointDifference_naturality
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {X Y : PullbackModuleCat}
    (φ : X ⟶ Y) :
    (rightAdjointSourceFunctor f g).map φ ≫
      rightAdjointDifference f g hcomm Y =
    rightAdjointDifference f g hcomm X ≫
      (rightAdjointTargetFunctor g).map φ := sorry

/-- The defining difference maps form a natural transformation on the categorical pullback. -/
private def rightAdjointDifferenceNatTrans
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :=
  let T : PullbackModuleCat ⥤ ModuleCat B' := rightAdjointTargetFunctor g
  show rightAdjointSourceFunctor f g ⟶ T from
    { app := fun X ↦ rightAdjointDifference f g hcomm X
      naturality := by
        intro X Y φ
        exact rightAdjointDifference_naturality f g hcomm φ }

/-- The canonical `Arrow (ModuleCat B')`-valued functor whose pointwise kernels are the
fibre-product modules attached to objects of the categorical pullback. -/
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


-- Proof sketch: compose the given pair of maps into the ambient product module. The compatibility
-- hypothesis is precisely the condition that this product morphism equalizes the two comparison
-- maps, hence annihilates their difference; the universal property of the kernel then produces the
-- desired map into the fibre-product module.
private theorem rightAdjointLift_condition
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat B'}
    {X : PullbackModuleCat}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (module_tensor_pullback_left_map f g hcomm X)
      (module_tensor_pullback_right_map g X)) :
    Limits.prod.lift u v ≫ rightAdjointDifference f g hcomm X = 0 := by
  rw [rightAdjointDifference, Preadditive.comp_sub, sub_eq_zero]
  calc
    Limits.prod.lift u v ≫ rightAdjointLeftMap f g hcomm X =
        u ≫ module_tensor_pullback_left_map f g hcomm X := by
          rw [rightAdjointLeftMap, ← Category.assoc, Limits.prod.lift_fst]
    _ = v ≫ module_tensor_pullback_right_map g X := by
          simpa using hcompat.w
    _ = Limits.prod.lift u v ≫ rightAdjointRightMap f g X := by
          symm
          rw [rightAdjointRightMap, ← Category.assoc, Limits.prod.lift_snd]

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
    L ⟶ (module_tensor_pullback_right_adjoint f g hcomm).obj X :=
  kernel.lift
    (rightAdjointDifference f g hcomm X)
    (Limits.prod.lift u v)
    (rightAdjointLift_condition f g hcomm u v hcompat)

-- Proof sketch: for `L' : ModuleCat B'` and `X = (N, M', φ)` in the categorical pullback, use the
-- adjunctions `extendScalars ⊣ restrictScalars` for `f`, `g`, and `t`, together with the kernel
-- description of `module_tensor_pullback_fiber_product`, to identify morphisms
-- `L' ⟶ N ×_φ M'` with pairs of morphisms to `N` and `M'` satisfying the pullback compatibility.
-- This is exactly the hom-set description of maps from
-- `(moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L'` to `X`.
private def rightAdjointHomEquiv
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L' : ModuleCat B') (X : PullbackModuleCat) :
    ((moduleCatBaseChangeToCategoricalPullback s t f g hcomm).obj L' ⟶ X) ≃
      (L' ⟶ kernel (rightAdjointDifference f g hcomm X)) where
  toFun φ :=
    let u : L' ⟶ (ModuleCat.restrictScalars f).obj X.fst :=
        (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _
          (by simpa using φ.fst)
    let v : L' ⟶ (ModuleCat.restrictScalars g).obj X.snd :=
      (ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _
        (by simpa using φ.snd)
    module_tensor_pullback_right_adjoint_lift f g hcomm u v (by
      sorry)
  invFun ψ :=
    { fst :=
        (by
          simpa using
            ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
              (ψ ≫
                kernel.ι (rightAdjointDifference f g hcomm X) ≫
                Limits.prod.fst))
      snd :=
        (by
          simpa using
            ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm
              (ψ ≫
                kernel.ι (rightAdjointDifference f g hcomm X) ≫
                Limits.prod.snd))
      w := by
        sorry }
  left_inv φ := by
    ext <;> sorry
  right_inv ψ := by
    sorry

/-- Lemma 15.5.4: the base-change functor
`Mod_{B'} → Mod_B ×[Mod_R] Mod_{R'}`
is left adjoint to the fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. -/
def module_tensor_pullback_adjunction
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    moduleCatBaseChangeToCategoricalPullback s t f g hcomm ⊣
      module_tensor_pullback_right_adjoint f g hcomm :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun L' X ↦ by
        simpa [module_tensor_pullback_right_adjoint] using
          rightAdjointHomEquiv f g hcomm L' X
      homEquiv_naturality_left_symm := by
        intro L₁ L₂ X a b
        sorry
      homEquiv_naturality_right := by
        intro L' X Y a b
        sorry }

/-- The counit of `module_tensor_pullback_adjunction` is an isomorphism, so the composite from the
categorical pullback back to itself through the fibre-product module functor and base change is the
identity functor up to canonical isomorphism. -/
theorem module_tensor_pullback_adjunction_counit_isIso
    (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    IsIso
      ((module_tensor_pullback_adjunction f g hcomm).counit :
        module_tensor_pullback_right_adjoint f g hcomm ⋙
            moduleCatBaseChangeToCategoricalPullback s t f g hcomm ⟶
          𝟭 PullbackModuleCat) := sorry

instance : (moduleCatBaseChangeToCategoricalPullback s t f g hcomm).IsLeftAdjoint :=
  (module_tensor_pullback_adjunction f g hcomm).isLeftAdjoint

instance : (module_tensor_pullback_right_adjoint f g hcomm).IsRightAdjoint :=
  (module_tensor_pullback_adjunction f g hcomm).isRightAdjoint

end
