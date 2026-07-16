import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_131_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Ring.DirectLimit
open Lemma_10_131_5

universe u

noncomputable section

section

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-- Helper for Chap10 Lemma 10 131 5: transport across equal composed extension-of-scalars
objects preserves the unit tensor before the composition isomorphism. -/
private theorem extendScalarsComp_transport_unit_app
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (k : A →+* C)
    (hk : g.comp f = k) (M : ModuleCat A)
    (hobj : (ModuleCat.extendScalars k).obj M = (ModuleCat.extendScalars (g.comp f)).obj M)
    (m : M) :
    ((eqToHom hobj ≫ (ModuleCat.extendScalarsComp f g).hom.app M).hom
      (((ModuleCat.extendRestrictScalarsAdj k).unit.app M) m)) =
    (((ModuleCat.extendRestrictScalarsAdj g).unit.app ((ModuleCat.extendScalars f).obj M))
      (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m)) := by
  -- Replace the auxiliary map `k` by the composite and remove the object transport.
  cases hk
  cases hobj
  rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  simp only [eqToHom_refl, ModuleCat.id_apply]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  erw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rfl

/-- Helper for Chap10 Lemma 10 131 5: extending a linear map carries iterated unit tensors to
the unit tensor of its value. -/
private theorem extendScalars_map_unit_unit_app
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) {M : ModuleCat A} {N : ModuleCat B}
    (φ : (ModuleCat.extendScalars f).obj M ⟶ N) (m : M) :
    ((ModuleCat.extendScalars g).map φ).hom
      (((ModuleCat.extendRestrictScalarsAdj g).unit.app ((ModuleCat.extendScalars f).obj M))
        (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m)) =
    (((ModuleCat.extendRestrictScalarsAdj g).unit.app N)
      (φ.hom (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m))) := by
  -- Expand the source-side adjunction units and evaluate the extension-of-scalars functor on a
  -- pure tensor.
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  erw [ModuleCat.ExtendScalars.map_tmul]

/-- Helper for Chap10 Lemma 10 131 5: after removing the equality transport, the composed
extension-of-scalars map sends a unit tensor to the unit tensor of the transitioned value. -/
private theorem extendScalarsComp_map_transport_unit_app
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (k : A →+* C)
    (hk : g.comp f = k) {M : ModuleCat A} {N : ModuleCat B}
    (φ : (ModuleCat.extendScalars f).obj M ⟶ N)
    (hobj : (ModuleCat.extendScalars k).obj M = (ModuleCat.extendScalars (g.comp f)).obj M)
    (m : M) :
    ((eqToHom hobj ≫ (ModuleCat.extendScalarsComp f g).hom.app M ≫
        (ModuleCat.extendScalars g).map φ).hom
      (((ModuleCat.extendRestrictScalarsAdj k).unit.app M) m)) =
    (((ModuleCat.extendRestrictScalarsAdj g).unit.app N)
      (φ.hom (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m))) := by
  -- Evaluate the first two maps, then the functorially extended stage map.
  calc
    ((eqToHom hobj ≫ (ModuleCat.extendScalarsComp f g).hom.app M ≫
        (ModuleCat.extendScalars g).map φ).hom
      (((ModuleCat.extendRestrictScalarsAdj k).unit.app M) m)) =
      ((ModuleCat.extendScalars g).map φ).hom
        (((ModuleCat.extendRestrictScalarsAdj g).unit.app ((ModuleCat.extendScalars f).obj M))
          (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m)) := by
        rw [← Category.assoc]
        rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
        rw [extendScalarsComp_transport_unit_app f g k hk M hobj m]
        rfl
    _ = (((ModuleCat.extendRestrictScalarsAdj g).unit.app N)
      (φ.hom (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m))) := by
        exact extendScalars_map_unit_unit_app f g φ m

/-- Helper for Lemma 10.131.5: the transition on the extended stagewise differentials sends the
canonical generator `1 ⊗ d x` to the corresponding generator at the later stage. -/
private theorem stageKaehlerDifferentialBaseChangeTransition_on_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (x : S i) :
    (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (CommRingCat.KaehlerDifferential.d x)) =
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ j).hom)).unit.app
          (@stageKaehlerDifferential I R S _ _ _ j))
        (CommRingCat.KaehlerDifferential.d (σ i j h x))) := by
  -- Expose the transport/extension/transition composite and evaluate it one piece at a time.
  unfold stageKaehlerDifferentialBaseChangeTransition
  dsimp only [stageKaehlerDifferentialBaseChange, stageDirectLimitTargetHom, stageTargetHom,
    stageKaehlerDifferential, CommRingCat.hom_ofHom]
  erw [extendScalarsComp_map_transport_unit_app
    (σ i j h)
    (stageDirectLimitTargetMap j)
    (stageDirectLimitTargetMap i)
    (directLimitTarget_of_comp (σ := σ) h)
    (φ := stageKaehlerDifferentialTransitionBase hcomm h)
    (m := CommRingCat.KaehlerDifferential.d x)]
  erw [stageKaehlerDifferentialTransitionBase_on_d (hcomm := hcomm) h x]

/-- Helper for Lemma 10.131.5: the stagewise maps to `Ω[S∞⁄R∞]` form a compatible cocone over the
extended stagewise differentials. -/
private theorem stageKaehlerDifferentialBaseChangeToTarget_compatible_on_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (y : S i) :
    (stageKaehlerDifferentialBaseChangeToTarget hcomm j).hom
        ((stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
          (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
              (@stageKaehlerDifferential I R S _ _ _ i))
            (CommRingCat.KaehlerDifferential.d y))) =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (CommRingCat.KaehlerDifferential.d y)) := by
  -- The two cocone maps already agree on the differential generators after the source-side
  -- transition is rewritten explicitly.
  rw [stageKaehlerDifferentialBaseChangeTransition_on_d,
    stageKaehlerDifferentialBaseChangeToTarget_on_d,
    stageKaehlerDifferentialBaseChangeToTarget_on_d]
  exact
    congrArg CommRingCat.KaehlerDifferential.d
      (DFunLike.congr_fun (directLimitTarget_of_comp h) y)

/-- Helper for Chap10 Lemma 10 131 5: the adjoint of a composite evaluates by first applying
the extension-of-scalars morphism and then the second map. -/
private theorem extendRestrictScalarsAdj_homEquiv_apply_unit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat A} {N : ModuleCat B}
    (φ : (ModuleCat.extendScalars f).obj M ⟶ N) (m : M) :
    ((((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N) φ).hom) m =
      φ.hom (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m) := by
  -- Record the adjunction evaluation formula in the same unit-map spelling used by the stage
  -- generator lemmas.
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  rfl

/-- Helper for Chap10 Lemma 10 131 5: the adjoint of a composite evaluates by first applying
the extension-of-scalars morphism and then the second map. -/
private theorem extendRestrictScalarsAdj_homEquiv_comp_apply
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat A} {N P : ModuleCat B}
    (φ : (ModuleCat.extendScalars f).obj M ⟶ N) (ψ : N ⟶ P) (m : M) :
    ((((ModuleCat.extendRestrictScalarsAdj f).homEquiv M P) (φ ≫ ψ)).hom) m =
      ψ.hom (φ.hom (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m)) := by
  -- Normalize the adjunction unit once, then read the composite as composition of linear maps.
  rw [extendRestrictScalarsAdj_homEquiv_apply_unit]
  rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]

/-- Helper for Chap10 Lemma 10 131 5: after adjunction, the stagewise maps to
`Ω[S∞⁄R∞]` are compatible on the differential generators. -/
private theorem stageKaehlerDifferentialBaseChangeToTarget_natural_adj
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    ((ModuleCat.extendRestrictScalarsAdj
      ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv _ _)
        ((stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫
          (stageKaehlerDifferentialBaseChangeToTarget hcomm j)) =
    ((ModuleCat.extendRestrictScalarsAdj
      ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv _ _)
        (stageKaehlerDifferentialBaseChangeToTarget hcomm i) := by
  -- The adjointed maps are maps out of the stage Kähler differential, so it is enough to check
  -- the universal generators `d y`.
  apply CommRingCat.KaehlerDifferential.ext
  intro y
  -- Normalize the left adjoint composite and the right adjoint map to the same unit-image form.
  rw [extendRestrictScalarsAdj_homEquiv_comp_apply]
  exact
    (stageKaehlerDifferentialBaseChangeToTarget_compatible_on_d (hcomm := hcomm) h y).trans
      (extendRestrictScalarsAdj_homEquiv_apply_unit
        ((@stageDirectLimitTargetHom I _ S _ σ i).hom)
        (stageKaehlerDifferentialBaseChangeToTarget hcomm i)
        (CommRingCat.KaehlerDifferential.d y)).symm

/-- Helper for Lemma 10.131.5: the stagewise maps to `Ω[S∞⁄R∞]` form a compatible cocone over the
extended stagewise differentials. -/
private theorem stageKaehlerDifferentialBaseChangeToTarget_comp
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫
        (stageKaehlerDifferentialBaseChangeToTarget hcomm j) =
      stageKaehlerDifferentialBaseChangeToTarget hcomm i := by
  -- The adjointed maps out of `Ω[S_i/R_i]` are already equal on generators, so the original
  -- morphisms agree by injectivity of the corresponding adjunction equivalence.
  let e :=
    ((ModuleCat.extendRestrictScalarsAdj
      ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv
        (@stageKaehlerDifferential I R S _ _ _ i)
        (@directLimitDifferential I _ R S _ _ _ ρ σ hcomm))
  exact e.injective (stageKaehlerDifferentialBaseChangeToTarget_natural_adj (hcomm := hcomm) h)

/-- Helper for Chap10 Lemma 10 131 5: the compatible cocone relation rewritten as an equality of
underlying `S∞`-linear maps. -/
private theorem stageKaehlerDifferentialBaseChangeToTarget_comp_hom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    ((stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫
        (stageKaehlerDifferentialBaseChangeToTarget hcomm j)).hom =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom := by
  -- Forget the categorical wrapper once so later direct-limit witnesses can evaluate this equality
  -- by `DFunLike.congr_fun` instead of rebuilding the transport proof at each use.
  exact congrArg ModuleCat.Hom.hom
    (stageKaehlerDifferentialBaseChangeToTarget_comp (hcomm := hcomm) h)

/-- Helper for Lemma 10.131.5: the stage generator family is compatible with the transition maps
in the direct-limit source module. -/
private theorem stageDirectLimitSourceGenerator_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (x : S i) :
    stageDirectLimitSourceGenerator hcomm j (σ i j h x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Rewrite the later-stage class through the named transition-on-generator formula, then use the
  -- direct-limit relation identifying a stage element with its image in any later stage.
  classical
  unfold stageDirectLimitSourceGenerator
  calc
    Module.DirectLimit.of S∞ I
        (fun i ↦ stageKaehlerDifferentialBaseChange i)
        (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) j
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ j).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ j))
          (CommRingCat.KaehlerDifferential.d (σ i j h x))) =
    Module.DirectLimit.of S∞ I
        (fun i ↦ stageKaehlerDifferentialBaseChange i)
        (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) j
        ((stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
          (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
              (@stageKaehlerDifferential I R S _ _ _ i))
            (CommRingCat.KaehlerDifferential.d x))) := by
          rw [stageKaehlerDifferentialBaseChangeTransition_on_d (hcomm := hcomm) h x]
    _ = Module.DirectLimit.of S∞ I
        (fun i ↦ stageKaehlerDifferentialBaseChange i)
        (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (CommRingCat.KaehlerDifferential.d x)) := by
          simpa using
            (Module.DirectLimit.of_f (R := S∞) (ι := I)
              (G := fun i ↦ stageKaehlerDifferentialBaseChange i)
              (f := fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom)
              (i := i) (j := j) (hij := h)
              (x := (((ModuleCat.extendRestrictScalarsAdj
                ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
                  (@stageKaehlerDifferential I R S _ _ _ i))
                (CommRingCat.KaehlerDifferential.d x))))

/-- Helper for Chap10 Lemma 10 131 5: the explicit `ModuleCat` owner for the direct limit of the
base-changed stagewise Kähler differentials. -/
private noncomputable abbrev kaehlerDifferentialDirectLimitOwner
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat S∞ :=
  kaehlerDifferentialDirectLimitModule (ρ := ρ) (σ := σ) hcomm

/-- Helper for Lemma 10.131.5: the explicit direct-limit owner carries its canonical left
`S∞`-module structure on the underlying type. -/
private instance kaehlerDifferentialDirectLimitOwner_module
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm) :=
  inferInstance

/-- Helper for Lemma 10.131.5: the explicit direct-limit owner carries the induced right action
needed to form trivial square-zero extensions over the commutative ring `S∞`. -/
private instance kaehlerDifferentialDirectLimitOwner_opModule
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module S∞ᵐᵒᵖ ↑(kaehlerDifferentialDirectLimitOwner hcomm) :=
  inferInstance

/-- Helper for Lemma 10.131.5: the explicit direct-limit owner is central over `S∞`. -/
private instance kaehlerDifferentialDirectLimitOwner_isCentral
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsCentralScalar S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm) :=
  inferInstance

/-- Helper for Lemma 10.131.5: the direct-limit class of the unit image of `a • d x` is the
corresponding `S∞`-scalar multiple of the class of `d x`. -/
private theorem stageDirectLimitSourceGenerator_smul_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    [DecidableEq I]
    (i : I) (a x : S i) :
    Module.DirectLimit.of S∞ I
        (fun i ↦ stageKaehlerDifferentialBaseChange i)
        (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i
        (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
            (@stageKaehlerDifferential I R S _ _ _ i))
          (a • CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x)) =
      (stageDirectLimitTargetMap i a : S∞) •
        Module.DirectLimit.of S∞ I
          (fun i ↦ stageKaehlerDifferentialBaseChange i)
          (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i
          (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
              (@stageKaehlerDifferential I R S _ _ _ i))
            (CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x)) := by
  -- Move the stage scalar across the tensor sign, then use `S∞`-linearity of the stage
  -- representative map into the module direct limit.
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply, TensorProduct.tmul_smul]
  exact
    (Module.DirectLimit.of S∞ I
      (fun i ↦ stageKaehlerDifferentialBaseChange i)
      (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i).map_smul
        (stageDirectLimitTargetMap i a)
        ((1 : S∞) ⊗ₜ[S i] CommRingCat.KaehlerDifferential.d
          (f := @stageHom I R S _ _ _ i) x)

/-- Helper for Lemma 10.131.5: the stage generator family satisfies the Leibniz relation after
passing to the direct-limit source module. -/
private theorem stageDirectLimitSourceGenerator_mul
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x y : S i) :
    stageDirectLimitSourceGenerator hcomm i (x * y) =
      (stageDirectLimitTargetMap i x : S∞) • stageDirectLimitSourceGenerator hcomm i y +
        (stageDirectLimitTargetMap i y : S∞) • stageDirectLimitSourceGenerator hcomm i x := by
  -- Expand the universal derivation by Leibniz, distribute through the two linear maps, and
  -- identify the two represented scalar multiples in the direct-limit source module.
  classical
  unfold stageDirectLimitSourceGenerator
  have hmul :
      CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) (x * y) =
        x • CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) y +
          y • CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x := by
    simpa using
      (ModuleCat.Derivation.d_mul
        (D := CommRingCat.KaehlerDifferential.D (@stageHom I R S _ _ _ i)) x y)
  rw [hmul]
  let F := Module.DirectLimit.of S∞ I
    (fun i ↦ stageKaehlerDifferentialBaseChange i)
    (fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom) i
  let u := ((ModuleCat.extendRestrictScalarsAdj
    ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
      (@stageKaehlerDifferential I R S _ _ _ i))
  let dy := CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) y
  let dx := CommRingCat.KaehlerDifferential.d (f := @stageHom I R S _ _ _ i) x
  have hadd : F (u (x • dy + y • dx)) = F (u (x • dy)) + F (u (y • dx)) := by
    calc
      F (u (x • dy + y • dx)) = F (u (x • dy) + u (y • dx)) := by
        exact congrArg F (u.hom.map_add (x • dy) (y • dx))
      _ = F (u (x • dy)) + F (u (y • dx)) := by
        exact F.map_add (u (x • dy)) (u (y • dx))
  rw [hadd]
  have hy := stageDirectLimitSourceGenerator_smul_d (hcomm := hcomm) i x y
  have hx := stageDirectLimitSourceGenerator_smul_d (hcomm := hcomm) i y x
  simpa [F, u, dy, dx] using congrArg₂ HAdd.hAdd hy hx

/-- Helper for Lemma 10.131.5: the stage generator family defines a derivation into the
direct-limit source module after restricting scalars along `S_i → S∞`. -/
private noncomputable def stageDirectLimitSourceDerivation
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    ((ModuleCat.restrictScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
        (kaehlerDifferentialDirectLimitOwner hcomm)).Derivation
      (@stageHom I R S _ _ _ i) :=
  -- Package the already-proved defining relations of the generator family into a derivation.
  ModuleCat.Derivation.mk
    (M := (ModuleCat.restrictScalars ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).obj
      (kaehlerDifferentialDirectLimitOwner hcomm))
    (f := @stageHom I R S _ _ _ i)
    (fun x ↦ stageDirectLimitSourceGenerator hcomm i x)
    (stageDirectLimitSourceGenerator_add hcomm i)
    (stageDirectLimitSourceGenerator_mul hcomm i)
    (stageDirectLimitSourceGenerator_on_algebraMap hcomm i)

/-- Helper for Lemma 10.131.5: the universal map out of `Ω[S_i/R_i]` attached to the stage
generator derivation sends `d x` to the named stage generator class. -/
private theorem stageDirectLimitSourceDerivation_desc_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    (stageDirectLimitSourceDerivation hcomm i).desc
        (CommRingCat.KaehlerDifferential.d x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Evaluate the descended universal morphism on the differential generator `d x`.
  simpa [stageDirectLimitSourceDerivation] using
    ModuleCat.Derivation.desc_d (D := stageDirectLimitSourceDerivation hcomm i) x

/-- Helper for Lemma 10.131.5: the stage square-zero lift is multiplicative because the stage
generator family satisfies the Leibniz rule. -/
private theorem stageDirectLimitTargetSquareZeroLift_map_mul
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x y : S i) :
    stageDirectLimitTargetSquareZeroLiftFun hcomm i (x * y) =
      stageDirectLimitTargetSquareZeroLiftFun hcomm i x *
        stageDirectLimitTargetSquareZeroLiftFun hcomm i y := by
  -- Compare the two square-zero lifts on both coordinates, using the stagewise Leibniz formula
  -- for the second coordinate.
  apply TrivSqZeroExt.ext
  · simp [stageDirectLimitTargetSquareZeroLiftFun]
  · simp [stageDirectLimitTargetSquareZeroLiftFun, stageDirectLimitSourceGenerator_mul]

/-- Helper for Lemma 10.131.5: each stage derivation packages into a square-zero lift from `S_i`
to the trivial square-zero extension over `S∞`. -/
private noncomputable def stageDirectLimitTargetSquareZeroLift
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    S i →+* TrivSqZeroExt S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm) :=
  { toFun := stageDirectLimitTargetSquareZeroLiftFun hcomm i
    map_one' := stageDirectLimitTargetSquareZeroLift_map_one hcomm i
    map_mul' := stageDirectLimitTargetSquareZeroLift_map_mul hcomm i
    map_zero' := stageDirectLimitTargetSquareZeroLift_map_zero hcomm i
    map_add' := stageDirectLimitTargetSquareZeroLift_map_add hcomm i }

/-- Helper for Lemma 10.131.5: the first projection of the stage square-zero lift recovers the
stage map into the target ring direct limit. -/
private theorem stageDirectLimitTargetSquareZeroLift_fst
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt.fst (stageDirectLimitTargetSquareZeroLift hcomm i x) =
      (@stageDirectLimitTargetMap I _ S _ σ i) x := by
  -- The bundled ring hom uses `stageDirectLimitTargetSquareZeroLiftFun` as its underlying map.
  exact stageDirectLimitTargetSquareZeroLiftFun_fst hcomm i x

/-- Helper for Lemma 10.131.5: the second projection of the stage square-zero lift recovers the
named stage generator in the source direct limit. -/
private theorem stageDirectLimitTargetSquareZeroLift_snd
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt.snd (stageDirectLimitTargetSquareZeroLift hcomm i x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- The bundled ring hom uses `stageDirectLimitTargetSquareZeroLiftFun` as its underlying map.
  exact stageDirectLimitTargetSquareZeroLiftFun_snd hcomm i x

/-- Helper for Lemma 10.131.5: the stage square-zero lifts are compatible with the transition maps
of the directed system. -/
private theorem stageDirectLimitTargetSquareZeroLift_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (stageDirectLimitTargetSquareZeroLift hcomm j).comp (σ i j h) =
      stageDirectLimitTargetSquareZeroLift hcomm i := by
  -- Compare the two stage lifts coordinatewise: the ring part is the direct-limit structure map,
  -- and the differential part is the direct-limit source-generator compatibility.
  ext x
  · exact DFunLike.congr_fun (directLimitTarget_of_comp (σ := σ) h) x
  · exact
      (stageDirectLimitTargetSquareZeroLift_snd (hcomm := hcomm) j ((σ i j h) x)).trans
        ((stageDirectLimitSourceGenerator_compatible (hcomm := hcomm) h x).trans
          (stageDirectLimitTargetSquareZeroLift_snd (hcomm := hcomm) i x).symm)

/-- Helper for Chap10 Lemma 10 131 5: the stagewise maps to `Ω[S∞⁄R∞]` are compatible after
forgetting the categorical wrapper to underlying linear maps. -/
private theorem kaehlerDifferential_directLimitComparison_hom_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : stageKaehlerDifferentialBaseChange i) :
    ((stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫
        (stageKaehlerDifferentialBaseChangeToTarget hcomm j)).hom x =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom x := by
  exact
    DFunLike.congr_fun
      (stageKaehlerDifferentialBaseChangeToTarget_comp_hom (hcomm := hcomm) h)
      x

/-- Helper for Chap10 Lemma 10 131 5: the family of base-changed stagewise Kähler differentials
used to present the source direct limit. -/
private abbrev kaehlerDifferentialDirectLimitFamily : I → Type u :=
  fun i ↦ ↑(@stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i)

/-- Helper for Chap10 Lemma 10 131 5: the transition maps in the source direct-limit system,
viewed as underlying `S∞`-linear maps. -/
private def kaehlerDifferentialDirectLimitTransition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i j : I) (h : i ≤ j) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i →ₗ[S∞]
      @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ j :=
  (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom

/-- Helper for Chap10 Lemma 10 131 5: the raw carrier of the source direct limit before rewrapping
it as a `ModuleCat S∞` object. -/
private noncomputable abbrev kaehlerDifferentialDirectLimitCarrier
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :=
  let _ : DecidableEq I := Classical.decEq I
  Module.DirectLimit
    (kaehlerDifferentialDirectLimitFamily)
    (kaehlerDifferentialDirectLimitTransition hcomm)

/-- Helper for Chap10 Lemma 10 131 5: the cocone maps from each stage differential into
`Ω[S∞⁄R∞]`, viewed as underlying `S∞`-linear maps. -/
private def kaehlerDifferentialDirectLimitStageMap
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i →ₗ[S∞]
      ↑(directLimitDifferential hcomm) :=
  (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom

/-- Helper for Chap10 Lemma 10 131 5: the source direct-limit cocone relation rewritten as an
equality of underlying `S∞`-linear maps in the spelling expected by `Module.DirectLimit.lift`. -/
private theorem kaehlerDifferentialDirectLimitStageMap_comp
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (kaehlerDifferentialDirectLimitStageMap hcomm j).comp
        (kaehlerDifferentialDirectLimitTransition hcomm i j h) =
      kaehlerDifferentialDirectLimitStageMap hcomm i := by
  -- Forget the categorical wrappers once so the cocone naturality proof can reuse a linear-map
  -- equality instead of re-normalizing the composite on every element.
  simpa [kaehlerDifferentialDirectLimitStageMap, kaehlerDifferentialDirectLimitTransition,
    ModuleCat.hom_comp] using
    stageKaehlerDifferentialBaseChangeToTarget_comp_hom (hcomm := hcomm) h

/-- Helper for Chap10 Lemma 10 131 5: the source direct-limit cocone relation evaluated on an
element of a stage differential. -/
private theorem kaehlerDifferentialDirectLimitStageMap_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) (x : kaehlerDifferentialDirectLimitFamily i) :
    ((kaehlerDifferentialDirectLimitStageMap hcomm j).comp
        (kaehlerDifferentialDirectLimitTransition hcomm i j h)) x =
      kaehlerDifferentialDirectLimitStageMap hcomm i x := by
  -- Evaluate the linear-map cocone compatibility on the chosen stage element.
  exact
    DFunLike.congr_fun
      (kaehlerDifferentialDirectLimitStageMap_comp (hcomm := hcomm) h)
      x

/-- The canonical comparison from the direct limit of the stagewise Kähler differentials to the
Kähler differential of the induced direct-limit ring map. -/
private noncomputable def kaehlerDifferentialDirectLimitOf
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i →ₗ[S∞]
      kaehlerDifferentialDirectLimitCarrier (ρ := ρ) (σ := σ) hcomm :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun k ↦ @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ k
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
  Module.DirectLimit.of (R := S∞) (ι := I)
    (G := G)
    (f := μ) i

/-- Helper for Chap10 Lemma 10 131 5: the base-changed stage generator `1 ⊗ d x` as an element
of the stage module over `S∞`. -/
private noncomputable def stageKaehlerDifferentialBaseChangeGenerator
    (i : I) (x : S i) :
    @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i :=
  (((ModuleCat.extendRestrictScalarsAdj ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).unit.app
      (@stageKaehlerDifferential I R S _ _ _ i))
    (CommRingCat.KaehlerDifferential.d x))

/-- Helper for Chap10 Lemma 10 131 5: any compatible family of stage maps out of the
base-changed stagewise Kähler differentials descends to the source direct limit. -/
private noncomputable def kaehlerDifferentialDirectLimitDesc
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {P : ModuleCat S∞}
    (g : ∀ i, @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i ⟶ P)
    (hg : ∀ ⦃i j : I⦄ (h : i ≤ j),
        (stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫ g j = g i) :
    kaehlerDifferentialDirectLimitOwner (ρ := ρ) (σ := σ) hcomm ⟶ P :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun k ↦ @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ k
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
  let P' : Type u := P
  let ν : ∀ i, G i →ₗ[S∞] P' := fun i ↦ (g i).hom
  ModuleCat.ofHom <|
    Module.DirectLimit.lift (R := S∞) (ι := I)
      (G := G)
      (f := μ)
      (P := P')
      ν
      (fun _ _ h x ↦ DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hg h)) x)

/-- Helper for Chap10 Lemma 10 131 5: the descended morphism associated to a compatible family
of stage maps evaluates on a represented stage class by the chosen stage map. -/
private theorem kaehlerDifferentialDirectLimitDesc_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {P : ModuleCat S∞}
    (g : ∀ i, @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ i ⟶ P)
    (hg : ∀ ⦃i j : I⦄ (h : i ≤ j),
        (stageKaehlerDifferentialBaseChangeTransition hcomm h) ≫ g j = g i)
    (i : I) (z : stageKaehlerDifferentialBaseChange i) :
    (kaehlerDifferentialDirectLimitDesc (ρ := ρ) (σ := σ) hcomm g hg).hom
        (kaehlerDifferentialDirectLimitOf hcomm i z) =
      (g i).hom z := by
  classical
  let G : I → Type u := fun k ↦ @stageKaehlerDifferentialBaseChange I _ R S _ _ _ σ k
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageKaehlerDifferentialBaseChangeTransition hcomm h).hom
  let P' : Type u := P
  let ν : ∀ i, G i →ₗ[S∞] P' := fun i ↦ (g i).hom
  change
    Module.DirectLimit.lift (R := S∞) (ι := I)
        (G := G)
        (f := μ)
        (P := P')
        ν
        (fun _ _ h x ↦ DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hg h)) x)
        (Module.DirectLimit.of (R := S∞) (ι := I) (G := G) (f := μ) i z) =
      ν i z
  exact
    (Module.DirectLimit.lift_of (R := S∞)
      (ι := I)
      (G := G)
      (f := μ)
      (P := P')
      ν
      (fun _ _ h x ↦ DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hg h)) x)
      (i := i) (x := z))

/-- The canonical comparison from the direct limit of the stagewise Kähler differentials to the
Kähler differential of the induced direct-limit ring map. -/
noncomputable def kaehlerDifferential_directLimitComparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    kaehlerDifferentialDirectLimitOwner (ρ := ρ) (σ := σ) hcomm ⟶
      directLimitDifferential (ρ := ρ) (σ := σ) hcomm :=
  kaehlerDifferentialDirectLimitDesc (ρ := ρ) (σ := σ) hcomm
    (fun i ↦ stageKaehlerDifferentialBaseChangeToTarget hcomm i)
    (fun _ _ h ↦ stageKaehlerDifferentialBaseChangeToTarget_comp (hcomm := hcomm) h)

/-- Helper for Chap10 Lemma 10 131 5: the canonical comparison evaluates on a represented stage
class by the corresponding stage-to-target map. -/
private theorem kaehlerDifferential_directLimitComparison_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (z : stageKaehlerDifferentialBaseChange i) :
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (kaehlerDifferentialDirectLimitOf hcomm i z) =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom z := by
  simpa [kaehlerDifferential_directLimitComparison] using
    kaehlerDifferentialDirectLimitDesc_of_stage (ρ := ρ) (σ := σ) hcomm
      (fun i ↦ stageKaehlerDifferentialBaseChangeToTarget hcomm i)
      (fun _ _ h ↦ stageKaehlerDifferentialBaseChangeToTarget_comp (hcomm := hcomm) h)
      i z

/-- Helper for Lemma 10.131.5: the canonical comparison sends the class of the stage generator
`1 ⊗ d x` to the differential of the image of `x` in the ring direct limit. -/
private theorem kaehlerDifferential_directLimitComparison_of_stage_generator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (stageDirectLimitSourceGenerator hcomm i x) =
      CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i x) := by
  classical
  -- Evaluate the comparison on the represented stage generator, then use the known stage formula.
  calc
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (stageDirectLimitSourceGenerator hcomm i x) =
      (stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom
        (stageKaehlerDifferentialBaseChangeGenerator i x) := by
            simpa [stageDirectLimitSourceGenerator, stageKaehlerDifferentialBaseChangeGenerator,
              kaehlerDifferentialDirectLimitOf] using
              kaehlerDifferential_directLimitComparison_of_stage (hcomm := hcomm) i
                (stageKaehlerDifferentialBaseChangeGenerator i x)
    _ = CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i x) := by
          simpa using stageKaehlerDifferentialBaseChangeToTarget_on_d (hcomm := hcomm) i x

/-- Helper for Lemma 10.131.5: the compatible stage square-zero lifts descend to a single
square-zero lift on the ring direct limit `S∞`. -/
private noncomputable def directLimitTargetSquareZeroLiftDesc
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    S∞ →+* TrivSqZeroExt S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm) :=
  -- Descend the compatible stage square-zero lifts through the ring direct-limit universal
  -- property.
  Ring.DirectLimit.lift S (fun i j h ↦ σ i j h)
    (TrivSqZeroExt S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm))
    (fun i ↦ stageDirectLimitTargetSquareZeroLift hcomm i)
    (fun _ _ hij x ↦
      DFunLike.congr_fun (stageDirectLimitTargetSquareZeroLift_compatible (hcomm := hcomm) hij) x)

/-- Helper for Lemma 10.131.5: the descended square-zero lift agrees with the stagewise lift on
each stage representative of `S∞`. -/
private theorem directLimitTargetSquareZeroLiftDesc_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    directLimitTargetSquareZeroLiftDesc hcomm (stageDirectLimitTargetMap i x) =
      stageDirectLimitTargetSquareZeroLift hcomm i x := by
  -- Evaluate the descended lift on the chosen stage representative by `Ring.DirectLimit.lift_of`.
  simp [directLimitTargetSquareZeroLiftDesc]

/-- Helper for Lemma 10.131.5: the first projection of the descended square-zero lift is the
identity on `S∞`. -/
private theorem directLimitTargetSquareZeroLiftDesc_fst
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x : S∞) :
    TrivSqZeroExt.fst (directLimitTargetSquareZeroLiftDesc hcomm x) = x := by
  -- Compare the first projection of the descended lift with the identity as ring maps out of the
  -- ring direct limit, then evaluate that ring-hom identity at `x`.
  classical
  let fstDesc : S∞ →+* S∞ :=
    (TrivSqZeroExt.fstHom S∞ S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm)).toRingHom.comp
      (directLimitTargetSquareZeroLiftDesc hcomm)
  have hfst : fstDesc = RingHom.id S∞ := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply, directLimitTargetSquareZeroLiftDesc_of_stage]
    exact stageDirectLimitTargetSquareZeroLift_fst (hcomm := hcomm) i y
  exact congrArg (fun f : S∞ →+* S∞ ↦ f x) hfst

/-- Helper for Lemma 10.131.5: on a stage representative, the second projection of the descended
square-zero lift is the named stage generator in the source direct limit. -/
private theorem directLimitTargetSquareZeroLiftDesc_snd_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    TrivSqZeroExt.snd
        (directLimitTargetSquareZeroLiftDesc hcomm ((@stageDirectLimitTargetMap I _ S _ σ i) x)) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Evaluate the descended lift on the stage representative and read off its second coordinate.
  rw [directLimitTargetSquareZeroLiftDesc_of_stage]
  exact stageDirectLimitTargetSquareZeroLift_snd (hcomm := hcomm) i x

/-- Helper for Lemma 10.131.5: the induced map on ring direct limits sends a stage representative
of `R∞` to the matching stage representative of `S∞`. -/
private theorem directLimitRingHom_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (r : R i) :
    directLimitRingHom hcomm ((Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) r) =
      (@stageDirectLimitTargetMap I _ S _ σ i) (algebraMap (R i) (S i) r) := by
  -- The canonical map of directed systems evaluates on stage representatives by `map_apply_of`.
  simp [directLimitRingHom, stageDirectLimitTargetMap]

/-- Helper for Lemma 10.131.5: the descended square-zero lift defines the underlying function of
the global derivation on `S∞`. -/
private noncomputable abbrev directLimitSourceDerivationDescFun
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x : S∞) :
    kaehlerDifferentialDirectLimitOwner hcomm :=
  TrivSqZeroExt.snd (directLimitTargetSquareZeroLiftDesc hcomm x)

/-- Helper for Lemma 10.131.5: on a stage representative, the descended derivation function agrees
with the named stage generator. -/
private theorem directLimitSourceDerivationDescFun_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    directLimitSourceDerivationDescFun hcomm ((@stageDirectLimitTargetMap I _ S _ σ i) x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- The descended derivation function is the second projection of the descended square-zero lift.
  exact directLimitTargetSquareZeroLiftDesc_snd_of_stage (hcomm := hcomm) i x

/-- Helper for Lemma 10.131.5: the descended square-zero lift is additive on its second
projection, so it defines an additive map `S∞ → M∞`. -/
private theorem directLimitSourceDerivationDescFun_add
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x y : S∞) :
    directLimitSourceDerivationDescFun hcomm (x + y) =
      directLimitSourceDerivationDescFun hcomm x +
        directLimitSourceDerivationDescFun hcomm y := by
  -- Apply `TrivSqZeroExt.snd` to the additive law of the descended square-zero lift.
  unfold directLimitSourceDerivationDescFun
  rw [map_add]
  simp

/-- Helper for Lemma 10.131.5: the descended square-zero lift satisfies the Leibniz rule on its
second projection. -/
private theorem directLimitSourceDerivationDescFun_mul
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x y : S∞) :
    directLimitSourceDerivationDescFun hcomm (x * y) =
      x • directLimitSourceDerivationDescFun hcomm y +
        y • directLimitSourceDerivationDescFun hcomm x := by
  -- Apply `TrivSqZeroExt.snd` to the multiplicativity of the descended square-zero lift, then
  -- rewrite the first coordinates using the identity proved above.
  unfold directLimitSourceDerivationDescFun
  rw [map_mul, TrivSqZeroExt.snd_mul, directLimitTargetSquareZeroLiftDesc_fst,
    directLimitTargetSquareZeroLiftDesc_fst]
  simp

/-- Helper for Lemma 10.131.5: the descended square-zero lift kills the image of the base ring,
so its second projection is a derivation relative to `R∞ → S∞`. -/
private theorem directLimitTargetSquareZeroLiftDesc_comp_directLimitRingHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (directLimitTargetSquareZeroLiftDesc hcomm).comp (directLimitRingHom hcomm) =
      (TrivSqZeroExt.inlHom S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm)).comp
        (directLimitRingHom hcomm) := by
  -- Compare the two ring homs out of `R∞` on each stage map: the first coordinates agree by the
  -- direct-limit ring map formula, and the second coordinates vanish stagewise on base elements.
  classical
  apply Ring.DirectLimit.hom_ext
  intro i
  ext r
  · rw [RingHom.comp_apply, RingHom.comp_apply, directLimitRingHom_of_stage,
      directLimitTargetSquareZeroLiftDesc_of_stage]
    exact stageDirectLimitTargetSquareZeroLift_fst
      (hcomm := hcomm) i ((algebraMap (R i) (S i)) r)
  · rw [RingHom.comp_apply, RingHom.comp_apply, directLimitRingHom_of_stage,
      directLimitTargetSquareZeroLiftDesc_of_stage]
    rw [stageDirectLimitTargetSquareZeroLift_snd]
    exact stageDirectLimitSourceGenerator_on_algebraMap (hcomm := hcomm) i r

/-- Helper for Lemma 10.131.5: the descended square-zero lift kills the image of the base ring,
so its second projection is a derivation relative to `R∞ → S∞`. -/
private theorem directLimitSourceDerivationDescFun_map
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (a : R∞) :
    directLimitSourceDerivationDescFun hcomm (directLimitRingHom hcomm a) = 0 := by
  -- Apply `TrivSqZeroExt.snd` to the ring-hom equality comparing the descended lift with the
  -- pure inclusion on `R∞`.
  have hpoint :=
    congrArg
      (fun f : R∞ →+* TrivSqZeroExt S∞ ↑(kaehlerDifferentialDirectLimitOwner hcomm) ↦ f a)
      (directLimitTargetSquareZeroLiftDesc_comp_directLimitRingHom (hcomm := hcomm))
  simpa [directLimitSourceDerivationDescFun, RingHom.comp_apply] using
    congrArg TrivSqZeroExt.snd hpoint

/-- Helper for Lemma 10.131.5: the descended square-zero lift induces the global derivation
`S∞ → M∞` relative to `R∞ → S∞`. -/
private noncomputable def directLimitSourceDerivationDesc
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (kaehlerDifferentialDirectLimitOwner hcomm).Derivation
      (CommRingCat.ofHom (directLimitRingHom hcomm)) :=
  ModuleCat.Derivation.mk
    (M := kaehlerDifferentialDirectLimitOwner hcomm)
    (f := CommRingCat.ofHom (directLimitRingHom hcomm))
    (directLimitSourceDerivationDescFun hcomm)
    (directLimitSourceDerivationDescFun_add hcomm)
    (directLimitSourceDerivationDescFun_mul hcomm)
    (directLimitSourceDerivationDescFun_map hcomm)

/-- Helper for Lemma 10.131.5: the descended derivation sends a stage representative of `S∞` to
the corresponding stage generator in the source direct limit. -/
private theorem directLimitSourceDerivationDesc_d_of_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    (directLimitSourceDerivationDesc hcomm).d ((@stageDirectLimitTargetMap I _ S _ σ i) x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Unfold only the underlying function of the descended derivation and use the stage formula for
  -- the second projection of the descended square-zero lift.
  simpa [directLimitSourceDerivationDesc] using
    directLimitSourceDerivationDescFun_of_stage (hcomm := hcomm) i x

/-- Helper for Lemma 10.131.5: the canonical comparison carries the descended derivation on `S∞`
to the universal derivation on `Ω[S∞⁄R∞]`. -/
private theorem kaehlerDifferential_directLimitComparison_on_descended_derivation
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x : S∞) :
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (directLimitSourceDerivationDescFun hcomm x) =
      CommRingCat.KaehlerDifferential.d x := by
  -- Compare the two square-zero lifts on `S∞` as ring homs out of the ring direct limit, then
  -- take the second projection.
  have hsq :
      ((TrivSqZeroExt.map (kaehlerDifferential_directLimitComparison hcomm).hom).toRingHom.comp
          (directLimitTargetSquareZeroLiftDesc hcomm)) =
        targetKaehlerSquareZeroLift hcomm := by
    classical
    apply Ring.DirectLimit.hom_ext
    intro i
    ext y
    · rw [RingHom.comp_apply, RingHom.comp_apply, directLimitTargetSquareZeroLiftDesc_of_stage]
      simp [targetKaehlerSquareZeroLift, targetKaehlerSquareZeroLiftFun,
        stageDirectLimitTargetSquareZeroLift_fst]
    · calc
        TrivSqZeroExt.snd
            (((TrivSqZeroExt.map (kaehlerDifferential_directLimitComparison hcomm).hom).toRingHom.comp
              (directLimitTargetSquareZeroLiftDesc hcomm))
              (stageDirectLimitTargetMap i y)) =
          (kaehlerDifferential_directLimitComparison hcomm).hom
            (stageDirectLimitSourceGenerator hcomm i y) := by
              rw [RingHom.comp_apply, directLimitTargetSquareZeroLiftDesc_of_stage]
              simp [stageDirectLimitTargetSquareZeroLift_snd]
        _ = CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i y) := by
              simpa using
                kaehlerDifferential_directLimitComparison_of_stage_generator (hcomm := hcomm) i y
        _ = TrivSqZeroExt.snd
            (targetKaehlerSquareZeroLift hcomm (stageDirectLimitTargetMap i y)) := by
              simp [targetKaehlerSquareZeroLift, targetKaehlerSquareZeroLiftFun]
  have hpoint :=
    congrArg
      (fun f : S∞ →+* TrivSqZeroExt S∞ ↑(directLimitDifferential hcomm) ↦ f x) hsq
  simpa [directLimitSourceDerivationDescFun, RingHom.comp_apply, targetKaehlerSquareZeroLift,
    targetKaehlerSquareZeroLiftFun] using congrArg TrivSqZeroExt.snd hpoint

-- Proof sketch: use the generators-and-relations presentation of Kähler differentials together
-- with the directed colimit description of `S∞`; the induced universal derivation on the direct
-- limit source identifies it with `Ω[S∞⁄R∞]`.
/-- Helper for Chap10 Lemma 10 131 5: the canonical direct-limit class map at stage `i`,
rewrapped as a `ModuleCat` morphism. -/
private noncomputable abbrev kaehlerDifferentialDirectLimitStageInclusion
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :=
  ModuleCat.ofHom (kaehlerDifferentialDirectLimitOf hcomm i)

/-- Helper for Chap10 Lemma 10 131 5: the named stage inclusion sends the base-changed generator
`1 ⊗ d x` to the corresponding source direct-limit generator. -/
private theorem kaehlerDifferentialDirectLimitStageInclusion_on_generator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    (kaehlerDifferentialDirectLimitStageInclusion hcomm i).hom
        (stageKaehlerDifferentialBaseChangeGenerator i x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Unfold the named stage inclusion once so the result is definitionally the chosen direct-limit
  -- representative of the stage generator.
  rfl

/-- Helper for Chap10 Lemma 10 131 5: composing the named stage inclusion with the canonical
comparison recovers the existing stage map to `Ω[S∞⁄R∞]`. -/
private theorem kaehlerDifferential_directLimitComparison_comp_stageInclusion
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    kaehlerDifferentialDirectLimitStageInclusion hcomm i ≫
        kaehlerDifferential_directLimitComparison hcomm =
      stageKaehlerDifferentialBaseChangeToTarget hcomm i := by
  classical
  -- Evaluate both morphisms on a represented stage class and reuse the direct-limit `lift_of`
  -- formula in the same spelling world.
  apply ModuleCat.hom_ext
  ext z
  simpa [kaehlerDifferentialDirectLimitStageInclusion, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] using
    kaehlerDifferential_directLimitComparison_of_stage (hcomm := hcomm) i z

/-- Helper for Lemma 10.131.5: on each base-changed stage module, the source-side composite is
the canonical structure map into the direct-limit source module. -/
private theorem kaehlerDifferential_directLimitComparison_leftInverse_stage_to_of
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    ((stageKaehlerDifferentialBaseChangeToTarget hcomm i) ≫
        (directLimitSourceDerivationDesc hcomm).desc).hom
        (stageKaehlerDifferentialBaseChangeGenerator i x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Evaluate the comparison map on `1 ⊗ d x`, then evaluate the descended derivation on the
  -- resulting universal differential.
  calc
    ((stageKaehlerDifferentialBaseChangeToTarget hcomm i) ≫
        (directLimitSourceDerivationDesc hcomm).desc).hom
        (stageKaehlerDifferentialBaseChangeGenerator i x) =
      ((directLimitSourceDerivationDesc hcomm).desc).hom
        ((stageKaehlerDifferentialBaseChangeToTarget hcomm i).hom
          (stageKaehlerDifferentialBaseChangeGenerator i x)) := by
            rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    _ =
      ((directLimitSourceDerivationDesc hcomm).desc).hom
        (CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i x)) := by
          exact congrArg
            (fun z ↦ (directLimitSourceDerivationDesc hcomm).desc.hom z)
            (by
              simpa [stageKaehlerDifferentialBaseChangeGenerator] using
                stageKaehlerDifferentialBaseChangeToTarget_on_d (hcomm := hcomm) i x)
    _ = (directLimitSourceDerivationDesc hcomm).d (stageDirectLimitTargetMap i x) := by
          simpa using
            (ModuleCat.Derivation.desc_d
              (D := directLimitSourceDerivationDesc hcomm) (stageDirectLimitTargetMap i x))
    _ = stageDirectLimitSourceGenerator hcomm i x := by
          exact directLimitSourceDerivationDesc_d_of_stage (hcomm := hcomm) i x

/-- Helper for Chap10 Lemma 10 131 5: after precomposing with the canonical stage inclusion,
the adjoint of the source-side composite sends each universal generator `d x` to the expected
direct-limit stage generator. -/
private theorem kaehlerDifferential_directLimitComparison_leftInverse_on_stageGenerator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    ((((ModuleCat.extendRestrictScalarsAdj
        ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv
        (@stageKaehlerDifferential I R S _ _ _ i)
        (kaehlerDifferentialDirectLimitOwner (ρ := ρ) (σ := σ) hcomm))
        (kaehlerDifferentialDirectLimitStageInclusion hcomm i ≫
          ((kaehlerDifferential_directLimitComparison hcomm) ≫
            (directLimitSourceDerivationDesc hcomm).desc))).hom)
        (CommRingCat.KaehlerDifferential.d x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Evaluate the adjointed composite on `d x`, then rewrite the first factor to the named stage
  -- map into `Ω[S∞⁄R∞]`.
  rw [extendRestrictScalarsAdj_homEquiv_apply_unit]
  rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  calc
    (directLimitSourceDerivationDesc hcomm).desc.hom
        ((kaehlerDifferential_directLimitComparison hcomm).hom
          ((kaehlerDifferentialDirectLimitStageInclusion hcomm i).hom
            (stageKaehlerDifferentialBaseChangeGenerator i x))) =
      (directLimitSourceDerivationDesc hcomm).desc.hom
        ((kaehlerDifferential_directLimitComparison hcomm).hom
          (stageDirectLimitSourceGenerator hcomm i x)) := by
            exact congrArg
              (fun m ↦ (directLimitSourceDerivationDesc hcomm).desc.hom
                ((kaehlerDifferential_directLimitComparison hcomm).hom m))
              (kaehlerDifferentialDirectLimitStageInclusion_on_generator
                (hcomm := hcomm) i x)
    _ =
      (directLimitSourceDerivationDesc hcomm).desc.hom
        (CommRingCat.KaehlerDifferential.d (stageDirectLimitTargetMap i x)) := by
          rw [kaehlerDifferential_directLimitComparison_of_stage_generator (hcomm := hcomm) i x]
    _ = (directLimitSourceDerivationDesc hcomm).d (stageDirectLimitTargetMap i x) := by
          simpa using
            (ModuleCat.Derivation.desc_d
              (D := directLimitSourceDerivationDesc hcomm) (stageDirectLimitTargetMap i x))
    _ = stageDirectLimitSourceGenerator hcomm i x := by
          exact directLimitSourceDerivationDesc_d_of_stage (hcomm := hcomm) i x

/-- Helper for Chap10 Lemma 10 131 5: the adjoint of the named stage inclusion sends each
universal generator `d x` to the corresponding direct-limit stage generator. -/
private theorem kaehlerDifferentialDirectLimitStageInclusion_adjoint_on_generator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) (x : S i) :
    ((((ModuleCat.extendRestrictScalarsAdj
        ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv
        (@stageKaehlerDifferential I R S _ _ _ i)
        (kaehlerDifferentialDirectLimitOwner (ρ := ρ) (σ := σ) hcomm))
        (kaehlerDifferentialDirectLimitStageInclusion hcomm i)).hom)
        (CommRingCat.KaehlerDifferential.d x) =
      stageDirectLimitSourceGenerator hcomm i x := by
  -- Evaluate the adjointed inclusion on `d x` and read off the defining stage class.
  rw [extendRestrictScalarsAdj_homEquiv_apply_unit]
  exact kaehlerDifferentialDirectLimitStageInclusion_on_generator (hcomm := hcomm) i x

/-- Helper for Chap10 Lemma 10 131 5: after precomposing with the canonical stage inclusion,
the source-side composite `comparison ≫ desc` already acts as the identity. -/
private theorem kaehlerDifferential_directLimitComparison_leftInverse_on_stageObject
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    kaehlerDifferentialDirectLimitStageInclusion hcomm i ≫
        ((kaehlerDifferential_directLimitComparison hcomm) ≫
          (directLimitSourceDerivationDesc hcomm).desc) =
      kaehlerDifferentialDirectLimitStageInclusion hcomm i := by
  -- Transport both maps back across the stage adjunction once, then compare them on the universal
  -- generators `d x`.
  apply ((ModuleCat.extendRestrictScalarsAdj
    ((@stageDirectLimitTargetHom I _ S _ σ i).hom)).homEquiv
    (@stageKaehlerDifferential I R S _ _ _ i)
    (kaehlerDifferentialDirectLimitOwner (ρ := ρ) (σ := σ) hcomm)).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  exact
    (kaehlerDifferential_directLimitComparison_leftInverse_on_stageGenerator
      (hcomm := hcomm) i x).trans
      (kaehlerDifferentialDirectLimitStageInclusion_adjoint_on_generator
        (hcomm := hcomm) i x).symm

/-- Helper for Lemma 10.131.5: the descended derivation is a left inverse to the canonical
comparison on the direct-limit source module. -/
private theorem kaehlerDifferential_directLimitComparison_leftInverse
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (kaehlerDifferential_directLimitComparison hcomm) ≫
        (directLimitSourceDerivationDesc hcomm).desc =
      𝟙 (kaehlerDifferentialDirectLimitOwner hcomm) := by
  classical
  -- Route correction: compare the two endomorphisms only after precomposing with each named stage
  -- inclusion, and discharge those stagewise equalities once by adjunction extensionality.
  apply ModuleCat.hom_ext
  apply Module.DirectLimit.hom_ext
  intro i
  -- The direct-limit extensionality goal asks for equality after each stage class map.
  simpa [kaehlerDifferentialDirectLimitStageInclusion, ModuleCat.hom_comp] using
    congrArg ModuleCat.Hom.hom
      (kaehlerDifferential_directLimitComparison_leftInverse_on_stageObject
        (hcomm := hcomm) i)

/-- Helper for Lemma 10.131.5: the target-side composite fixes every universal generator `d x`. -/
private theorem kaehlerDifferential_directLimitComparison_rightInverse_on_d
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (x : S∞) :
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (((directLimitSourceDerivationDesc hcomm).desc).hom
          (CommRingCat.KaehlerDifferential.d x)) =
      CommRingCat.KaehlerDifferential.d x := by
  -- Evaluate the descended inverse on `d x`, then compare with the already-descended derivation.
  calc
    (kaehlerDifferential_directLimitComparison hcomm).hom
        (((directLimitSourceDerivationDesc hcomm).desc).hom
          (CommRingCat.KaehlerDifferential.d x)) =
      (kaehlerDifferential_directLimitComparison hcomm).hom
        ((directLimitSourceDerivationDesc hcomm).d x) := by
          simpa using
            congrArg
              (fun z ↦ (kaehlerDifferential_directLimitComparison hcomm).hom z)
              (ModuleCat.Derivation.desc_d (D := directLimitSourceDerivationDesc hcomm) x)
    _ = (kaehlerDifferential_directLimitComparison hcomm).hom
        (directLimitSourceDerivationDescFun hcomm x) := by
          rfl
    _ = CommRingCat.KaehlerDifferential.d x := by
          exact
            kaehlerDifferential_directLimitComparison_on_descended_derivation
              (hcomm := hcomm) x

/-- Helper for Lemma 10.131.5: the descended derivation is a right inverse to the canonical
comparison on `Ω[S∞⁄R∞]`. -/
private theorem kaehlerDifferential_directLimitComparison_rightInverse
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (directLimitSourceDerivationDesc hcomm).desc ≫
        (kaehlerDifferential_directLimitComparison hcomm) =
      𝟙 (directLimitDifferential hcomm) := by
  -- The target differential is generated by `d x`, so fixing those generators gives the identity.
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  simpa using
    kaehlerDifferential_directLimitComparison_rightInverse_on_d (hcomm := hcomm) x

/-- Chap10 Lemma 10 131 5: the canonical comparison from the direct limit module of the stagewise Kähler
differentials to the Kähler differential of the induced direct-limit ring map is an isomorphism. -/
@[stacks 031G]
theorem kaehlerDifferential_directLimitComparison_isIso
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (kaehlerDifferential_directLimitComparison hcomm) := by
  classical
  -- Route correction: prove both inverse identities by universal properties only.  On the source
  -- direct limit and on the target differential, the two inverse laws are now isolated in the
  -- dedicated helper lemmas proved above.
  refine ⟨⟨(directLimitSourceDerivationDesc hcomm).desc, ?_, ?_⟩⟩
  · exact kaehlerDifferential_directLimitComparison_leftInverse (hcomm := hcomm)
  · exact kaehlerDifferential_directLimitComparison_rightInverse (hcomm := hcomm)

end
