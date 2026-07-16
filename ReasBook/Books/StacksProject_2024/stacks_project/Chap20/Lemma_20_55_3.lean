import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap17.Definition_17_23_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap20.IdealSheafStalkIdeal
import StacksProject_2024.stacks_project.Chap20.Lemma_20_26_4
import StacksProject_2024.stacks_project.Chap20.Situation_20_55_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open MonoidalCategory
open Opposite
open TopologicalSpace
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [monoidalModX : MonoidalCategory (RingedSpace.Modules X)]
variable {I : Subobject
  (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) :
    RingedSpace.Modules X)}
variable {ℱ : RingedSpace.Modules X}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" =>
  (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) : ModX)

/- Domain-style sampling for Lemma 20.55.3:
- primary domain: canonical ideal sheaves `I : Subobject 𝒪X` acting on
  `𝒪X`-modules in `RingedSpace.Modules X`, together with their tensor/internal-Hom
  torsion owners, local-generator multiplication maps, and stalkwise regularity formulations;
- sampled owner declarations of the same kind:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `idealTensorAction`,
  `IsIdealTorsionFreeModule`,
  `SheafOfModules.localSectionMul`,
  `SheafOfModules.annihilator`,
  `RingedSpace.moduleStalkHom`,
  `RingedSpace.unitStalkLinearMap`;
- best owner abstraction:
  `source-facing`: the five equivalent regularity conditions in Lemma `20.55.3`, with the first
    two stated through the actual torsion subsheaves `ℱ[I]` and `ℱ[I^n]`;
  `core/canonical`: the action morphism `idealTensorAction I ℱ : ℐ ⊗ ℱ ⟶ ℱ`, its mono predicate
    `IsIdealTorsionFreeModule I ℱ`, the induced internal-Hom transpose whose kernel owns `ℱ[I]`,
    and the iterated tensor-action analogue for `ℱ[I^n]`;
  `bridge/view`: the local-generator injectivity and stalk-generator regularity predicates, plus
    the stalk ideal `idealSheafStalkIdeal I x`.
- primitive data: the ideal sheaf `I : Subobject 𝒪X`;
- derived API: the source-facing torsion subsheaf owners `idealTorsionSubsheaf` and
  `idealPowerTorsionSubsheaf`, their bracket notation `ℱ[I]` and `ℱ[I^n]`, the local-generator
  injectivity predicate, the stalk regularity predicate, the stalk ideal, and the owner-level
  mono condition `IsIdealTorsionFreeModule I ℱ`.

The former local clauses `idealTorsionSubsheafVanishes` and
`idealPowerTorsionSubsheafVanishes` only exposed stalkwise bridge predicates. The chapter owner
for the third clause is already `idealTensorAction` / `IsIdealTorsionFreeModule`, so the first two
clauses should likewise be centered on the sheaf-level torsion owners obtained as kernels of the
canonical internal-Hom transposes of the tensor actions. -/

/-- The action map `(I : ModX) ⊗ ℱ ⟶ ℱ` induced by the ideal inclusion
`I.arrow : (I : ModX) ⟶ 𝒪X`. -/
noncomputable def idealTensorAction
    (I : Subobject 𝒪X) (ℱ : ModX) :
    tensorObj (I : ModX) ℱ ⟶ ℱ :=
  tensorHom I.arrow (𝟙 ℱ) ≫
    ((SheafOfModules.unitIsoTensorUnit ▷ᵢ ℱ) ≪≫ λ_ ℱ).hom

/-- An `𝒪X`-module is `I`-torsion free when multiplication by `I` embeds
`(I : ModX) ⊗ ℱ` into `ℱ`. -/
class IsIdealTorsionFreeModule
    (I : Subobject 𝒪X) (ℱ : ModX) : Prop where
  /-- The canonical action map `(I : ModX) ⊗ ℱ ⟶ ℱ` is monic. -/
  mono : Mono (idealTensorAction I ℱ)

attribute [instance] IsIdealTorsionFreeModule.mono

section IdealTorsionSubsheafDefs

variable [MonoidalClosed (RingedSpace.Modules X)]

private def idealTensorPowerObj
    (I : Subobject 𝒪X) : ℕ → ModX
  | 0 => (I : ModX)
  | n + 1 => tensorObj (I : ModX) (idealTensorPowerObj I n)

private def idealTensorPowerAction
    (I : Subobject 𝒪X) (ℱ : ModX) : ∀ n : ℕ, tensorObj (idealTensorPowerObj I n) ℱ ⟶ ℱ
  | 0 => idealTensorAction I ℱ
  | n + 1 =>
      (α_ (I : ModX) (idealTensorPowerObj I n) ℱ).hom ≫
        ((I : ModX) ◁ idealTensorPowerAction I ℱ n) ≫
        idealTensorAction I ℱ

private noncomputable def idealPowerActionAdjoint
    (I : Subobject 𝒪X) (ℱ : ModX) (n : ℕ+) :
    ℱ ⟶ (ihom (idealTensorPowerObj I ((n : ℕ) - 1))).obj ℱ :=
  MonoidalClosed.curry (idealTensorPowerAction I ℱ ((n : ℕ) - 1))

/-- The subsheaf `ℱ[I^n]` of sections annihilated by the `n`th power of `I`, realized as the
kernel of the canonical `n`-fold tensor-action adjoint. -/
noncomputable def idealPowerTorsionSubsheaf
    (I : Subobject 𝒪X) (ℱ : ModX) (n : ℕ+) : ModX :=
  Limits.kernel (idealPowerActionAdjoint I ℱ n)

/-- The canonical inclusion `ℱ[I^n] ⟶ ℱ`. -/
noncomputable def idealPowerTorsionSubsheafι
    (I : Subobject 𝒪X) (ℱ : ModX) (n : ℕ+) :
    idealPowerTorsionSubsheaf I ℱ n ⟶ ℱ :=
  Limits.kernel.ι (idealPowerActionAdjoint I ℱ n)

/-- The subsheaf `ℱ[I]` of sections annihilated by `I`. -/
noncomputable abbrev idealTorsionSubsheaf
    (I : Subobject 𝒪X) (ℱ : ModX) : ModX :=
  idealPowerTorsionSubsheaf I ℱ 1

/-- The canonical inclusion `ℱ[I] ⟶ ℱ`. -/
noncomputable abbrev idealTorsionSubsheafι
    (I : Subobject 𝒪X) (ℱ : ModX) :
    idealTorsionSubsheaf I ℱ ⟶ ℱ :=
  idealPowerTorsionSubsheafι I ℱ 1

namespace IdealSheafTorsion

/- Source-facing notation for the sheaf torsion owners `ℱ[I]` and `ℱ[I^n]`. -/
scoped notation:max ℱ:max "[" I:max "]" =>
  AlgebraicGeometry.RingedSpace.idealTorsionSubsheaf I ℱ
scoped notation:max ℱ:max "[" I:max "^" n:max "]" =>
  AlgebraicGeometry.RingedSpace.idealPowerTorsionSubsheaf I ℱ n

end IdealSheafTorsion

end IdealTorsionSubsheafDefs

open scoped IdealSheafTorsion

/-- On every neighbourhood where `I` is identified with a principal ideal generated by a local
section, the induced multiplication morphism on the restricted module sheaf is injective. -/
def localGeneratorActsInjectivelyOnNeighborhoods
    (I : Subobject 𝒪X) (ℱ : ModX) : Prop :=
  ∀ (U : Opens X)
    (e : SheafOfModules.over (I : ModX) U ≅ SheafOfModules.over 𝒪X U)
    (s : X.presheaf.obj (op U)),
      (e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
        I.arrow |_ U) →
      Mono (SheafOfModules.localSectionMul X.sheaf ℱ U s)

/-- The stalkwise nonzerodivisor condition for generators of
`idealSheafStalkIdeal I x ⊆ X.presheaf.stalk x`. -/
def stalkGeneratorActsRegularly
    (I : Subobject 𝒪X) (ℱ : ModX) : Prop :=
  ∀ (x : X) (f : X.presheaf.stalk x),
    (Ideal.span ({f} : Set (X.presheaf.stalk x)) = idealSheafStalkIdeal I x) →
      IsSMulRegular (RingedSpace.stalkModuleCat ℱ x) f

/-- Helper for Lemma 20.55.3: stalkwise regularity depends only on the principal ideal generated
by the chosen scalar. -/
private theorem isSMulRegular_iff_of_span_singleton_eq
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (f g : A)
    (hfg : Ideal.span ({f} : Set A) = Ideal.span ({g} : Set A)) :
    IsSMulRegular (ModuleCat.of A M) f ↔ IsSMulRegular (ModuleCat.of A M) g := by
  constructor
  · intro hf
    -- Proof comment: if `(f) = (g)`, then `f = g * a` for some `a`, so regularity of `f`
    -- forces regularity of the left factor `g`.
    rcases Ideal.span_singleton_le_span_singleton.mp hfg.le with ⟨a, rfl⟩
    exact (IsSMulRegular.mul_iff.mp hf).1
  · intro hg
    -- Proof comment: the reverse implication is symmetric after swapping the two generators.
    rcases Ideal.span_singleton_le_span_singleton.mp hfg.ge with ⟨a, rfl⟩
    exact (IsSMulRegular.mul_iff.mp hg).1

omit monoidalModX in
/-- Helper for Lemma 20.55.3: on a smaller open `W ⟶ U`, the local multiplication map induced by
the section `s : X.presheaf.obj (op U)` acts on germs exactly by multiplication with the ambient
germ of `s`. -/
private theorem localSectionMul_app_germ_eq_smul_germ
    (U W : Opens X) (i : W ⟶ U) (y : X) (hy : y ∈ W)
    (s : X.presheaf.obj (op U)) (t : ℱ.val.obj (op W)) :
    TopCat.Presheaf.germ ℱ.val.presheaf W y hy
        (((SheafOfModules.localSectionMul X.sheaf ℱ U s).val.app
          (op (Over.mk i))) t) =
      (X.presheaf.germ U y (i.le hy) s) •
        TopCat.Presheaf.germ ℱ.val.presheaf W y hy t := by
  -- Proof comment: evaluate `localSectionMul` on the object `W ⟶ U`, where it is literal scalar
  -- multiplication by the restricted section, and then move to germs with `germ_smul`.
  calc
    TopCat.Presheaf.germ ℱ.val.presheaf W y hy
        (((SheafOfModules.localSectionMul X.sheaf ℱ U s).val.app
          (op (Over.mk i))) t) =
      TopCat.Presheaf.germ ℱ.val.presheaf W y hy ((X.presheaf.map i.op s) • t) := by
        rfl
    _ =
        (X.presheaf.germ W y hy (X.presheaf.map i.op s)) •
          TopCat.Presheaf.germ ℱ.val.presheaf W y hy t := by
        -- Proof comment: germs are linear, so the germ of a scalar multiple is the scalar germ
        -- times the germ of the section.
        simpa using
          (PresheafOfModules.germ_smul ℱ.val y W hy (X.presheaf.map i.op s) t)
    _ =
        (X.presheaf.germ U y (i.le hy) s) •
          TopCat.Presheaf.germ ℱ.val.presheaf W y hy t := by
        -- Proof comment: the germ of the restricted section is the ambient germ of `s`.
        rw [TopCat.Presheaf.germ_res_apply X.presheaf i y hy s]

omit monoidalModX in
/-- Helper for Lemma 20.55.3: on a principal chart, the stalk map of the ideal inclusion sends a
germ from the ideal sheaf to the chart generator germ times the germ of its coefficient in the
restricted structure sheaf. -/
private theorem idealSheafStalkToRing_chart_germ_eq_mul
    (U : Opens X)
    (e : SheafOfModules.over (I : ModX) U ≅ SheafOfModules.over 𝒪X U)
    (s : X.presheaf.obj (op U))
    (he :
      e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
        I.arrow |_ U)
    (W : Opens X) (i : W ⟶ U) (x : X) (hx : x ∈ W)
    (t : (I : ModX).val.obj (op W)) :
    idealSheafStalkToRing I x
        (TopCat.Presheaf.germ (I : ModX).val.presheaf W x hx t) =
      (X.presheaf.germ U x (i.le hx) s) *
        X.presheaf.germ W x hx
          (SheafOfModules.unitSectionToRingSection W
            (((e.hom).val.app (op (Over.mk i))) t)) := by
  let ι : (I : ModX) ⟶ 𝒪X := I.arrow
  have hstalk :
      RingedSpace.moduleStalkMap x ι
          (TopCat.Presheaf.germ (I : ModX).val.presheaf W x hx t) =
        TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx ((ι.val.app (op W)) t) := by
    -- Proof comment: first rewrite the ideal stalk map on a germ by the canonical stalk-map
    -- formula for a module morphism.
    simpa [RingedSpace.moduleStalkHom] using
      RingedSpace.moduleStalkMap_germ x ι W hx t
  have hcomp :
      ((e.hom).val.app (op (Over.mk i))) ≫
        ((SheafOfModules.localSectionMul X.sheaf 𝒪X U s).val.app (op (Over.mk i))) =
      ι.val.app (op W) := by
    -- Proof comment: evaluate the chart identity `e.hom ≫ localSectionMul = I.arrow |_ U`
    -- on the object `W ⟶ U`, where the restricted ideal inclusion is just the ambient section map
    -- on `W`.
    simpa using congrArg (fun f ↦ f.val.app (op (Over.mk i))) he
  have hsec :
      ((ι.val.app (op W)) t) =
        ((SheafOfModules.localSectionMul X.sheaf 𝒪X U s).val.app (op (Over.mk i)))
          (((e.hom).val.app (op (Over.mk i))) t) := by
    -- Proof comment: apply the sectionwise chart identity to the chosen ideal section `t`.
    have hcomp_apply := congrArg (fun g ↦ g t) hcomp
    simpa using hcomp_apply.symm
  calc
    idealSheafStalkToRing I x
        (TopCat.Presheaf.germ (I : ModX).val.presheaf W x hx t) =
      (RingedSpace.unitStalkLinearMap x).hom
        (TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx ((ι.val.app (op W)) t)) := by
          change
            (RingedSpace.unitStalkLinearMap x).hom
              (RingedSpace.moduleStalkMap x ι
                (TopCat.Presheaf.germ (I : ModX).val.presheaf W x hx t)) =
              (RingedSpace.unitStalkLinearMap x).hom
                (TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx
                  ((ι.val.app (op W)) t))
          rw [hstalk]
    _ =
      X.presheaf.germ W x hx
        (SheafOfModules.unitSectionToRingSection W ((ι.val.app (op W)) t)) := by
          simpa using
            SheafOfModules.unitStalkLinearMap_germ x W hx ((ι.val.app (op W)) t)
    _ =
      X.presheaf.germ W x hx
        (SheafOfModules.unitSectionToRingSection W
          (((SheafOfModules.localSectionMul X.sheaf 𝒪X U s).val.app (op (Over.mk i)))
            (((e.hom).val.app (op (Over.mk i))) t))) := by
          rw [hsec]
    _ =
      (RingedSpace.unitStalkLinearMap x).hom
        (TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx
          (((SheafOfModules.localSectionMul X.sheaf 𝒪X U s).val.app (op (Over.mk i)))
            (((e.hom).val.app (op (Over.mk i))) t))) := by
          symm
          simpa using
            SheafOfModules.unitStalkLinearMap_germ x W hx
              (((SheafOfModules.localSectionMul X.sheaf 𝒪X U s).val.app (op (Over.mk i)))
                (((e.hom).val.app (op (Over.mk i))) t))
    _ =
      (RingedSpace.unitStalkLinearMap x).hom
        ((X.presheaf.germ U x (i.le hx) s) •
          TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx
            (((e.hom).val.app (op (Over.mk i))) t)) := by
          rw [localSectionMul_app_germ_eq_smul_germ
            U W i x hx s (((e.hom).val.app (op (Over.mk i))) t)]
    _ =
      (X.presheaf.germ U x (i.le hx) s) *
        (RingedSpace.unitStalkLinearMap x).hom
          (TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx
            (((e.hom).val.app (op (Over.mk i))) t)) := by
          -- Proof comment: the unit-stalk comparison is linear over the stalk ring, so the scalar
          -- factor `germ s` can be pulled out as multiplication in the ring.
          simpa [smul_eq_mul] using
            (RingedSpace.unitStalkLinearMap x).hom.map_smul
              (X.presheaf.germ U x (i.le hx) s)
              (TopCat.Presheaf.germ (𝒪X : ModX).val.presheaf W x hx
                (((e.hom).val.app (op (Over.mk i))) t))
    _ =
      (X.presheaf.germ U x (i.le hx) s) *
        X.presheaf.germ W x hx
          (SheafOfModules.unitSectionToRingSection W
            (((e.hom).val.app (op (Over.mk i))) t)) := by
          congr 1
          simpa using
            SheafOfModules.unitStalkLinearMap_germ x W hx
              (((e.hom).val.app (op (Over.mk i))) t)

/-- Helper for Lemma 20.55.3: on a principal chart, the ambient stalk ideal is exactly the
principal ideal generated by the chart germ. -/
private theorem idealSheafStalkIdeal_chart_eq_span_germ
    (U : Opens X)
    (e : SheafOfModules.over (I : ModX) U ≅ SheafOfModules.over 𝒪X U)
    (s : X.presheaf.obj (op U))
    (he :
      e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
        I.arrow |_ U)
    (x : X) (hx : x ∈ U) :
    idealSheafStalkIdeal I x =
      Ideal.span ({X.presheaf.germ U x hx s} : Set (X.presheaf.stalk x)) := by
  sorry
  /-
  apply le_antisymm
  · intro r hr
    rcases hr with ⟨m, rfl⟩
    obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.germ_exist (I : ModX).val.presheaf x m
    let W : Opens X := V ⊓ U
    let hxW : x ∈ W := ⟨hxV, hx⟩
    let iWV : W ⟶ V := homOfLE inf_le_left
    let iWU : W ⟶ U := homOfLE inf_le_right
    let tW : (I : ModX).val.obj (op W) := (I : ModX).val.map iWV.op t
    have hm :
        m = TopCat.Presheaf.germ (I : ModX).val.presheaf W x hxW tW := by
      -- Proof comment: shrink the chosen stalk representative to `W = V ∩ U` so the chart data
      -- applies to the same germ.
      calc
        m = TopCat.Presheaf.germ (I : ModX).val.presheaf V x hxV t := ht.symm
        _ = TopCat.Presheaf.germ (I : ModX).val.presheaf W x hxW tW := by
          rw [show tW = (I : ModX).val.map iWV.op t by rfl]
          symm
          exact TopCat.Presheaf.germ_res_apply (I : ModX).val.presheaf iWV x hxW t
    rw [hm]
    -- Proof comment: every element of the image ideal is `germ s` times a coefficient, so it
    -- belongs to the principal ideal generated by `germ s`.
    rw [idealSheafStalkToRing_chart_germ_eq_mul U e s he W iWU x hxW tW]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (by simp : X.presheaf.germ U x hx s ∈ ({X.presheaf.germ U x hx s} :
        Set (X.presheaf.stalk x))))
  · refine (Ideal.span_singleton_le_iff_mem _).2 ?_
    let oneU :
        (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) : ModX).val.obj
          (op U) :=
      show
          (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) : ModX).val.obj
            (op U) from
        (1 : X.presheaf.obj (op U))
    let tU : (I : ModX).val.obj (op U) :=
      ((e.inv).val.app (op (Over.mk (𝟙 U))))
        oneU
    have htU :
        ((e.hom).val.app (op (Over.mk (𝟙 U)))) tU = oneU := by
      -- Proof comment: take the inverse-image of the unit section under the chart isomorphism.
      have hcomp :
          ((e.inv).val.app (op (Over.mk (𝟙 U)))) ≫
            ((e.hom).val.app (op (Over.mk (𝟙 U)))) =
              𝟙 ((𝒪X : ModX).val.obj (op U)) := by
        exact (e.app (op (Over.mk (𝟙 U)))).inv_hom_id
      simpa [tU] using ConcreteCategory.congr_hom hcomp oneU
    have hgen' :
        idealSheafStalkToRing I x
            (TopCat.Presheaf.germ (I : ModX).val.presheaf U x hx tU) =
          X.presheaf.germ U x hx s := by
      -- Proof comment: apply the germ-level factorization to the preimage of `1`; the coefficient
      -- becomes the unit in the stalk ring.
      calc
        idealSheafStalkToRing I x
            (TopCat.Presheaf.germ (I : ModX).val.presheaf U x hx tU) =
          (X.presheaf.germ U x hx s) *
            X.presheaf.germ U x hx
              (SheafOfModules.unitSectionToRingSection U
                (((e.hom).val.app (op (Over.mk (𝟙 U)))) tU)) := by
                  exact idealSheafStalkToRing_chart_germ_eq_mul
                    U e s he U (𝟙 U) x hx tU
        _ =
          (X.presheaf.germ U x hx s) *
            X.presheaf.germ U x hx (1 : X.presheaf.obj (op U)) := by
                rw [show
                    SheafOfModules.unitSectionToRingSection U
                        (((e.hom).val.app (op (Over.mk (𝟙 U)))) tU) =
                      (1 : X.presheaf.obj (op U)) by
                      simpa [oneU, SheafOfModules.unitSectionToRingSection] using
                        congrArg (SheafOfModules.unitSectionToRingSection U) htU]
        _ = (X.presheaf.germ U x hx s) *
            (ConcreteCategory.hom (X.presheaf.germ U x hx)) 1 := by
          rfl
        _ = (X.presheaf.germ U x hx s) * 1 := by
          rw [map_one]
        _ = X.presheaf.germ U x hx s := by simp
    -- Proof comment: the generator itself lies in the image ideal, so the principal ideal it
    -- generates is contained in the ambient stalk ideal.
    exact LinearMap.mem_range.2 ⟨TopCat.Presheaf.germ (I : ModX).val.presheaf U x hx tU, hgen'⟩
  -/

omit monoidalModX in
/-- Helper for Lemma 20.55.3: if the restriction of `ℱ` is zero on some neighborhood of `x`,
then the stalk `ℱ_x` is zero. -/
private theorem stalk_isZero_of_local_isZero_over
    (ℱ : ModX) (x : X)
    (h : ∃ (U : Opens X), x ∈ U ∧ Limits.IsZero (ℱ.over U)) :
    Limits.IsZero (RingedSpace.stalkModuleCat ℱ x) := by
  rcases h with ⟨U, hxU, hU_zero⟩
  let F := ℱ.val.presheaf
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun m n ↦ ?_⟩
  -- Proof comment: represent each stalk element on a neighborhood meeting the zero restriction,
  -- then shrink to the intersection where every section vanishes.
  have hm_zero : m = 0 := by
    obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.germ_exist F x m
    let W : Opens X := V ⊓ U
    let xW : W := ⟨x, ⟨hxV, hxU⟩⟩
    let t : F.obj (op W) := F.map (homOfLE inf_le_left).op s
    let evalW :=
      SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op <| Over.mk (homOfLE inf_le_right : W ⟶ U))
    letI : evalW.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have hW_zero : Limits.IsZero (evalW.obj (ℱ.over U)) := Functor.map_isZero evalW hU_zero
    have hW_subsingleton : Subsingleton (F.obj (op W)) := by
      simpa [SheafOfModules.over, SheafOfModules.pushforward, SheafOfModules.evaluation, W] using
        (ModuleCat.isZero_iff_subsingleton.1 hW_zero)
    have ht_zero : t = 0 := hW_subsingleton.elim _ _
    calc
      m = TopCat.Presheaf.germ F V x hxV s := hs.symm
      _ = TopCat.Presheaf.germ F W x xW.2 t := by
        rw [show t = F.map (homOfLE inf_le_left).op s by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_left) x xW.2 s
      _ = 0 := by
        rw [ht_zero]
        change (TopCat.Presheaf.germ F W x xW.2).hom 0 = 0
        exact (TopCat.Presheaf.germ F W x xW.2).hom.map_zero
  have hn_zero : n = 0 := by
    obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.germ_exist F x n
    let W : Opens X := V ⊓ U
    let xW : W := ⟨x, ⟨hxV, hxU⟩⟩
    let t : F.obj (op W) := F.map (homOfLE inf_le_left).op s
    let evalW :=
      SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op <| Over.mk (homOfLE inf_le_right : W ⟶ U))
    letI : evalW.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have hW_zero : Limits.IsZero (evalW.obj (ℱ.over U)) := Functor.map_isZero evalW hU_zero
    have hW_subsingleton : Subsingleton (F.obj (op W)) := by
      simpa [SheafOfModules.over, SheafOfModules.pushforward, SheafOfModules.evaluation, W] using
        (ModuleCat.isZero_iff_subsingleton.1 hW_zero)
    have ht_zero : t = 0 := hW_subsingleton.elim _ _
    calc
      n = TopCat.Presheaf.germ F V x hxV s := hs.symm
      _ = TopCat.Presheaf.germ F W x xW.2 t := by
        rw [show t = F.map (homOfLE inf_le_left).op s by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_left) x xW.2 s
      _ = 0 := by
        rw [ht_zero]
        change (TopCat.Presheaf.germ F W x xW.2).hom 0 = 0
        exact (TopCat.Presheaf.germ F W x xW.2).hom.map_zero
  rw [hm_zero, hn_zero]

omit monoidalModX in
/-- Helper for Lemma 20.55.3: if every point has a neighborhood on which `ℱ` restricts to the
zero sheaf, then `ℱ` itself is zero. -/
private theorem isZero_of_local_zero_restrictions
    (ℱ : ModX)
    (h : ∀ x : X, ∃ (U : Opens X), x ∈ U ∧ Limits.IsZero (ℱ.over U)) :
    Limits.IsZero ℱ := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨ℱ.val.presheaf, ℱ.isSheaf⟩
  rw [Limits.IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  -- Proof comment: it is enough to show every section has zero germ at every point, since the
  -- underlying additive sheaf is separated.
  have hs_zero : s = 0 := by
    apply TopCat.Presheaf.section_ext F U.unop s 0
    intro x hx
    have hx_zero : Limits.IsZero (RingedSpace.stalkModuleCat ℱ x) :=
      stalk_isZero_of_local_isZero_over ℱ x (h x)
    have hx_subsingleton : Subsingleton (RingedSpace.stalkModuleCat ℱ x) :=
      ModuleCat.isZero_iff_subsingleton.1 hx_zero
    exact hx_subsingleton.elim _ _
  simpa [hs_zero]

omit monoidalModX in
/-- Helper for Lemma 20.55.3: if multiplication by a local generator is monic on the restricted
module sheaf over `U`, then the germ of that generator acts regularly on every stalk above `U`. -/
private theorem stalkwise_regular_of_mono_localSectionMul
    (U : Opens X) (s : X.presheaf.obj (op U))
    (hmono : Mono (SheafOfModules.localSectionMul X.sheaf ℱ U s)) :
    ∀ y : X, ∀ hy : y ∈ U,
      IsSMulRegular (RingedSpace.stalkModuleCat ℱ y) (X.presheaf.germ U y hy s) := by
  let φ := SheafOfModules.localSectionMul X.sheaf ℱ U s
  have hφval : Mono φ.val := (SheafOfModules.forget (X.ringCatSheaf.over U)).map_mono φ
  intro y hy
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro m hm
  let F := ℱ.val.presheaf
  -- Proof comment: represent the stalk element on some neighborhood of `y`, then shrink into `U`
  -- so that the monic local multiplication map is defined on that representative.
  obtain ⟨V, hyV, tV, htV⟩ := TopCat.Presheaf.germ_exist F y m
  let W : Opens X := V ⊓ U
  let hyW : y ∈ W := ⟨hyV, hy⟩
  let iWV : W ⟶ V := homOfLE inf_le_left
  let iWU : W ⟶ U := homOfLE inf_le_right
  let t : ℱ.val.obj (op W) := F.map iWV.op tV
  have hm_repr : m = TopCat.Presheaf.germ F W y hyW t := by
    -- Proof comment: the stalk class `m` can be rewritten using the restricted representative on
    -- the smaller neighborhood `W = V ∩ U`.
    calc
      m = TopCat.Presheaf.germ F V y hyV tV := htV.symm
      _ = TopCat.Presheaf.germ F W y hyW t := by
        rw [show t = F.map iWV.op tV by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply F iWV y hyW tV
  have hgerm_zero :
      TopCat.Presheaf.germ F W y hyW ((φ.val.app (op (Over.mk iWU))) t) = 0 := by
    -- Proof comment: the assumed vanishing `(germ s) • m = 0` is exactly the vanishing of the germ
    -- of the local multiplication map on the chosen representative.
    calc
      TopCat.Presheaf.germ F W y hyW ((φ.val.app (op (Over.mk iWU))) t) =
          (X.presheaf.germ U y hy s) • TopCat.Presheaf.germ F W y hyW t := by
            simpa [φ] using localSectionMul_app_germ_eq_smul_germ
              U W iWU y hyW s t
      _ = (X.presheaf.germ U y hy s) • m := by rw [hm_repr]
      _ = 0 := hm
  have hgerm_eq :
      TopCat.Presheaf.germ F W y hyW ((φ.val.app (op (Over.mk iWU))) t) =
        TopCat.Presheaf.germ F W y hyW (0 : F.obj (op W)) := by
    simpa using hgerm_zero
  obtain ⟨Z, hyZ, iZW₁, iZW₂, hsec⟩ :=
    TopCat.Presheaf.germ_eq F y hyW hyW ((φ.val.app (op (Over.mk iWU))) t) 0 hgerm_eq
  have hφ_app_inj :
      Function.Injective (φ.val.app (op (Over.mk (iZW₁ ≫ iWU)))) := by
    letI : Mono φ.val := hφval
    simpa using PresheafOfModules.injective_of_mono φ.val (op (Over.mk (iZW₁ ≫ iWU)))
  have htZ_zero : F.map iZW₁.op t = 0 := by
    -- Proof comment: equality of germs gives a smaller neighborhood where the multiplied section
    -- vanishes; monicity of the section map on that neighborhood forces the restricted section to
    -- vanish there as well.
    change (((ℱ.val.map iZW₁.op).hom t : ℱ.val.obj (op Z))) = 0
    have hmul_zero :
        ((φ.val.app (op (Over.mk (iZW₁ ≫ iWU)))).hom
            (((ℱ.val.map iZW₁.op).hom t : ℱ.val.obj (op Z)))) = 0 := by
      let fOver : Over.mk (iZW₁ ≫ iWU) ⟶ Over.mk iWU :=
        Over.homMk iZW₁ (by simp)
      have hnat :
          (((ℱ.val.map iZW₁.op).hom
                (((φ.val.app (op (Over.mk iWU)))).hom t) : ℱ.val.obj (op Z))) =
            ((φ.val.app (op (Over.mk (iZW₁ ≫ iWU)))).hom
              (((ℱ.val.map iZW₁.op).hom t : ℱ.val.obj (op Z)))) := by
        exact ConcreteCategory.congr_hom ((φ.val.naturality fOver.op).symm) t
      rw [← hnat]
      simpa using hsec
    apply hφ_app_inj
    rw [hmul_zero]
    exact (φ.val.app (op (Over.mk (iZW₁ ≫ iWU)))).hom.map_zero.symm
  -- Proof comment: once the restricted representative is zero on a smaller neighborhood, its germ
  -- and hence the original stalk element vanish.
  calc
    m = TopCat.Presheaf.germ F W y hyW t := hm_repr
    _ = TopCat.Presheaf.germ F Z y hyZ (F.map iZW₁.op t) := by
      symm
      exact TopCat.Presheaf.germ_res_apply F iZW₁ y hyZ t
    _ = 0 := by
      rw [htZ_zero]
      change (TopCat.Presheaf.germ F Z y hyZ).hom 0 = 0
      exact (TopCat.Presheaf.germ F Z y hyZ).hom.map_zero

omit monoidalModX in
/-- Helper for Lemma 20.55.3: stalkwise regularity of a local generator on `U` forces the
restricted multiplication morphism to be monic. -/
private theorem mono_localSectionMul_of_stalkwise_regular
    (U : Opens X) (s : X.presheaf.obj (op U))
    (hreg : ∀ y : X, ∀ hy : y ∈ U,
      IsSMulRegular (RingedSpace.stalkModuleCat ℱ y) (X.presheaf.germ U y hy s)) :
    Mono (SheafOfModules.localSectionMul X.sheaf ℱ U s) := by
  let φ := SheafOfModules.localSectionMul X.sheaf ℱ U s
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨ℱ.val.presheaf, ℱ.isSheaf⟩
  have hφ_app_inj : ∀ V : Over U, Function.Injective (φ.val.app (op V)) := by
    intro V t₁ t₂ ht
    -- Proof comment: equality of the multiplied sections can be tested on germs; on each stalk,
    -- regularity of the generator germ makes scalar multiplication injective.
    apply TopCat.Presheaf.section_ext F V.left t₁ t₂
    intro y hy
    have hmul_eq :
        (X.presheaf.germ U y (V.hom.le hy) s) •
            TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy t₁ =
          (X.presheaf.germ U y (V.hom.le hy) s) •
            TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy t₂ := by
      calc
        (X.presheaf.germ U y (V.hom.le hy) s) •
            TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy t₁ =
            TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy ((φ.val.app (op V)) t₁) := by
              symm
              simpa [φ] using
                localSectionMul_app_germ_eq_smul_germ
                  U V.left V.hom y hy s t₁
        _ = TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy ((φ.val.app (op V)) t₂) := by
              exact congrArg (TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy) ht
        _ =
            (X.presheaf.germ U y (V.hom.le hy) s) •
              TopCat.Presheaf.germ ℱ.val.presheaf V.left y hy t₂ := by
              simpa [φ] using
                localSectionMul_app_germ_eq_smul_germ
                  U V.left V.hom y hy s t₂
    have hreg_y :
        Function.Injective
          (fun m : RingedSpace.stalkModuleCat ℱ y ↦
            (X.presheaf.germ U y (V.hom.le hy) s) • m) := by
      simpa [IsSMulRegular] using hreg y (V.hom.le hy)
    exact hreg_y hmul_eq
  refine ⟨?_⟩
  intro 𝒢 g h hcomp
  -- Proof comment: equality after composing with `φ` can be tested objectwise on every open over
  -- `U`, where `hφ_app_inj` lets us cancel multiplication by the regular generator.
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext t
  apply hφ_app_inj V.unop
  simpa using congrArg (fun k ↦ ((k.val.app V).hom t)) hcomp

omit monoidalModX in
/-- Helper for Lemma 20.55.3: local injectivity of multiplication by a generator is equivalent to
stalkwise regularity of the corresponding germ. -/
private theorem mono_localSectionMul_iff_stalkwise_regular
    (U : Opens X) (s : X.presheaf.obj (op U)) :
    Mono (SheafOfModules.localSectionMul X.sheaf ℱ U s) ↔
      ∀ y : X, ∀ hy : y ∈ U,
        IsSMulRegular (RingedSpace.stalkModuleCat ℱ y) (X.presheaf.germ U y hy s) := by
  constructor
  · -- Proof comment: evaluate the monomorphism on germs to get regularity on every stalk.
    exact stalkwise_regular_of_mono_localSectionMul U s
  · -- Proof comment: conversely, stalkwise regularity forces sectionwise injectivity on every
    -- smaller open over `U`, so the local multiplication morphism is monic.
    exact mono_localSectionMul_of_stalkwise_regular U s

omit monoidalModX in
/-- Helper for Lemma 20.55.3: clause `(4)` is exactly the principal-chart version of stalkwise
regularity for the chosen generator. -/
private theorem localGeneratorActsInjectivelyOnNeighborhoods_iff_chartwise_regular
    (I : Subobject 𝒪X) (ℱ : ModX) :
    localGeneratorActsInjectivelyOnNeighborhoods I ℱ ↔
      ∀ (U : Opens X)
        (e : SheafOfModules.over (I : ModX) U ≅ SheafOfModules.over 𝒪X U)
        (s : X.presheaf.obj (op U)),
          (e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
            I.arrow |_ U) →
          ∀ y : X, ∀ hy : y ∈ U,
            IsSMulRegular (RingedSpace.stalkModuleCat ℱ y) (X.presheaf.germ U y hy s) := by
  constructor
  · intro h U e s he
    -- Proof comment: unfold clause `(4)` on the chosen chart, then apply the local `(4) ↔ (5)`
    -- bridge for multiplication by the chart generator.
    exact (mono_localSectionMul_iff_stalkwise_regular U s).1 (h U e s he)
  · intro h U e s he
    -- Proof comment: the chartwise stalk-regularity formulation immediately reconstructs the
    -- monomorphism required in clause `(4)`.
    exact (mono_localSectionMul_iff_stalkwise_regular U s).2 (h U e s he)

omit monoidalModX in
/-- Helper for Lemma 20.55.3: once the stalk ideal on every principal chart is identified with
the principal ideal generated by the chart germ, clauses `(4)` and `(5)` become equivalent. -/
private theorem localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly_of_chartwise_stalkIdeal_span
    (I : Subobject 𝒪X) (ℱ : ModX)
    [hprincipal : SatisfiesLocallyPrincipalRegularIdealCondition I]
    (hspan :
      ∀ (U : Opens X)
        (e : SheafOfModules.over (I : ModX) U ≅ SheafOfModules.over 𝒪X U)
        (s : X.presheaf.obj (op U)),
          (e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
            I.arrow |_ U) →
        ∀ (x : X) (hx : x ∈ U),
          idealSheafStalkIdeal I x =
            Ideal.span ({X.presheaf.germ U x hx s} : Set (X.presheaf.stalk x))) :
    localGeneratorActsInjectivelyOnNeighborhoods I ℱ ↔
      stalkGeneratorActsRegularly I ℱ := by
  constructor
  · intro hlocal x f hf
    obtain ⟨U, hxU, e, s, he⟩ :=
      hprincipal.exists_chart x
    have hchart :
        ∀ y : X, ∀ hy : y ∈ U,
          IsSMulRegular (RingedSpace.stalkModuleCat ℱ y) (X.presheaf.germ U y hy s) :=
      (localGeneratorActsInjectivelyOnNeighborhoods_iff_chartwise_regular I ℱ).1 hlocal U e s he
    have hs_regular :
        IsSMulRegular (RingedSpace.stalkModuleCat ℱ x) (X.presheaf.germ U x hxU s) :=
      hchart x hxU
    have hfg :
        Ideal.span ({f} : Set (X.presheaf.stalk x)) =
          Ideal.span ({X.presheaf.germ U x hxU s} : Set (X.presheaf.stalk x)) :=
      hf.trans (hspan U e s he x hxU)
    -- Proof comment: on the chosen principal chart, clause `(4)` yields regularity of the chart
    -- germ; the span equality transports regularity to any generator of the same stalk ideal.
    exact (isSMulRegular_iff_of_span_singleton_eq
      f (X.presheaf.germ U x hxU s) hfg).2 hs_regular
  · intro hstalk U e s he
    refine (mono_localSectionMul_iff_stalkwise_regular U s).2 ?_
    intro y hy
    -- Proof comment: clause `(5)` applied to the chart germ gives the stalkwise regularity needed
    -- for the local multiplication map once the stalk ideal is identified with its principal span.
    exact hstalk y (X.presheaf.germ U y hy s) (hspan U e s he y hy).symm

/-- In Situation `20.55.2`, injectivity of multiplication by local generators on principal charts
is equivalent to stalkwise regularity for generators of the stalk ideal. -/
private theorem localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly_aux
    (I : Subobject 𝒪X) (ℱ : ModX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I] :
    localGeneratorActsInjectivelyOnNeighborhoods I ℱ ↔
      stalkGeneratorActsRegularly I ℱ := by
  -- Proof comment: feed the chartwise stalk-ideal/span identity from the new principal-chart
  -- computation into the abstract `(4) ↔ (5)` bridge proved just above.
  refine
    localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly_of_chartwise_stalkIdeal_span
      I ℱ ?_
  intro U e s he x hx
  exact idealSheafStalkIdeal_chart_eq_span_germ U e s he x hx

/-- Helper for Lemma 20.55.3: the remaining source-faithful core is the four-clause TFAE relating
the torsion subsheaves, the tensor action, and injectivity of multiplication by local generators. -/
private theorem locallyPrincipalRegularIdeal_torsion_tfae_up_to_local_generators
    (I : Subobject 𝒪X) (ℱ : ModX)
    [MonoidalClosed (RingedSpace.Modules X)]
    [SatisfiesLocallyPrincipalRegularIdealCondition I] :
    ([ Limits.IsZero ℱ[I]
      , ∀ n : ℕ+, Limits.IsZero ℱ[I^n]
      , IsIdealTorsionFreeModule I ℱ
      , localGeneratorActsInjectivelyOnNeighborhoods I ℱ
      ] : List Prop).TFAE := by
  -- Route correction: the global `(4) ↔ (5)` bridge is now completely separated, so the only
  -- unresolved source-faithful content is the four-clause core comparing torsion kernels,
  -- `idealTensorAction`, and principal-chart multiplication.
  -- TODO: prove the chartwise tensor-action comparison and the local description of `ℱ[I^n]` as
  -- the kernel of multiplication by the chart generator powers, then assemble
  -- `(1) → (4) → (2) → (1)` together with the chartwise `(3) ↔ (4)` bridge.
  sorry

-- Proof sketch: this is the sheaf-theoretic version of Lemma `15.89.3`, applied stalkwise and
-- then glued using the locally principal regular ideal presentations from Situation `20.55.2`.
-- The principal-local clause identifies the tensor map of `I.arrow` with multiplication by a local
-- generator, while the stalk clause is the usual module-theoretic nonzerodivisor condition.
/-- Lemma 20.55.3: in Situation `20.55.2`, for `ℱ : ModX`, the following are equivalent:
`ℱ[I]` is zero, all `ℱ[I^n]` for `n ≥ 1` are zero, the canonical action map
`idealTensorAction I ℱ : (I : ModX) ⊗ ℱ ⟶ ℱ` is injective, multiplication by every local
generator of `I` is injective on the corresponding restriction of `ℱ`, and every generator of
`idealSheafStalkIdeal I x` acts as a nonzerodivisor on `RingedSpace.stalkModuleCat ℱ x`. -/
@[stacks 0GT5]
theorem locallyPrincipalRegularIdeal_torsion_tfae
    (I : Subobject 𝒪X) (ℱ : ModX)
    [MonoidalClosed (RingedSpace.Modules X)]
    [SatisfiesLocallyPrincipalRegularIdealCondition I] :
    ([ Limits.IsZero ℱ[I]
      , ∀ n : ℕ+, Limits.IsZero ℱ[I^n]
      , IsIdealTorsionFreeModule I ℱ
      , localGeneratorActsInjectivelyOnNeighborhoods I ℱ
      , stalkGeneratorActsRegularly I ℱ
      ] : List Prop).TFAE :=
  by
  have hcore :
      ([ Limits.IsZero ℱ[I]
        , ∀ n : ℕ+, Limits.IsZero ℱ[I^n]
        , IsIdealTorsionFreeModule I ℱ
        , localGeneratorActsInjectivelyOnNeighborhoods I ℱ
        ] : List Prop).TFAE :=
    locallyPrincipalRegularIdeal_torsion_tfae_up_to_local_generators I ℱ
  have h45 :
      localGeneratorActsInjectivelyOnNeighborhoods I ℱ ↔
        stalkGeneratorActsRegularly I ℱ :=
    localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly_aux I ℱ
  -- Proof comment: the only remaining unresolved content is the four-clause source-faithful core;
  -- once that is available, the already-proved global `(4) ↔ (5)` bridge extends it to the full
  -- five-way TFAE.
  tfae_have 1 → 2 := by
    -- Proof comment: read the first implication off the four-clause core.
    intro h1
    exact (hcore.out 0 1 (by simp) (by simp)).1 h1
  tfae_have 2 → 3 := by
    -- Proof comment: read the second implication off the four-clause core.
    intro h2
    exact (hcore.out 1 2 (by simp) (by simp)).1 h2
  tfae_have 3 → 4 := by
    -- Proof comment: the tensor-action clause still feeds the local-generator clause through the
    -- same core statement.
    intro h3
    exact (hcore.out 2 3 (by simp) (by simp)).1 h3
  tfae_have 4 → 5 := by
    -- Proof comment: this is the closed global bridge from local injectivity to stalkwise
    -- regularity.
    intro h4
    exact h45.1 h4
  tfae_have 5 → 1 := by
    -- Proof comment: go back across `(5) ↔ (4)` and then close the cycle using the four-clause
    -- core.
    intro h5
    exact (hcore.out 3 0 (by simp) (by simp)).1 (h45.2 h5)
  tfae_finish

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace

noncomputable section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" =>
  (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) : ModX)

/-- In Situation `20.55.2`, injectivity of multiplication by local generators on principal charts
is equivalent to stalkwise regularity for generators of the stalk ideal. -/
theorem localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly
    (I : Subobject 𝒪X) (ℱ : ModX)
    [SatisfiesLocallyPrincipalRegularIdealCondition I] :
    localGeneratorActsInjectivelyOnNeighborhoods I ℱ ↔
      stalkGeneratorActsRegularly I ℱ :=
  localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly_aux I ℱ

/-- In Situation `20.55.2`, local injectivity of multiplication by generators on principal charts
implies stalkwise regularity for generators of the stalk ideal. -/
theorem localGeneratorActsInjectivelyOnNeighborhoods.stalkGeneratorActsRegularly
    {I : Subobject 𝒪X} {ℱ : ModX}
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (h : localGeneratorActsInjectivelyOnNeighborhoods I ℱ) :
    stalkGeneratorActsRegularly I ℱ :=
  (localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly I ℱ).1 h

/-- In Situation `20.55.2`, stalkwise regularity for generators of the stalk ideal implies local
injectivity of multiplication by generators on principal charts. -/
theorem stalkGeneratorActsRegularly.localGeneratorActsInjectivelyOnNeighborhoods
    {I : Subobject 𝒪X} {ℱ : ModX}
    [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (h : stalkGeneratorActsRegularly I ℱ) :
    localGeneratorActsInjectivelyOnNeighborhoods I ℱ :=
  (localGeneratorActsInjectivelyOnNeighborhoods_iff_stalkGeneratorActsRegularly I ℱ).2 h

end

end AlgebraicGeometry.RingedSpace
