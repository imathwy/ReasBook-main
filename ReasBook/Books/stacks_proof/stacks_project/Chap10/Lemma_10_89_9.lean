import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Proposition_10_89_3
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u v w x

namespace Module

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Helper for Chap10 Lemma 10 89 9: the transition map in the underlying module system of a
preorder-indexed `ModuleCat` diagram. -/
private abbrev moduleSystemMap
    (F : I ⥤ ModuleCat.{max v w} R) (i j : I) (hij : i ≤ j) :
    F.obj i →ₗ[R] F.obj j :=
  (F.map (homOfLE hij)).hom

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the module-system transition at `i ≤ i` is the identity. -/
private lemma moduleSystemMap_self
    (F : I ⥤ ModuleCat.{max v w} R) (i : I) (m : F.obj i) :
    moduleSystemMap (R := R) F i i (le_refl i) m = m := by
  -- The preorder morphism `homOfLE (le_refl i)` is the identity, so functoriality gives the claim.
  change ((F.map (𝟙 i)).hom) m = m
  exact congr(($((F.map_id i)) m))

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the module-system transitions compose as expected. -/
private lemma moduleSystemMap_map_map
    (F : I ⥤ ModuleCat.{max v w} R) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (m : F.obj i) :
    moduleSystemMap (R := R) F j k hjk (moduleSystemMap (R := R) F i j hij m) =
      moduleSystemMap (R := R) F i k (hij.trans hjk) m := by
  -- This is the linear-map form of `F.map_comp`, with proof-irrelevance for preorder morphisms.
  change ((F.map (homOfLE hjk)).hom) (((F.map (homOfLE hij)).hom) m) =
    ((F.map (homOfLE (hij.trans hjk))).hom) m
  simpa using congr(($((F.map_comp (homOfLE hij) (homOfLE hjk)).symm) m))

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the directed-system composition law in mathlib's argument
order. -/
private lemma moduleSystemMap_directed_map_map
    (F : I ⥤ ModuleCat.{max v w} R) {k j i : I}
    (hij : i ≤ j) (hjk : j ≤ k) (m : F.obj i) :
    moduleSystemMap (R := R) F j k hjk (moduleSystemMap (R := R) F i j hij m) =
      moduleSystemMap (R := R) F i k (hij.trans hjk) m := by
  -- This is just the composition lemma with the binder order expected by `DirectedSystem`.
  exact moduleSystemMap_map_map (R := R) F hij hjk m

/-- Helper for Chap10 Lemma 10 89 9: the underlying module system of `F` is a directed system. -/
private instance moduleSystem_directedSystem
    (F : I ⥤ ModuleCat.{max v w} R) :
    DirectedSystem (fun i ↦ (F.obj i : Type (max v w)))
      (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) where
  map_self := moduleSystemMap_self (R := R) F
  map_map := fun {k j i} hij hjk x =>
    moduleSystemMap_directed_map_map (R := R) (F := F) (i := i) (j := j) (k := k)
      hij hjk x

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the quotient-model direct-limit cocone is natural over `F`. -/
private lemma moduleDirectLimitCocone_naturality
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) {i j : I} (f : i ⟶ j) :
    F.map f ≫ ModuleCat.ofHom
        (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) j) =
      ModuleCat.ofHom
        (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i) := by
  -- The direct-limit relation identifies a stage element with its image along any transition.
  apply ModuleCat.hom_ext
  ext m
  simpa [moduleSystemMap, homOfLE_leOfHom f] using
    Module.DirectLimit.of_f (R := R) (ι := I)
      (G := fun i ↦ (F.obj i : Type (max v w)))
      (f := fun i j hij ↦ moduleSystemMap (R := R) F i j hij)
      (hij := leOfHom f) (x := m)

/-- Helper for Chap10 Lemma 10 89 9: the quotient-model direct limit is a cocone over `F`. -/
private noncomputable def moduleDirectLimitCocone
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) : Cocone F where
  pt := ModuleCat.of R
    (Module.DirectLimit (fun i ↦ (F.obj i : Type (max v w)))
      (fun i j hij ↦ moduleSystemMap (R := R) F i j hij))
  ι :=
    { app := fun i => ModuleCat.ofHom
        (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i)
      naturality := fun _ _ f => moduleDirectLimitCocone_naturality (R := R) F f }

/-- Helper for Chap10 Lemma 10 89 9: the chosen colimit maps to the quotient-model direct
limit. -/
private noncomputable def colimitToModuleDirectLimit
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) :
    (colimit F : ModuleCat.{max v w} R) →ₗ[R]
      Module.DirectLimit (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) :=
  (colimit.desc F (moduleDirectLimitCocone (R := R) F)).hom

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the map from the chosen colimit to the quotient-model direct
limit sends each categorical stage leg to the quotient stage class. -/
private lemma colimitToModuleDirectLimit_ι
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) (i : I) :
    (colimitToModuleDirectLimit (R := R) F).comp (colimit.ι F i).hom =
      Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i := by
  -- This is the defining computation rule for `colimit.desc` applied to the direct-limit cocone.
  ext m
  exact DFunLike.congr_fun
    (ModuleCat.hom_ext_iff.mp (colimit.ι_desc (moduleDirectLimitCocone (R := R) F) i)) m

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the quotient-model direct limit maps back to the chosen
categorical colimit. -/
private lemma moduleDirectLimitToColimit_compat
    (F : I ⥤ ModuleCat.{max v w} R) (i j : I) (hij : i ≤ j) (m : F.obj i) :
    (colimit.ι F j).hom (moduleSystemMap (R := R) F i j hij m) =
      (colimit.ι F i).hom m := by
  -- Naturality of the categorical colimit cocone identifies a stage element with its transition.
  have hcat : F.map (homOfLE hij) ≫ colimit.ι F j = colimit.ι F i := by
    simp
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hcat) m

/-- Helper for Chap10 Lemma 10 89 9: the quotient-model direct limit maps back to the chosen
categorical colimit. -/
private noncomputable def moduleDirectLimitToColimit
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) :
    Module.DirectLimit (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) →ₗ[R]
      (colimit F : ModuleCat.{max v w} R) :=
  Module.DirectLimit.lift R I (fun i ↦ (F.obj i : Type (max v w)))
    (fun i j hij ↦ moduleSystemMap (R := R) F i j hij)
    (fun i ↦ (colimit.ι F i).hom)
    (moduleDirectLimitToColimit_compat (R := R) F)

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the quotient-model map back to the chosen colimit computes on
stage classes as the categorical colimit leg. -/
private lemma moduleDirectLimitToColimit_of
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) (i : I) (m : F.obj i) :
    moduleDirectLimitToColimit (R := R) F
        (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i m) =
      (colimit.ι F i).hom m := by
  -- This is the quotient-model direct-limit lift computation rule.
  simpa [moduleDirectLimitToColimit] using
    Module.DirectLimit.lift_of (R := R) (ι := I)
      (G := fun i ↦ (F.obj i : Type (max v w)))
      (f := fun i j hij ↦ moduleSystemMap (R := R) F i j hij)
      (g := fun i ↦ (colimit.ι F i).hom)
      (Hg := moduleDirectLimitToColimit_compat (R := R) F)
      (i := i) (x := m)

/-- Helper for Chap10 Lemma 10 89 9: composing from the quotient-model direct limit to the chosen
colimit and back is the identity. -/
private lemma colimitToModuleDirectLimit_comp_moduleDirectLimitToColimit
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) :
    (colimitToModuleDirectLimit (R := R) F).comp
      (moduleDirectLimitToColimit (R := R) F) = LinearMap.id := by
  -- Check the equality on quotient-model direct-limit generators.
  apply LinearMap.ext
  intro y
  induction y using Module.DirectLimit.induction_on with
  | ih i m =>
      calc
        colimitToModuleDirectLimit (R := R) F
            (moduleDirectLimitToColimit (R := R) F
              (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
                (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i m))
            = colimitToModuleDirectLimit (R := R) F ((colimit.ι F i).hom m) := by
                rw [moduleDirectLimitToColimit_of]
        _ = Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
              (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i m := by
                exact DFunLike.congr_fun (colimitToModuleDirectLimit_ι (R := R) F i) m

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: composing from the chosen colimit to the quotient-model
direct limit and back is the identity. -/
private lemma moduleDirectLimitToColimit_comp_colimitToModuleDirectLimit
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) :
    (moduleDirectLimitToColimit (R := R) F).comp
      (colimitToModuleDirectLimit (R := R) F) = LinearMap.id := by
  -- It is enough to compare after every colimit stage leg.
  have hhom :
      ModuleCat.ofHom ((moduleDirectLimitToColimit (R := R) F).comp
          (colimitToModuleDirectLimit (R := R) F)) =
        𝟙 (colimit F) := by
    apply (colimit.isColimit F).hom_ext
    intro i
    apply ModuleCat.hom_ext
    ext m
    calc
      ((moduleDirectLimitToColimit (R := R) F).comp
          (colimitToModuleDirectLimit (R := R) F)) ((colimit.ι F i).hom m)
          = moduleDirectLimitToColimit (R := R) F
              (((colimitToModuleDirectLimit (R := R) F).comp (colimit.ι F i).hom) m) := rfl
      _ = moduleDirectLimitToColimit (R := R) F
            (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
              (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i m) := by
            rw [colimitToModuleDirectLimit_ι]
      _ = (colimit.ι F i).hom m := moduleDirectLimitToColimit_of (R := R) F i m
  ext x
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hhom) x

/-- Helper for Chap10 Lemma 10 89 9: the chosen categorical colimit and quotient-model direct
limit are linearly equivalent. -/
private noncomputable def colimitLinearEquivDirectLimit
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R) :
    (colimit F : ModuleCat.{max v w} R) ≃ₗ[R]
      Module.DirectLimit (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) :=
  LinearEquiv.ofLinear (colimitToModuleDirectLimit (R := R) F)
    (moduleDirectLimitToColimit (R := R) F)
    (colimitToModuleDirectLimit_comp_moduleDirectLimitToColimit (R := R) F)
    (moduleDirectLimitToColimit_comp_colimitToModuleDirectLimit (R := R) F)

/-- Helper for Chap10 Lemma 10 89 9: tensoring the categorical colimit by `Q` identifies with the
quotient-model direct limit of the stage tensor products. -/
private noncomputable def colimitTensorDirectLimitEquiv
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q] :
    ((colimit F : ModuleCat.{max v w} R) ⊗[R] Q) ≃ₗ[R]
      Module.DirectLimit (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
        (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) :=
  ((colimitLinearEquivDirectLimit (R := R) F).rTensor Q).trans
    (TensorProduct.directLimitLeft (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) Q)

/-- Helper for Chap10 Lemma 10 89 9: the tensor/direct-limit equivalence sends a stage tensor
map to the corresponding direct-limit stage class. -/
private lemma colimitTensorDirectLimitEquiv_rTensor
    [DecidableEq I]
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q]
    (i : I) (z : (F.obj i : Type (max v w)) ⊗[R] Q) :
    colimitTensorDirectLimitEquiv (R := R) F Q
        (((colimit.ι F i).hom.rTensor Q) z) =
      Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
        (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z := by
  -- First transport the stage map through the colimit/direct-limit comparison isomorphism.
  let e := colimitLinearEquivDirectLimit (R := R) F
  have hcomp :
      e.toLinearMap.comp (colimit.ι F i).hom =
        Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i := by
    change (colimitToModuleDirectLimit (R := R) F).comp (colimit.ι F i).hom =
      Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i
    exact colimitToModuleDirectLimit_ι (R := R) F i
  have hstage :
      (e.rTensor Q) (((colimit.ι F i).hom.rTensor Q) z) =
        (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i).rTensor Q z := by
    -- Functoriality of `rTensor` turns the composed stage map into the direct-limit inclusion.
    change (e.toLinearMap.rTensor Q) (((colimit.ι F i).hom.rTensor Q) z) =
      (Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
        (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i).rTensor Q z
    rw [← LinearMap.rTensor_comp_apply, hcomp]
  -- Then use mathlib's tensor/direct-limit computation rule.
  calc
    colimitTensorDirectLimitEquiv (R := R) F Q
        (((colimit.ι F i).hom.rTensor Q) z)
        = TensorProduct.directLimitLeft
            (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) Q
            ((e.rTensor Q) (((colimit.ι F i).hom.rTensor Q) z)) := rfl
    _ = TensorProduct.directLimitLeft
          (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) Q
          ((Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)))
            (fun i j hij ↦ moduleSystemMap (R := R) F i j hij) i).rTensor Q z) := by
            rw [hstage]
    _ = Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
          (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z := by
            simpa using TensorProduct.directLimitLeft_rTensor_of
              (f := fun i j hij ↦ moduleSystemMap (R := R) F i j hij) (M := Q) (x := z)

/-- Helper for Chap10 Lemma 10 89 9: every tensor over the colimit comes from one stage. -/
private lemma exists_colimit_rTensor_preimage
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q]
    (z : (colimit F : ModuleCat.{max v w} R) ⊗[R] Q) :
    ∃ (i : I) (zᵢ : (F.obj i : Type (max v w)) ⊗[R] Q),
      ((colimit.ι F i).hom.rTensor Q) zᵢ = z := by
  -- Represent the image of `z` in the quotient-model tensor direct limit by a single stage.
  classical
  obtain ⟨i, zᵢ, hzᵢ⟩ :=
    Module.DirectLimit.exists_of
      (colimitTensorDirectLimitEquiv (R := R) F Q z)
  refine ⟨i, zᵢ, ?_⟩
  apply (colimitTensorDirectLimitEquiv (R := R) F Q).injective
  rw [colimitTensorDirectLimitEquiv_rTensor]
  exact hzᵢ

/-- Helper for Chap10 Lemma 10 89 9: a stage tensor map into the colimit tensor product is
injective when all later transition maps are universally injective. -/
private lemma colimitι_rTensor_injective_of_universallyInjective_transitions
    (F : I ⥤ ModuleCat.{max v w} R)
    (hF :
      ∀ ⦃i j : I⦄ (hij : i ≤ j),
        LinearMap.UniversallyInjective.{u, max v w, max v w, x}
          ((F.map (homOfLE hij)).hom))
    (Q : Type x) [AddCommGroup Q] [Module R Q] (i : I) :
    Function.Injective ((colimit.ι F i).hom.rTensor Q) := by
  -- Compare equal stage tensors in the tensor direct limit; equality eventually occurs at a later
  -- stage, where the transition tensor map is injective by universal injectivity.
  classical
  intro z z' hzz'
  have hdirect :
      Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
          (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z =
        Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
          (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z' := by
    calc
      Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
          (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z =
        colimitTensorDirectLimitEquiv (R := R) F Q
          (((colimit.ι F i).hom.rTensor Q) z) := by
            symm
            exact colimitTensorDirectLimitEquiv_rTensor (R := R) F Q i z
      _ = colimitTensorDirectLimitEquiv (R := R) F Q
          (((colimit.ι F i).hom.rTensor Q) z') := by
            rw [hzz']
      _ = Module.DirectLimit.of R I (fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
          (fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) i z' :=
            colimitTensorDirectLimitEquiv_rTensor (R := R) F Q i z'
  obtain ⟨j, hij, hstage⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq (R := R) (ι := I)
      (G := fun i ↦ (F.obj i : Type (max v w)) ⊗[R] Q)
      (f := fun i j hij ↦ (moduleSystemMap (R := R) F i j hij).rTensor Q) hdirect
  exact (hF hij Q inferInstance inferInstance) hstage

/-- Helper for Chap10 Lemma 10 89 9: the product comparison map for the colimit is injective
under universally injective transition maps. -/
private lemma piRightHom_colimit_injective_of_universallyInjective_transitions
    (F : I ⥤ ModuleCat.{max v w} R)
    [∀ i, MittagLeffler R (F.obj i)]
    (hF :
      ∀ ⦃i j : I⦄ (hij : i ≤ j),
        LinearMap.UniversallyInjective.{u, max v w, max v w, x}
          ((F.map (homOfLE hij)).hom))
    (A : Type x) (Q : A → Type x)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Injective (TensorProduct.piRightHom R R
      ((colimit F : ModuleCat.{max v w} R)) Q) := by
  -- Reduce equality to the vanishing of a difference, then lift that difference to a stage.
  classical
  intro z z' hzz'
  suffices hzero : z - z' = 0 by
    exact sub_eq_zero.mp hzero
  let Qprod : Type x := ∀ a, Q a
  have hPiZero :
      TensorProduct.piRightHom R R ((colimit F : ModuleCat.{max v w} R)) Q (z - z') = 0 := by
    ext a
    simp [map_sub, congr_fun hzz' a]
  obtain ⟨i, zᵢ, hzᵢ⟩ :=
    exists_colimit_rTensor_preimage (R := R) F Qprod (z - z')
  have hzᵢPi :
      TensorProduct.piRightHom R R (F.obj i) Q zᵢ = 0 := by
    -- Each coordinate vanishes after applying the injective stage-to-colimit tensor map.
    ext a
    apply colimitι_rTensor_injective_of_universallyInjective_transitions
      (R := R) F hF (Q a) i
    calc
      ((colimit.ι F i).hom.rTensor (Q a))
          ((TensorProduct.piRightHom R R (F.obj i) Q zᵢ) a)
          = (TensorProduct.piRightHom R R ((colimit F : ModuleCat.{max v w} R)) Q
              (((colimit.ι F i).hom.rTensor Qprod) zᵢ)) a := by
              simpa using
                (congr_fun
                  (piRightHom_rTensor_apply_linear (R := R) (Q := Q)
                    (colimit.ι F i).hom zᵢ) a).symm
      _ = (TensorProduct.piRightHom R R ((colimit F : ModuleCat.{max v w} R)) Q
              (z - z')) a := by
            rw [hzᵢ]
      _ = 0 := by
            exact congr_fun hPiZero a
  have hstageInj :
      Function.Injective (TensorProduct.piRightHom R R (F.obj i) Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective
      (R := R) (M := (F.obj i : Type (max v w)))).1
      (inferInstance : MittagLeffler R (F.obj i)) A Q
  have hzᵢZero : zᵢ = 0 := hstageInj hzᵢPi
  calc
    z - z' = ((colimit.ι F i).hom.rTensor Qprod) zᵢ := hzᵢ.symm
    _ = ((colimit.ι F i).hom.rTensor Qprod) 0 := by rw [hzᵢZero]
    _ = 0 := by simp

/-!
The helpers below set up the source route without using the same-universe monoidal
`tensorRight` functor.  They build the right-tensor diagram explicitly in the larger universe
where the tensor products live.
-/

/-- Helper for Chap10 Lemma 10 89 9: right tensoring sends the identity map to the identity
morphism in the enlarged module category. -/
private lemma rTensorFunctor_map_id
    {V : Type w} [AddCommGroup V] [Module R V]
    {Q : Type x} [AddCommGroup Q] [Module R Q] :
    ModuleCat.ofHom ((LinearMap.id : V →ₗ[R] V).rTensor Q) =
      𝟙 (ModuleCat.of.{max w x} R (V ⊗[R] Q)) := by
  -- It is enough to check pure tensors, where the identity is definitionally transparent.
  apply ModuleCat.hom_ext
  ext v q
  rfl

/-- Helper for Chap10 Lemma 10 89 9: right tensoring is compatible with composition in the
enlarged module category. -/
private lemma rTensorFunctor_map_comp
    {V : Type w} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W]
    {X : Type w} [AddCommGroup X] [Module R X]
    {Q : Type x} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) (g : W →ₗ[R] X) :
    ModuleCat.ofHom ((g.comp f).rTensor Q) =
      (ModuleCat.ofHom (f.rTensor Q) : ModuleCat.of.{max w x} R (V ⊗[R] Q) ⟶
          ModuleCat.of.{max w x} R (W ⊗[R] Q)) ≫
        ModuleCat.ofHom (g.rTensor Q) := by
  -- Both sides are the same tensor-product map, so pure tensors determine the equality.
  apply ModuleCat.hom_ext
  ext v q
  rfl

/-- Helper for Chap10 Lemma 10 89 9: right tensoring by a fixed module as a
universe-flexible functor on `ModuleCat`. -/
private def rTensorFunctor
    (Q : Type x) [AddCommGroup Q] [Module R Q] :
    ModuleCat.{w} R ⥤ ModuleCat.{max w x} R where
  obj N := ModuleCat.of.{max w x} R (N ⊗[R] Q)
  map φ := ModuleCat.ofHom (φ.hom.rTensor Q)
  map_id N := rTensorFunctor_map_id (R := R) (V := N) (Q := Q)
  map_comp f g := rTensorFunctor_map_comp (R := R) (Q := Q) f.hom g.hom

/-- Helper for Chap10 Lemma 10 89 9: the diagram obtained by tensoring every stage of a
directed module diagram on the right. -/
private abbrev rTensorDiagram
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q] :
    I ⥤ ModuleCat.{max (max v w) x} R :=
  F ⋙ (rTensorFunctor (R := R) Q :
    ModuleCat.{max v w} R ⥤ ModuleCat.{max (max v w) x} R)

omit [Nonempty I] [IsDirectedOrder I] in
/-- Helper for Chap10 Lemma 10 89 9: the canonical stage-to-colimit tensor maps are natural in
the tensorized diagram. -/
private lemma rTensorColimitCocone_naturality
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q]
    {i j : I} (f : i ⟶ j) :
    (rTensorDiagram (R := R) F Q).map f ≫
        ModuleCat.ofHom (((colimit.ι F j).hom).rTensor Q) =
      ModuleCat.ofHom (((colimit.ι F i).hom).rTensor Q) := by
  -- The ordinary colimit cocone naturality gives the linear-map equality before tensoring.
  apply ModuleCat.hom_ext
  ext z
  have hcat : F.map f ≫ colimit.ι F j = colimit.ι F i := by
    simp
  have hlin : (colimit.ι F j).hom.comp (F.map f).hom = (colimit.ι F i).hom := by
    ext y
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hcat) y
  have hrtensor :
      ((colimit.ι F j).hom.rTensor Q).comp ((F.map f).hom.rTensor Q) =
        (colimit.ι F i).hom.rTensor Q := by
    rw [← LinearMap.rTensor_comp, hlin]
  exact DFunLike.congr_fun hrtensor z

/-- Helper for Chap10 Lemma 10 89 9: the canonical cocone from the tensorized stages to the
right tensor product of the original colimit. -/
private noncomputable def rTensorColimitCocone
    (F : I ⥤ ModuleCat.{max v w} R)
    (Q : Type x) [AddCommGroup Q] [Module R Q] :
    Cocone (rTensorDiagram (R := R) F Q) where
  pt := ModuleCat.of.{max (max v w) x} R ((colimit F : ModuleCat.{max v w} R) ⊗[R] Q)
  ι :=
    { app := fun i => ModuleCat.ofHom (((colimit.ι F i).hom).rTensor Q)
      naturality := fun _ _ f => rTensorColimitCocone_naturality (R := R) F Q f }

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the chapter
  owner `Module.MittagLeffler`.
* inspected owner declarations:
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `LinearMap.UniversallyInjective` from `Definition_10_82_1`,
  `mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`, and
  `CategoryTheory.ShortComplex.universallyExact_colimit_of_isFiltered` from `Example_10_82_2`.
* best owner abstraction: the chapter owners `Module.MittagLeffler` and
  `LinearMap.UniversallyInjective`; this lemma should build directly on them rather than introduce
  a local wrapper for directed systems with tensor-injective transition maps.
* layer: `source-facing`; the theorem records the directed-colimit closure statement from the
  source, not a new owner abstraction.
* primitive data: the directed diagram `F` and the universally injective transition-map
  hypothesis `hF`.
* derived API: the induced Mittag-Leffler structure on the colimit module `colimit F`.
-/
-- Proof sketch: by Proposition `10.89.5`, it is enough to show injectivity of the canonical map
-- `M ⊗[R] ∏ Q_α → ∏ (M ⊗[R] Q_α)` for the colimit module `M = colimit F`. Tensor product with a
-- fixed module commutes with filtered colimits, so this reduces to the corresponding injectivity at
-- each stage `F.obj i`, where it holds because `F.obj i` is Mittag-Leffler. The maps into the
-- product of the colimit tensors are injective because the transition maps are universally
-- injective after tensoring with each `Q_α`.
/-- Chap10 Lemma 10 89 9: the colimit of a directed system of Mittag-Leffler `R`-modules with
universally injective transition maps is a Mittag-Leffler `R`-module. -/
@[stacks 0AS7]
theorem mittagLeffler_colimit_of_directedSystem
    (F : I ⥤ ModuleCat.{max v w} R)
    [∀ i, MittagLeffler R (F.obj i)]
    (hF :
      ∀ ⦃i j : I⦄ (hij : i ≤ j),
        LinearMap.UniversallyInjective.{u, max v w, max v w, x}
          ((F.map (homOfLE hij)).hom)) :
    MittagLeffler R ((colimit F : ModuleCat.{max v w} R)) := by
  -- Route correction: the same-universe monoidal `tensorRight` route is not available for the
  -- universe of `F`, so the proof is organized around the explicit `rTensorDiagram` above.
  -- By Proposition 10.89.5 it remains to prove injectivity of `TensorProduct.piRightHom` for the
  -- colimit module; the missing bridge is that `rTensorColimitCocone` is a colimit and hence
  -- stage tensors inject into the colimit tensor under the universally injective transitions.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective
    (R := R) (M := (colimit F : ModuleCat.{max v w} R))).2 ?_
  intro (A : Type x) (Q : A → Type x) _ _
  -- The direct-limit tensor bridge lifts any kernel element to a stage, and universal injectivity
  -- of transitions makes every stage-to-colimit tensor map injective.
  exact piRightHom_colimit_injective_of_universallyInjective_transitions
    (R := R) F hF A Q

end

end Module
