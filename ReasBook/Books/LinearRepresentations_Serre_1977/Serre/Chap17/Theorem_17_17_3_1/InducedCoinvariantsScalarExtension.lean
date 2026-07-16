import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.InducedCoinvariantsMaps

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance inducedCoinvariantsScalarExtensionResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance inducedCoinvariantsScalarExtensionResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: scalar extension commutes with the induction coinvariants
quotient, expressed directly as a linear equivalence rather than through a submodule equality. -/
noncomputable def scalarExtension_induced_source_coinvariants_tensor_equiv_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    TensorProduct A k (Representation.IndV H.subtype ρA_HU) ≃ₗ[k]
      Representation.Coinvariants sourceScalarρ := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  have hfixed_apply_mk :
      ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
            (Representation.Coinvariants.mk ρrawA y) =
          Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y) := by
    intro y
    rfl
  have hforward_backward_mk :
      ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_forward_local
            (A := A) (G := G) (ρA_HU := ρA_HU)
            (scalarExtension_induced_source_coinvariants_backward_local ρA_HU
              (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y))) =
          Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
    intro z y
    calc
      scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (scalarExtension_induced_source_coinvariants_backward_local ρA_HU
            (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y))) =
        scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y) := by
              rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
                (A := A) (G := G) (ρA_HU := ρA_HU)]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
            (Representation.Coinvariants.mk ρrawA y) := by
              simp [scalarExtension_induced_source_coinvariants_forward_local,
                LinearMap.liftBaseChange_tmul]
      _ =
        z • Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y) := by
            rw [hfixed_apply_mk y]
      _ =
        Representation.Coinvariants.mk sourceScalarρ (z • ((1 : k) ⊗ₜ[A] y)) := by
            rw [← (Representation.Coinvariants.mk sourceScalarρ).map_smul]
      _ = Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
            congr 1
            simpa [one_mul] using TensorProduct.smul_tmul' z (1 : k) y
  have hbackward_forward_mk :
      ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
        scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (scalarExtension_induced_source_coinvariants_forward_local
              (A := A) (G := G) (ρA_HU := ρA_HU)
              (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y)) =
          z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y := by
    intro z y
    calc
      scalarExtension_induced_source_coinvariants_backward_local
          ρA_HU
          (scalarExtension_induced_source_coinvariants_forward_local
            (A := A) (G := G) (ρA_HU := ρA_HU)
            (z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y)) =
      scalarExtension_induced_source_coinvariants_backward_local
          ρA_HU
          (z •
            scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
              (Representation.Coinvariants.mk ρrawA y)) := by
              simp [scalarExtension_induced_source_coinvariants_forward_local,
                LinearMap.liftBaseChange_tmul]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)
              (Representation.Coinvariants.mk ρrawA y)) := by
                rw [map_smul]
      _ =
        z •
          scalarExtension_induced_source_coinvariants_backward_local
            ρA_HU
            (Representation.Coinvariants.mk sourceScalarρ ((1 : k) ⊗ₜ[A] y)) := by
                rw [hfixed_apply_mk y]
      _ = z • ((1 : k) ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y) := by
            rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
      _ = z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y := by
            simpa [one_mul] using
              (TensorProduct.smul_tmul' z (1 : k)
                (Representation.Coinvariants.mk ρrawA y))
  refine LinearEquiv.ofLinear
    (scalarExtension_induced_source_coinvariants_forward_local
      (A := A) (G := G) (ρA_HU := ρA_HU))
    (scalarExtension_induced_source_coinvariants_backward_local ρA_HU)
    ?_ ?_
  · apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [LinearMap.comp_apply]
    · intro z y
      simpa [LinearMap.comp_apply] using
        hforward_backward_mk z y
    · intro t₁ t₂ ht₁ ht₂
      simp [LinearMap.comp_apply, map_add, ht₁, ht₂]
  · apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [LinearMap.comp_apply]
    · intro z v
      refine Representation.Coinvariants.induction_on (ρ := ρrawA) v ?_
      intro y
      simpa [LinearMap.comp_apply] using hbackward_forward_mk z y
    · intro t₁ t₂ ht₁ ht₂
      simp [LinearMap.comp_apply, map_add, ht₁, ht₂]

/-- Helper for Theorem 17-17.3-1: descending the raw tensor equivalence through the induction
relation gives the quotient-level comparison used in the proper-overgroup branch. -/
noncomputable def induced_scalarExtension_source_coinvariants_equiv_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) ≃ₗ[k]
      (Representation.IndV H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU)) := by
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let rawCoinvEquiv :
      Representation.Coinvariants
          (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
            Representation.scalarExtension
              (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) ≃ₗ[k]
        Representation.IndV H.subtype
          (show Representation k H (TensorProduct A k W0) from
            Representation.scalarExtension ρA_HU) := by
    let rawHom :
        Representation.Coinvariants
            (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
              Representation.scalarExtension
                (Representation.tprod ((Representation.leftRegular A G).comp H.subtype)
                  ρA_HU)) →ₗ[k]
          Representation.IndV H.subtype
            (show Representation k H (TensorProduct A k W0) from
              Representation.scalarExtension ρA_HU) :=
      Representation.Coinvariants.map _ _
        (induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0))
        (induced_scalarExtension_source_hom_rel_local
          (A := A) (G := G) (ρA_HU := ρA_HU))
    let rawInv :
        Representation.IndV H.subtype
            (show Representation k H (TensorProduct A k W0) from
              Representation.scalarExtension ρA_HU) →ₗ[k]
          Representation.Coinvariants
            (show Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) from
              Representation.scalarExtension
                (Representation.tprod ((Representation.leftRegular A G).comp H.subtype)
                  ρA_HU)) :=
      Representation.Coinvariants.map _ _
        (induced_scalarExtension_source_inv_local
          (A := A) (G := G) (W0 := W0))
        (induced_scalarExtension_source_inv_rel_local
          (A := A) (G := G) (ρA_HU := ρA_HU))
    refine LinearEquiv.ofLinear rawHom rawInv ?_ ?_
    · ext x
      simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
    · ext x
      simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
  exact
    (scalarExtension_induced_source_coinvariants_tensor_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)).trans
      rawCoinvEquiv

/-- Helper for Theorem 17-17.3-1: on standard generators, the direct scalar-extension/coinvariants
equivalence sends `1 ⊗ IndV.mk g x` to the scalar-extended raw basis class `[(1 ⊗ single g ⊗ x)]`.
-/
theorem scalarExtension_induced_source_coinvariants_tensor_equiv_apply_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_tensor_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  simpa [scalarExtension_induced_source_coinvariants_tensor_equiv_local] using
    scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
      (A := A) (G := G) (ρA_HU := ρA_HU) (1 : k) g xU

/-- Helper for Theorem 17-17.3-1: on standard generators, the descended scalar-extension/source
equivalence carries the induced source basis vector to the corresponding scalar-extended basis
vector. -/
theorem induced_scalarExtension_source_coinvariants_equiv_apply_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (g : G) (xU : W0) :
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_coinvariants_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.IndV.mk H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU) g
        (1 ⊗ₜ[A] xU) := by
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  let targetρ :
      Representation k H (TensorProduct k (G →₀ k) (TensorProduct A k W0)) :=
    Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)
  let tensorEquiv :=
    scalarExtension_induced_source_coinvariants_tensor_equiv_local
      (A := A) (G := G) (ρA_HU := ρA_HU)
  let rawMap :
      Representation.Coinvariants sourceScalarρ →ₗ[k]
        Representation.IndV H.subtype
          (show Representation k H (TensorProduct A k W0) from
            Representation.scalarExtension ρA_HU) :=
    Representation.Coinvariants.map _ _
      (induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0))
      (induced_scalarExtension_source_hom_rel_local
        (A := A) (G := G) (ρA_HU := ρA_HU))
  change rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
    Representation.IndV.mk H.subtype
      (show Representation k H (TensorProduct A k W0) from
        Representation.scalarExtension ρA_HU) g
      (1 ⊗ₜ[A] xU)
  calc
    rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      rawMap (Representation.Coinvariants.mk sourceScalarρ
        (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          rw [scalarExtension_induced_source_coinvariants_tensor_equiv_apply_mk_local
            (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ =
      Representation.Coinvariants.mk targetρ
        (induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0)
          (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          simp [rawMap, targetρ]
    _ =
      Representation.Coinvariants.mk targetρ
        ((Finsupp.single g (1 : k)) ⊗ₜ[k] (1 ⊗ₜ[A] xU)) := by
          rw [induced_scalarExtension_source_hom_apply_basis_local
            (A := A) (G := G) (W0 := W0)]
    _ =
      Representation.IndV.mk H.subtype
        (show Representation k H (TensorProduct A k W0) from
          Representation.scalarExtension ρA_HU) g
        (1 ⊗ₜ[A] xU) := by
          rfl

/-- Helper for Theorem 17-17.3-1: evaluating the scalar-extension/source equivalence on the pure
tensor `1 ⊗ xU` recovers the reduced coefficient `red_HU xU`. -/
theorem scalarExtension_source_equiv_apply_one_tmul_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (xU : ULift.{max (max u v) w} W0) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    let eHU :
        (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
      scalarExtension_source_equiv_of_residueFieldLift_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
    eHU (1 ⊗ₜ[A] xU) = red_HU xU := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  let eHU :
      (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
    scalarExtension_source_equiv_of_residueFieldLift_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  simpa [eHU, scalarExtension_source_equiv_of_residueFieldLift_local, ρA_HU, red_HU, hLiftHU] using
    hLiftHU.1.equiv_tmul (1 : k) xU

/-- Helper for Theorem 17-17.3-1: the Frobenius-produced `ULift`-source induction map is the
canonical base-change map once checked on the standard induced generators. -/
theorem induced_subrepresentation_lift_ulift_source_isBaseChange_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (red_u :
        Representation.IndV H.subtype
          (uliftRepresentation_witness_local (A := A) ρA_H) →ₗ[A]
          Representation.IndV H.subtype W.toRepresentation)
    (hred_u :
        ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
          red_u
              (Representation.IndV.mk H.subtype
                (uliftRepresentation_witness_local (A := A) ρA_H) g xU) =
            Representation.IndV.mk H.subtype W.toRepresentation g
              ((red_H.comp
                  (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap) xU)) :
    IsBaseChange k red_u := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
    TensorProduct.leftModule
  let _ : Module k
      (TensorProduct A k
        (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  -- Pin the `A`-action on the (k-module) induced target so `restrictScalars A` / the `= red_u`
  -- check in `hEq` below does not re-explore the `compHom` instance search (it otherwise hits the
  -- 20000 `synthInstance` budget now that the chain is universe-polymorphic).
  let _ : Module A (Representation.IndV H.subtype W.toRepresentation) :=
    Module.compHom _ (algebraMap A k)
  -- Pin both scalar towers so `LinearMap.CompatibleSMul … A k` (required by `restrictScalars A`)
  -- resolves without exploring the `compHom`/canonical `IsScalarTower` diamond.
  let _ : IsScalarTower A k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower A k (Representation.IndV H.subtype W.toRepresentation) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eHU : (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
    scalarExtension_source_equiv_of_residueFieldLift_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let eCanon :
      TensorProduct A k (Representation.IndV H.subtype ρA_HU) ≃ₗ[k]
        Representation.IndV H.subtype W.toRepresentation :=
    (induced_scalarExtension_source_coinvariants_equiv_local
      (A := A) (G := G) (ρA_HU := ρA_HU)).trans
      ((ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU).toLinearEquiv)
  have hEq :
      ((eCanon.toLinearMap.restrictScalars A).comp
        (TensorProduct.mk A k (Representation.IndV H.subtype ρA_HU) 1)) = red_u := by
    apply Representation.IndV.hom_ext
    intro g
    ext xU
    calc
      ((eCanon.toLinearMap.restrictScalars A).comp
          (TensorProduct.mk A k (Representation.IndV H.subtype ρA_HU) 1))
          (Representation.IndV.mk H.subtype ρA_HU g xU) =
          eCanon (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) := by
            rfl
      _ =
          (ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU)
            (Representation.IndV.mk H.subtype
              (show Representation k H
                  (TensorProduct A k (ULift.{max (max u v) w} W0)) from
                Representation.scalarExtension ρA_HU) g
              (1 ⊗ₜ[A] xU)) := by
                rw [LinearEquiv.trans_apply]
                rw [induced_scalarExtension_source_coinvariants_equiv_apply_mk_local
                  (A := A) (G := G) (ρA_HU := ρA_HU)]
                rfl
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (eHU (1 ⊗ₜ[A] xU)) := by
            rw [ind_equiv_of_source_equiv_over_local_apply_mk]
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
            rw [scalarExtension_source_equiv_apply_one_tmul_local
              (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
      _ =
          red_u
            (Representation.IndV.mk H.subtype ρA_HU g xU) := by
            symm
            simpa [ρA_HU, red_HU] using hred_u g xU
  refine IsBaseChange.of_equiv eCanon ?_
  intro x
  exact LinearMap.congr_fun hEq x

end

end Representation
