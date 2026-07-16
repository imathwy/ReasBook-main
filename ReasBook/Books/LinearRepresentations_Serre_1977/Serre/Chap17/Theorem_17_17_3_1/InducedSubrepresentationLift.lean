import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.SameUniverseInductionPackaging
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.InducedCoinvariantsMaps

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance inducedLiftResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance inducedLiftResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: scalar extension commutes with the induction coinvariants
quotient, expressed directly as a tensor-to-coinvariants linear equivalence localized inside the
consumer file so the proof no longer depends on the missing compiled owner. -/
private noncomputable def inducedSourceCoinvariantsTensorEquivLocal
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
    -- Route correction: rebuild the quotient bridge from the already-compiled forward/backward
    -- maps instead of importing the missing owner module.
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
    -- The inverse calculation uses the same fixed-`1` normalization on quotient generators.
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
  · -- First certify the quotient-side inverse on raw tensor classes, then descend by generators.
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp [LinearMap.comp_apply]
    · intro z y
      simpa [LinearMap.comp_apply] using hforward_backward_mk z y
    · intro t₁ t₂ ht₁ ht₂
      simp [LinearMap.comp_apply, map_add, ht₁, ht₂]
  · -- Then certify the tensor-side inverse on pure tensors and the quotient factor generators.
    apply LinearMap.ext
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
relation gives the local scalar-extension/source comparison needed for the base-change step. -/
private noncomputable def inducedSourceScalarExtensionEquivLocal
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
    -- Package the descended raw source comparison before composing it with the tensor bridge.
    refine LinearEquiv.ofLinear rawHom rawInv ?_ ?_
    · ext x
      simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
    · ext x
      simp [rawHom, rawInv, Representation.Coinvariants.map_comp]
  exact (inducedSourceCoinvariantsTensorEquivLocal
      (ρA_HU := ρA_HU)).trans rawCoinvEquiv

/-- Helper for Theorem 17-17.3-1: on standard generators, the localized tensor/coinvariants
equivalence sends `1 ⊗ IndV.mk g x` to the expected scalar-extended raw basis class. -/
private theorem inducedSourceCoinvariantsTensorEquivApplyMkLocal
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
    inducedSourceCoinvariantsTensorEquivLocal
        (ρA_HU := ρA_HU)
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
  -- Evaluate the localized tensor bridge directly on the standard induced generator.
  simpa [inducedSourceCoinvariantsTensorEquivLocal] using
    scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
      (A := A) (G := G) (ρA_HU := ρA_HU) (1 : k) g xU

/-- Helper for Theorem 17-17.3-1: on standard generators, the localized scalar-extension/source
equivalence carries the induced basis vector to the scalar-extended coefficient basis vector. -/
private theorem inducedSourceScalarExtensionEquivApplyMkLocal
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (g : G) (xU : W0) :
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    inducedSourceScalarExtensionEquivLocal
        (ρA_HU := ρA_HU)
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
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
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
    inducedSourceCoinvariantsTensorEquivLocal
      (ρA_HU := ρA_HU)
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
  -- Compare the descended equivalence with the raw source map on the standard basis vector.
  change rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
    Representation.IndV.mk H.subtype
      (show Representation k H (TensorProduct A k W0) from
        Representation.scalarExtension ρA_HU) g
      (1 ⊗ₜ[A] xU)
  calc
    rawMap (tensorEquiv (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      rawMap (Representation.Coinvariants.mk sourceScalarρ
          (1 ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          rw [inducedSourceCoinvariantsTensorEquivApplyMkLocal (ρA_HU := ρA_HU)]
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

/-- Helper for Theorem 17-17.3-1: evaluating the subgroup scalar-extension equivalence on
`1 ⊗ xU` recovers the reduced coefficient `red_HU xU`. -/
private theorem scalarExtensionSourceEquivApplyOneTmulLocal
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
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
    TensorProduct.leftModule
  let eHU :
      (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
    scalarExtension_source_equiv_of_residueFieldLift_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  -- The local lift equivalence already records the desired tensor-normalization formula.
  simpa [eHU, scalarExtension_source_equiv_of_residueFieldLift_local, ρA_HU, red_HU, hLiftHU] using
    hLiftHU.1.equiv_tmul (1 : k) xU

/-- Helper for Theorem 17-17.3-1: the Frobenius-produced `ULift`-source induction map is the
canonical base-change map once the comparison is checked on the standard induced generators. -/
private theorem inducedSubrepresentationLiftBaseChangeLocal
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
  -- Pin the `A`-action on the (k-module) induced target + both scalar towers so
  -- `restrictScalars A`'s `LinearMap.CompatibleSMul … A k` in `hEq` resolves without re-exploring
  -- the `compHom`/canonical `IsScalarTower` diamond (which otherwise hits the 20000 budget once the
  -- helper chain is universe-polymorphic).
  let _ : Module A (Representation.IndV H.subtype W.toRepresentation) :=
    Module.compHom _ (algebraMap A k)
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
    (inducedSourceScalarExtensionEquivLocal
      (ρA_HU := ρA_HU)).trans
      ((ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU).toLinearEquiv)
  have hEq :
      ((eCanon.toLinearMap.restrictScalars A).comp
        (TensorProduct.mk A k (Representation.IndV H.subtype ρA_HU) 1)) = red_u := by
    -- The induced source is generated by the standard `IndV.mk` basis vectors, so it is enough
    -- to compare the canonical base-change map and `red_u` there.
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
                rw [inducedSourceScalarExtensionEquivApplyMkLocal (ρA_HU := ρA_HU)]
                rfl
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (eHU (1 ⊗ₜ[A] xU)) := by
            rw [ind_equiv_of_source_equiv_over_local_apply_mk]
      _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
            rw [scalarExtensionSourceEquivApplyOneTmulLocal
              (ρ := ρ) W ρA_H red_H hLiftH]
      _ =
          red_u
            (Representation.IndV.mk H.subtype ρA_HU g xU) := by
            symm
            simpa [ρA_HU, red_HU] using hred_u g xU
  -- The canonical equivalence now certifies that `red_u` is exactly the expected base-change map.
  refine IsBaseChange.of_equiv eCanon ?_
  intro x
  exact LinearMap.congr_fun hEq x

/-- Helper for Theorem 17-17.3-1: once the standard induced model already has a packaged
residue-field lift, any explicit representation equivalence from that model to the ambient
representation `ρ` finishes the proper-overgroup branch by a single postcomposition of the
reduction map. -/
private theorem transport_induced_residueFieldLift_along_equiv
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W' : Type u} [AddCommGroup W'] [Module A W']
    [Module.Free A W'] [Module.Finite A W']
    (ρA_ind : Representation A G W')
    (red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation)
    (hLiftInd :
      IsResidueFieldLift (Representation.ind H.subtype W.toRepresentation) ρA_ind red_ind)
    (eInd : (Representation.ind H.subtype W.toRepresentation).Equiv ρ) :
    ∃ (W'' : Type u) (_ : AddCommGroup W'') (_ : Module A W'')
      (_ : Module.Free A W'') (_ : Module.Finite A W'')
      (ρA : Representation A G W'')
      (red : W'' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- The source route has already finished induction; only the final target transport remains.
  exact
    ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, ρA_ind,
      (eInd.toLinearMap.restrictScalars A).comp red_ind,
      residueFieldLift_of_equiv_target
        (A := A) (G := G) (V := V) hLiftInd eInd⟩

/-- Helper for Theorem 17-17.3-1: the standard induced lift can be packaged on a same-universe
carrier once the subgroup lift has been converted into the canonical induced `ULift` model and
then compressed back to a free finite ambient carrier. -/
private theorem induced_standard_model_residueFieldLift_exists_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA_ind : Representation A G W')
      (red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation),
        IsResidueFieldLift (Representation.ind H.subtype W.toRepresentation) ρA_ind red_ind := by
  -- Keep Serre's proper-overgroup route on the canonical induced model, then compress only at the
  -- end to a same-universe free finite carrier.
  let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  let red_u :
      Representation.IndV H.subtype ρA_HU →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
  have hred_u :
      ∀ g : G, ∀ xU : ULift.{max (max u v) w} W0,
        red_u (Representation.IndV.mk H.subtype ρA_HU g xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
    intro g xU
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_apply_mk_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g xU
  have hBase_u : IsBaseChange k red_u := by
    exact
      inducedSubrepresentationLiftBaseChangeLocal
        (ρ := ρ) W ρA_H red_H hLiftH red_u hred_u
  have hInter_u :
      (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_u := by
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_isIntertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let eU : ρA_HU.Equiv ρA_H :=
    Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
      -- The `ULift` wrapper leaves the subgroup action unchanged pointwise.
      ext y
      rfl
  let eInd_native :
      (Representation.ind H.subtype ρA_HU).Equiv
        (Representation.ind H.subtype ρA_H) :=
    ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
  let red_native :
      Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_u.comp eInd_native.symm.toLinearMap
  have hred_native :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    -- Remove the `ULift` from the induced source before packaging the same-universe carrier.
    simpa [red_native] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        hBase_u hInter_u eInd_native.symm
  have hBase_native : IsBaseChange k red_native := by
    simpa [RawIsResidueFieldReduction_local] using hred_native.1
  have hInter_native :
      (Representation.ind H.subtype ρA_H).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_native := by
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    have heq :
        eInd_native.symm ((Representation.ind H.subtype ρA_H) g x) =
          (Representation.ind H.subtype ρA_HU) g (eInd_native.symm x) := by
      simpa using LinearMap.congr_fun (eInd_native.symm.isIntertwining' g) x
    calc
      red_native ((Representation.ind H.subtype ρA_H) g x) =
          red_u ((Representation.ind H.subtype ρA_HU) g (eInd_native.symm x)) := by
            simpa [red_native, LinearMap.comp_apply] using congrArg red_u heq
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_u (eInd_native.symm x)) := by
              simpa [Representation.restrictScalars_apply] using
                hInter_u.isIntertwining g (eInd_native.symm x)
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (red_native x) := by
              simp [red_native, LinearMap.comp_apply]
  have hPackedInduced :
      ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
        (_ : Module.Free A W') (_ : Module.Finite A W')
        (ρA_ind : Representation A G W'),
          Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) := by
    exact
      exists_same_universe_finite_free_induced_model_local
        (A := A) (G := G) (H := H) ρA_H
  rcases hPackedInduced with
    ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, hEquiv⟩
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  rcases hEquiv with ⟨ePack⟩
  let red_ind : W' →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_native.comp ePack.toLinearMap
  have hred_ind :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        ρA_ind
        red_ind := by
    -- Then move from the native induced source to the packaged same-universe source.
    simpa [red_ind] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        (ρA' := ρA_ind)
        (ρA := Representation.ind H.subtype ρA_H)
        (red := red_native)
        hBase_native hInter_native ePack
  refine ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, ?_⟩
  -- The packaged source is free and finite, so the raw reduction data upgrades to a lift.
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_ind

/-- Helper for Theorem 17-17.3-1: when the ambient residue representation lives in a smaller
universe, transport the inducedness equivalence through an ambient `ULift` and then descend it
back to the original carrier. -/
private noncomputable def inducedFromSubrepresentation_explicit_equiv_general_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    (Representation.ind H.subtype W.toRepresentation).Equiv ρ := by
  let ρU : Representation k G (ULift.{max (max u v) w, w} V) :=
    { toFun := fun g =>
        { toFun := fun x ↦ ⟨ρ g x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let eU : ρ.Equiv ρU :=
    Representation.Equiv.mk
      (ULift.moduleEquiv.symm : V ≃ₗ[k] ULift.{max (max u v) w, w} V) fun g ↦ by
        -- The `ULift` wrapper does not change the ambient action pointwise.
        ext x
        rfl
  let WU : Subrepresentation (ρU.comp H.subtype) :=
    transported_subrepresentation_of_equiv_local_c17
      (comp_subtype_equiv_local_c17 eU H) W
  have hIndU :
      ρU.IsInducedFromSubrepresentation H WU := by
    -- Transport inducedness to the lifted ambient carrier.
    simpa [WU] using
      (isInducedFromSubrepresentation_of_equiv_local_c17
        (ρ₁ := ρ) (ρ₂ := ρU) eU H W hInd)
  let eW : W.toRepresentation.Equiv WU.toRepresentation := by
    -- The transported source subrepresentation is just the image under the ambient equivalence.
    simpa [WU, transported_subrepresentation_of_equiv_local_c17, subrepresentationOrderIso_local_c17] using
      (subrepresentation_equiv_of_equiv_image_local_c17
        (comp_subtype_equiv_local_c17 eU H) W)
  let eIndU :
      (Representation.ind H.subtype WU.toRepresentation).Equiv ρU :=
    inducedFromSubrepresentation_explicit_equiv
      (ρ := ρU) (W := WU) hIndU
  let eSource :
      (Representation.ind H.subtype W.toRepresentation).Equiv
        (Representation.ind H.subtype WU.toRepresentation) :=
    ind_equiv_of_source_equiv_local_c17 H.subtype eW
  -- Compose the source transport, the lifted ambient equivalence, and the ambient `ULift` removal.
  exact (eSource.trans eIndU).trans eU.symm

/-- Helper for Theorem 17-17.3-1: the proper-overgroup branch should be exported from the split
Chapter `17.3` API rather than rebuilt inside Chapter `17.6`. -/
lemma exists_residueFieldLift_of_isInducedFromSubrepresentation
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA : Representation A G W')
      (red : W' →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  obtain ⟨W', hW'add, hW'mod, hW'free, hW'finite, ρA_ind, red_ind, hLiftInd⟩ :=
    induced_standard_model_residueFieldLift_exists_local
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  let eInd :
      (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
    inducedFromSubrepresentation_explicit_equiv_general_local
      (A := A) (G := G) (V := V) ρ W hInd
  -- After packaging the induced lift, only the final Chapter `7` transport back to `ρ` remains.
  exact
    transport_induced_residueFieldLift_along_equiv
      (A := A) (G := G) (V := V) ρ W ρA_ind red_ind hLiftInd eInd

end

end Representation
