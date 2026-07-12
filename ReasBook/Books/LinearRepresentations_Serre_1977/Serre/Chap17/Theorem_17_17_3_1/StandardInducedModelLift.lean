import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedCoinvariantsMaps
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedCoinvariantsScalarExtension

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
noncomputable local instance standardInducedModelLiftResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance standardInducedModelLiftResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: every free finite `A[G]`-representation can be moved to the
same-universe coordinate model `Fin (finrank A W) → A` without changing the action up to
equivalence. -/
theorem exists_same_universe_finite_free_rep_model_local
    {G' : Type*} [Group G']
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA : Representation A G' W0) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρW : Representation A G' W'),
        Nonempty (ρW.Equiv ρA) := by
  letI : Module A A := Semiring.toModule
  let n := Module.finrank A W0
  let W' : Type u := Fin n → A
  letI : AddCommGroup W' := Pi.addCommGroup
  letI : Module A W' := Pi.Function.module (Fin n) A A
  letI : Module.Free A W' := Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A W' := Module.Finite.of_basis (Pi.basisFun A (Fin n))
  let e : W0 ≃ₗ[A] W' := (Module.finBasis A W0).equivFun
  let ρW : Representation A G' W' :=
    { toFun := fun g ↦ e.conj (ρA g)
      map_one' := by
        -- Conjugation carries the identity action to the coordinate identity operator.
        calc
          e.conj (ρA 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        -- The transported action remains multiplicative after conjugation.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  refine
    ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  apply LinearMap.ext
  intro x
  change e.symm (e (ρA g (e.symm x))) = ρA g (e.symm x)
  simp


/-- Helper for Theorem 17-17.3-1: evaluating a coinduced function on inverse representatives
identifies the coinduced model over a commutative ring with functions on a finite left
transversal. -/
noncomputable def coind_representative_equiv_local
    {H : Subgroup G}
    {W0 : Type*} [AddCommGroup W0] [Module A W0]
    (ρA_H : Representation A H W0)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G)) :
    Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W0) where
  toFun f r := f.1 ((r : G)⁻¹)
  invFun ξ :=
    ⟨fun g ↦
        let x := hR.equiv g⁻¹
        ρA_H x.2⁻¹ (ξ x.1), by
        intro h g
        -- Move the subgroup factor in the complement decomposition to the coefficient action.
        simpa [mul_assoc, ← Module.End.mul_apply, ← map_mul] using
          congrArg
            (fun x : ↥(R : Set G) × H ↦ ρA_H x.2⁻¹ (ξ x.1))
            (hR.equiv_mul_right g⁻¹ h⁻¹)⟩
  map_add' _ _ := by
    ext r
    simp
  map_smul' _ _ := by
    ext r
    simp
  left_inv f := by
    ext g
    let x := hR.equiv g⁻¹
    have hg : ((x.2 : H) : G)⁻¹ * ((x.1 : (R : Set G)) : G)⁻¹ = g := by
      simpa [x, mul_inv_rev] using congrArg Inv.inv (hR.equiv_fst_mul_equiv_snd g⁻¹)
    -- Rewrite `g` through the complement decomposition of `g⁻¹`.
    change ρA_H x.2⁻¹ (f.1 (((x.1 : ↥(R : Set G)) : G)⁻¹)) = f.1 g
    simpa [hg] using
      ((f.2 x.2⁻¹ (((x.1 : (R : Set G)) : G)⁻¹)).symm)
  right_inv ξ := by
    ext r
    have hfst :
        (hR.equiv (r : G)).fst = r :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    have hsnd :
        (hR.equiv (r : G)).snd = (1 : H) :=
      hR.equiv_snd_eq_one_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    -- At a representative inverse, the complement decomposition is the trivial one `r * 1`.
    dsimp
    simp [hfst, hsnd]
/-- Helper for Theorem 17-17.3-1: after inducing a free finite `A[H]`-model, the induced source
can be compressed to a same-universe free finite carrier by passing through the finite-index
coinduced model on representative coordinates. -/
theorem exists_same_universe_finite_free_induced_model_from_rep_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0) :
    ∃ (W_ind : Type u) (_ : AddCommGroup W_ind) (_ : Module A W_ind)
      (_ : Module.Free A W_ind) (_ : Module.Finite A W_ind)
      (ρA_ind : Representation A G W_ind),
        Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) := by
  classical
  obtain ⟨S, hS, _⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : Subgroup.IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  let eIndCoind :
      (Representation.ind H.subtype ρA_H).Equiv
        (Representation.coind H.subtype ρA_H) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of ρA_H))
  let eCoind :
      Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W0) :=
    coind_representative_equiv_local (A := A) (G := G) ρA_H R hR
  let ρR : Representation A G (↥(R : Set G) → W0) :=
    { toFun := fun g ↦ eCoind.conj ((Representation.coind H.subtype ρA_H) g)
      map_one' := by
        calc
          eCoind.conj ((Representation.coind H.subtype ρA_H) 1) = eCoind.conj 1 := by
            rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eR : ρR.Equiv (Representation.coind H.subtype ρA_H) :=
    Representation.Equiv.mk eCoind.symm fun g ↦ by
      apply LinearMap.ext
      intro x
      change
        eCoind.symm (eCoind ((Representation.coind H.subtype ρA_H) g (eCoind.symm x))) =
          (Representation.coind H.subtype ρA_H) g (eCoind.symm x)
      simp [ρR]
  letI : Finite ↥(R : Set G) := Set.toFinite (R : Set G)
  letI : Fintype ↥(R : Set G) := Fintype.ofFinite _
  rcases
      exists_same_universe_finite_free_rep_model_local
        (A := A) (G' := G) (ρA := ρR) with
    ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, hEquiv⟩
  rcases hEquiv with ⟨ePack⟩
  refine ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, ?_⟩
  exact ⟨ePack.trans (eR.trans eIndCoind.symm)⟩

/-
The native-source induced lift below remains as a deleted draft: the active theorem uses the
universe-packaged route directly, and keeping this second owner live only reintroduces elaboration
pressure.
theorem induced_subrepresentation_lift_standard_target_isResidueFieldLift_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    [_hFreeInd : Module.Free A (Representation.IndV H.subtype ρA_H)]
    [_hFiniteInd : Module.Finite A (Representation.IndV H.subtype ρA_H)]
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ∃ red_native :
        Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation,
      IsResidueFieldLift
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
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
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let eHU : (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
      scalarExtension_source_equiv_of_residueFieldLift_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
    let eCanon :
        TensorProduct A k (Representation.IndV H.subtype ρA_HU) ≃ₗ[k]
          Representation.IndV H.subtype W.toRepresentation :=
      (induced_scalarExtension_source_coinvariants_equiv_local
        (A := A) (G := G) (ρA_HU := ρA_HU)).trans
        ((ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU).toLinearEquiv)
    let redCanon :
        Representation.IndV H.subtype ρA_HU →ₗ[A]
          Representation.IndV H.subtype W.toRepresentation :=
      (eCanon.toLinearMap.restrictScalars A).comp
        (TensorProduct.mk A k (Representation.IndV H.subtype ρA_HU) 1)
    have hCanon : IsBaseChange k redCanon := by
      refine IsBaseChange.of_equiv eCanon ?_
      intro x
      rfl
    have hEq : redCanon = red_u := by
      apply Representation.IndV.hom_ext
      intro g
      ext xU
      calc
        redCanon (Representation.IndV.mk H.subtype ρA_HU g xU) =
            eCanon (1 ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) := by
              rfl
        _ =
            (ind_equiv_of_source_equiv_over_local (R := k) H.subtype eHU)
              (Representation.IndV.mk H.subtype
                (show Representation k H (TensorProduct A k (ULift.{max (max u v) w} W0)) from
                  Representation.scalarExtension ρA_HU) g
                (1 ⊗ₜ[A] xU)) := by
                  rw [LinearEquiv.trans_apply]
                  rw [induced_scalarExtension_source_coinvariants_equiv_apply_mk_local
                    (A := A) (G := G) (ρA_HU := ρA_HU)]
        _ = Representation.IndV.mk H.subtype W.toRepresentation g (eHU (1 ⊗ₜ[A] xU)) := by
              rw [ind_equiv_of_source_equiv_over_local_apply_mk]
        _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
              rw [scalarExtension_source_equiv_apply_one_tmul_local
                (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH]
        _ = red_u (Representation.IndV.mk H.subtype ρA_HU g xU) := by
              symm
              simpa [ρA_HU, red_HU] using hred_u g xU
    rw [hEq] at hCanon
    exact hCanon
  have hInter_u :
      (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
        red_u := by
    simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
      induced_subrepresentation_lift_ulift_source_isIntertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  let _ := hBase_u
  let _ := hInter_u
  let eU : ρA_HU.Equiv ρA_H :=
    Representation.Equiv.mk ULift.moduleEquiv fun h ↦ by
      -- The `ULift` wrapper leaves the subgroup action unchanged pointwise.
      ext y
      rfl
  let eInd :
      (Representation.ind H.subtype ρA_HU).Equiv
        (Representation.ind H.subtype ρA_H) :=
    ind_equiv_of_source_equiv_over_local (R := A) H.subtype eU
  let red_native :
      Representation.IndV H.subtype ρA_H →ₗ[A] Representation.IndV H.subtype W.toRepresentation :=
    red_u.comp eInd.symm.toLinearMap
  -- Transport the raw reduction data back across the induced `ULift` source equivalence.
  have hred_native :
      RawIsResidueFieldReduction_local
        (A := A)
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    simpa [red_native] using
      residueFieldReduction_of_equiv_source_local
        (A := A)
        (ρ := Representation.ind H.subtype W.toRepresentation)
        hBase_u hInter_u eInd.symm
  -- Repackage the transported raw reduction as the native induced residue-field lift.
  have hLift_native :
      IsResidueFieldLift
        (Representation.ind H.subtype W.toRepresentation)
        (Representation.ind H.subtype ρA_H)
        red_native := by
    simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_native
  exact ⟨red_native, hLift_native⟩
-/

theorem induced_standard_model_residueFieldLift_exists
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
  -- Route correction: do not first force the native induced source into an `IsResidueFieldLift`,
  -- since that would require free/finite instances on `IndV`. Instead, transport the raw
  -- reduction data from the `ULift` source to the native induced source, then to the packaged
  -- same-universe source.
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
    -- Reuse the closed scalar-extension bridge instead of rebuilding the canonical comparison
    -- map inside this theorem.
    exact
      induced_subrepresentation_lift_ulift_source_isBaseChange_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH red_u hred_u
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
    -- First remove the `ULift` from the induced source while keeping only the raw reduction data.
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
          Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) :=
      by
        simpa using
          exists_same_universe_finite_free_induced_model_from_rep_local
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
  -- The packaged source is free and finite, so the raw reduction data upgrades immediately to an
  -- actual residue-field lift.
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hred_ind

/-- Helper for Theorem 17-17.3-1: once the standard induced model already has a packaged
residue-field lift, any explicit representation equivalence from that model to the ambient
representation `ρ` finishes the proper-overgroup branch by a single postcomposition of the
reduction map. -/
theorem transport_induced_residueFieldLift_along_equiv
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

/-- Helper for Theorem 17-17.3-1: the Chapter `7` inducedness witness should give an explicit
representation equivalence from the standard induced model back to the ambient representation,
without assuming the ambient carrier already lives in `Type (max u v w)`. -/
noncomputable def inducedFromSubrepresentation_explicit_equiv_general_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
  by
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
        -- The `ULift` wrapper does not change the pointwise action of `ρ`.
        ext x
        rfl
  let WU : Subrepresentation (ρU.comp H.subtype) :=
    transported_subrepresentation_of_equiv_local_c17
      (comp_subtype_equiv_local_c17 eU H) W
  have hIndU :
      ρU.IsInducedFromSubrepresentation H WU := by
    -- Transport the inducedness data to the lifted ambient carrier.
    simpa [WU] using
      (isInducedFromSubrepresentation_of_equiv_local_c17
        (ρ₁ := ρ) (ρ₂ := ρU) eU H W hInd)
  let eW : W.toRepresentation.Equiv WU.toRepresentation :=
    by
      -- Reuse the standard image-subrepresentation equivalence for the transported carrier.
      simpa [WU, transported_subrepresentation_of_equiv_local_c17, subrepresentationOrderIso_local_c17]
        using
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
  -- Build the explicit induced equivalence on the lifted carrier, then remove the `ULift`.
  exact (eSource.trans eIndU).trans eU.symm

/-- Helper for Theorem 17-17.3-1: once the standard induced model has been lifted on a same-
universe carrier, the only remaining proper-overgroup step is the final Chapter `7` transport
across `ρ.inducedFromSubrepresentationHom H W`. -/
lemma exists_residueFieldLift_of_isInducedFromSubrepresentation_local
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
    induced_standard_model_residueFieldLift_exists
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH
  letI : AddCommGroup W' := hW'add
  letI : Module A W' := hW'mod
  letI : Module.Free A W' := hW'free
  letI : Module.Finite A W' := hW'finite
  let eInd :
      (Representation.ind H.subtype W.toRepresentation).Equiv ρ :=
    inducedFromSubrepresentation_explicit_equiv_general_local
      (A := A) (G := G) (V := V) ρ W hInd
  -- After packaging the induced lift on a same-universe source, only the final Chapter `7`
  -- transport back to the ambient representation remains.
  exact
    transport_induced_residueFieldLift_along_equiv
      (A := A) (G := G) (V := V) ρ W ρA_ind red_ind hLiftInd eInd

/-- Helper for Theorem 17-17.3-1: once the Clifford split lands in the proper-overgroup branch,
the proof continues by recursing on that smaller subgroup and then inducing the lifted module back
to `G`. -/
lemma exists_residueFieldLift_of_proper_overgroup_induced
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (hrecSame :
      ∀ {H : Subgroup G} {W0 : Type w} [AddCommGroup W0] [Module k W0]
        [FiniteDimensional k W0]
        {C0 P0 : Subgroup H}
        (hH : H < ⊤)
        (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
        (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
        (σ : Representation k H W0) [σ.IsIrreducible],
          ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
            (_ : Module.Free A W') (_ : Module.Finite A W')
            (ρA_H : Representation A H W')
            (red_H : W' →ₗ[A] W0),
              IsResidueFieldLift σ ρA_H red_H)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        C ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hproper with ⟨H, hCH, hHlt, W, hWirred, hInd⟩
  let C0 : Subgroup H := C.subgroupOf H
  let P0 : Subgroup H := (H ⊓ P).subgroupOf H
  have hHdecomp :
      C0.Normal ∧ C0.IsComplement' P0 ∧ IsCyclic C0 ∧ Nat.Coprime p (Nat.card C0) ∧ IsPGroup p P0 :=
    subgroup_cyclicNormalByPGroupDecomposition_of_le
      (p := p) (C := C) (P := P) hCH hC hCP hCyclic hCoprime hP
  rcases hHdecomp with ⟨hC0, hC0P0, hC0cyc, hC0cop, hP0⟩
  letI : W.toRepresentation.IsIrreducible := hWirred
  -- Route correction: the outer cardinal induction now supplies the smaller-group recursion, so
  -- the only remaining work in this branch is the induced transport step below.
  have hLiftH :
      ∃ (W0 : Type u) (_ : AddCommGroup W0) (_ : Module A W0)
        (_ : Module.Free A W0) (_ : Module.Finite A W0)
        (ρA_H : Representation A H W0)
        (red_H : W0 →ₗ[A] W.toSubmodule),
          IsResidueFieldLift W.toRepresentation ρA_H red_H := by
    -- Apply the recursive hypothesis to the inherited cyclic-normal-by-`p` decomposition on `H`.
    exact hrecSame hHlt hC0 hC0P0 hC0cyc hC0cop hP0 W.toRepresentation
  rcases hLiftH with ⟨W0, hW0add, hW0mod, hW0free, hW0finite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup W0 := hW0add
  letI : Module A W0 := hW0mod
  letI : Module.Free A W0 := hW0free
  letI : Module.Finite A W0 := hW0finite
  -- The recursion on `H` is now isolated above; from here on we only need the induction
  -- transport from the lifted `H`-model of `W` back to the ambient representation `ρ`.
  exact
    exists_residueFieldLift_of_isInducedFromSubrepresentation_local
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH hInd



end

end Representation
