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
noncomputable local instance uLiftScalarExtensionPreparationResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance uLiftScalarExtensionPreparationResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: after induction on the native lifted subgroup carrier, the only
remaining proper-overgroup blocker is a comparison from that native reduced target to the standard
`k`-induced target. Once that comparison is packaged, the native induced source is already the
right `A[G]`-lift before same-universe compression. -/
noncomputable def induced_subrepresentation_lift_unit_intertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    ρA_H.IntertwiningMap
      (((Representation.ind H.subtype W.toRepresentation).restrictScalars A).comp H.subtype) := by
  -- Route correction: before invoking Frobenius reciprocity, package the unit-coset map as an
  -- actual subgroup intertwiner. This isolates the adjunction step from the pointwise proof.
  let f := ((Representation.IndV.mk H.subtype W.toRepresentation 1).restrictScalars A) ∘ₗ red_H
  exact
    LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := ρA_H)
      (σ := (((Representation.ind H.subtype W.toRepresentation).restrictScalars A).comp H.subtype))
      f
    (fun g x ↦
      (induced_subrepresentation_lift_unit_isIntertwining
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH).isIntertwining g x)

/-- Helper for Theorem 17-17.3-1: the packaged unit-coset subgroup intertwiner still sends
`x : W0` to the unit-coset generator with coefficient `red_H x`. -/
theorem induced_subrepresentation_lift_unit_intertwining_apply_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (x : W0) :
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH x =
        Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H x) := by
  -- The bundled intertwiner was constructed from the explicit unit-coset insertion map.
  change
    (((Representation.IndV.mk H.subtype W.toRepresentation 1).restrictScalars A) ∘ₗ red_H) x =
      Representation.IndV.mk H.subtype W.toRepresentation 1 (red_H x)
  rfl

/-- Helper for Theorem 17-17.3-1: the inverse Frobenius-reciprocity map evaluates on a standard
induced generator by translating the subgroup intertwiner along that generator. -/
theorem indResHomEquiv_symm_apply_mk_local
    {H' : Type*} [Group H']
    {G' : Type*} [Group G']
    (φ : H' →* G')
    (M : Rep A H')
    (N : Rep A G')
  (f : M ⟶ Rep.res φ N)
  (g : G') (x : M.V) :
    (((Rep.indResHomEquiv φ M N).symm f).hom) (Representation.IndV.mk φ M.ρ g x) =
      N.ρ g⁻¹ (f.hom x) := by
  let inv : Rep.ind φ M ⟶ N := (Rep.indResHomEquiv φ M N).symm f
  have hseed :
      inv.hom (Representation.IndV.mk φ M.ρ 1 x) = f.hom x := by
    have hEq : (Rep.indResHomEquiv φ M N) inv = f :=
      LinearEquiv.apply_symm_apply (Rep.indResHomEquiv φ M N) f
    have htmp :
        (((Rep.indResHomEquiv φ M N) inv).hom) x =
          inv.hom (Representation.IndV.mk φ M.ρ 1 x) := by
      rw [Rep.indResHomEquiv_apply]
      rfl
    simpa [hEq] using htmp.symm
  -- Move the general generator back to the unit-coset seed, then use intertwining.
  calc
    inv.hom (Representation.IndV.mk φ M.ρ g x) =
        inv.hom ((Representation.ind φ M.ρ) g⁻¹ (Representation.IndV.mk φ M.ρ 1 x)) := by
          rw [Representation.ind_mk]
          simp
    _ = N.ρ g⁻¹ (inv.hom (Representation.IndV.mk φ M.ρ 1 x)) := by
        simpa using
          (hom_comm_apply inv g⁻¹ (Representation.IndV.mk φ M.ρ 1 x))
    _ = N.ρ g⁻¹ (f.hom x) := by
        rw [hseed]

/-- Helper for Theorem 17-17.3-1: the Frobenius-induced map built from the `ULift`ed subgroup
source sends each standard induced generator to the corresponding standard target generator with
the coefficient reduced by `red_HU`. -/
theorem induced_subrepresentation_lift_ulift_source_apply_mk_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H)
    (g : G) (xU : ULift.{max (max u v) w} W0) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let fHU :=
      induced_subrepresentation_lift_unit_intertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
      (Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let fHU :=
    induced_subrepresentation_lift_unit_intertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU
  -- First evaluate the Frobenius-produced map on the generator, then rewrite the packaged unit
  -- intertwiner and the induced action on the standard target.
  calc
    (((Rep.indResHomEquiv
        H.subtype (Rep.of ρA_HU)
        (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
      (Rep.ofHom fHU)).hom)
      (Representation.IndV.mk H.subtype ρA_HU g xU) =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g⁻¹ (fHU xU) := by
          exact
            indResHomEquiv_symm_apply_mk_local
              (A := A) H.subtype (Rep.of ρA_HU)
              (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))
              (Rep.ofHom fHU) g xU
    _ =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g⁻¹
          (Representation.IndV.mk H.subtype W.toRepresentation 1 (red_HU xU)) := by
            rw [induced_subrepresentation_lift_unit_intertwining_apply_local
              (A := A) (G := G) (ρ := ρ) W ρA_HU red_HU hLiftHU]
    _ = Representation.IndV.mk H.subtype W.toRepresentation g (red_HU xU) := by
          simpa only [Representation.restrictScalars_apply, inv_inv, one_mul] using
            (Representation.ind_mk
              (φ := H.subtype) (ρ := W.toRepresentation) g⁻¹ 1 (red_HU xU))

/-- Helper for Theorem 17-17.3-1: the Frobenius-produced map on the `ULift`ed subgroup source
already intertwines the induced `A[G]`-action with the standard target action. -/
theorem induced_subrepresentation_lift_ulift_source_isIntertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
      uliftRepresentation_witness_local (A := A) ρA_H
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
        Representation.IndV H.subtype ρA_HU →ₗ[A]
          Representation.IndV H.subtype W.toRepresentation :=
      (((Rep.indResHomEquiv
          H.subtype (Rep.of ρA_HU)
          (Rep.of ((Representation.ind H.subtype W.toRepresentation).restrictScalars A))).symm
        (Rep.ofHom fHU)).hom)
    (Representation.ind H.subtype ρA_HU).IsIntertwiningMap
      ((Representation.ind H.subtype W.toRepresentation).restrictScalars A)
      red_u := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
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
  refine Representation.IsIntertwiningMap.mk ?_
  intro g v
  -- The induced source is generated by `IndV.mk`, so the generator formula for `red_u` already
  -- determines the whole equivariance statement after repackaging it as a linear-map equality.
  have hcomp :
      red_u ∘ₗ (Representation.ind H.subtype ρA_HU) g =
        ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g ∘ₗ red_u := by
    apply Representation.IndV.hom_ext
    intro g'
    ext xU
    have hmk_mul :
        red_u (Representation.IndV.mk H.subtype ρA_HU (g' * g⁻¹) xU) =
          Representation.IndV.mk H.subtype W.toRepresentation (g' * g⁻¹) (red_HU xU) := by
      simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
        induced_subrepresentation_lift_ulift_source_apply_mk_local
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH (g' * g⁻¹) xU
    have hmk :
        red_u (Representation.IndV.mk H.subtype ρA_HU g' xU) =
          Representation.IndV.mk H.subtype W.toRepresentation g' (red_HU xU) := by
      simpa [ρA_HU, red_HU, hLiftHU, fHU, red_u] using
        induced_subrepresentation_lift_ulift_source_apply_mk_local
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH g' xU
    calc
      red_u
          ((Representation.ind H.subtype ρA_HU) g
            (Representation.IndV.mk H.subtype ρA_HU g' xU)) =
        red_u (Representation.IndV.mk H.subtype ρA_HU (g' * g⁻¹) xU) := by
          rw [Representation.ind_mk]
      _ = Representation.IndV.mk H.subtype W.toRepresentation (g' * g⁻¹) (red_HU xU) := by
          exact hmk_mul
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
            (Representation.IndV.mk H.subtype W.toRepresentation g' (red_HU xU)) := by
              rw [Representation.restrictScalars_apply, Representation.ind_mk]
      _ =
          ((Representation.ind H.subtype W.toRepresentation).restrictScalars A) g
          (red_u (Representation.IndV.mk H.subtype ρA_HU g' xU)) := by
              rw [hmk]
  exact LinearMap.congr_fun hcomp v

/-- Helper for Theorem 17-17.3-1: on pure tensors, the subgroup residue-field lift on the
`ULift`ed source already satisfies the scalar-extension equivariance identity required before
induction. -/
theorem scalarExtension_source_equiv_tmul_intertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let red_HU :=
      red_H.comp
        (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
    let _ : Module A k := Algebra.toModule
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    ∀ h : H, ∀ z : k, ∀ xU : ULift.{max (max u v) w} W0,
      hLiftHU.1.equiv (((ρA_HU h).baseChange k) (z ⊗ₜ[A] xU)) =
        W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU)) := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let red_HU :=
    red_H.comp
      (ULift.moduleEquiv : ULift.{max (max u v) w} W0 ≃ₗ[A] W0).toLinearMap
  letI : Module A k := Algebra.toModule
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  -- The subgroup reduction already intertwines the `H`-action after passing to `ULift`.
  have hulift_intertwining :
      ∀ h : H, ∀ xU : ULift.{max (max u v) w} W0,
        red_HU (ρA_HU h xU) = (W.toRepresentation.restrictScalars A) h (red_HU xU) := by
    intro h xU
    have hred0 :
        red_H (ρA_H h xU.down) = (W.toRepresentation.restrictScalars A) h (red_H xU.down) := by
      simpa using
        subrepresentation_lift_pointwise
          (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH h xU.down
    simpa [red_HU, ρA_HU, Representation.restrictScalars_apply] using hred0
  dsimp only
  intro h z xU
  -- Check equivariance on pure tensors, where the base-change action is explicit.
  rw [LinearMap.baseChange_tmul]
  calc
    hLiftHU.1.equiv (z ⊗ₜ[A] (ρA_HU h xU)) = z • red_H ((ρA_HU h xU).down) := by
      simpa using hLiftHU.1.equiv_tmul z (ρA_HU h xU)
    _ = z • red_HU (ρA_HU h xU) := by
      rfl
    _ = z • ((W.toRepresentation.restrictScalars A) h (red_HU xU)) := by
      rw [hulift_intertwining h xU]
    _ = z • (W.toRepresentation h (red_HU xU)) := by
      rfl
    _ = W.toRepresentation h (z • red_HU xU) := by
      simp [smul_assoc]
    _ = W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU)) := by
      rw [hLiftHU.1.equiv_tmul]

/-- Helper for Theorem 17-17.3-1: the subgroup residue-field base-change equivalence already
intertwines the scalar-extended `H`-action on pure tensors, so it is an honest representation
intertwiner. -/
theorem scalarExtension_source_equiv_isIntertwining_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    (Representation.scalarExtension ρA_HU).IsIntertwiningMap
      W.toRepresentation hLiftHU.1.equiv.toLinearMap := by
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  refine Representation.IsIntertwiningMap.mk ?_
  intro h
  intro v
  -- On pure tensors, the packaged base-change equivalence is exactly the previously proved
  -- scalar-extension intertwining identity.
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro z xU
    change hLiftHU.1.equiv (((ρA_HU h).baseChange k) (z ⊗ₜ[A] xU)) =
        W.toRepresentation h (hLiftHU.1.equiv (z ⊗ₜ[A] xU))
    simpa [ρA_HU, hLiftHU] using
      scalarExtension_source_equiv_tmul_intertwining_local
        (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH h z xU
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Theorem 17-17.3-1: the pure-tensor intertwining identity packages the subgroup
scalar extension into an honest `H`-equivariant source equivalence. -/
noncomputable abbrev scalarExtension_source_equiv_of_residueFieldLift_local
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    [Module.Free A W0] [Module.Finite A W0]
    (ρA_H : Representation A H W0)
    (red_H : W0 →ₗ[A] W.toSubmodule)
    (hLiftH : IsResidueFieldLift W.toRepresentation ρA_H red_H) :
    let ρA_HU := uliftRepresentation_witness_local (A := A) ρA_H
    let hLiftHU :=
      residueFieldLift_ulift_witness_local
        (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) :=
      TensorProduct.leftModule
    (Representation.scalarExtension ρA_HU).Equiv W.toRepresentation :=
  let ρA_HU : Representation A H (ULift.{max (max u v) w} W0) :=
    uliftRepresentation_witness_local (A := A) ρA_H
  let hLiftHU :=
    residueFieldLift_ulift_witness_local
      (A := A) (ρ := W.toRepresentation) (ρA := ρA_H) (red := red_H) hLiftH
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (TensorProduct A k (ULift.{max (max u v) w} W0)) := TensorProduct.leftModule
  let hInter :=
    scalarExtension_source_equiv_isIntertwining_local
      (A := A) (G := G) (ρ := ρ) W ρA_H red_H hLiftH
  Representation.Equiv.mk hLiftHU.1.equiv
    (fun h ↦ LinearMap.ext fun v ↦ hInter.isIntertwining h v)



end

end Representation
