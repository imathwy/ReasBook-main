import Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionDefs

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientIdentityProjectionRepresentativeSeeds
    (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _


/-- Helper for Proposition 7-7.4-1: a left `H`-translate of an induced generator is absorbed
by the coefficient representation. -/
theorem ind_mk_left_translate
    (H : Subgroup G) (ρ : Representation k H V)
    (h : H) (g : G) (v : V) :
    Representation.IndV.mk H.subtype ρ ((h : G) * g) v =
      Representation.IndV.mk H.subtype ρ g (ρ h⁻¹ v) := by
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Proposition 7-7.4-1: an inverse left `H`-translate of an induced generator is
absorbed by the coefficient representation. -/
theorem ind_mk_inv_left_translate
    (H : Subgroup G) (ρ : Representation k H V)
    (h : H) (g : G) (v : V) :
    Representation.IndV.mk H.subtype ρ ((h : G)⁻¹ * g) v =
      Representation.IndV.mk H.subtype ρ g (ρ h v) := by
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]


/-- Helper for Proposition 7-7.4-1: on the identity Mackey block, the unit-copy projection
intertwines the ambient `H`-action with `ρ`. -/
theorem identity_mackey_unit_projection_intertwine
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)] (h : H)
    (y : identity_mackey_block (k := k) H ρ) :
    identity_mackey_unit_projection (k := k) H ρ
        (((mackeySummand H H (of ρ)
          (doubleCosetRepresentative H (identity_mackey_double_coset H))).ρ) h y) =
      ρ h (identity_mackey_unit_projection (k := k) H ρ y) := by
  let K : Subgroup H := identity_mackey_subgroup H
  let σ : Representation k K V := identity_mackey_representation (k := k) H ρ
  change inducedIdentityCopyProjection K σ (((Rep.ind K.subtype (of σ)).ρ) h y) =
    ρ h (inducedIdentityCopyProjection K σ y)
  have hlin :
      inducedIdentityCopyProjection K σ ∘ₗ (((Rep.ind K.subtype (of σ)).ρ) h) =
        (ρ h) ∘ₗ inducedIdentityCopyProjection K σ := by
    apply Representation.IndV.hom_ext (φ := K.subtype) (ρ := σ)
    intro g
    ext v
    simp [K, σ, identity_mackey_subgroup, identity_mackey_double_coset,
      doubleCosetRepresentative_identity, mackeySubgroup, inducedIdentityCopyProjection,
      inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul]
    change (ρ (h * g⁻¹)) v = (ρ h) ((ρ g⁻¹) v)
    simpa [Module.End.mul_apply] using
      congrArg (fun T : V →ₗ[k] V ↦ T v) (ρ.map_mul h g⁻¹)
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hlin y


/-- Helper for Proposition 7-7.4-1: the identity Mackey-block projection intertwines the
restricted `H`-action with the identity Mackey summand action. -/
theorem identity_mackey_block_projection_intertwine
    (H : Subgroup G) (ρ : Representation k H V)
    (h : H) (x : Representation.IndV H.subtype ρ) :
    identity_mackey_block_projection (k := k) H ρ
        (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) h x) =
      (((mackeySummand H H (of ρ)
        (doubleCosetRepresentative H (identity_mackey_double_coset H))).ρ) h)
        (identity_mackey_block_projection (k := k) H ρ x) := by
  let q1 : ULift (DoubleCoset.Quotient (H : Set G) H) :=
    ⟨DoubleCoset.mk H H (1 : G)⟩
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun q ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
  let e : Representation.IndV H.subtype ρ →ₗ[k] DirectSum _ M :=
    ((induced_restriction_mackey_iso (k := k) H ρ).hom.hom.toLinearMap :
      Representation.IndV H.subtype ρ →ₗ[k] DirectSum _ M)
  change (DirectSum.component k _ M q1) (e (((Rep.res H.subtype
      (Rep.ind H.subtype (of ρ))).ρ) h x)) =
    (((mackeySummand H H (of ρ) (doubleCosetRepresentative H q1.down)).ρ) h)
      ((DirectSum.component k _ M q1) (e x))
  have he := LinearMap.congr_fun
    (((induced_restriction_mackey_iso (k := k) H ρ).hom.hom.2 h)) x
  change e (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) h x) =
    ((Representation.directSum fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
      (mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)).ρ) h) (e x) at he
  rw [he]
  change (((Representation.directSum fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
      (mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)).ρ) h) (e x)) q1 =
    (((mackeySummand H H (of ρ) (doubleCosetRepresentative H q1.down)).ρ) h) ((e x) q1)
  simp [Representation.directSum, DirectSum.lmap_apply]


/-- Helper for Proposition 7-7.4-1: the unit projection after the identity Mackey-block
projection is equivariant for the restricted `H`-action. -/
theorem identity_mackey_unit_projection_comp_projection_intertwine
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero (Nat.card (identity_mackey_subgroup H) : k)]
    (h : H) (x : Representation.IndV H.subtype ρ) :
    identity_mackey_unit_projection (k := k) H ρ
        (identity_mackey_block_projection (k := k) H ρ
          (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) h x)) =
      ρ h (identity_mackey_unit_projection (k := k) H ρ
        (identity_mackey_block_projection (k := k) H ρ x)) := by
  rw [identity_mackey_block_projection_intertwine (k := k) H ρ h x]
  exact identity_mackey_unit_projection_intertwine (k := k) H ρ h
    (identity_mackey_block_projection (k := k) H ρ x)

/-- Helper for Proposition 7-7.4-1: the identity Mackey-block projector kills the translated
seed attached to any nonidentity double coset. -/
theorem identity_mackey_block_projection_apply_mk_inv_representative_of_ne_identity
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (v : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    identity_mackey_block_projection (k := k) H ρ
        (Representation.IndV.mk H.subtype ρ
          (doubleCosetRepresentative H q)⁻¹ v) = 0 := by
  let y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ) :=
    Representation.IndV.mk
      (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)).ρ)
      1 v
  have hqU : (⟨q⟩ : ULift (DoubleCoset.Quotient (H : Set G) H)) ≠
      ⟨DoubleCoset.mk H H (1 : G)⟩ := by
    intro h
    exact hq (ULift.ext_iff.mp h)
  have hseed :
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q' ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
          ⟨q⟩ y)) =
        Representation.IndV.mk H.subtype ρ
          (doubleCosetRepresentative H q)⁻¹ v := by
    simpa [y] using
      induced_restriction_mackey_iso_inv_apply_lof_seed (k := k) H ρ q v
  calc
    identity_mackey_block_projection (k := k) H ρ
        (Representation.IndV.mk H.subtype ρ
          (doubleCosetRepresentative H q)⁻¹ v) =
      identity_mackey_block_projection (k := k) H ρ
        (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
            DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
              (fun q' ↦
                Representation.IndV
                  (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                  ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
            Representation.IndV H.subtype ρ)
          (DirectSum.lof k _
            (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
            ⟨q⟩ y)) := by
          rw [hseed]
    _ = 0 := by
          exact identity_mackey_block_projection_apply_mackey_lof_of_ne
            (k := k) H ρ ⟨q⟩ hqU y

/-- Helper for Proposition 7-7.4-1: after the identity Mackey-block projection, the
unit-copy projection kills every translated seed from a nonidentity double coset. -/
theorem identity_mackey_block_unit_projection_comp_mk_inv_representative_of_ne_identity
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero (Nat.card (identity_mackey_subgroup H) : k)]
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G)) :
    identity_mackey_unit_projection (k := k) H ρ ∘ₗ
      identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (Representation.IndV.mk H.subtype ρ
          (doubleCosetRepresentative H q)⁻¹) = 0 := by
  ext v
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    identity_mackey_block_projection_apply_mk_inv_representative_of_ne_identity
      (k := k) H ρ hq v]
  simp

end MackeyIrreducibilityCriterion

end Representation
