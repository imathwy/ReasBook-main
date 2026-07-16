import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionTransport

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientSingletonOffIdentityBoundary (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: away from the singleton support, the transported Mackey
summands land in the kernel of the identity-block projection after applying `F`. -/
theorem identity_mackey_block_projection_apply_singleton_off_identity_lof_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero (Nat.card (identity_mackey_subgroup H) : k)]
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (q' : ULift (DoubleCoset.Quotient (H : Set G) H))
    (hq' : q'.down = DoubleCoset.mk H H (1 : G) ∨ q'.down ≠ q)
    (y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) :
    identity_mackey_block_projection (k := k) H ρ
      (F.hom
        (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
            DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
              (fun r ↦
                Representation.IndV
                  (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
                  ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ)) →ₗ[k]
            Representation.IndV H.subtype ρ)
          (DirectSum.lof k _
            (fun r : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ))
            q' y))) = 0 := by
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun r ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ)
  let x : Representation.IndV H.subtype ρ :=
    (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M →ₗ[k]
        Representation.IndV H.subtype ρ)
      (DirectSum.lof k _ M q' y))
  have hrestricted_down :
      (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom x).down = 0 := by
    simpa [x, M] using
      singleton_off_identity_restricted_hom_apply_lof_eq_zero
        (k := k) H ρ hq f F hF q' hq' y
  have hunit_copy : inducedIdentityCopyProjection H ρ (F.hom x) = 0 := by
    calc
      inducedIdentityCopyProjection H ρ (F.hom x) =
          (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom x).down := by
            symm
            exact restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ F x
      _ = 0 := hrestricted_down
  have hunit_block :
      identity_mackey_unit_projection (k := k) H ρ
        (identity_mackey_block_projection (k := k) H ρ (F.hom x)) = 0 := by
    have hcomp := LinearMap.congr_fun
      (identity_mackey_block_unit_projection_eq_unit_copy_projection (k := k) H ρ)
      (F.hom x)
    change identity_mackey_unit_projection (k := k) H ρ
        (identity_mackey_block_projection (k := k) H ρ (F.hom x)) =
      inducedIdentityCopyProjection H ρ (F.hom x) at hcomp
    rw [hcomp, hunit_copy]
  change identity_mackey_block_projection (k := k) H ρ (F.hom x) = 0
  apply (identity_mackey_block_unit_projection_injective (k := k) H ρ)
  simpa [identity_mackey_unit_projection, identity_mackey_subgroup,
    identity_mackey_representation, identity_mackey_double_coset] using hunit_block

end MackeyIrreducibilityCriterion

end Representation
