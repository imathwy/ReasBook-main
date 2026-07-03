import Serre.Chap07.Proposition_7_7_4_1.MackeySeedTransport

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientSelfMapCoordinates (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: morphisms out of a representation direct sum are equivalent to
families of morphisms out of the individual summands. -/
theorem identity_coordinate_eq_unit_copy_composite_apply
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ)) (v : V) :
    (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
          (DoubleCoset.mk H H (1 : G)))).hom) v =
      inducedIdentityCopyProjection H ρ
        (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
  let q1 : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H (1 : G)
  let q1U : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨q1⟩
  let y :
      Representation.IndV
        (mackeySubgroup H H (doubleCosetRepresentative H q1)).subtype
        ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q1)).ρ) :=
    Representation.IndV.mk
      (mackeySubgroup H H (doubleCosetRepresentative H q1)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q1)).ρ)
      1 v
  -- Route correction: specialize the inverse Mackey seed transport at the identity double coset,
  -- then read the same vector first through the intermediate block and finally through the
  -- restricted Frobenius/unit-copy projection.
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
          q1U y)) =
        Representation.IndV.mk H.subtype ρ 1 v := by
    -- The identity representative is `1`, so the inverse Mackey transport lands on the usual
    -- unit generator.
    simpa [q1, q1U, y, identity_doubleCosetRepresentative_inv (H := H)] using
      induced_restriction_mackey_iso_inv_apply_lof_seed (k := k) H ρ q1 v
  calc
    (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
            (DoubleCoset.mk H H (1 : G)))).hom) v =
      (Rep.Hom.hom
        ((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          ((mackey_coordinate_hom_equiv (k := k) H ρ
              (doubleCosetRepresentative H q1))
            (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F)
              q1U)))) v := by
          simpa [q1, q1U] using
            identity_coordinate_eq_intermediate_block_apply (k := k) H ρ F v
    _ = ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q1U).hom y).down := by
          -- Evaluate the identity Mackey coordinate on the standard seed of the identity block.
          simpa [q1, q1U, y, doubleCosetRepresentative_identity] using
            mackey_coordinate_hom_equiv_apply (k := k) H ρ
              (doubleCosetRepresentative H q1)
              (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q1U) v
    _ = ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
          (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
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
              q1U y))).down := by
          -- The intermediate Mackey block is read by applying the restricted Frobenius morphism
          -- to the inverse-transported direct-sum seed.
          simpa [q1, q1U, y] using
            intermediate_block_apply_eq_restricted_hom_apply (k := k) H ρ F q1U y
    _ = (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom
          (Representation.IndV.mk H.subtype ρ 1 v)).down := by
          -- Substitute the explicit inverse-image of the identity direct-sum seed.
          simpa [q1, q1U, y] using congrArg
            (fun z : Representation.IndV H.subtype ρ ↦
              (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom z).down)
            hseed
    _ = inducedIdentityCopyProjection H ρ
          (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
          -- The restricted Frobenius morphism is exactly the unit-copy projection on the target.
          simpa using
            restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ F
              (Representation.IndV.mk H.subtype ρ 1 v)

/-- Helper for Proposition 7-7.4-1: the identity Mackey coordinate of `Rep.indMap` recovers the
original self-intertwiner `g`. -/
theorem induced_self_map_identity_coordinate
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ) :
    (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
          (Rep.indMap H.subtype g)) (DoubleCoset.mk H H (1 : G))) = g := by
  -- Evaluate the identity coordinate on `v`, then compare with the concrete `unit-copy` formula.
  apply Rep.Hom.ext
  ext v
  calc
    (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
            (Rep.indMap H.subtype g)) (DoubleCoset.mk H H (1 : G)))).hom) v =
      inducedIdentityCopyProjection H ρ
        ((Rep.indMap H.subtype g).hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
          simpa using
            identity_coordinate_eq_unit_copy_composite_apply (k := k) H ρ
              (Rep.indMap H.subtype g) v
    _ =
      g.hom (inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 v)) := by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun (induced_identity_copy_projection_indMap H ρ g)
            (Representation.IndV.mk H.subtype ρ 1 v)
    _ = g.hom v := by
        rw [induced_identity_copy_projection_apply_mk_one]

/-- Helper for Proposition 7-7.4-1: every nonidentity Mackey coordinate of `Rep.indMap` is zero. -/
theorem induced_self_map_off_identity_coordinate_apply_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
      (Rep.indMap H.subtype g)) q).hom x = 0 := by
  let qU : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨q⟩
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun q' ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)
  let R :
      Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ⟶
        Rep.of (uliftRepresentation (k := k) ρ) :=
    (induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ)
      (Rep.indMap H.subtype g)
  have htransport :
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
            (Rep.indMap H.subtype g)) qU).hom
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
            1 x)).down =
        (R.hom
          (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
              DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M →ₗ[k]
                Representation.IndV H.subtype ρ)
            (DirectSum.lof k _ M qU
              (Representation.IndV.mk
                (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
                1 x)))).down := by
    -- This is the same direct-sum-to-restricted-hom adapter as in the identity block, now read at
    -- the off-identity summand.
    simpa [R, qU, M] using
      intermediate_block_apply_eq_restricted_hom_apply (k := k) H ρ
        (Rep.indMap H.subtype g) qU
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
          1 x)
  have hseed :
      (R.hom
        (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
            DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M →ₗ[k]
              Representation.IndV H.subtype ρ)
          (DirectSum.lof k _ M qU
            (Representation.IndV.mk
              (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
              1 x)))).down =
        (R.hom
          (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)).down := by
    -- The inverse Mackey isomorphism sends the `q`-summand seed back to the translated generator.
    simpa [R, qU, M] using
      congrArg (fun z : Representation.IndV H.subtype ρ ↦ (R.hom z).down)
        (induced_restriction_mackey_iso_inv_apply_lof_seed (k := k) H ρ q x)
  calc
    (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)) q).hom x =
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
            (Rep.indMap H.subtype g)) qU).hom
          (Representation.IndV.mk
            (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
            1 x)).down := by
          -- Read the fixed `q`-block on its standard seed generator.
          calc
            (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
                (Rep.indMap H.subtype g)) q).hom x =
              (((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q))
                    (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
                      (Rep.indMap H.subtype g)) qU)).hom) x := by
                    simpa [qU] using
                      off_identity_coordinate_eq_intermediate_block_apply (k := k) H ρ g q x
            _ = ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
                    (Rep.indMap H.subtype g)) qU).hom
                  (Representation.IndV.mk
                    (mackeySubgroup H H (doubleCosetRepresentative H qU.down)).subtype
                    ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H qU.down)).ρ)
                    1 x)).down := by
                    simpa [qU] using
                      mackey_coordinate_hom_equiv_apply (k := k) H ρ
                        (doubleCosetRepresentative H q)
                        (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
                          (Rep.indMap H.subtype g)) qU)
                        x
    _ = (R.hom (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)).down :=
        htransport.trans hseed
    _ = 0 := by
        exact restricted_indMap_apply_translated_generator_eq_zero (k := k) H ρ g q hq x

/-- Helper for Proposition 7-7.4-1: a bundled representation morphism is zero once all of its
values are zero. -/
theorem induced_self_map_off_identity_coordinate_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (hq : q ≠ DoubleCoset.mk H H (1 : G)) :
    ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
      (Rep.indMap H.subtype g)) q = 0 := by
  -- Reassemble the already-normalized pointwise vanishing into equality of bundled morphisms.
  exact rep_hom_eq_zero_of_apply_eq_zero
    (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
      (Rep.indMap H.subtype g)) q)
    (fun x ↦ induced_self_map_off_identity_coordinate_apply_eq_zero (k := k) H ρ g q hq x)
end MackeyIrreducibilityCriterion

end Representation
