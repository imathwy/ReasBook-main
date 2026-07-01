import Serre.Chap07.Proposition_7_7_4_1.MackeyCoordinateEquivalences

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientFrobenius (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: the unit-copy projection intertwines an induced self-map
with the original self-map of `ρ`. -/
theorem induced_identity_copy_projection_indMap
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ) :
    inducedIdentityCopyProjection H ρ ∘ₗ (Rep.indMap H.subtype g).hom =
      g.hom ∘ₗ inducedIdentityCopyProjection H ρ := by
  -- Equality on the induced representation is checked on the standard generators `IndV.mk`.
  apply Representation.IndV.hom_ext
  intro h
  ext v
  classical
  by_cases hh : h ∈ H
  · -- On the unit-copy translate indexed by `h ∈ H`, both sides reduce to the same `ρ h⁻¹` term.
    have hleft :
        inducedIdentityCopyProjection H ρ
            ((Rep.indMap H.subtype g).hom (Representation.IndV.mk H.subtype ρ h v)) =
          ρ ⟨h, hh⟩⁻¹ (g.hom v) := by
      simp [Rep.indMap, inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux,
        TensorProduct.lift.tmul, hh, LinearMap.comp_apply]
    have hright :
        g.hom (inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ h v)) =
          ρ ⟨h, hh⟩⁻¹ (g.hom v) := by
      calc
        g.hom (inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ h v)) =
            g.hom (ρ ⟨h, hh⟩⁻¹ v) := by
              simp [inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux,
                TensorProduct.lift.tmul, hh]
        _ = ρ ⟨h, hh⟩⁻¹ (g.hom v) := by
              simpa using LinearMap.congr_fun (g.hom.2 ⟨h, hh⟩⁻¹) v
    simpa [LinearMap.comp_apply] using hleft.trans hright.symm
  · -- Outside the unit-copy block, the explicit projection kills both sides.
    simp [Rep.indMap, inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux,
      TensorProduct.lift.tmul, hh, LinearMap.comp_apply]
/-- Helper for Proposition 7-7.4-1: evaluating the `ULift`ed `Ind ≅ Coind` comparison at `1`
recovers the explicit projection onto the unit copy of `ρ` inside `Ind_H^G(ρ)`. -/
theorem ulift_indCoind_evaluate_one_eq_unit_copy_projection
    (H : Subgroup G) (ρ : Representation k H V) :
    let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
    ULift.moduleEquiv.toLinearMap ∘ₗ
        LinearMap.proj (1 : G) ∘ₗ
          (Representation.coindV H.subtype (uliftRepresentation (k := k) ρ)).subtype ∘ₗ
            ((Rep.mkIso
                (inducedRepresentationEquiv (k := k) H
                  (uliftRepresentationEquiv (k := k) ρ)) ≪≫
                Rep.indCoindIso (Rep.of (uliftRepresentation (k := k) ρ))).hom.hom.toLinearMap)
      = inducedIdentityCopyProjection H ρ := by
  classical
  let _ : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  -- Both sides are determined by their values on the standard generators `IndV.mk h v`.
  apply Representation.IndV.hom_ext
  intro h
  ext v
  by_cases hh : h ∈ H
  · -- On the unit-copy block, the finite-index `Ind ≅ Coind` comparison evaluates to `ρ h⁻¹`.
    have hrel : (QuotientGroup.rightRel H).r (1 : G) h := by
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      simp
    simp [LinearMap.comp_apply, inducedRepresentationEquiv, uliftRepresentationEquiv,
      Rep.indCoindIso, Rep.indToCoind, Rep.indToCoindAux, inducedIdentityCopyProjection,
      inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul, hh, hrel]
    change (ρ ⟨h⁻¹, H.inv_mem hh⟩ v) = (ρ ⟨h, hh⟩⁻¹) v
    rfl
  · -- Outside the unit-copy block, both the explicit projection and evaluation at `1` vanish.
    have hrel : ¬ (QuotientGroup.rightRel H).r (1 : G) h := by
      intro hrel
      rcases hrel with ⟨s, hs⟩
      apply hh
      have hs_mul : (s : G) * h = 1 := by
        simpa using hs
      have hs_inv : h⁻¹ = (s : G) := inv_eq_of_mul_eq_one_left hs_mul
      have : h = (s : G)⁻¹ := by
        simpa using congrArg Inv.inv hs_inv
      rw [this]
      exact H.inv_mem s.2
    simp [LinearMap.comp_apply, inducedRepresentationEquiv, uliftRepresentationEquiv,
      Rep.indCoindIso, Rep.indToCoind, Rep.indToCoindAux, inducedIdentityCopyProjection,
      inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul, hh, hrel]
/-- Helper for Proposition 7-7.4-1: the Frobenius-restricted hom attached to an induced
endomorphism is obtained by applying the endomorphism and then projecting to the unit copy. -/
theorem restricted_hom_apply_eq_unit_copy_projection
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (x : Representation.IndV H.subtype ρ) :
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom x).down =
      inducedIdentityCopyProjection H ρ (F.hom x) := by
  classical
  let _ : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  -- Route correction: prove the Frobenius transport exactly at the restricted-hom stage, before
  -- any Mackey decomposition or coordinate reindexing is applied.
  simp [induced_endomorphism_to_restricted_hom_equiv, homCongrRight, intertwiningMapCongrRight,
    LinearMap.comp_apply]
  simpa [LinearMap.comp_apply] using
    congrArg (fun T ↦ T (F.hom x))
      (ulift_indCoind_evaluate_one_eq_unit_copy_projection (k := k) H ρ)
/-- Helper for Proposition 7-7.4-1: for an induced self-map `Rep.indMap H.subtype g`, the
restricted Frobenius image is obtained by first projecting to the unit copy and then applying
`g`. -/
theorem restricted_indMap_apply_eq_self_on_projection
    (H : Subgroup G) (ρ : Representation k H V)
    (g : Rep.of ρ ⟶ Rep.of ρ)
    (x : Representation.IndV H.subtype ρ) :
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)).hom x).down =
      g.hom (inducedIdentityCopyProjection H ρ x) := by
  -- First rewrite the restricted Frobenius image as the explicit unit-copy projection.
  calc
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)).hom x).down =
      inducedIdentityCopyProjection H ρ ((Rep.indMap H.subtype g).hom x) := by
        exact restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ
          (Rep.indMap H.subtype g) x
    _ = g.hom (inducedIdentityCopyProjection H ρ x) := by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun (induced_identity_copy_projection_indMap H ρ g) x
/-- Helper for Proposition 7-7.4-1: the restricted Frobenius image of `Rep.indMap H.subtype g`
vanishes on the translated seed vector attached to any nonidentity double coset. -/
theorem restricted_indMap_apply_translated_generator_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    (g : Rep.of ρ ⟶ Rep.of ρ)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)).hom
        (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)).down = 0 := by
  -- The Frobenius image factors through the unit-copy projection, and that projection kills any
  -- translated seed from a nonidentity double coset.
  calc
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)).hom
        (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)).down =
      g.hom
        (inducedIdentityCopyProjection H ρ
          (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)) := by
        exact restricted_indMap_apply_eq_self_on_projection (k := k) H ρ g
          (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ x)
    _ = g.hom 0 := by
        rw [induced_identity_copy_projection_apply_mk_inv_representative_of_ne_identity
          (k := k) (H := H) (ρ := ρ) (q := q) hq x]
    _ = 0 := by simp
/-- Helper for Proposition 7-7.4-1: the Frobenius map `Rep.indResHomEquiv` evaluates an induced
intertwiner on the seed generator `IndV.mk ... 1`. -/
theorem indResHomEquiv_apply_mk_one
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    {φ : Γ →* Δ}
    {A : Rep k Γ} {B : Rep k Δ}
    (f : Rep.ind φ A ⟶ B) (x : A.V) :
    (((Rep.indResHomEquiv φ A B) f).hom) x =
      f.hom (Representation.IndV.mk φ A.ρ 1 x) := by
  -- This is exactly the defining `toFun` formula for Frobenius reciprocity.
  rw [Rep.indResHomEquiv_apply]
  rfl
/-- Helper for Proposition 7-7.4-1: the inverse `resCoind` adjunction evaluates a coinduced map
at `1`. -/
theorem resCoindHomEquiv_symm_apply_one
    {Γ Δ : Type*} [Monoid Γ] [Monoid Δ]
    {φ : Γ →* Δ}
    {B : Rep k Δ} {A : Rep k Γ}
    (f : B ⟶ Rep.coind φ A) (x : B.V) :
    (((Rep.resCoindHomEquiv φ B A).symm f).hom) x =
      ((Representation.coindV φ A.ρ).subtype (f.hom x)) 1 := by
  -- This is the defining `invFun` formula for the coinduction adjunction.
  rw [Rep.resCoindHomEquiv_symm_apply]
  rfl
/-- Helper for Proposition 7-7.4-1: after isolating the identity double-coset component, the
identity-coordinate statement is exactly the fixed-`s` Mackey block followed by the canonical
identity-coordinate equivalence. -/
theorem identity_coordinate_eq_intermediate_block_apply
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ)) (v : V) :
    (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
          (DoubleCoset.mk H H (1 : G)))).hom) v =
      (Rep.Hom.hom
        ((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          ((mackey_coordinate_hom_equiv (k := k) H ρ
              (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))))
            (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F)
              ⟨DoubleCoset.mk H H (1 : G)⟩))))
        v := by
  -- This is the already-verified reduction from the global coordinate family to the fixed
  -- identity Mackey block.
  rw [induced_endomorphism_coordinate_eq_reindexed]
  rw [ulift_doubleCoset_family_equiv_apply]
  simp [mackey_coordinate_hom_equiv_ulift, mackey_identity_coordinate_equiv_self_hom]
/-- Helper for Proposition 7-7.4-1: at a nonidentity Mackey block, the Frobenius coordinate of an
induced self-map is already reduced to the fixed-`s` Mackey block before the final seed
computation. -/
theorem coordinate_eq_intermediate_block_apply
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q).hom x =
      (Rep.Hom.hom
        ((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q))
          (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F)
            ⟨q⟩)))
        x := by
  let qU : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨q⟩
  -- This is the fixed-`q` specialization of the final `ULift` reindexing step.
  rw [induced_endomorphism_coordinate_eq_reindexed]
  rw [ulift_doubleCoset_family_equiv_apply]
  -- After evaluating the reindexed family at `⟨q⟩`, only the fixed-`q` block remains.
  change
    ((((mackey_coordinate_hom_equiv_ulift (k := k) H ρ qU)
        (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) qU)).hom) x) =
      (Rep.Hom.hom
        ((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q))
          (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) qU)))
        x
  rfl
/-- Helper for Proposition 7-7.4-1: the intermediate Mackey family is definitionally the
coordinate family obtained from the transported direct-sum morphism before the final Frobenius
step. -/
theorem induced_endomorphism_mackey_intermediate_coordinate_eq_directSum_coordinate
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (q : ULift (DoubleCoset.Quotient (H : Set G) H)) :
    let τ : Rep k G := Rep.ind H.subtype (of ρ)
    let π : ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H := fun q' ↦
      mackeySummand H H (of ρ) (doubleCosetRepresentative H q'.down)
    let R :
        Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ) :=
      (induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F
    let S :
        Rep.of (Representation.directSum fun q' ↦ (π q').ρ) ⟶
          Rep.of (uliftRepresentation (k := k) ρ) :=
      (homCongrLeft (k := k)
        (A := Rep.res H.subtype τ)
        (B := Rep.of (Representation.directSum fun q' ↦ (π q').ρ))
        (C := Rep.of (uliftRepresentation (k := k) ρ))
        (induced_restriction_mackey_iso (k := k) H ρ)) R
    ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q =
      ((directSum_hom_equivPi_local (k := k) π
          (Rep.of (uliftRepresentation (k := k) ρ))) S) q := by
  -- This just unfolds the final direct-sum coordinate stage of the intermediate equivalence.
  rfl
/-- Helper for Proposition 7-7.4-1: the intermediate Mackey block at `q` is obtained by applying
the restricted Frobenius morphism to the vector transported back from the `q`-summand through the
inverse Mackey isomorphism. -/
theorem intermediate_block_apply_eq_restricted_hom_apply
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (x : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) :
    ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q).hom x).down =
      ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
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
            q x))).down := by
  classical
  let τ : Rep k G := Rep.ind H.subtype (of ρ)
  let π : ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H := fun q' ↦
    mackeySummand H H (of ρ) (doubleCosetRepresentative H q'.down)
  let R :
      Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ) :=
    (induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F
  let S :
      Rep.of (Representation.directSum fun q' ↦ (π q').ρ) ⟶
        Rep.of (uliftRepresentation (k := k) ρ) :=
    (homCongrLeft (k := k)
      (A := Rep.res H.subtype τ)
      (B := Rep.of (Representation.directSum fun q' ↦ (π q').ρ))
      (C := Rep.of (uliftRepresentation (k := k) ρ))
      (induced_restriction_mackey_iso (k := k) H ρ)) R
  -- Rewrite the intermediate block as the `q`-th direct-sum coordinate of the transported
  -- restricted map, then evaluate that coordinate on the named `DirectSum.lof` seed.
  change
    ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q).hom x).down =
      (S.hom (DirectSum.lof k _ (fun q' ↦ (π q').V) q x)).down
  rw [induced_endomorphism_mackey_intermediate_coordinate_eq_directSum_coordinate
    (k := k) H ρ F q]
  rw [directSum_hom_equivPi_local_apply (k := k)
    (π := π)
    (τ := Rep.of (uliftRepresentation (k := k) ρ))
    S q x]
/-- Helper for Proposition 7-7.4-1: at a nonidentity Mackey block, the Frobenius coordinate of an
induced self-map is already reduced to the fixed-`s` Mackey block before the final seed
computation. -/
theorem off_identity_coordinate_eq_intermediate_block_apply
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q)) :
    (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
        (Rep.indMap H.subtype g)) q).hom x =
      (Rep.Hom.hom
        ((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q))
          (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
            (Rep.indMap H.subtype g)) ⟨q⟩)))
        x := by
  -- This is the general coordinate-to-intermediate reduction specialized to `Rep.indMap`.
  exact coordinate_eq_intermediate_block_apply (k := k) H ρ (Rep.indMap H.subtype g) q x
end MackeyIrreducibilityCriterion

end Representation
