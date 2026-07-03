import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientIdentityProjectionTransport (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: if a nonzero linear projection vanishes on the image of a
surjective map, then that map cannot be surjective. -/
theorem induced_self_map_off_identity_intermediate_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (hq : q ≠ DoubleCoset.mk H H (1 : G)) :
    ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ)
      (Rep.indMap H.subtype g)) ⟨q⟩ = 0 := by
  -- The final coordinate equivalence is just the `ULift` reindexing of the intermediate family.
  simpa [induced_endomorphism_coordinate_eq_reindexed, ulift_doubleCoset_family_equiv_apply] using
    induced_self_map_off_identity_coordinate_eq_zero (k := k) H ρ g q hq

/-- Helper for Proposition 7-7.4-1: if a Mackey coordinate family is a singleton supported at `q`,
then every distinct intermediate block already vanishes before the final Frobenius transport. -/
theorem singleton_off_identity_family_projection_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (v : V) :
    inducedIdentityCopyProjection H ρ
      (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) = 0 := by
  have hidentity_coordinate_zero :
      ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
        (DoubleCoset.mk H H (1 : G)) = 0 := by
    simpa [hF] using
      singleton_mackey_coordinate_family_identity_eq_zero (k := k) H ρ hq f
  -- Apply the identity-coordinate formula to the unit generator and use that the singleton family
  -- vanishes at the identity double coset.
  have hEval := congrArg
      (fun z ↦ ((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ) z).hom v)
      hidentity_coordinate_zero
  calc
    inducedIdentityCopyProjection H ρ
        (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) =
      ((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
            (DoubleCoset.mk H H (1 : G)))).hom v := by
          symm
          exact identity_coordinate_eq_unit_copy_composite_apply (k := k) H ρ F v
    _ = 0 := by
        simpa using hEval

/-- Helper for Proposition 7-7.4-1: a Mackey singleton supported away from the identity double
coset kills the entire identity Mackey block, so its explicit unit-copy projection vanishes on
every generator indexed by an element of `H`. -/
theorem singleton_off_identity_identity_block_projection_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (h : H) (v : V) :
    inducedIdentityCopyProjection H ρ
      (F.hom (Representation.IndV.mk H.subtype ρ (h : G) v)) = 0 := by
  let R :
      Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ⟶
        Rep.of (uliftRepresentation (k := k) ρ) :=
    (induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F
  have hunit_zero_down :
      (R.hom (Representation.IndV.mk H.subtype ρ 1 v)).down = 0 := by
    -- The identity-supported unit generator case is the already-proved identity-coordinate
    -- vanishing for an off-identity singleton Mackey family.
    calc
      (R.hom (Representation.IndV.mk H.subtype ρ 1 v)).down =
          inducedIdentityCopyProjection H ρ
            (F.hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
            simpa [R] using
              restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ F
                (Representation.IndV.mk H.subtype ρ 1 v)
      _ = 0 := singleton_off_identity_family_projection_eq_zero (k := k) H ρ hq f F hF v
  have hunit_zero :
      R.hom (Representation.IndV.mk H.subtype ρ 1 v) = 0 := by
    exact ULift.ext _ _ hunit_zero_down
  have htransport :
      R.hom (Representation.IndV.mk H.subtype ρ (h : G) v) = 0 := by
    -- Intertwining transports the vanishing from the unit generator across the whole identity
    -- double-coset block indexed by `H`.
    have hintertwine :=
      LinearMap.congr_fun (R.hom.2 h⁻¹) (Representation.IndV.mk H.subtype ρ 1 v)
    calc
      R.hom (Representation.IndV.mk H.subtype ρ (h : G) v) =
          R.hom
            ((((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) h⁻¹)
              (Representation.IndV.mk H.subtype ρ 1 v)) := by
            simp
      _ = (uliftRepresentation (k := k) ρ) h⁻¹
            (R.hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
            simpa using hintertwine
      _ = 0 := by
            rw [hunit_zero]
            simp
  -- Translate the restricted-hom statement back to the explicit unit-copy projection.
  calc
    inducedIdentityCopyProjection H ρ
        (F.hom (Representation.IndV.mk H.subtype ρ (h : G) v)) =
      (R.hom (Representation.IndV.mk H.subtype ρ (h : G) v)).down := by
        symm
        simpa [R] using
          restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ F
            (Representation.IndV.mk H.subtype ρ (h : G) v)
    _ = 0 := by
        simpa using congrArg ULift.down htransport

/-- Helper for Proposition 7-7.4-1: a Mackey singleton supported away from the identity double
coset has restricted Frobenius image zero on every generator indexed by an element of `H`. -/
theorem singleton_off_identity_restricted_hom_identity_block_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (h : H) (v : V) :
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom
      (Representation.IndV.mk H.subtype ρ (h : G) v)).down = 0 := by
  -- Convert the restricted Frobenius map to the explicit unit-copy projection and reuse the
  -- identity-block vanishing that was already established on all `H`-indexed generators.
  calc
    (((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom
        (Representation.IndV.mk H.subtype ρ (h : G) v)).down =
      inducedIdentityCopyProjection H ρ
        (F.hom (Representation.IndV.mk H.subtype ρ (h : G) v)) := by
          simpa using
            restricted_hom_apply_eq_unit_copy_projection (k := k) H ρ F
              (Representation.IndV.mk H.subtype ρ (h : G) v)
    _ = 0 := by
        exact singleton_off_identity_identity_block_projection_eq_zero (k := k) H ρ
          hq f F hF h v

/-- Helper for Proposition 7-7.4-1: project the restricted induced representation onto the
identity Mackey summand by transporting through the Mackey direct-sum decomposition and then
taking the identity direct-sum component. -/
theorem induced_self_map_coordinates
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ) :
    (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
          (Rep.indMap H.subtype g)) (DoubleCoset.mk H H (1 : G))) = g ∧
      ∀ q : DoubleCoset.Quotient (H : Set G) H,
        q ≠ DoubleCoset.mk H H (1 : G) →
          ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ)
            (Rep.indMap H.subtype g)) q = 0 := by
  -- Combine the identity-block computation with the off-identity vanishing statement.
  refine ⟨induced_self_map_identity_coordinate (k := k) H ρ g, ?_⟩
  intro q hq
  exact induced_self_map_off_identity_coordinate_eq_zero (k := k) H ρ g q hq

/-- Helper for Proposition 7-7.4-1: an endomorphism whose Mackey family is supported at the
identity double coset is induced from its identity coordinate. -/
theorem endomorphism_eq_indMap_of_identity_supported
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      ∀ q : DoubleCoset.Quotient (H : Set G) H,
        q ≠ DoubleCoset.mk H H (1 : G) →
          ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q = 0) :
    F = Rep.indMap H.subtype
      ((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
          (DoubleCoset.mk H H (1 : G)))) := by
  let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
  let q1 : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H (1 : G)
  let g : Rep.of ρ ⟶ Rep.of ρ :=
    (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ) ((e F) q1)
  have hgcoord :
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          ((e (Rep.indMap H.subtype g)) q1) = g ∧
        ∀ q : DoubleCoset.Quotient (H : Set G) H,
          q ≠ q1 → (e (Rep.indMap H.subtype g)) q = 0 :=
    induced_self_map_coordinates (k := k) H ρ g
  -- Compare the two endomorphisms through the Mackey-coordinate linear equivalence.
  apply e.injective
  funext q
  by_cases hq : q = q1
  · subst hq
    -- The distinguished identity coordinate was chosen precisely to recover `g`.
    apply (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ).injective
    simpa [e, q1, g] using hgcoord.1.symm
  · -- Every off-identity coordinate vanishes for both families.
    rw [hF q hq, hgcoord.2 q hq]

/-- Helper for Proposition 7-7.4-1: a nonzero self-intertwiner of `ρ` induces a nonzero
endomorphism of `Ind_H^G(ρ)`. -/
theorem induced_identity_copy_projection_comp_generator_eq_zero_of_singleton_off_identity
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (h : H) :
    inducedIdentityCopyProjection H ρ ∘ₗ
        (F.hom : Representation.IndV H.subtype ρ →ₗ[k] Representation.IndV H.subtype ρ) ∘ₗ
        (Representation.IndV.mk H.subtype ρ (h : G)) = 0 := by
  -- Route correction: the identity-block vanishing is now packaged as a linear-map statement on a
  -- single `IndV.mk` generator, matching the source proof's focus on the identity double coset.
  ext v
  -- Evaluate the composite on the chosen identity-block generator.
  simpa [LinearMap.comp_apply] using
    singleton_off_identity_identity_block_projection_eq_zero (k := k) H ρ hq f F hF h v

/-- Helper for Proposition 7-7.4-1: on the identity Mackey block, vanishing after the
unit-copy projection already forces the original linear map to vanish. -/
theorem identity_mackey_block_map_eq_zero_of_unit_projection_comp_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) [NeZero (Nat.card H : k)]
    {W : Type*} [AddCommGroup W] [Module k W]
    (L : W →ₗ[k] identity_mackey_block (k := k) H ρ)
    (hL : identity_mackey_unit_projection (k := k) H ρ ∘ₗ L = 0) :
    L = 0 := by
  ext w
  -- Evaluate the vanished composite at `w`, then use injectivity of the unit-copy projection on
  -- the identity block to recover that the original vector was already zero.
  have hw :
      identity_mackey_unit_projection (k := k) H ρ (L w) = 0 := by
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun T :
          W →ₗ[k] V ↦ T w)
        hL
  exact
    (identity_mackey_block_unit_projection_injective (k := k) H ρ) <| by
      simpa [identity_mackey_unit_projection, identity_mackey_subgroup,
        identity_mackey_representation, identity_mackey_double_coset] using hw

/-- Helper for Proposition 7-7.4-1: on a generator indexed by an element of `H`, the identity
Mackey-block projector lands on the corresponding unit generator inside the identity block. -/
theorem identity_mackey_block_projection_apply_mk_mem
    (H : Subgroup G) (ρ : Representation k H V)
    (h : H) (v : V) :
    identity_mackey_block_projection (k := k) H ρ
        (Representation.IndV.mk H.subtype ρ (h : G) v) =
      Representation.IndV.mk
        (identity_mackey_subgroup H).subtype
        (identity_mackey_representation (k := k) H ρ)
        1 (ρ h⁻¹ v) := by
  let q1 : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H (1 : G)
  let y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q1)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q1)).ρ) :=
    Representation.IndV.mk
      (mackeySubgroup H H (doubleCosetRepresentative H q1)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q1)).ρ)
      1 (ρ h⁻¹ v)
  have hseed :
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
          ⟨q1⟩ y)) =
        Representation.IndV.mk H.subtype ρ (h : G) v := by
    simpa [q1, y, doubleCosetRepresentative_identity] using
      induced_restriction_mackey_iso_inv_apply_lof_seed (k := k) H ρ q1 (ρ h⁻¹ v)
  calc
    identity_mackey_block_projection (k := k) H ρ
        (Representation.IndV.mk H.subtype ρ (h : G) v) =
      identity_mackey_block_projection (k := k) H ρ
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
            ⟨q1⟩ y)) := by
          rw [hseed]
    _ = y := by
          exact identity_mackey_block_projection_apply_mackey_lof_identity (k := k) H ρ y
    _ = Representation.IndV.mk
        (identity_mackey_subgroup H).subtype
        (identity_mackey_representation (k := k) H ρ)
        1 (ρ h⁻¹ v) := by
          rfl


/-- Helper for Proposition 7-7.4-1: the original unit-copy projection evaluates an
`H`-indexed generator by the usual inverse-action formula. -/
theorem induced_identity_copy_projection_apply_mk_mem
    (H : Subgroup G) (ρ : Representation k H V)
    (h : H) (v : V) :
    inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ (h : G) v) =
      ρ h⁻¹ v := by
  -- Rewrite the `H`-indexed generator as the unit generator in the same copy and then apply the
  -- explicit unit-copy projection formula.
  calc
    inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ (h : G) v) =
      inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ 1 (ρ h⁻¹ v)) := by
          exact congrArg (inducedIdentityCopyProjection H ρ)
            (ind_mk_eq_mk_one_inv (k := k) (θ := ρ) h v)
    _ = ρ h⁻¹ v := by
          exact induced_identity_copy_projection_apply_mk_one H ρ (ρ h⁻¹ v)

/-- Helper for Proposition 7-7.4-1: on generators indexed by elements of `H`, the identity-block
unit projection agrees with the original unit-copy projection after applying the identity Mackey
projector. -/
theorem identity_mackey_block_unit_projection_comp_mk_mem
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero
      (Nat.card
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))) : k)]
    (h : H) :
    identity_mackey_unit_projection (k := k) H ρ ∘ₗ
      identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (Representation.IndV.mk H.subtype ρ (h : G)) =
      inducedIdentityCopyProjection H ρ ∘ₗ
        (Representation.IndV.mk H.subtype ρ (h : G)) := by
  let K : Subgroup H := identity_mackey_subgroup H
  let σ : Representation k K V := identity_mackey_representation (k := k) H ρ
  -- On an `H`-indexed generator, both sides reduce to the same coefficient `ρ h⁻¹ v`.
  ext v
  calc
    ((inducedIdentityCopyProjection K σ ∘ₗ
            identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (Representation.IndV.mk H.subtype ρ (h : G))) v) =
      inducedIdentityCopyProjection K σ
        (Representation.IndV.mk K.subtype σ 1 (ρ h⁻¹ v)) := by
          rw [LinearMap.comp_apply, LinearMap.comp_apply,
            identity_mackey_block_projection_apply_mk_mem (k := k) H ρ h v]
    _ = ρ h⁻¹ v := by
          simpa [K, σ] using induced_identity_copy_projection_apply_mk_one K σ (ρ h⁻¹ v)
    _ = ((inducedIdentityCopyProjection H ρ ∘ₗ
          (Representation.IndV.mk H.subtype ρ (h : G))) v) := by
          symm
          simpa [LinearMap.comp_apply] using
            induced_identity_copy_projection_apply_mk_mem (k := k) H ρ h v

/-- Helper for Proposition 7-7.4-1: outside the original `H`-copy, the identity Mackey-block
unit projection vanishes on concrete induced generators. -/
theorem identity_mackey_block_unit_projection_comp_mk_of_not_mem
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero (Nat.card (identity_mackey_subgroup H) : k)]
    {g : G} (hg : g ∉ H) :
    identity_mackey_unit_projection (k := k) H ρ ∘ₗ
      identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (Representation.IndV.mk H.subtype ρ g) = 0 := by
  classical
  ext v
  let q : DoubleCoset.Quotient (H : Set G) H := DoubleCoset.mk H H g⁻¹
  have hginv : g⁻¹ ∉ H := by
    intro hmem
    exact hg (by simpa using H.inv_mem hmem)
  have hq : q ≠ DoubleCoset.mk H H (1 : G) := by
    simpa [q] using doubleCoset_ne_identity_of_not_mem H hginv
  have hrep :
      DoubleCoset.mk H H (doubleCosetRepresentative H q) =
        DoubleCoset.mk H H g⁻¹ := by
    simpa [q] using doubleCosetRepresentative_spec H q
  rcases (DoubleCoset.eq H H (doubleCosetRepresentative H q) g⁻¹).1 hrep with
    ⟨a, ha, b, hb, hab⟩
  let aH : H := ⟨a, ha⟩
  let bH : H := ⟨b, hb⟩
  have hg_label : g = (b : G)⁻¹ * (doubleCosetRepresentative H q)⁻¹ * (a : G)⁻¹ := by
    calc
      g = (g⁻¹)⁻¹ := by simp
      _ = (a * doubleCosetRepresentative H q * b)⁻¹ := by rw [hab]
      _ = (b : G)⁻¹ * (doubleCosetRepresentative H q)⁻¹ * (a : G)⁻¹ := by
          simp [mul_assoc]
  have hmk :
      (Representation.IndV.mk H.subtype ρ g) v =
        (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) aH)
          ((Representation.IndV.mk H.subtype ρ
            (doubleCosetRepresentative H q)⁻¹) (ρ bH v)) := by
    calc
      (Representation.IndV.mk H.subtype ρ g) v =
          (Representation.IndV.mk H.subtype ρ
            ((b : G)⁻¹ * (doubleCosetRepresentative H q)⁻¹ * (a : G)⁻¹)) v := by
            rw [hg_label]
      _ = (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) aH)
          ((Representation.IndV.mk H.subtype ρ
            ((b : G)⁻¹ * (doubleCosetRepresentative H q)⁻¹)) v) := by
            symm
            simpa [aH, mul_assoc] using
              Representation.ind_mk (φ := H.subtype) (ρ := ρ) aH
                ((b : G)⁻¹ * (doubleCosetRepresentative H q)⁻¹) v
      _ = (((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) aH)
          ((Representation.IndV.mk H.subtype ρ
            (doubleCosetRepresentative H q)⁻¹) (ρ bH v)) := by
            rw [ind_mk_inv_left_translate (k := k) H ρ bH
              (doubleCosetRepresentative H q)⁻¹ v]
  calc
    ((identity_mackey_unit_projection (k := k) H ρ ∘ₗ
        identity_mackey_block_projection (k := k) H ρ ∘ₗ
          (Representation.IndV.mk H.subtype ρ g)) v) =
      identity_mackey_unit_projection (k := k) H ρ
        (identity_mackey_block_projection (k := k) H ρ
          ((((Rep.res H.subtype (Rep.ind H.subtype (of ρ))).ρ) aH)
            ((Representation.IndV.mk H.subtype ρ
              (doubleCosetRepresentative H q)⁻¹) (ρ bH v)))) := by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hmk]
    _ = ρ aH
        (identity_mackey_unit_projection (k := k) H ρ
          (identity_mackey_block_projection (k := k) H ρ
            ((Representation.IndV.mk H.subtype ρ
              (doubleCosetRepresentative H q)⁻¹) (ρ bH v)))) := by
          exact identity_mackey_unit_projection_comp_projection_intertwine
            (k := k) H ρ aH
            ((Representation.IndV.mk H.subtype ρ
              (doubleCosetRepresentative H q)⁻¹) (ρ bH v))
    _ = 0 := by
          have hzero := LinearMap.congr_fun
            (identity_mackey_block_unit_projection_comp_mk_inv_representative_of_ne_identity
              (k := k) H ρ hq) ((ρ bH) v)
          change identity_mackey_unit_projection (k := k) H ρ
              (identity_mackey_block_projection (k := k) H ρ
                ((Representation.IndV.mk H.subtype ρ
                  (doubleCosetRepresentative H q)⁻¹) ((ρ bH) v))) = 0 at hzero
          rw [hzero]
          simp

/-- Helper for Proposition 7-7.4-1: after projecting to the identity Mackey block, the unit-copy
projection agrees with the original unit-copy projection on the whole induced representation. -/
theorem identity_mackey_block_unit_projection_eq_unit_copy_projection
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero (Nat.card (identity_mackey_subgroup H) : k)] :
    identity_mackey_unit_projection (k := k) H ρ ∘ₗ
      identity_mackey_block_projection (k := k) H ρ =
      inducedIdentityCopyProjection H ρ := by
  -- Compare the two maps on concrete generators of the induced representation, separating the
  -- identity-copy case from the off-copy case before any transport can accumulate.
  apply Representation.IndV.hom_ext (φ := H.subtype) (ρ := ρ)
  intro g
  by_cases hg : g ∈ H
  · let h : H := ⟨g, hg⟩
    simpa [h, identity_mackey_unit_projection, identity_mackey_subgroup,
      identity_mackey_representation, identity_mackey_double_coset] using
      identity_mackey_block_unit_projection_comp_mk_mem (k := k) H ρ h
  · have hleft :
        (identity_mackey_unit_projection (k := k) H ρ ∘ₗ
            identity_mackey_block_projection (k := k) H ρ) ∘ₗ
          (Representation.IndV.mk H.subtype ρ g) = 0 := by
        simpa [LinearMap.comp_assoc] using
          identity_mackey_block_unit_projection_comp_mk_of_not_mem (k := k) H ρ hg
    have hright :
        inducedIdentityCopyProjection H ρ ∘ₗ
          (Representation.IndV.mk H.subtype ρ g) = 0 := by
      ext v
      exact induced_identity_copy_projection_apply_mk_of_not_mem (k := k) H ρ hg v
    rw [hleft, hright]

/-- Helper for Proposition 7-7.4-1: the final componentwise `ULift`-removal step inside
`induced_restriction_mackey_iso` already sends the `q`-summand seed to the unlifted seed. -/
theorem induced_restriction_mackey_iso_ulift_removal_apply_lof_seed
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (x : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)) :
    (DirectSum.lmap fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        (mackeySummand_ulift_equiv (k := k) H ρ
          (doubleCosetRepresentative H q'.down)).toLinearEquiv.toLinearMap :
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
                (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
          (fun q' ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)))
      (DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
              (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
            (doubleCosetRepresentative H q.down)).ρ)
          1 (ULift.up x))) =
      DirectSum.lof k _
        (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
        q
        (Representation.IndV.mk
          (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
          1 x) := by
  rw [DirectSum.lmap_lof]
  exact congrArg
    (DirectSum.lof k _
      (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
        Representation.IndV
          (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
          ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
      q)
    (mackeySummand_ulift_equiv_apply_mk_one (k := k) H ρ
      (doubleCosetRepresentative H q.down) x)


/-- Helper for Proposition 7-7.4-1: after transporting an off-identity `DirectSum.lof` generator
back through the inverse Mackey isomorphism, the identity-block unit projection already vanishes.
-/
theorem identity_mackey_block_unit_projection_apply_mackey_lof_of_ne
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)]
    [NeZero
      (Nat.card
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))) : k)]
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (hq : q ≠ ⟨DoubleCoset.mk H H (1 : G)⟩)
    (y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) :
    inducedIdentityCopyProjection
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))))
        ((mackeyTwist H H (of ρ)
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)
        (identity_mackey_block_projection (k := k) H ρ
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
              q y))) = 0 := by
  have hproj :
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
            q y)) = 0 := by
    simp [identity_mackey_block_projection, DirectSum.component.of, hq]
  rw [hproj]
  simp


end MackeyIrreducibilityCriterion

end Representation
