import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.MackeyWeights

open CategoryTheory

universe u v w x

namespace Representation

noncomputable section

section SemidirectAbelian

open scoped Representation

variable {A : Type u} [CommGroup A]
variable {H : Type v} [Group H]
variable (φ : H →* MulAut A)

section Proposition

variable [Finite H]

/-- Helper for Proposition 8-8.2-1: an irreducible representation has a nontrivial carrier. -/
theorem nontrivial_of_isIrreducible
    {K : Type*} [Group K]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ K V) [τ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation τ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Proposition 8-8.2-1: an ambient representation equivalence restricts to an
equivalence on every fixed `A`-weight subrepresentation. -/
noncomputable def character_weight_subrepresentation_equiv_of_equiv
    {τ τ' : Rep.{x} ℂ (A ⋊[φ] H)} (e : τ.ρ.Equiv τ'.ρ) (ψ : A →* ℂˣ) :
    (character_weight_subrepresentation (φ := φ) τ ψ).ρ.Equiv
      (character_weight_subrepresentation (φ := φ) τ' ψ).ρ :=
  Representation.Equiv.mk
    { toFun := fun x ↦
        ⟨e x.1,
          map_mem_character_weight_submodule_of_equiv (φ := φ) e ψ x.property⟩
      invFun := fun x ↦
        ⟨e.symm x.1,
          map_mem_character_weight_submodule_of_equiv (φ := φ) e.symm ψ x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        change e (x.1 + y.1) = e x.1 + e y.1
        simpa using e.toLinearEquiv.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        change e (c • x.1) = c • e x.1
        simpa using e.toLinearEquiv.map_smul c x.1 }
    (by
      intro h
      ext x
      -- The stabilizer action is given by the ambient operator at `(1,h)`, so equivariance
      -- follows directly from the ambient intertwining relation.
      apply Subtype.ext
      change e (τ.ρ ⟨1, h⟩ x.1) = τ'.ρ ⟨1, h⟩ (e x.1)
      simpa using LinearMap.congr_fun (e.isIntertwining' ⟨1, h⟩) x.1)

/-- Helper for Proposition 8-8.2-1: a `χ`-weight vector in the coinduced packet model vanishes
away from the packet subgroup, because the weight condition and the coinduced covariance relation
force two distinct scalars to act on the same value. -/
theorem theta_coind_character_weight_apply_eq_zero_of_not_mem
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    {y : character_weight_submodule (φ := φ)
      (Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)) χ}
    {u : A ⋊[φ] H}
    (hu : u ∉ character_stabilizer_subgroup (φ := φ) χ) :
    y.1.1 u = 0 := by
  have huinv : u⁻¹ ∉ character_stabilizer_subgroup (φ := φ) χ := by
    intro huinv
    apply hu
    simpa using (character_stabilizer_subgroup (φ := φ) χ).inv_mem huinv
  obtain ⟨a, ha⟩ :=
    exists_character_mismatch_of_not_mem_character_stabilizer_subgroup (φ := φ) χ huinv
  have hy_weight_eval :
      y.1.1 (u * (⟨a, 1⟩ : A ⋊[φ] H)) = (χ a : ℂ) • y.1.1 u := by
    -- Evaluate the `χ`-weight relation at the point `u`.
    simpa [Representation.coind_apply] using congrArg (fun z ↦ z.1 u) (y.2 a)
  have hy_coind :=
    (Representation.mem_coindV
      (φ := (character_stabilizer_subgroup (φ := φ) χ).subtype)
      (σ := (theta_packet_source (φ := φ) χ ρ).ρ)
      (f := y.1)).mp y.1.2
  have hs_mem :
      (⟨φ u.right a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ := by
    simpa using
      semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ (φ u.right a)
  let gS : character_stabilizer_subgroup (φ := φ) χ := ⟨⟨φ u.right a, 1⟩, hs_mem⟩
  have hy_source_eval :
      y.1.1 ((⟨φ u.right a, 1⟩ : A ⋊[φ] H) * u) =
        (χ (φ u.right a) : ℂ) • y.1.1 u := by
    -- The coinduced covariance relation identifies the same translate with the subgroup action.
    calc
      y.1.1 (gS.1 * u) = (theta_packet_source (φ := φ) χ ρ).ρ gS (y.1.1 u) := by
        simpa using hy_coind gS u
      _ = (χ (φ u.right a) : ℂ) • y.1.1 u := by
        simpa [gS, theta_packet_source] using
          character_stabilizer_subgroup_source_apply_inl
            (φ := φ) χ ρ (φ u.right a) hs_mem (y.1.1 u)
  have hscalar :
      ((transportedCharacter (φ := φ) u.right⁻¹ χ a : ℂ)) • y.1.1 u =
        (χ a : ℂ) • y.1.1 u := by
    -- Compare the subgroup-covariance scalar with the `χ`-weight scalar on the same translate.
    calc
      ((transportedCharacter (φ := φ) u.right⁻¹ χ a : ℂ)) • y.1.1 u =
          (χ (φ u.right a) : ℂ) • y.1.1 u := by
            rw [transportedCharacter_apply]
            simp
      _ = y.1.1 ((⟨φ u.right a, 1⟩ : A ⋊[φ] H) * u) := by
            rw [hy_source_eval]
      _ = y.1.1 (u * (⟨a, 1⟩ : A ⋊[φ] H)) := by
            rw [semidirectProduct_mul_inl_eq_inl_mul (φ := φ) u a]
      _ = (χ a : ℂ) • y.1.1 u := hy_weight_eval
  have hsub :
      (((transportedCharacter (φ := φ) u.right⁻¹ χ a : ℂ) - (χ a : ℂ)) • y.1.1 u) = 0 := by
    calc
      (((transportedCharacter (φ := φ) u.right⁻¹ χ a : ℂ) - (χ a : ℂ)) • y.1.1 u) =
          ((transportedCharacter (φ := φ) u.right⁻¹ χ a : ℂ) • y.1.1 u) -
            ((χ a : ℂ) • y.1.1 u) := by
              simp [sub_smul]
      _ = 0 := by rw [hscalar, sub_self]
  exact
    (smul_eq_zero.mp hsub).resolve_left <| sub_ne_zero.mpr <| by
      intro hEq
      apply ha
      exact Units.ext hEq

/-- Helper for Proposition 8-8.2-1: the subgroup-supported function attached to a packet-source
vector is automatically a `χ`-weight vector in the coinduced packet model. -/
theorem subgroupSupportedFunction_mem_theta_character_weight_submodule
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) (v : ρ) :
    Representation.subgroupSupportedFunction
        (character_stabilizer_subgroup (φ := φ) χ)
        (theta_packet_source (φ := φ) χ ρ).ρ v ∈
      character_weight_submodule (φ := φ)
        (Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
          (theta_packet_source (φ := φ) χ ρ)) χ := by
  intro a
  ext u
  by_cases hu : u ∈ character_stabilizer_subgroup (φ := φ) χ
  · have hu_mul :
        u * (⟨a, 1⟩ : A ⋊[φ] H) ∈ character_stabilizer_subgroup (φ := φ) χ := by
      simpa using hu
    let gχ : character_stabilizer_subgroup (φ := φ) χ := by
      refine ⟨⟨φ u.right a, 1⟩, ?_⟩
      simpa using
        semidirectProduct_inl_mem_character_stabilizer_subgroup (φ := φ) χ (φ u.right a)
    have hmul :
        (⟨u * (⟨a, 1⟩ : A ⋊[φ] H), hu_mul⟩ :
          character_stabilizer_subgroup (φ := φ) χ) =
          gχ * ⟨u, hu⟩ := by
      apply Subtype.ext
      exact semidirectProduct_mul_inl_eq_inl_mul (φ := φ) u a
    -- On the packet subgroup, right-translation by `(a,1)` becomes left multiplication by
    -- `((φ u.right) a, 1)`, and the source acts there by the scalar `χ(a)`.
    calc
      (((Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
            (theta_packet_source (φ := φ) χ ρ)).ρ ⟨a, 1⟩)
          (Representation.subgroupSupportedFunction
            (character_stabilizer_subgroup (φ := φ) χ)
            (theta_packet_source (φ := φ) χ ρ).ρ v)).1 u =
          (Representation.subgroupSupportedFunction
            (character_stabilizer_subgroup (φ := φ) χ)
            (theta_packet_source (φ := φ) χ ρ).ρ v).1
            (u * (⟨a, 1⟩ : A ⋊[φ] H)) := by
              rfl
      _ = (theta_packet_source (φ := φ) χ ρ).ρ ⟨u * (⟨a, 1⟩ : A ⋊[φ] H), hu_mul⟩ v := by
            simpa using
              Representation.subgroupSupportedFunction_of_mem
                (character_stabilizer_subgroup (φ := φ) χ)
                (theta_packet_source (φ := φ) χ ρ).ρ v hu_mul
      _ = (theta_packet_source (φ := φ) χ ρ).ρ (gχ * ⟨u, hu⟩) v := by
            rw [hmul]
      _ = (theta_packet_source (φ := φ) χ ρ).ρ gχ
            ((theta_packet_source (φ := φ) χ ρ).ρ ⟨u, hu⟩ v) := by
            simp [map_mul]
      _ = (χ (φ u.right a) : ℂ) •
            ((theta_packet_source (φ := φ) χ ρ).ρ ⟨u, hu⟩ v) := by
            simpa [gχ, theta_packet_source] using
              character_stabilizer_subgroup_source_apply_inl
                (φ := φ) χ ρ (φ u.right a) gχ.2
                ((theta_packet_source (φ := φ) χ ρ).ρ ⟨u, hu⟩ v)
      _ = (χ a : ℂ) •
            ((theta_packet_source (φ := φ) χ ρ).ρ ⟨u, hu⟩ v) := by
            rw [characterStabilizer_apply (φ := φ) χ ⟨u.right, hu⟩ a]
      _ = (χ a : ℂ) •
            ((Representation.subgroupSupportedFunction
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ).ρ v).1 u) := by
            rw [Representation.subgroupSupportedFunction_of_mem
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ).ρ v hu]
  · have hu_mul :
        u * (⟨a, 1⟩ : A ⋊[φ] H) ∉ character_stabilizer_subgroup (φ := φ) χ := by
      simpa using hu
    -- Away from the packet subgroup, both the subgroup-supported function and its translate vanish.
    calc
      (((Rep.coind (character_stabilizer_subgroup (φ := φ) χ).subtype
            (theta_packet_source (φ := φ) χ ρ)).ρ ⟨a, 1⟩)
          (Representation.subgroupSupportedFunction
            (character_stabilizer_subgroup (φ := φ) χ)
            (theta_packet_source (φ := φ) χ ρ).ρ v)).1 u =
          (Representation.subgroupSupportedFunction
            (character_stabilizer_subgroup (φ := φ) χ)
            (theta_packet_source (φ := φ) χ ρ).ρ v).1
            (u * (⟨a, 1⟩ : A ⋊[φ] H)) := by
              rfl
      _ = 0 := by
            simpa [hu_mul] using
              Representation.subgroupSupportedFunction_of_not_mem
                (character_stabilizer_subgroup (φ := φ) χ)
                (theta_packet_source (φ := φ) χ ρ).ρ v hu_mul
      _ = (χ a : ℂ) •
            ((Representation.subgroupSupportedFunction
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ).ρ v).1 u) := by
            rw [Representation.subgroupSupportedFunction_of_not_mem
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ).ρ v hu]
            simp

/-- Helper for Proposition 8-8.2-1: the distinguished `χ`-weight subrepresentation of the packet
`θ[φ; χ, ρ]` recovers the stabilizer representation `ρ`. -/
noncomputable def theta_character_weight_subrepresentation_equiv
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    (character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ.Equiv ρ.ρ := by
  let S : Subgroup (A ⋊[φ] H) := character_stabilizer_subgroup (φ := φ) χ
  let σ : Rep ℂ S := theta_packet_source (φ := φ) χ ρ
  let ecoind_weight :
      (character_weight_subrepresentation (φ := φ)
        (Rep.coind S.subtype σ) χ).ρ.Equiv ρ.ρ :=
    Representation.Equiv.mk
      { toFun := fun y ↦ y.1.1 1
        invFun := fun v ↦
          ⟨Representation.subgroupSupportedFunction S σ.ρ v,
            subgroupSupportedFunction_mem_theta_character_weight_submodule
              (φ := φ) χ ρ v⟩
        left_inv := by
          intro y
          apply Subtype.ext
          ext u
          by_cases hu : u ∈ S
          · have hy_coind :=
              (Representation.mem_coindV
                (φ := S.subtype) (σ := σ.ρ) (f := y.1)).mp y.1.2
            -- On the packet subgroup, the coinduced covariance relation reconstructs the value
            -- from the evaluation at `1`.
            have hyu : y.1.1 u = σ.ρ ⟨u, hu⟩ (y.1.1 1) := by
              simpa using hy_coind ⟨u, hu⟩ (1 : A ⋊[φ] H)
            calc
              (Representation.subgroupSupportedFunction S σ.ρ (y.1.1 1)).1 u =
                  σ.ρ ⟨u, hu⟩ (y.1.1 1) := by
                    simpa using
                      Representation.subgroupSupportedFunction_of_mem S σ.ρ (y.1.1 1) hu
              _ = y.1.1 u := hyu.symm
          · -- Off the packet subgroup, the weight condition forces the coinduced function to
            -- vanish, so the subgroup-supported inverse matches it there as well.
            have hyu :
                y.1.1 u = 0 :=
              theta_coind_character_weight_apply_eq_zero_of_not_mem
                (φ := φ) χ ρ (y := y) hu
            calc
              (Representation.subgroupSupportedFunction S σ.ρ (y.1.1 1)).1 u = 0 := by
                simpa using
                  Representation.subgroupSupportedFunction_of_not_mem S σ.ρ (y.1.1 1) hu
              _ = y.1.1 u := hyu.symm
        right_inv := by
          intro v
          -- Evaluating the subgroup-supported function at `1` recovers the original vector.
          calc
            (Representation.subgroupSupportedFunction S σ.ρ v).1 1 =
                σ.ρ ⟨1, S.one_mem⟩ v := by
                  simpa using
                    Representation.subgroupSupportedFunction_of_mem S σ.ρ v S.one_mem
            _ = v := by
                  change σ.ρ (1 : S) v = v
                  simpa using LinearMap.congr_fun (σ.ρ.map_one) v
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro c x
          rfl }
      (by
        intro h
        ext y
        change (((Rep.coind S.subtype σ).ρ ⟨1, h⟩ y.1).1 1) = ρ.ρ h (y.1.1 1)
        have hmem : (⟨1, h⟩ : A ⋊[φ] H) ∈ S := by
          simpa [S] using h.property
        have hy_coind :=
          (Representation.mem_coindV
            (φ := S.subtype) (σ := σ.ρ) (f := y.1)).mp y.1.2
        -- Evaluating the coinduced action at `1` turns the `H_[φ; χ]`-action on the weight space
        -- into the original `ρ`-action.
        calc
          (((Rep.coind S.subtype σ).ρ ⟨1, h⟩ y.1).1 1) = y.1.1 (⟨1, h⟩ : A ⋊[φ] H) := by
            simp [Representation.coind_apply]
          _ = σ.ρ ⟨⟨1, h⟩, hmem⟩ (y.1.1 1) := by
            simpa using hy_coind ⟨⟨1, h⟩, hmem⟩ (1 : A ⋊[φ] H)
          _ = ρ.ρ h (y.1.1 1) := by
            change
              (stabilizerRepresentation φ χ ρ).ρ
                (⟨1, h⟩ : A ⋊[stabilizerAction φ χ] H_[φ; χ]) (y.1.1 1) =
                  ρ.ρ h (y.1.1 1)
            change
              ((stabilizerCharacter φ χ
                    (⟨1, h⟩ : A ⋊[stabilizerAction φ χ] H_[φ; χ]) : ℂ) •
                  ρ.ρ h (y.1.1 1)) =
                ρ.ρ h (y.1.1 1)
            simp [stabilizerCharacter_apply])
  let etransport :
      (character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ.Equiv
        (character_weight_subrepresentation (φ := φ) (Rep.coind S.subtype σ) χ).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ)
      (theta_coind_character_stabilizer_subgroup_equiv (φ := φ) χ ρ) χ
  -- Route correction: Serre's source proof recovers `ρ` from the distinguished `χ`-weight by
  -- passing to the coinduced model, forcing support on the packet subgroup, and evaluating at `1`.
  exact etransport.trans ecoind_weight

/-- Helper for Proposition 8-8.2-1: the `ψ`-weight representation of a subrepresentation embeds
into the ambient `ψ`-weight representation by forgetting the carrier witness. -/
noncomputable def character_weight_subrepresentation_inclusion
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (U : Subrepresentation τ.ρ) (ψ : A →* ℂˣ) :
    (character_weight_subrepresentation (φ := φ) (Rep.of U.toRepresentation) ψ) ⟶
      (character_weight_subrepresentation (φ := φ) τ ψ) :=
  let i :
      (character_weight_subrepresentation (φ := φ) (Rep.of U.toRepresentation) ψ).V →ₗ[ℂ]
        (character_weight_subrepresentation (φ := φ) τ ψ).V :=
    { toFun := fun x ↦
        ⟨x.1.1, fun a ↦ congrArg Subtype.val (x.property a)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  Rep.ofHom <|
    LinearMap.intertwiningMap_of_isIntertwiningMap
      ((character_weight_subrepresentation (φ := φ) (Rep.of U.toRepresentation) ψ).ρ)
      ((character_weight_subrepresentation (φ := φ) τ ψ).ρ)
      i
      (by
        intro h x
        -- Both weight actions are induced by the ambient operator `τ(1,h)`.
        apply Subtype.ext
        rfl)

/-- Helper for Proposition 8-8.2-1: the distinguished `χ`-weight representation inside
`θ[φ; χ, ρ]` is irreducible because it is equivariantly equivalent to the stabilizer
representation `ρ`. -/
theorem theta_character_weight_subrepresentation_isIrreducible
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    [ρ.ρ.IsIrreducible] :
    ((character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ).IsIrreducible := by
  -- Transport irreducibility across the explicit equivalence with the source representation `ρ`.
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := ρ.ρ)
      (σ := (character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ)
      ⟨(theta_character_weight_subrepresentation_equiv (φ := φ) χ ρ).symm⟩

/-- Helper for Proposition 8-8.2-1: any nonzero `H_[φ; χ]`-stable subrepresentation of the
distinguished `χ`-weight of `θ[φ; χ, ρ]` is already the whole weight representation. -/
theorem theta_character_weight_subrepresentation_eq_top_of_ne_bot
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    [ρ.ρ.IsIrreducible]
    (U : Subrepresentation
      ((character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ))
    (hU : U.toSubmodule ≠ ⊥) :
    U = ⊤ := by
  letI :
      ((character_weight_subrepresentation (φ := φ) (θ[φ; χ, ρ]) χ).ρ).IsIrreducible :=
    theta_character_weight_subrepresentation_isIrreducible (φ := φ) χ ρ
  -- In an irreducible representation, every nonzero subrepresentation is the whole space.
  have hU' : U ≠ ⊥ := by
    intro hUeq
    apply hU
    simpa using congrArg Subrepresentation.toSubmodule hUeq
  exact (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU'

/-- Helper for Proposition 8-8.2-1: the weight-space inclusion simply forgets the carrier witness
coming from the subrepresentation and keeps the same ambient vector. -/
@[simp] theorem character_weight_subrepresentation_inclusion_apply
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (U : Subrepresentation τ.ρ) (ψ : A →* ℂˣ)
    (x : character_weight_subrepresentation (φ := φ) (Rep.of U.toRepresentation) ψ) :
    (character_weight_subrepresentation_inclusion (φ := φ) U ψ).hom x =
      ⟨x.1.1, fun a ↦ congrArg Subtype.val (x.property a)⟩ := by
  -- This is the concrete adapter needed later when passing from a packet subrepresentation to the
  -- ambient distinguished weight space.
  rfl

/-- Helper for Proposition 8-8.2-1: if the ambient `ψ`-weight representation is irreducible,
then any subrepresentation with nonzero `ψ`-weight already contains the whole ambient
`ψ`-weight submodule. -/
theorem character_weight_submodule_le_of_nonzero_subweight_irreducible
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (T : Subrepresentation τ.ρ)
    [((character_weight_subrepresentation (φ := φ) τ ψ).ρ).IsIrreducible]
    (hTψ : character_weight_submodule (φ := φ) (Rep.of T.toRepresentation) ψ ≠ ⊥) :
    character_weight_submodule (φ := φ) τ ψ ≤ T.toSubmodule := by
  let Tψ := character_weight_subrepresentation (φ := φ) (Rep.of T.toRepresentation) ψ
  let τψ := character_weight_subrepresentation (φ := φ) τ ψ
  let ι : Tψ ⟶ τψ :=
    character_weight_subrepresentation_inclusion (φ := φ) T ψ
  have hrange_ne_bot : ι.hom.range ≠ ⊥ := by
    rcases (Submodule.ne_bot_iff _).mp hTψ with ⟨x, hx, hx0⟩
    intro hrange_bot
    have hx_image_zero : (ι.hom ⟨x, hx⟩ : τψ) = 0 := by
      have hx_image_mem :
          (ι.hom ⟨x, hx⟩ : τψ) ∈ (ι.hom.range.toSubmodule : Submodule ℂ τψ) :=
        ⟨⟨x, hx⟩, rfl⟩
      have hrange_bot_submodule :
          (ι.hom.range.toSubmodule : Submodule ℂ τψ) = ⊥ := by
        simpa using congrArg Subrepresentation.toSubmodule hrange_bot
      rw [Submodule.eq_bot_iff] at hrange_bot_submodule
      exact hrange_bot_submodule _ hx_image_mem
    apply hx0
    apply Subtype.ext
    have hx_image_zero' :
        ((character_weight_subrepresentation_inclusion (φ := φ) T ψ).hom ⟨x, hx⟩ : τψ) = 0 := by
      simpa [ι] using hx_image_zero
    have hx_image_zero'' :
        (((character_weight_subrepresentation_inclusion (φ := φ) T ψ).hom ⟨x, hx⟩ : τψ).1) = 0 := by
      exact congrArg (fun z : τψ ↦ z.1) hx_image_zero'
    simpa [character_weight_subrepresentation_inclusion_apply] using hx_image_zero''
  have hrange_top : ι.hom.range = ⊤ := by
    -- Irreducibility turns the nonzero image of the inclusion into the whole ambient weight
    -- representation.
    exact (IsSimpleOrder.eq_bot_or_eq_top ι.hom.range).resolve_left hrange_ne_bot
  intro x hx
  let xψ : τψ := ⟨x, hx⟩
  have hx_range : xψ ∈ ι.hom.range.toSubmodule := by
    have hx_top :
        xψ ∈ ((⊤ : Subrepresentation τψ.ρ).toSubmodule : Submodule ℂ τψ) := by
      change xψ ∈ (⊤ : Submodule ℂ τψ)
      simp
    simpa [hrange_top] using hx_top
  rcases hx_range with ⟨y, hy⟩
  -- Surjectivity of the weight-space inclusion shows that the ambient vector of `x` already
  -- lies in the carrier of `T`.
  have hy_val : y.1.1 = x := by
    simpa [xψ, Tψ, τψ, character_weight_subrepresentation_inclusion_apply] using
      congrArg Subtype.val hy
  simpa [hy_val] using y.1.2

/-- Helper for Proposition 8-8.2-1: forgetting the `U`-carrier inside a `ψ`-weight constituent
keeps the same underlying vector of `τ`. -/
noncomputable def character_weight_constituent_forgetLinear
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ) :
    U.toSubmodule →ₗ[ℂ] τ :=
  { toFun := fun x ↦ x.1.1
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro c x
      rfl }

/-- Helper for Proposition 8-8.2-1: the inclusion of a `ψ`-weight constituent into `τ`
intertwines the `A ⋊ H_[φ; ψ]`-action with the restriction of `τ`. -/
theorem character_weight_constituent_forgetLinear_isIntertwining
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ) :
    ∀ g x,
      character_weight_constituent_forgetLinear (φ := φ) (τ := τ) ψ U
          (((stabilizerRepresentation φ ψ (Rep.of U.toRepresentation)).ρ) g x) =
        ((Rep.res (stabilizerInclusion φ ψ) τ).ρ g)
          (character_weight_constituent_forgetLinear (φ := φ) (τ := τ) ψ U x) := by
  intro g x
  rcases g with ⟨a, h⟩
  -- Expand the stabilizer-side action into the scalar `ψ a` and the transported `H_[φ; ψ]`-action
  -- on the chosen `ψ`-weight constituent `U`.
  change (((stabilizerRepresentation φ ψ (Rep.of U.toRepresentation)).ρ ⟨a, h⟩ x).1.1) = _
  change ((stabilizerCharacter φ ψ ⟨a, h⟩ : ℂ) • (((Rep.of U.toRepresentation).ρ h x).1.1)) = _
  -- Then rewrite the ambient action at `⟨a,h⟩` as `⟨a,1⟩ * ⟨1,h⟩` and use the `ψ`-weight
  -- relation carried by `x`.
  -- The underlying vector of `x` is already a `ψ`-weight vector, so `τ(a,1)` contributes the same
  -- scalar `ψ a` on the ambient side.
  calc
    ((stabilizerCharacter φ ψ ⟨a, h⟩ : ℂ) • (((Rep.of U.toRepresentation).ρ h x).1.1)) =
        (ψ a : ℂ) • (((Rep.of U.toRepresentation).ρ h x).1.1) := by
          simp [stabilizerCharacter_apply]
    _ = τ.ρ ⟨a, 1⟩ (((Rep.of U.toRepresentation).ρ h x).1.1) := by
          simpa using (((Rep.of U.toRepresentation).ρ h x).1.property a).symm
    _ = τ.ρ ⟨a, 1⟩ (τ.ρ ⟨1, h⟩ x.1.1) := by
          rfl
    _ = τ.ρ (⟨a, 1⟩ * ⟨1, h⟩) x.1.1 := by
          simp [map_mul]
    _ = τ.ρ ⟨a, h⟩ x.1.1 := by
          have hmul : (⟨a, 1⟩ : A ⋊[φ] H) * ⟨1, h⟩ = ⟨a, h⟩ := by
            ext
            · change a * φ (1 : H) (1 : A) = a
              simp
            · change (1 : H) * h = h
              simp
          rw [hmul]
    _ = ((Rep.res (stabilizerInclusion φ ψ) τ).ρ ⟨a, h⟩)
          (character_weight_constituent_forgetLinear (φ := φ) (τ := τ) ψ U x) := by
          rfl

/-- Helper for Proposition 8-8.2-1: an irreducible constituent of the `ψ`-weight space of `τ`
already gives the subgroup-side morphism required by Frobenius reciprocity. -/
noncomputable def stabilizer_representation_hom_of_character_weight_constituent
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ) :
    stabilizerRepresentation φ ψ (Rep.of U.toRepresentation) ⟶
      Rep.res (stabilizerInclusion φ ψ) τ :=
  Rep.ofHom <|
    LinearMap.intertwiningMap_of_isIntertwiningMap
      ((stabilizerRepresentation φ ψ (Rep.of U.toRepresentation)).ρ)
      ((Rep.res (stabilizerInclusion φ ψ) τ).ρ)
      (character_weight_constituent_forgetLinear (φ := φ) (τ := τ) ψ U)
      (character_weight_constituent_forgetLinear_isIntertwining
        (φ := φ) (τ := τ) ψ U)

/-- Helper for Proposition 8-8.2-1: the subgroup-side Frobenius map evaluates by forgetting both
subtype witnesses. -/
@[simp] theorem stabilizer_representation_hom_of_character_weight_constituent_apply
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ)
    (x : U.toSubmodule) :
    (stabilizer_representation_hom_of_character_weight_constituent
        (φ := φ) (τ := τ) ψ U).hom x = x.1.1 := by
  rfl

/-- Helper for Proposition 8-8.2-1: the subgroup-side map attached to a nonzero weight
constituent is itself nonzero. -/
theorem stabilizer_representation_hom_of_character_weight_constituent_ne_zero
    {τ : Rep.{x} ℂ (A ⋊[φ] H)} (ψ : A →* ℂˣ)
    (U : Subrepresentation (character_weight_subrepresentation (φ := φ) τ ψ).ρ)
    (hU : U.toSubmodule ≠ ⊥) :
    stabilizer_representation_hom_of_character_weight_constituent
        (φ := φ) (τ := τ) ψ U ≠ 0 := by
  rcases (Submodule.ne_bot_iff _).mp hU with ⟨x, hx, hx0⟩
  let ux : U.toSubmodule := ⟨x, hx⟩
  intro hzero
  have hux :
      (stabilizer_representation_hom_of_character_weight_constituent
          (φ := φ) (τ := τ) ψ U).hom ux = 0 := by
    have hhom :
        (stabilizer_representation_hom_of_character_weight_constituent
            (φ := φ) (τ := τ) ψ U).hom = 0 := by
      simpa using congrArg Rep.Hom.hom hzero
    rw [hhom]
    rfl
  -- Evaluating the subgroup-side map at a nonzero vector of `U` recovers the same ambient vector.
  exact hx0 <| by
    have hx_val_zero : x.1 = 0 := by
      calc
        x.1 =
            (stabilizer_representation_hom_of_character_weight_constituent
              (φ := φ) (τ := τ) ψ U).hom ux := by
                symm
                simpa [ux] using
                  stabilizer_representation_hom_of_character_weight_constituent_apply
                    (φ := φ) (τ := τ) ψ U ux
        _ = 0 := hux
    apply Subtype.ext
    simpa using hx_val_zero

end Proposition

end SemidirectAbelian

end

end Representation
