import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1.ElementarySubgroupBridge
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryCoherence

noncomputable section

universe u v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalSubgroupLinearPairing1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: mapping a subgroup-of-subgroup back to the ambient group gives
the original subgroup. -/
theorem subgroup_chain_map_subgroupOf_eq_local
    (H : Subgroup G) (L : Subgroup G) (hL : L ≤ H) :
    ((L.subgroupOf H).map H.subtype : Subgroup G) = L := by
  -- Passing to `subgroupOf H` only changes the ambient type; mapping back undoes that change.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hL hx⟩, hx, rfl⟩

/-- Helper for Remark 11-11.1-3: if `J ≤ M` and the subgroup cut out by `J` inside `M` is all
of `M`, then `J` already equals `M`. -/
theorem subgroup_eq_of_le_of_subgroupOf_eq_top_local
    {H0 : Type} [Group H0] [Finite H0]
    (M J : Subgroup H0) (hJM : J ≤ M) (hJtop : J.subgroupOf M = ⊤) :
    J = M := by
  have hmap :
      ((J.subgroupOf M).map M.subtype : Subgroup H0) = J :=
    subgroup_chain_map_subgroupOf_eq_local (G := H0) M J hJM
  have htop_subgroupOf : (M.subgroupOf M : Subgroup M) = ⊤ := by
    -- Inside `M`, the subgroup cut out by `M` itself is the top subgroup.
    ext x
    simp
  have htop_map : (((⊤ : Subgroup M).map M.subtype : Subgroup H0)) = M := by
    -- Map the tautological top subgroup of `M` back to the ambient group.
    rw [← htop_subgroupOf]
    simpa using (subgroup_chain_map_subgroupOf_eq_local (G := H0) M M le_rfl)
  -- Map the `subgroupOf` equality back to the ambient group, then identify the mapped top with
  -- `M`.
  calc
    J = ((J.subgroupOf M).map M.subtype : Subgroup H0) := hmap.symm
    _ = ((⊤ : Subgroup M).map M.subtype : Subgroup H0) := by rw [hJtop]
    _ = M := htop_map

/-- Helper for Remark 11-11.1-3: mapping a subgroup along an injective subgroup inclusion does not
change its cardinality. -/
theorem subgroup_chain_map_card_eq_local
    (H : Subgroup G) (K : Subgroup H) :
    Nat.card (K.map H.subtype) = Nat.card K := by
  -- The mapped subgroup is canonically equivalent to the original subgroup through the injective
  -- ambient inclusion.
  exact (Nat.card_congr (K.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm

/-- Helper for Remark 11-11.1-3: every proper subgroup of a finite ambient subgroup has strictly
smaller cardinality. -/
theorem subgroup_card_lt_of_lt_top_local
    (H : Subgroup G) (K : Subgroup H) (hK : K < ⊤) :
    Nat.card K < Nat.card H := by
  have hsubset : (K : Set H) ⊂ Set.univ := by
    refine ⟨by intro x hx; simp, ?_⟩
    intro htop
    exact hK.ne <| eq_top_iff.2 (by
      intro x hx
      exact htop (show x ∈ (Set.univ : Set H) by simp))
  -- Proper inclusion of finite sets forces a strict cardinal drop.
  simpa using (Set.toFinite (Set.univ : Set H)).card_lt_card hsubset

/-- Helper for Remark 11-11.1-3: a coatom of an ambient elementary subgroup is strictly smaller in
cardinality than the ambient subgroup. -/
theorem coatom_card_lt_ambient_local
    (H : Subgroup G) (M : Subgroup H) (hM : IsCoatom M) :
    Nat.card M < Nat.card H := by
  have hsubset : (M : Set H) ⊂ Set.univ := by
    refine ⟨by intro x hx; simp, ?_⟩
    intro htop
    exact hM.1 <| eq_top_iff.2 (by
      intro x hx
      exact htop (show x ∈ (Set.univ : Set H) by simp))
  -- Proper inclusion of finite sets gives the cardinality drop required by strong induction.
  simpa using (Set.toFinite (Set.univ : Set H)).card_lt_card hsubset

/-- Helper for Remark 11-11.1-3: a linear character on `K ≤ H` transports to the image subgroup
`K.map H.subtype`. -/
def mapped_linear_character_local
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    K.map H.subtype →* ℂˣ :=
  χ.comp (K.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom

/-- Helper for Remark 11-11.1-3: pairing an integral virtual character with a degree-`1`
character lands in the image of `ℤ`. -/
theorem pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
    {H : Type u} [Group H] [Finite H] (η : R(H)) (χ : H →* ℂˣ) :
    ⟪χ.toCharacterRing, (η : H → ℂ)⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
  let S : Set (H → ℂ) :=
    { ψ |
        ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
          (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : H → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : H → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          have hψ' :
              ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
                ψ = σ.character := by
            simpa [S] using hψ
          rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              have hξ' :
                  ∃ (Y : Type u) (_ : AddCommGroup Y) (_ : Module ℂ Y)
                    (_ : FiniteDimensional ℂ Y) (τ : Representation ℂ H Y),
                    ξ = τ.character := by
                simpa [S] using hξ
              rcases hξ' with ⟨Y, _instYAdd, _instYMod, _instYfd, τ, rfl⟩
              let π : Representation ℂ H (TensorProduct ℂ X Y) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ X Y, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : H → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact
                (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : H → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S) : (0 : H → ℂ) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : H → ℂ) ∈ Submodule.span ℤ S := by
    -- Reduce the bundled character ring element to the `ℤ`-span of honest characters.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span
        ⟨(σ : Type u), inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ H (ULift.{u} ℂ)).character = (1 : H → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      have hmap :
          algebraMap ℤ (H → ℂ) n =
            n • (Representation.trivial ℂ H (ULift.{u} ℂ)).character := by
        ext x
        simp [htriv]
      rw [hmap]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ULift.{u} ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ H (ULift.{u} ℂ), rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Commute the pairing so the `ℤ`-span induction hits the integral character input.
  rw [Representation.groupFunctionPairing_comm]
  have hpair_span :
      ∀ f : H → ℂ, f ∈ Submodule.span ℤ S →
        ⟪f, χ.toCharacterRing⟫ ∈ Set.range (algebraMap ℤ ℂ) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ hψ =>
        have hψ' :
            ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
              (_ : FiniteDimensional ℂ X) (σ : Representation ℂ H X),
              ψ = σ.character := by
          simpa [S] using hψ
        rcases hψ' with ⟨X, _instXAdd, _instXMod, _instXfd, σ, rfl⟩
        have hcard_ne : (Nat.card H : ℂ) ≠ 0 := by
          exact_mod_cast Nat.card_pos.ne'
        letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard_ne
        have hpair :
            ⟪σ.character, χ.toCharacterRing⟫ =
              Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) := by
          simpa [MonoidHom.toCharacterRing_apply] using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              (K := ℂ) σ χ.toRepresentation)
        refine ⟨(Module.finrank ℂ (σ.IntertwiningMap χ.toRepresentation) : ℤ), ?_⟩
        simpa using hpair.symm
    | zero =>
        refine ⟨0, ?_⟩
        simp [Representation.groupFunctionPairingOverField]
    | add ψ ξ _ _ hψ hξ =>
        rcases hψ with ⟨a, ha⟩
        rcases hξ with ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        calc
          algebraMap ℤ ℂ (a + b) = algebraMap ℤ ℂ a + algebraMap ℤ ℂ b := by simp
          _ = groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) +
                groupFunctionPairingOverField ℂ ξ (χ.toCharacterRing : H → ℂ) := by
              rw [ha, hb]
          _ = groupFunctionPairingOverField ℂ (ψ + ξ) (χ.toCharacterRing : H → ℂ) := by
              rw [Representation.groupFunctionPairing_add_left]
    | smul n ψ _ hψ =>
        rcases hψ with ⟨a, ha⟩
        refine ⟨n * a, ?_⟩
        calc
          algebraMap ℤ ℂ (n * a) = (n : ℂ) * algebraMap ℤ ℂ a := by
            simp [map_mul, mul_comm]
          _ = (n : ℂ) * groupFunctionPairingOverField ℂ ψ (χ.toCharacterRing : H → ℂ) := by
              rw [ha]
          _ = groupFunctionPairingOverField ℂ (n • ψ) (χ.toCharacterRing : H → ℂ) := by
              symm
              simpa [zsmul_eq_mul] using
                (Representation.groupFunctionPairing_smul_left
                  (a := (n : ℂ)) (φ := ψ) (ψ := (χ.toCharacterRing : H → ℂ)))
  exact hpair_span (η : H → ℂ) hηspan

/-- Helper for Remark 11-11.1-3: transporting a mapped subgroup coordinate back along the
canonical equivalence identifies it with the ordinary local restriction from `H` to `K`. -/
theorem mapped_coordinate_transport_eq_local_restriction
    (H : Subgroup G) (K : Subgroup H) (η : R(H)) :
    Subgroup.characterRingTransport
        (K.equivMapOfInjective H.subtype H.subtype_injective)
        ((Subgroup.characterRingRestrictionOfLe (subgroup_chain_map_le_local H K)) η) =
      (K ↾R[ℂ]) η := by
  apply Subtype.ext
  ext k
  -- Both sides evaluate the same ambient character on the underlying subgroup element.
  simp only [Subgroup.characterRingTransport_apply,
    Subgroup.characterRingRestrictionOfLe_apply,
    Subgroup.characterRingRestriction_apply]
  congr 1

/-- Helper for Remark 11-11.1-3: linear-character pairing is invariant under transporting a
character-ring element back from `K.map H.subtype` to `K`. -/
theorem linear_character_pairing_transport_eq
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
        (η : K.map H.subtype → ℂ)⟫ =
      ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ := by
  classical
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  let ambient : K.map H.subtype → ℂ := fun y ↦
    (((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ) y) *
      (η : K.map H.subtype → ℂ) y⁻¹
  let nested : K → ℂ := fun y ↦
    ((χ.toCharacterRing : K → ℂ) y) *
      ((Subgroup.characterRingTransport e η : R(K)) : K → ℂ) y⁻¹
  -- Reindex the normalized character-pairing sum along the subgroup equivalence.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcardNat : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr e.toEquiv).symm
  have hcard : ((Nat.card (K.map H.subtype) : ℕ) : ℂ) = (Nat.card K : ℂ) := by
    exact_mod_cast hcardNat
  rw [hcard]
  refine congrArg (fun z : ℂ ↦ (Nat.card K : ℂ)⁻¹ * z) ?_
  change (∑ t : K.map H.subtype, ambient t) = ∑ t : K, nested t
  exact
    (Fintype.sum_equiv e nested ambient fun y ↦ by
      -- Transporting both the character and the local value along `e` returns the original pair.
      dsimp [nested, ambient, mapped_linear_character_local]
      congr 1
      simp [e]).symm

/-- Helper for Remark 11-11.1-3: if a subgroup family over `H` is indexed by all subgroups of
`H`, then the top coordinate already detects whether the ambient class function is integral. -/
theorem subgroup_restriction_detection_on_elementary_group
    {H : Subgroup G}
    (φ : classFunctionSubmodule ℂ H)
    (hφ : ∀ J : (Finset.univ : Finset (Subgroup H)),
      (J.1.classFunctionRestriction φ : J.1 → ℂ) ∈ R(J.1)) :
    (φ : H → ℂ) ∈ R(H) := by
  let Jtop : (Finset.univ : Finset (Subgroup H)) := ⟨⊤, by simp⟩
  -- The top restriction is literally the original class function, transported along the
  -- tautological isomorphism `↥(⊤ : Subgroup H) ≃* H`.
  let ζ : R(↥(⊤ : Subgroup ↥H)) :=
    ⟨((⊤ : Subgroup ↥H).classFunctionRestriction φ : ↥(⊤ : Subgroup ↥H) → ℂ), hφ Jtop⟩
  have hζ := (Subgroup.characterRingTransport (Subgroup.topEquiv (G := ↥H)).symm ζ).2
  have hfun :
      ((Subgroup.characterRingTransport (Subgroup.topEquiv (G := ↥H)).symm ζ : R(↥H)) :
        ↥H → ℂ) = (φ : ↥H → ℂ) := by
    ext h
    simp [ζ, Subgroup.characterRingTransport_apply]
  exact hfun ▸ hζ

/-- Helper for Remark 11-11.1-3: choose the unique integer recording the pairing of a local
character-ring element with the transported degree-`1` character on `K.map H.subtype`. -/
noncomputable def linear_character_pairing_int_toFun
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    R(K.map H.subtype) → ℤ :=
  fun η ↦ Classical.choose <|
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := η) (χ := mapped_linear_character_local H K χ)

/-- Helper for Remark 11-11.1-3: the chosen integer witness recovers the corresponding complex
linear-character pairing. -/
theorem linear_character_pairing_int_toFun_spec
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
  -- Unpack the chosen witness from the integrality theorem above.
  exact Classical.choose_spec <|
    pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := η) (χ := mapped_linear_character_local H K χ)

/-- Helper for Remark 11-11.1-3: the integer witness for linear-character pairing is additive. -/
theorem linear_character_pairing_int_toFun_map_add
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η θ : R(K.map H.subtype)) :
    linear_character_pairing_int_toFun H K χ (η + θ) =
      linear_character_pairing_int_toFun H K χ η +
        linear_character_pairing_int_toFun H K χ θ := by
  apply (Int.cast_injective : Function.Injective ((↑) : ℤ → ℂ))
  -- Compare both integers after casting to `ℂ`, where the pairing is manifestly additive.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ (η + θ)) =
        ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            ((η + θ : R(K.map H.subtype)) : K.map H.subtype → ℂ)⟫ := by
          exact linear_character_pairing_int_toFun_spec H K χ (η + θ)
    _ = ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            (η : K.map H.subtype → ℂ)⟫ +
          ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            (θ : K.map H.subtype → ℂ)⟫ := by
          exact Representation.groupFunctionPairing_add_right
            (((mapped_linear_character_local H K χ).toCharacterRing : R(K.map H.subtype)) :
              K.map H.subtype → ℂ)
            (η : K.map H.subtype → ℂ)
            (θ : K.map H.subtype → ℂ)
    _ = algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) +
          algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ θ) := by
          rw [linear_character_pairing_int_toFun_spec H K χ η,
            linear_character_pairing_int_toFun_spec H K χ θ]
    _ = algebraMap ℤ ℂ
          (linear_character_pairing_int_toFun H K χ η +
            linear_character_pairing_int_toFun H K χ θ) := by
          simp

/-- Helper for Remark 11-11.1-3: the integer witness for linear-character pairing is `ℤ`-linear.
-/
theorem linear_character_pairing_int_toFun_map_zsmul
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (n : ℤ) (η : R(K.map H.subtype)) :
    linear_character_pairing_int_toFun H K χ (n • η) =
      n * linear_character_pairing_int_toFun H K χ η := by
  apply (Int.cast_injective : Function.Injective ((↑) : ℤ → ℂ))
  -- After casting to `ℂ`, this is exactly right-linearity of the pairing.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ (n • η)) =
        ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
            ((n • η : R(K.map H.subtype)) : K.map H.subtype → ℂ)⟫ := by
          exact linear_character_pairing_int_toFun_spec H K χ (n • η)
    _ = (n : ℂ) *
          ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
              (η : K.map H.subtype → ℂ)⟫ := by
          have hcoe : ((n • η : R(K.map H.subtype)) : K.map H.subtype → ℂ) =
              (n : ℂ) • (η : K.map H.subtype → ℂ) := by
            ext x
            simp [zsmul_eq_mul]
          rw [hcoe]
          exact Representation.groupFunctionPairing_smul_right
            (a := (n : ℂ))
            (φ := (((mapped_linear_character_local H K χ).toCharacterRing :
              R(K.map H.subtype)) : K.map H.subtype → ℂ))
            (ψ := (η : K.map H.subtype → ℂ))
    _ = (n : ℂ) * algebraMap ℤ ℂ (linear_character_pairing_int_toFun H K χ η) := by
          rw [linear_character_pairing_int_toFun_spec H K χ η]
    _ = algebraMap ℤ ℂ (n * linear_character_pairing_int_toFun H K χ η) := by
          simp [Int.cast_mul]

/-- Helper for Remark 11-11.1-3: the transported degree-`1` pairing is represented by a
`ℤ`-linear functional on the local character ring. -/
noncomputable def linear_character_pairing_int
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) :
    R(K.map H.subtype) →ₗ[ℤ] ℤ :=
  { toFun := linear_character_pairing_int_toFun H K χ
    map_add' := linear_character_pairing_int_toFun_map_add H K χ
    map_smul' := linear_character_pairing_int_toFun_map_zsmul H K χ }

/-- Helper for Remark 11-11.1-3: the integer-valued pairing linear map casts back to the original
complex pairing. -/
theorem linear_character_pairing_int_spec
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
  exact linear_character_pairing_int_toFun_spec H K χ η

/-- Helper for Remark 11-11.1-3: after transporting a `K.map H.subtype` coordinate back to `K`,
the resulting local pairing is still the integer-valued ambient pairing. -/
theorem subgroup_linear_character_pairing_int_transport_eq
    (H : Subgroup G) (K : Subgroup H) (χ : K →* ℂˣ) (η : R(K.map H.subtype)) :
    ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ =
      algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) := by
  -- First rewrite the transported pairing back to the ambient `K.map H.subtype` coordinate,
  -- then read off the chosen integer witness for that pairing.
  calc
    ⟪(χ.toCharacterRing : K → ℂ),
        ((Subgroup.characterRingTransport
          (K.equivMapOfInjective H.subtype H.subtype_injective) η : R(K)) : K → ℂ)⟫ =
      ⟪((mapped_linear_character_local H K χ).toCharacterRing : K.map H.subtype → ℂ),
          (η : K.map H.subtype → ℂ)⟫ := by
        symm
        exact linear_character_pairing_transport_eq H K χ η
    _ = algebraMap ℤ ℂ (linear_character_pairing_int H K χ η) := by
        symm
        exact linear_character_pairing_int_spec H K χ η

/-- Helper for Remark 11-11.1-3: when `J ≤ M ≤ H`, the ambient integer pairing computed in `H`
agrees with the same pairing computed in the smaller ambient subgroup `M` after transporting the
coordinate back along the canonical subgroup-chain equivalence. -/
theorem linear_character_pairing_int_subgroupOf_eq
    (H : Subgroup G) (M : Subgroup H) (J : Subgroup M) (α : J →* ℂˣ)
    (η : R((J.map M.subtype).map H.subtype)) :
    linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
      linear_character_pairing_int M J α
        (Subgroup.characterRingTransport
          ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) := by
  apply (Int.cast_injective : Function.Injective ((↑) : ℤ → ℂ))
  -- First rewrite the ambient pairing in `H` as the transported pairing on `J.map M.subtype`.
  calc
    algebraMap ℤ ℂ
        (linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η) =
      ⟪((mapped_linear_character_local H (J.map M.subtype)
            (mapped_linear_character_local M J α)).toCharacterRing :
          (J.map M.subtype).map H.subtype → ℂ),
          (η : (J.map M.subtype).map H.subtype → ℂ)⟫ := by
            exact
              linear_character_pairing_int_spec H (J.map M.subtype)
                (mapped_linear_character_local M J α) η
    _ =
      ⟪((mapped_linear_character_local M J α).toCharacterRing : J.map M.subtype → ℂ),
          ((Subgroup.characterRingTransport
              ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η :
                R(J.map M.subtype)) : J.map M.subtype → ℂ)⟫ := by
            exact
              linear_character_pairing_transport_eq H (J.map M.subtype)
                (mapped_linear_character_local M J α) η
    _ =
      algebraMap ℤ ℂ
        (linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η)) := by
            symm
            exact
              linear_character_pairing_int_spec M J α
                (Subgroup.characterRingTransport
                  ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η)

/-- Helper for Remark 11-11.1-3: divisibility of the smaller-ambient pairing transports unchanged
across the subgroup chain `J ≤ M ≤ H`. -/
theorem subgroup_chain_pairing_divisible_transport_local
    (H : Subgroup G) (M : Subgroup H) (J : Subgroup M) (α : J →* ℂˣ)
    (η : R((J.map M.subtype).map H.subtype)) {n : ℤ}
    (hdiv :
      ∃ c : ℤ,
        linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) =
          n * c) :
    ∃ c : ℤ,
      linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
        n * c := by
  rcases hdiv with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- Rewrite the ambient pairing as the transported smaller-ambient pairing, then reuse the same
  -- integer witness.
  calc
    linear_character_pairing_int H (J.map M.subtype) (mapped_linear_character_local M J α) η =
        linear_character_pairing_int M J α
          (Subgroup.characterRingTransport
            ((J.map M.subtype).equivMapOfInjective H.subtype H.subtype_injective) η) := by
              exact linear_character_pairing_int_subgroupOf_eq H M J α η
    _ = n * c := hc

/-- Helper for Remark 11-11.1-3: transporting the ambient restriction-defect identity from `X`
to the full subgroup family of a fixed `H ∈ X` produces the source-faithful local defect
equation. -/
theorem transported_subgroup_family_defect_eq_zsmul
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let δH : (J : XH) → R(J.1) := fun J ↦
      let JX : X := ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
      let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (t.1 pJ)
    ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH := by
  classical
  dsimp
  ext J j
  let JX : X := ⟨J.1.map H.1.subtype,
    (hXelem (J.1.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
  let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
  have hp :
      ((Subgroup.characterRingRestrictionOfLe (subgroup_chain_map_le_local H.1 J.1)) (x H) :
          R(JX.1)) - x JX = n • t.1 pJ := by
    have hp' := congrFun (congrArg Prod.fst hdx) pJ
    -- The global first defect block specializes to the `H ⟶ JX` restriction equation.
    simpa [elementary_coherence_defect, pJ, JX] using hp'
  have hp_eval := congrArg
    (fun ζ : R(JX.1) ↦
      ((ζ : JX.1 → ℂ) ((J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective) j))) hp
  -- Evaluating at the subgroup equivalence turns the ambient coordinate identity into the local
  -- transported family equation on `J`.
  simpa [JX, pJ, Representation.characterRingRestriction_apply, Pi.sub_apply, Pi.smul_apply,
    Subgroup.characterRingTransport_apply, Subgroup.characterRingRestrictionOfLe_apply,
    Subgroup.coe_equivMapOfInjective_apply, zsmul_eq_mul] using hp_eval

/-- Helper for Remark 11-11.1-3: once the local defect identity is written on the subgroup family
of `H`, the residual projector turns it into a pure `n`-multiple identity. -/
theorem local_residual_projector_eq_neg_zsmul
    {H0 : Type} [Group H0] [Finite H0]
    (XH : Finset (Subgroup H0))
    (sH : ((J : XH) → R(J.1)) →ₗ[ℤ] R(H0))
    (hsH : Function.LeftInverse sH (Representation.characterRingRestriction XH).toLinearMap)
    {ξ : R(H0)} {ψ δ : (J : XH) → R(J.1)} {n : ℤ}
    (hξ : ((Representation.characterRingRestriction XH).toLinearMap ξ) - ψ = n • δ) :
    let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
      (Representation.characterRingRestriction XH).toLinearMap
    let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
      LinearMap.id - fH.comp sH
    rH ψ = (-n) • rH δ := by
  dsimp
  let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) := (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) := LinearMap.id - fH.comp sH
  have hrξ : rH (fH ξ) = 0 := by
    -- The residual projector kills the actual image of the local restriction-family map.
    change fH ξ - fH (sH (fH ξ)) = 0
    rw [hsH ξ]
    simp
  have hneg : -rH ψ = n • rH δ := by
    -- Apply the projector to the transported defect equation and use `rH ∘ fH = 0`.
    have h : rH (fH ξ) - rH ψ = n • rH δ := by
      rw [← map_sub, ← map_zsmul]
      exact congrArg rH hξ
    rwa [hrξ, zero_sub] at h
  have hfinal := congrArg Neg.neg hneg
  simpa [neg_smul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

/-- Helper for Remark 11-11.1-3: applying the local residual projector to the transported subgroup
family keeps the image term `fH (sH ψ)` explicit, and the remaining error is an `n`-multiple in
the `K`-pairing. -/
theorem local_residual_pairing_decomposition_of_defect_multiple
    {H0 : Type} [Group H0] [Finite H0]
    (XH : Finset (Subgroup H0))
    (sH : ((J : XH) → R(J.1)) →ₗ[ℤ] R(H0))
    (hsH : Function.LeftInverse sH (Representation.characterRingRestriction XH).toLinearMap)
    {ψ δ : (J : XH) → R(J.1)} {n : ℤ}
    (htransported :
      let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
        (Representation.characterRingRestriction XH).toLinearMap
      fH (sH ψ) - ψ = n •
        (((LinearMap.id : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1))) -
          ((Representation.characterRingRestriction XH).toLinearMap).comp sH) δ))
    (K : XH) (χ : K.1 →* ℂˣ) :
    ∃ m : ℤ,
      ⟪(χ.toCharacterRing : K.1 → ℂ), (ψ K : K.1 → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K.1 → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
              K.1 → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
  let fH : R(H0) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    LinearMap.id - fH.comp sH
  have hresidual : ψ - fH (sH ψ) = (-n) • rH δ := by
    -- Route correction: keep the local-image term explicit instead of trying to identify `ψ K`
    -- directly with the pure residual coordinate; the transported defect equation contributes
    -- the residual with a sign.
    have h : fH (sH ψ) - ψ = n • rH δ := htransported
    have h' : ψ - fH (sH ψ) = -(n • rH δ) := by rw [← h, neg_sub]
    rw [h', neg_smul]
  let pairK : R(K.1) →ₗ[ℤ] ℂ :=
    { toFun := fun η ↦ ⟪(χ.toCharacterRing : K.1 → ℂ), (η : K.1 → ℂ)⟫
      map_add' := by
        intro η θ
        exact Representation.groupFunctionPairing_add_right
          (χ.toCharacterRing : K.1 → ℂ) (η : K.1 → ℂ) (θ : K.1 → ℂ)
      map_smul' := by
        intro a η
        have hcoe : ((a • η : R(K.1)) : K.1 → ℂ) = (a : ℂ) • (η : K.1 → ℂ) := by
          ext x
          simp [zsmul_eq_mul]
        have h := Representation.groupFunctionPairing_smul_right
          (a := (a : ℂ))
          (φ := (χ.toCharacterRing : K.1 → ℂ))
          (ψ := (η : K.1 → ℂ))
        simp only [RingHom.id_apply]
        rw [hcoe, h, zsmul_eq_mul] }
  rcases pairing_mem_range_int_of_mem_characterRing_with_linear_character_local
      (η := rH δ K) (χ := χ) with ⟨b, hb⟩
  have hpair_sub :
      pairK (ψ K - fH (sH ψ) K) = algebraMap ℤ ℂ (n * (-b)) := by
    have hcoord := congrArg (fun ζ : (J : XH) → R(J.1) ↦ ζ K) hresidual
    calc
      pairK (ψ K - fH (sH ψ) K) = pairK ((-n) • rH δ K) := by
        simpa [Pi.smul_apply] using congrArg pairK hcoord
      _ = algebraMap ℤ ℂ (n * (-b)) := by
        rw [LinearMap.map_smul]
        have hbK : pairK (rH δ K) = algebraMap ℤ ℂ b := hb.symm
        rw [hbK]
        simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, Int.cast_mul, Int.cast_neg]
        ring
  refine ⟨-b, ?_⟩
  have hpair_eq :
      ⟪(χ.toCharacterRing : K.1 → ℂ), (ψ K : K.1 → ℂ)⟫ -
          ⟪(χ.toCharacterRing : K.1 → ℂ),
              (((Representation.characterRingRestriction XH) (sH ψ) K : R(K.1)) :
                K.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * (-b)) := by
    have h := hpair_sub
    rw [map_sub] at h
    exact h
  -- Move the explicit image term to the right-hand side; only the `n`-multiple remains.
  exact sub_eq_iff_eq_add'.mp hpair_eq



end CharacterizationOfCharacters

end Representation
