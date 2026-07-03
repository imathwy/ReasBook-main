import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Exercise_7_7_2_3
import LinearRepresentations_Serre_1977.Chap13.Remark_13_13_1_9

noncomputable section

universe u v

open scoped Representation

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type u} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

local instance : DecidableEq (Subgroup G) := Classical.decEq _

private abbrev characterRingElement (ρ : Representation ℚ G V) : R[ℚ](G) :=
  ⟨ρ.character, Representation.rep_character_mem_characterRingOverField (Rep.of ρ)⟩

/- The irreducible rational character attached to `ρ`, viewed in `R_ℚ(G)`, is written `χ_ρ` on
the source-facing theorem surface. The underlying bridge to `R_ℚ(G)` is the canonical Chapter 12
theorem `Representation.rep_character_mem_characterRingOverField`; `characterRingElement` is only
the private named carrier needed by Lean's notation elaborator. -/
scoped[Representation] notation:max "χ_" ρ:max =>
  characterRingElement ρ

/-- Helper for Exercise 13-13.1-13: intertwining maps from the quotient permutation
representation on `G ⧸ H` to `ρ` are in bijection with `H`-fixed vectors of `ρ`. -/
private theorem quotient_permutation_intertwining_finrank_eq_finrank_invariants
    (ρ : Representation ℚ G V) (H : Subgroup G) :
    Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) =
      Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) := by
  let v₀ : G ⧸ H := QuotientGroup.mk (1 : G)
  let e : ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) ≃ₗ[ℚ]
      Representation.invariants (ρ.comp H.subtype) :=
    { toFun := fun f ↦ by
        -- Evaluate an equivariant map at the trivial coset to obtain an `H`-fixed vector.
        refine ⟨f (Finsupp.single v₀ (1 : ℚ)), ?_⟩
        intro h
        have hmk : ((h : G) : G ⧸ H) = v₀ := by
          apply (QuotientGroup.eq).2
          simpa using h.2
        have hf := LinearMap.congr_fun (f.2 h) (Finsupp.single v₀ (1 : ℚ))
        simpa [v₀, Representation.ofMulAction_single, hmk] using hf.symm
      invFun := fun v ↦ by
        -- Rebuild the equivariant map by sending the coset `gH` to `ρ(g)v`.
        let vec : G ⧸ H → V :=
          Quotient.lift (fun g : G ↦ ρ g v)
            (by
              intro a b hab
              have hmem : a⁻¹ * b ∈ H := by
                simpa [QuotientGroup.leftRel_apply] using hab
              have hv : ρ (a⁻¹ * b) v = v := v.2 ⟨a⁻¹ * b, hmem⟩
              calc
                ρ a v = ρ a (ρ (a⁻¹ * b) v) := by rw [hv]
                _ = ρ b v := by simp [map_mul])
        refine
          { toLinearMap := Finsupp.linearCombination ℚ vec
            isIntertwining' := ?_ }
        intro g
        apply Finsupp.lhom_ext'
        intro q
        refine Quotient.inductionOn q ?_
        intro a
        ext
        simp [vec, Finsupp.linearCombination, Representation.ofMulAction_single, map_mul]
      left_inv := by
        intro f
        -- Two equivariant maps out of a permutation module agree once they agree on basis vectors.
        apply Representation.IntertwiningMap.ext
        apply Finsupp.lhom_ext'
        intro q
        refine Quotient.inductionOn q ?_
        intro a
        ext
        have hf := LinearMap.congr_fun (f.2 a) (Finsupp.single v₀ (1 : ℚ))
        simpa [v₀, Finsupp.linearCombination, Representation.ofMulAction_single] using hf.symm
      right_inv := by
        intro v
        -- Evaluating the reconstructed map back at the trivial coset returns the original vector.
        apply Subtype.ext
        simp [v₀]
      map_add' := by
        intro f g
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a f
        apply Subtype.ext
        rfl }
  exact e.finrank_eq

/-- Helper for Exercise 13-13.1-13: restricting to the trivial subgroup fixes every vector. -/
private theorem bottom_subgroup_invariants_eq_top
    (ρ : Representation ℚ G V) :
    Representation.invariants (ρ.comp (⊥ : Subgroup G).subtype) = ⊤ := by
  -- The bottom subgroup has only the identity element, so its invariants are all of `V`.
  apply top_unique
  intro x hx
  rw [Representation.mem_invariants]
  intro h
  have hh : h = 1 := Subsingleton.elim _ _
  simpa [hh]

/-- Helper for Exercise 13-13.1-13: if `ρ` is faithful and irreducible and `H` is a nontrivial
normal subgroup, then `ρ` has no nonzero `H`-fixed vectors. -/
private theorem invariants_eq_bot_of_irreducible_faithful_normal_ne_bot
    (ρ : Representation ℚ G V) [ρ.IsIrreducible]
    (hfaithful : Function.Injective ρ)
    (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    Representation.invariants (ρ.comp H.subtype) = ⊥ := by
  let i : (ρ.toInvariants H).IntertwiningMap ρ :=
    ⟨Submodule.subtype _, fun _ ↦ rfl⟩
  have hrange : i.range.toSubmodule = Representation.invariants (ρ.comp H.subtype) := by
    -- The inclusion of the invariant subspace has range exactly the invariant subspace.
    simpa [i, Representation.IntertwiningMap.range] using
      (Submodule.map_subtype_top (Representation.invariants (ρ.comp H.subtype)))
  by_cases hbot : Representation.invariants (ρ.comp H.subtype) = ⊥
  · exact hbot
  · have hrange_ne_bot : i.range ≠ ⊥ := by
      intro hr
      apply hbot
      exact hrange ▸ congrArg Subrepresentation.toSubmodule hr
    have hrange_top : i.range = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top i.range).resolve_left hrange_ne_bot
    have hinv_top : Representation.invariants (ρ.comp H.subtype) = ⊤ := by
      rw [← hrange]
      exact congrArg Subrepresentation.toSubmodule hrange_top
    have hHbot : H = ⊥ := by
      -- If every vector is `H`-fixed, faithfulness forces every element of `H` to be trivial.
      ext g
      constructor
      · intro hg
        have hρg : ρ g = ρ 1 := by
          ext v
          have hv : v ∈ Representation.invariants (ρ.comp H.subtype) := by
            simpa [hinv_top]
          simpa using hv ⟨g, hg⟩
        simpa using hfaithful hρg
      · intro hg
        have : g = 1 := by simpa using hg
        simpa [this] using H.one_mem
    exact False.elim (hH hHbot)

-- Proof sketch: when `H = ⊥`, the quotient `G ⧸ H` is canonically the left-regular `G`-set `G`.
-- The resulting intertwining-space dimension agrees with that of the regular representation, so
-- after dividing by `dim_ℚ End_G(ρ)` the irreducible multiplicities also agree.
/-- Exercise 13-13.1-13 (1): when `H = {1}`, the permutation representation on `G / H` has the
same irreducible-multiplicity coefficient for `ρ` as the regular rational representation. -/
theorem quotientPermutation_irreducibleMultiplicity_eq_of_eq_bot
    (ρ : Representation ℚ G V) {H : Subgroup G} (hH : H = ⊥) :
    Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) /
        Module.finrank ℚ (ρ.IntertwiningMap ρ) =
      Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) /
        Module.finrank ℚ (ρ.IntertwiningMap ρ) := by
  subst hH
  -- Replace quotient-permutation intertwiners by fixed vectors for the restricted action, then
  -- divide the resulting equality by `dim_ℚ End_G(ρ)`.
  exact congrArg
    (fun n ↦ n / Module.finrank ℚ (ρ.IntertwiningMap ρ))
    (by
      calc
        Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ (⊥ : Subgroup G))).IntertwiningMap ρ)
          = Module.finrank ℚ (Representation.invariants (ρ.comp (⊥ : Subgroup G).subtype)) := by
              exact quotient_permutation_intertwining_finrank_eq_finrank_invariants ρ ⊥
        _ = Module.finrank ℚ V := by
              rw [bottom_subgroup_invariants_eq_top ρ]
              simp
        _ = Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
              exact (Representation.leftRegularMapEquiv ρ).finrank_eq.symm)

-- Proof sketch: a copy of `ρ` inside the permutation representation on `G ⧸ H` gives, by
-- Frobenius reciprocity, a nonzero `H`-fixed subspace of `ρ`. Since `H` is normal, that fixed
-- subspace is `G`-stable; irreducibility makes it either `0` or all of `V`, and faithfulness
-- rules out the latter when `H ≠ ⊥`. Hence the numerator in the multiplicity quotient is `0`.
/-- Exercise 13-13.1-13 (2): if `H ≠ {1}` and `H` is normal, then the
irreducible-multiplicity coefficient of the faithful irreducible rational representation `ρ` in
the permutation representation on `G / H` is `0`. -/
theorem quotientPermutation_irreducibleMultiplicity_eq_zero_of_ne_bot
    (ρ : Representation ℚ G V) [ρ.IsIrreducible]
    (hfaithful : Function.Injective ρ)
    {H : Subgroup G} (hnormal : H.Normal) (hH : H ≠ ⊥) :
    Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) /
        Module.finrank ℚ (ρ.IntertwiningMap ρ) = 0 := by
  letI : H.Normal := hnormal
  -- Reduce again to the `H`-fixed subspace, show the numerator vanishes, and hence so does the
  -- multiplicity quotient.
  calc
    Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) /
        Module.finrank ℚ (ρ.IntertwiningMap ρ)
      = 0 / Module.finrank ℚ (ρ.IntertwiningMap ρ) := by
          congr
          calc
            Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ)
              = Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) := by
                  exact quotient_permutation_intertwining_finrank_eq_finrank_invariants ρ H
            _ = 0 := by
                  rw [invariants_eq_bot_of_irreducible_faithful_normal_ne_bot ρ hfaithful H hH]
                  simp
    _ = 0 := by simp

/-- Helper for Exercise 13-13.1-13: Frobenius reciprocity rewrites the pairing of a restricted
character against a subgroup character as the pairing against the induced character. -/
private theorem groupFunctionPairing_character_comp_eq_character_ind_local
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (α : H →* G) (E : Representation ℚ G V)
    (θ : Representation ℚ H W) :
    ⟪θ.character, Representation.character (E.comp α)⟫ =
      ⟪(Representation.ind α θ).character, E.character⟫ := by
  let _ : Fintype H := Fintype.ofFinite H
  letI : Invertible (Nat.card H : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- This is the Chapter 7 Frobenius pairing identity specialized to the present rational setting.
  simpa using groupFunctionPairing_character_comp_eq_character_ind α E θ

/-- Helper for Exercise 13-13.1-13: pairing `χ_ρ` with the subgroup permutation character `ℓ_H^G`
recovers the intertwining-space dimension for the permutation representation on `G ⧸ H`. -/
private theorem character_pairing_subgroupPermutationCharacter_eq_quotient_permutation_intertwining_finrank
    (ρ : Representation ℚ G V) (H : Subgroup G) :
    ⟪((χ_ ρ : R[ℚ](G)) : G → ℚ), ((ℓ_{H}^G : R[ℚ](G)) : G → ℚ)⟫ =
      Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) := by
  let _ : Fintype H := Fintype.ofFinite H
  let τ : Representation ℚ H ℚ := Representation.trivial ℚ H ℚ
  have htriv : τ.character = (1 : H → ℚ) := by
    -- The trivial representation has constant character `1`.
    ext h
    simp [τ, Representation.character, Representation.trivial]
  letI : Invertible (Nat.card H : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hperm :
      ((ℓ_{H}^G : R[ℚ](G)) : G → ℚ) = (Representation.ind H.subtype τ).character := by
    -- Rewrite the subgroup permutation character as the induced trivial character.
    calc
      ((ℓ_{H}^G : R[ℚ](G)) : G → ℚ)
          = (H.classFunctionInduction (1 : H → ℚ) : G → ℚ) := by
              rfl
      _ = (H.classFunctionInduction τ.character : G → ℚ) := by
            rw [htriv]
      _ = (Representation.ind H.subtype τ).character := by
            simpa [Subgroup.classFunctionInduction_apply] using
              (Subgroup.inducedClassFunction_eq_character_ind (H := H) (K := ℚ) τ)
  -- Rewrite the subgroup permutation character as an induced trivial character, then use
  -- Frobenius reciprocity and the already-established quotient-permutation/intertwining bridge.
  calc
    ⟪((χ_ ρ : R[ℚ](G)) : G → ℚ), ((ℓ_{H}^G : R[ℚ](G)) : G → ℚ)⟫
        = ⟪ρ.character, ((ℓ_{H}^G : R[ℚ](G)) : G → ℚ)⟫ := by
            rfl
    _ = ⟪(Representation.ind H.subtype τ).character, ρ.character⟫ := by
          rw [hperm, Representation.groupFunctionPairing_comm]
    _ = ⟪τ.character, Representation.character (ρ.comp H.subtype)⟫ := by
          symm
          exact groupFunctionPairing_character_comp_eq_character_ind_local H.subtype ρ τ
    _ = ⟪Representation.character (ρ.comp H.subtype), τ.character⟫ := by
          rw [Representation.groupFunctionPairing_comm]
    _ = (Nat.card H : ℚ)⁻¹ *
          ∑ s : H, Representation.character (ρ.comp H.subtype) s := by
          rw [htriv]
          rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
          simp
    _ = Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) := by
          simpa using
            (Representation.card_inv_mul_sum_char_eq_finrank (ρ := ρ.comp H.subtype))
    _ = Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) := by
          exact_mod_cast (quotient_permutation_intertwining_finrank_eq_finrank_invariants ρ H).symm

/-- Helper for Exercise 13-13.1-13: the pairing test is additive on the rational character ring. -/
private theorem subgroup_permutation_pairing_test_map_add
    (ρ : Representation ℚ G V) (χ ψ : R[ℚ](G)) :
    ⟪(((χ + ψ : R[ℚ](G)) : G → ℚ)), ρ.character⟫ =
      ⟪(χ : G → ℚ), ρ.character⟫ + ⟪(ψ : G → ℚ), ρ.character⟫ := by
  -- The test is the pairing with a fixed character, so additivity is the left-linearity of that
  -- pairing.
  simpa using
    (Representation.groupFunctionPairing_add_left (χ : G → ℚ) (ψ : G → ℚ) ρ.character)

/-- Helper for Exercise 13-13.1-13: the pairing test is `ℤ`-linear on the rational character
ring. -/
private theorem subgroup_permutation_pairing_test_map_smul
    (ρ : Representation ℚ G V) (a : ℤ) (χ : R[ℚ](G)) :
    ⟪(((a • χ : R[ℚ](G)) : G → ℚ)), ρ.character⟫ =
      a • ⟪(χ : G → ℚ), ρ.character⟫ := by
  -- Integer scaling on the character ring is scalar multiplication on the underlying
  -- `ℚ`-valued class functions, so the pairing remains homogeneous.
  simpa using
    (Representation.groupFunctionPairing_smul_left (((a : ℤ) : ℚ)) (χ : G → ℚ) ρ.character)

/-- Helper for Exercise 13-13.1-13: the obstruction functional records the pairing with
`ρ.character`. -/
private def subgroup_permutation_pairing_test
    (ρ : Representation ℚ G V) :
    R[ℚ](G) →ₗ[ℤ] ℚ :=
  { toFun := fun χ ↦ ⟪(χ : G → ℚ), ρ.character⟫
    map_add' := subgroup_permutation_pairing_test_map_add ρ
    map_smul' := subgroup_permutation_pairing_test_map_smul ρ }

/-- Helper for Exercise 13-13.1-13: the obstruction functional takes the subgroup permutation
generators to either the regular intertwining dimension or `0`. -/
private theorem subgroup_permutation_pairing_test_on_generator
    (ρ : Representation ℚ G V) [ρ.IsIrreducible]
    (hfaithful : Function.Injective ρ)
    (hallNormal : ∀ K : Subgroup G, K.Normal)
    (H : Subgroup G) :
    subgroup_permutation_pairing_test ρ (ℓ_{H}^G) =
      if H = ⊥ then Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) else 0 := by
  classical
  by_cases hH : H = ⊥
  · subst hH
    -- For the trivial subgroup the permutation representation is the left-regular representation,
    -- so the pairing gives the regular intertwining dimension.
    calc
      subgroup_permutation_pairing_test ρ (ℓ_{(⊥ : Subgroup G)}^G)
          =
            Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ (⊥ : Subgroup G))).IntertwiningMap ρ) := by
              change ⟪(((ℓ_{(⊥ : Subgroup G)}^G : R[ℚ](G)) : G → ℚ)), ρ.character⟫ =
                Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ (⊥ : Subgroup G))).IntertwiningMap ρ)
              rw [Representation.groupFunctionPairing_comm]
              exact
                character_pairing_subgroupPermutationCharacter_eq_quotient_permutation_intertwining_finrank
                  ρ ⊥
      _ = Module.finrank ℚ (Representation.invariants (ρ.comp (⊥ : Subgroup G).subtype)) := by
            exact_mod_cast quotient_permutation_intertwining_finrank_eq_finrank_invariants ρ ⊥
      _ = Module.finrank ℚ V := by
            rw [bottom_subgroup_invariants_eq_top ρ]
            simp
      _ = Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
            exact_mod_cast (Representation.leftRegularMapEquiv ρ).finrank_eq.symm
      _ = if (⊥ : Subgroup G) = ⊥ then Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ)
            else 0 := by
            simp
  · letI : H.Normal := hallNormal H
    -- For a nontrivial normal subgroup, irreducibility and faithfulness force the fixed vectors
    -- to vanish, so the pairing vanishes as well.
    calc
      subgroup_permutation_pairing_test ρ (ℓ_{H}^G)
          =
            Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ) := by
              change ⟪(((ℓ_{H}^G : R[ℚ](G)) : G → ℚ)), ρ.character⟫ =
                Module.finrank ℚ ((ofMulAction ℚ G (G ⧸ H)).IntertwiningMap ρ)
              rw [Representation.groupFunctionPairing_comm]
              exact
                character_pairing_subgroupPermutationCharacter_eq_quotient_permutation_intertwining_finrank
                  ρ H
      _ = Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) := by
            exact_mod_cast quotient_permutation_intertwining_finrank_eq_finrank_invariants ρ H
      _ = 0 := by
            rw [invariants_eq_bot_of_irreducible_faithful_normal_ne_bot ρ hfaithful H hH]
            simp
      _ = if H = ⊥ then Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) else 0 := by
            simp [hH]

/-- Helper for Exercise 13-13.1-13: on the subgroup-permutation span, the obstruction functional
lands in the lattice of multiples of the regular intertwining dimension. -/
private theorem subgroup_permutation_pairing_test_mem_regular_multiples
    (ρ : Representation ℚ G V) [ρ.IsIrreducible]
    (hfaithful : Function.Injective ρ)
    (hallNormal : ∀ K : Subgroup G, K.Normal)
    {χ : R[ℚ](G)}
    (hχ : χ ∈ subgroupPermutationCharacterSpanOverQ G) :
    ∃ z : ℤ,
      subgroup_permutation_pairing_test ρ χ =
        (z : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
  classical
  -- The subgroup-permutation span is generated by the `ℓ_H^G`, and the test takes values `0` or
  -- the regular intertwining dimension on those generators.
  change χ ∈ Submodule.span ℤ (Set.range fun H : Subgroup G ↦ (ℓ_{H}^G : R[ℚ](G))) at hχ
  let p :
      (x : R[ℚ](G)) →
        x ∈ Submodule.span ℤ (Set.range fun H : Subgroup G ↦ (ℓ_{H}^G : R[ℚ](G))) →
          Prop :=
    fun x _ ↦
      ∃ z : ℤ,
        subgroup_permutation_pairing_test ρ x =
          (z : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ)
  exact
    Submodule.span_induction
      (p := p)
      (mem := by
        intro x hx
        rcases hx with ⟨H, rfl⟩
        refine ⟨if H = ⊥ then 1 else 0, ?_⟩
        simpa [mul_comm] using
          subgroup_permutation_pairing_test_on_generator ρ hfaithful hallNormal H)
      (zero := by
        refine ⟨0, ?_⟩
        simpa using (subgroup_permutation_pairing_test ρ).map_zero)
      (add := by
        intro x y hx hy hx_mul hy_mul
        rcases hx_mul with ⟨m, hm⟩
        rcases hy_mul with ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        calc
          subgroup_permutation_pairing_test ρ (x + y)
              = subgroup_permutation_pairing_test ρ x + subgroup_permutation_pairing_test ρ y := by
                  simpa using (subgroup_permutation_pairing_test ρ).map_add x y
          _ = (m : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) +
                (n : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                simp [hm, hn]
          _ = ((m + n : ℤ) : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                calc
                  (m : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) +
                      (n : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ)
                    = ((m : ℚ) + (n : ℚ)) *
                        Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                          ring
                  _ = ((m + n : ℤ) : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                        norm_num)
      (smul := by
        intro a x hx hx_mul
        rcases hx_mul with ⟨n, hn⟩
        refine ⟨a * n, ?_⟩
        calc
          subgroup_permutation_pairing_test ρ (a • x)
              = a • subgroup_permutation_pairing_test ρ x := by
                  simpa using (subgroup_permutation_pairing_test ρ).map_smul a x
          _ = ((a : ℤ) : ℚ) * ((n : ℚ) *
                Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ)) := by
                simp [hn]
          _ = ((a * n : ℤ) : ℚ) *
                Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                calc
                  ((a : ℤ) : ℚ) * ((n : ℚ) *
                      Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ))
                    = (((a : ℤ) : ℚ) * (n : ℚ)) *
                        Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                          ring
                  _ = ((a * n : ℤ) : ℚ) * Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) := by
                        norm_num)
      hχ

-- Proof sketch: the generators of `subgroupPermutationCharacterSpanOverQ G` are the permutation
-- characters `ℓ_H^G`. By parts (1) and (2), the coefficient of `χ_ρ` in each such generator is
-- either the Artin-Wedderburn matrix-size parameter of `ρ` when `H = ⊥` or `0` when `H ≠ ⊥`;
-- therefore every element of the `ℤ`-span has `χ_ρ`-coefficient divisible by that matrix size.
-- If that matrix size is at least `2`, the irreducible character `χ_ρ` itself cannot lie in the
-- span.
/-- Exercise 13-13.1-13 (3): if the Artin-Wedderburn matrix-size parameter of the faithful
irreducible rational representation `ρ` is at least `2`, then its irreducible character `χ_ρ`
does not belong to the subgroup of `R_ℚ(G)` generated by the subgroup permutation characters
`ℓ_H^G`. -/
theorem irreducibleCharacter_not_mem_subgroupPermutationCharacterSpanOverQ
    (ρ : Representation ℚ G V) [ρ.IsIrreducible]
    (hfaithful : Function.Injective ρ)
    (hallNormal : ∀ K : Subgroup G, K.Normal)
    (hmatrix :
      2 ≤
        Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ) /
          Module.finrank ℚ (ρ.IntertwiningMap ρ)) :
    χ_ ρ ∉ subgroupPermutationCharacterSpanOverQ G := by
  intro hχ
  letI : Invertible (Nat.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set d : ℕ := Module.finrank ℚ (ρ.IntertwiningMap ρ)
  set N : ℕ := Module.finrank ℚ ((leftRegular ℚ G).IntertwiningMap ρ)
  have hmatrix' : 2 ≤ N / d := by
    simpa [d, N] using hmatrix
  have hdpos : 0 < d := by
    by_contra hd
    have hdzero : d = 0 := Nat.eq_zero_of_not_pos hd
    simp [hdzero] at hmatrix'
  have htwo_mul_le : 2 * d ≤ N := by
    exact (Nat.le_div_iff_mul_le hdpos).mp hmatrix'
  have hNpos : 0 < N := by
    have htwo_pos : 0 < 2 * d := by
      exact Nat.mul_pos (by decide) hdpos
    exact lt_of_lt_of_le htwo_pos htwo_mul_le
  rcases subgroup_permutation_pairing_test_mem_regular_multiples ρ hfaithful hallNormal hχ with
    ⟨z, hz⟩
  have hself :
      subgroup_permutation_pairing_test ρ (χ_ ρ) = d := by
    -- Evaluating the test on `χ_ρ` is the self-pairing of `ρ.character`.
    simpa [subgroup_permutation_pairing_test, d, characterRingElement] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap ℚ ρ ρ)
  have hEq : (d : ℚ) = (z : ℚ) * (N : ℚ) := by
    simpa [d, N] using (hself.symm.trans hz)
  have htwo_mul_le_rat : (2 : ℚ) * d ≤ N := by
    exact_mod_cast htwo_mul_le
  have hdpos_rat : (0 : ℚ) < d := by
    exact_mod_cast hdpos
  have hNpos_rat : (0 : ℚ) < N := by
    exact_mod_cast hNpos
  have hzpos_rat : (0 : ℚ) < z := by
    nlinarith [hEq, hdpos_rat, hNpos_rat]
  have hzpos : 0 < z := by
    exact_mod_cast hzpos_rat
  have hzone : (1 : ℚ) ≤ z := by
    have hzge : (1 : ℤ) ≤ z := by
      omega
    exact_mod_cast hzge
  -- The span forces the self-pairing to be a multiple of `N`, but `N ≥ 2d` by hypothesis.
  nlinarith [hEq, htwo_mul_le_rat, hNpos_rat, hzone]

end

end Representation
