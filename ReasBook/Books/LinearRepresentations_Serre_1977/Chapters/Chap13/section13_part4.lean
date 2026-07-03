import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_13_1_13 (from Chap13) -/
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

/-! ### Exercise_13_13_1_14 (from Chap13) -/
noncomputable section

universe u v

open scoped Representation
open scoped Quaternion

namespace Representation

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3
local notation "ρ" => quaternionCyclicWitnessRepresentation

local instance : Fintype Q8 := inferInstance
local instance : Fintype C3 := inferInstance
local instance : DecidableEq Q8 := inferInstance
local instance : DecidableEq C3 := inferInstance
local instance : Finite G0 := inferInstance
local instance : Fintype G0 := inferInstance
local instance : DecidableEq G0 := inferInstance
local instance : DecidableEq ℍ[ℚ] := by
  intro a b
  by_cases hre : a.re = b.re
  · by_cases himI : a.imI = b.imI
    · by_cases himJ : a.imJ = b.imJ
      · by_cases himK : a.imK = b.imK
        · exact isTrue (by ext <;> assumption)
        · exact isFalse (by
            intro h
            exact himK (congrArg QuaternionAlgebra.imK h))
      · exact isFalse (by
          intro h
          exact himJ (congrArg QuaternionAlgebra.imJ h))
    · exact isFalse (by
        intro h
        exact himI (congrArg QuaternionAlgebra.imI h))
  · exact isFalse (by
      intro h
      exact hre (congrArg QuaternionAlgebra.re h))
local instance : DecidableEq (Units ℍ[ℚ]) := fun a b =>
  if h : (a : ℍ[ℚ]) = (b : ℍ[ℚ]) then
    isTrue (Units.ext h)
  else
    isFalse fun hab ↦ h (congrArg Units.val hab)
local instance : Finite (ULift.{u} G0) := inferInstance
local instance (H : Subgroup G0) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup (ULift.{u} G0)) : Fintype H := Fintype.ofFinite H
local instance (H : Subgroup G0) : DecidablePred fun x : G0 ↦ x ∈ H := Classical.decPred _
local instance : DecidableEq (Subgroup G0) := Classical.decEq _

-- Proof sketch: the images of `a 1` and `xa 0` are the distinct units `i` and `j`, and the eight
-- resulting unit products are pairwise distinct in `ℍ[ℚ]`.
/-- Exercise 13-13.1-14: the map `quaternionGroupTwoToQuaternionUnits` realizes `QuaternionGroup
2` as a subgroup of `ℍ[ℚ]ˣ`. -/
theorem quaternionGroupTwoToQuaternionUnits_injective :
    Function.Injective quaternionGroupTwoToQuaternionUnits := by
  -- The explicit `Q8` table is finite, so Lean can check the eight quaternion-unit values are
  -- pairwise distinct directly.
  native_decide

-- Proof sketch: the generator is sent to a unit of order `3`, so the resulting monoid hom from
-- the cyclic group of order `3` is injective.
/-- Exercise 13-13.1-14: the map `cyclicOrderThreeToQuaternionUnits` realizes the cyclic group of
order `3` as a subgroup of `ℍ[ℚ]ˣ`. -/
theorem cyclicOrderThreeToQuaternionUnits_injective :
    Function.Injective cyclicOrderThreeToQuaternionUnits := by
  -- The cyclic factor has only three elements, so injectivity reduces to a finite computation.
  native_decide

-- Proof sketch: identify `ℍ[ℚ]` as a simple bimodule for the commuting left action of the cubic
-- root of unity field and the right action of `Q₈`, then use the double-centralizer description of
-- the constructed action.
/-- Exercise 13-13.1-14: the witness representation `ρ` is irreducible over `ℚ`. -/
theorem quaternionCyclicWitnessRepresentation_isIrreducible :
    (ρ).IsIrreducible := by
  exact quaternion_cyclic_witness_isIrreducible

/-- Helper for Exercise 13-13.1-14: the witness irreducibility theorem promoted to an instance. -/
instance : (ρ).IsIrreducible :=
  quaternionCyclicWitnessRepresentation_isIrreducible

-- Proof sketch: both factors embed faithfully into `ℍ[ℚ]ˣ`, and commuting left and right
-- multiplication determine the pair of group elements uniquely.
/-- Exercise 13-13.1-14: the witness representation `ρ` is faithful. -/
theorem quaternionCyclicWitnessRepresentation_faithful :
    Function.Injective ρ := by
  -- Evaluating at `1` turns a kernel computation into an explicit equality in `ℍ[ℚ]`, where the
  -- `24` possibilities can be checked directly.
  intro g h hgh
  have hker : quaternionCyclicWitnessRepresentation (g * h⁻¹) = 1 := by
    calc
      quaternionCyclicWitnessRepresentation (g * h⁻¹)
          = quaternionCyclicWitnessRepresentation g *
              quaternionCyclicWitnessRepresentation h⁻¹ := by
              simp [map_mul]
      _ = quaternionCyclicWitnessRepresentation h *
            quaternionCyclicWitnessRepresentation h⁻¹ := by
            rw [hgh]
      _ = 1 := by
            simpa using (quaternionCyclicWitnessRepresentation.map_mul h h⁻¹).symm
  have hkernel_eval :
      quaternionCyclicWitnessRepresentation (g * h⁻¹) (1 : ℍ[ℚ]) = 1 := by
    simpa using LinearMap.congr_fun hker (1 : ℍ[ℚ])
  have hkernel :
      g * h⁻¹ = 1 := by
    let hdetect :
        ∀ x : G0, quaternionCyclicWitnessRepresentation x (1 : ℍ[ℚ]) = 1 → x = 1 := by
      native_decide
    exact hdetect (g * h⁻¹) hkernel_eval
  have hmul := congrArg (fun x : G0 ↦ x * h) hkernel
  simpa [mul_assoc] using hmul

-- Proof sketch: `Q8 × C3` is Hamiltonian; equivalently, every subgroup is normal.
/-- Exercise 13-13.1-14: every subgroup of `Q8 × C3` is normal. -/
theorem quaternionCyclicWitnessGroup_allSubgroups_normal
    (H : Subgroup G0) :
    H.Normal := by
  -- Split each subgroup element into its `Q8` and `C3` coordinates; the second factor is central,
  -- and conjugation in `Q8` preserves each cyclic order-`4` subgroup up to inversion.
  refine ⟨?_⟩
  rintro ⟨q, c⟩ hn ⟨a, b⟩
  have hsnd : (1, c) ∈ H := by
    have hpow : ((q, c) : G0) ^ 4 = (1, c) := by
      simpa using quaternion_cyclic_pow_four (n := (q, c))
    exact hpow ▸ H.pow_mem hn 4
  have hfst : (q, 1) ∈ H := by
    have hmul : (q, c) * (1, c)⁻¹ = (q, 1) := by
      ext <;> simp
    exact hmul ▸ H.mul_mem hn (H.inv_mem hsnd)
  have hconj_fst : (a * q * a⁻¹, 1) ∈ H := by
    -- In `Q8`, conjugation fixes each cyclic order-`4` subgroup setwise, so the conjugate of
    -- `(q, 1)` is either itself or its inverse.
    cases q with
    | a i =>
        cases a with
        | a j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
        | xa j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
    | xa i =>
        cases a with
        | a j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
        | xa j =>
            fin_cases i <;> fin_cases j <;>
              first | simpa using hfst | simpa using H.inv_mem hfst
  have hmul : (a * q * a⁻¹, 1) * (1, c) = (a, b) * (q, c) * (a, b)⁻¹ := by
    ext <;> simp [mul_assoc]
  exact hmul ▸ H.mul_mem hconj_fst hsnd


-- Proof sketch: the simple algebra attached to this rational irreducible representation is the
-- range of the canonical action homomorphism `ℚ[Q8 × C3] →ₐ[ℚ] Endℚ(ℍ[ℚ])`; compute its center as
-- the cubic-root-of-unity field and its degree over that center as `2`.
/-- Helper for Exercise 13-13.1-14: the cubic coefficient field is exactly the cyclotomic field
generated by a primitive cube root of unity. -/
theorem quaternion_cubic_subfield_algEquiv_cyclotomicField3_exists :
    Nonempty (↥quaternion_cubic_subfield ≃ₐ[ℚ] CyclotomicField 3 ℚ) := by
  let ω : quaternion_cubic_subfield :=
    ⟨quaternionCubeRootOfUnity, quaternion_cube_root_mem_cubic_subfield⟩
  have hω3 : quaternionCubeRootOfUnity ^ 3 = (1 : ℍ[ℚ]) := by
    -- Compute the third power through the explicit square `ω²`.
    rw [pow_succ, pow_two, ← quaternion_cube_root_squared_eq]
    ext <;> norm_num [quaternionCubeRootOfUnity, quaternion_cube_root_squared]
  have hω2ne : ω ^ 2 ≠ (1 : quaternion_cubic_subfield) := by
    -- The square still has nonzero `i`-coordinate, so it cannot be `1`.
    intro h
    have h' : quaternionCubeRootOfUnity * quaternionCubeRootOfUnity = (1 : ℍ[ℚ]) := by
      simpa [pow_two, ω] using congrArg Subtype.val h
    rw [← quaternion_cube_root_squared_eq] at h'
    have hi := congrArg QuaternionAlgebra.imI h'
    norm_num [ω, quaternionCubeRootOfUnity, quaternion_cube_root_squared] at hi
  have hω1ne : ω ≠ (1 : quaternion_cubic_subfield) := by
    -- The generator itself has nonzero `i`-coordinate, so it is not the unit element.
    intro h
    have h' := congrArg Subtype.val h
    have hi := congrArg QuaternionAlgebra.imI h'
    norm_num [ω, quaternionCubeRootOfUnity] at hi
  have hω : IsPrimitiveRoot ω 3 := by
    -- The explicit quaternion `ω` has order exactly `3`, so it gives the primitive generator
    -- required by the cyclotomic-field characterization.
    rw [IsPrimitiveRoot.iff (by decide : 0 < 3)]
    constructor
    · exact Subtype.ext hω3
    · intro l hl hk hpow
      interval_cases l
      · exact hω1ne (by simpa using hpow)
      · exact hω2ne (by simpa using hpow)
  have htop : IntermediateField.adjoin ℚ {ω} = ⊤ := by
    -- Every cubic-subfield element is an affine-linear combination of `1` and `ω`, so the simple
    -- adjoin already contains the whole field.
    rw [eq_top_iff]
    intro x _
    have hcoords : (x : ℍ[ℚ]).imI = (x : ℍ[ℚ]).imJ ∧ (x : ℍ[ℚ]).imJ = (x : ℍ[ℚ]).imK :=
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (x : ℍ[ℚ]))).1
        x.property
    have hxpair :
        (x : ℍ[ℚ]) =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI) :=
      quaternion_eq_cubic_pair_of_equal_im_coordinates (q := (x : ℍ[ℚ])) hcoords.1 hcoords.2
    let q : quaternion_cubic_subfield :=
      (((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI : ℚ) • (1 : quaternion_cubic_subfield) +
        (2 * (x : ℍ[ℚ]).imI : ℚ) • ω)
    have hqval :
        (q : ℍ[ℚ]) =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI) := by
      change
        ((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI : ℚ) • (1 : ℍ[ℚ]) +
            (2 * (x : ℍ[ℚ]).imI : ℚ) • quaternionCubeRootOfUnity =
          quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI)
      symm
      exact quaternion_cubic_pair_eq_smul_one_add_smul_cube_root
        ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI)
    have hxexpr : x = q := by
      apply Subtype.ext
      exact hxpair.trans hqval.symm
    rw [hxexpr]
    refine IntermediateField.add_mem _ ?_ ?_
    · simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ {ω})
        ((x : ℍ[ℚ]).re + (x : ℍ[ℚ]).imI)
    · exact IntermediateField.smul_mem _
        (IntermediateField.mem_adjoin_simple_self ℚ ω)
  have hcycloTop :
      IsCyclotomicExtension {3} ℚ
        ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      3 ℚ ↥quaternion_cubic_subfield
      (⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) hω).2 htop.symm
  letI :
      IsCyclotomicExtension {3} ℚ
        ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) :=
    hcycloTop
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  refine
    ⟨(IntermediateField.topEquiv :
        (⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) ≃ₐ[ℚ]
          ↥quaternion_cubic_subfield).symm.trans ?_⟩
  exact
    IsCyclotomicExtension.algEquiv
      {3} ℚ ↥(⊤ : IntermediateField ℚ ↥quaternion_cubic_subfield) (CyclotomicField 3 ℚ)

/-- Helper for Exercise 13-13.1-14: a chosen algebra equivalence from the cubic coefficient field
to the cubic cyclotomic field. -/
noncomputable def quaternion_cubic_subfield_algEquiv_cyclotomicField3 :
    ↥quaternion_cubic_subfield ≃ₐ[ℚ] CyclotomicField 3 ℚ :=
  Classical.choice quaternion_cubic_subfield_algEquiv_cyclotomicField3_exists

/-- Exercise 13-13.1-14: the simple `ℚ`-algebra attached to `ρ`, realized as the range of its
canonical group-algebra action on `ℍ[ℚ]`, is isomorphic to `M₂(CyclotomicField 3 ℚ)`. -/
theorem quaternionCyclicWitnessRepresentation_imageSubalgebra_equiv_matrix_over_cyclotomicField3 :
    Nonempty
      ((ρ).asAlgebraHom.range ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) (CyclotomicField 3 ℚ)) := by
  -- Route correction: use LinearRepresentations_Serre_1977's exact chain `A ≃ End_K(H_Q) ≃ M₂(K)`, with the middle arrow
  -- cached above so the final composition is just coefficient transport to `CyclotomicField 3`.
  let e1 :
      quaternion_cyclic_imageSubalgebra ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield :=
    quaternion_cyclic_imageSubalgebra_algEquiv_matrix_over_cubic_subfield
  let e2 :
      Matrix (Fin 2) (Fin 2) ↥quaternion_cubic_subfield ≃ₐ[ℚ]
        Matrix (Fin 2) (Fin 2) (CyclotomicField 3 ℚ) :=
    AlgEquiv.mapMatrix quaternion_cubic_subfield_algEquiv_cyclotomicField3
  exact ⟨e1.trans e2⟩

-- Proof sketch: the Artin-Wedderburn component `M₂(K)` has matrix size `2`, with
-- `K = CyclotomicField 3 ℚ`. Equivalently, the raw regular intertwining multiplicity divided by
-- `dimℚ End_G(ρ)` is `2`.
/-- Exercise 13-13.1-14: the Artin-Wedderburn matrix-size parameter attached to `ρ` is `2`. -/
theorem quaternionCyclicWitnessRepresentation_matrixSize_two :
    Module.finrank ℚ
        ((leftRegular ℚ G0).IntertwiningMap (ρ)) /
      Module.finrank ℚ
        ((ρ).IntertwiningMap (ρ)) =
      2 := by
  -- Route correction: compute the numerator and denominator separately. The numerator is the
  -- regular multiplicity `dimℚ ℍ[ℚ] = 4`, and the denominator is the explicit cubic-plane
  -- self-intertwiner dimension `2`.
  have hnum :
      Module.finrank ℚ ((leftRegular ℚ G0).IntertwiningMap ρ) = 4 := by
    calc
      Module.finrank ℚ ((leftRegular ℚ G0).IntertwiningMap ρ)
          = Module.finrank ℚ ℍ[ℚ] := by
              simpa using (Representation.leftRegularMapEquiv ρ).finrank_eq
      _ = 4 := rational_quaternion_finrank_eq_four
  have hden :
      Module.finrank ℚ ((ρ).IntertwiningMap (ρ)) = 2 :=
    quaternion_cyclic_self_intertwining_finrank_eq_two
  rw [hnum, hden]

-- Proof sketch: the explicit witness character satisfies LinearRepresentations_Serre_1977's four central-value test, and the
-- obstruction theorem above excludes every element of the subgroup-permutation span.
/-- Exercise 13-13.1-14: the irreducible rational character of
`quaternionCyclicWitnessRepresentation` is not an integral linear combination of the subgroup
permutation characters `ℓ_H^G`. -/
theorem
    quaternionCyclicWitnessRepresentation_character_not_mem_subgroupPermutationCharacterSpanOverQ
    :
    χ_ ρ ∉ subgroupPermutationCharacterSpanOverQ G0 := by
  -- Route correction: the broken upstream import chain is replaced here by a local four-point
  -- obstruction theorem tailored to the central values of LinearRepresentations_Serre_1977's quaternionic witness.
  refine quaternion_cyclic_obstruction_of_central_values ?_ ?_ ?_ ?_
  · -- The character value at the identity is the dimension `4`.
    change LinearMap.trace ℚ ℍ[ℚ] (ρ ((1 : Q8), (1 : C3))) = 4
    rw [quaternion_witness_apply_identity]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (1 : ℍ[ℚ])) = 4
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (1 : ℍ[ℚ])
    norm_num at h ⊢
    exact h
  · -- The central involution acts with trace `-4`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_two) = -4
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_two]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (-1 : ℍ[ℚ])) = -4
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (-1 : ℍ[ℚ])
    norm_num at h ⊢
    exact h
  · -- The central order-`3` element acts with trace `-2`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_three) = -2
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_three]
    exact trace_mulLeft_quaternion_cube_root_of_unity_eq_neg_two
  · -- The central order-`6` element acts with trace `2`.
    change
      LinearMap.trace ℚ ℍ[ℚ]
        (quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_six) = 2
    rw [quaternionCyclicWitnessRepresentation_apply_central_order_six]
    change
      LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
        (LinearMap.mulLeft ℚ (-quaternionCubeRootOfUnity)) = 2
    have h := rational_quaternion_left_mul_trace_eq_four_mul_re (-quaternionCubeRootOfUnity)
    norm_num [quaternionCubeRootOfUnity] at h ⊢
    exact h

end

end Representation
