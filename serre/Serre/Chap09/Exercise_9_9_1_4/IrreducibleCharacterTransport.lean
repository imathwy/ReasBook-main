import Mathlib
import Serre.Chap02.Remark_2_2_1_2
import Serre.Chap02.Remark_2_2_4_4
import Serre.Chap06.Exercise_6_6_3_3
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_3_1
import Serre.GroupTheory.ConjClassesPower
import Serre.Chap06.Exercise_6_6_5_6
import Serre.Chap09.Exercise_9_9_1_3
import Serre.Chap11.Theorem_11_11_2_1
import Serre.Chap12.Proposition_12_12_1_1
import Serre.RepresentationTheory.SymmetricExterior

open scoped BigOperators MonoidAlgebra Representation
open Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: the degree-`1` Adams operator is the identity on class
functions. -/
private lemma adamsOperator_one
    {A : Type*} (f : G → A) :
    Ψ^(1 : ℕ+)(f) = f := by
  -- Unfold the Adams operator and simplify the first power map.
  ext g
  simp [Representation.adamsOperator]

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: the `0`th exterior-power character is the trivial character. -/
private lemma nthExteriorPower_zero_character
    (V : FDRep ℂ G) :
    (Representation.nthExteriorPower V.ρ 0).character = (1 : G → ℂ) := by
  let e : (⋀[ℂ]^0 ↑V.V) ≃ₗ[ℂ] ℂ := exteriorPower.zeroEquiv ℂ ↑V.V
  ext g
  -- Conjugate the `0`th exterior-power action through `zeroEquiv`, where it becomes the identity.
  change LinearMap.trace ℂ (⋀[ℂ]^0 ↑V.V) (exteriorPower.map 0 (V.ρ g)) = 1
  rw [← LinearMap.trace_conj' (exteriorPower.map 0 (V.ρ g)) e]
  have hconj : e.conj (exteriorPower.map 0 (V.ρ g)) = (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
    -- Naturality of `zeroEquiv` identifies the transported action with the scalar identity.
    apply LinearMap.ext
    intro y
    have h := congrArg (fun f : ⋀[ℂ]^0 ↑V.V →ₗ[ℂ] ℂ => f (e.symm y))
      (exteriorPower.zeroEquiv_naturality (R := ℂ) (M := ↑V.V) (N := ↑V.V) (V.ρ g))
    simpa [LinearEquiv.conj_apply, e] using h
  rw [hconj, LinearMap.trace_id]
  simp

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: split the Newton recurrence for exterior powers into its lower
Adams terms and the top `Ψ^n` summand. -/
private lemma nthExteriorPowerCharacter_recurrence_split_last
    (n : ℕ+) (V : FDRep ℂ G) :
    (n : ℂ) • (Representation.nthExteriorPower V.ρ n).character =
      (∑ x ∈ Finset.range n.natPred,
        (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(V.character)) *
          (Representation.nthExteriorPower V.ρ ((n : ℕ) - (x + 1))).character) +
        (((-1 : ℂ) ^ n.natPred) • Ψ^n(V.character)) *
          (Representation.nthExteriorPower V.ρ ((n : ℕ) - (n.natPred + 1))).character := by
  -- Reindex the positive-index recurrence by predecessors and split off the final summand.
  have hrec := Representation.nthExteriorPowerCharacter_recurrence (k := ℂ) V.ρ n
  rw [show (Finset.Icc 1 n) = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ by
    simpa using Representation.pnat_Icc_one_eq_map_range n] at hrec
  rw [Finset.sum_map] at hrec
  rw [show (Finset.range (n : ℕ)) = Finset.range (n.natPred + 1) by
    simp [PNat.natPred_add_one]] at hrec
  rw [Finset.sum_range_succ] at hrec
  simpa [PNat.succPNat_natPred, PNat.natPred_add_one, add_comm, add_left_comm, add_assoc] using
    hrec

omit [Group G] [Finite G] in
/-- Helper for Exercise 9-9.1-4: a complex scalar coming from an integer is the same as the
corresponding integer `zsmul` on class functions. -/
private lemma intCast_smul_eq_zsmul (m : ℤ) (f : G → ℂ) :
    ((m : ℂ) • f) = (m • f : G → ℂ) := by
  -- Check the two scalar actions pointwise on each group element.
  ext g
  simp [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: the Adams transform of a finite-dimensional character should land
back in Serre's character ring. -/
lemma psiPower_mem_characterRing (n : ℕ+) (V : FDRep ℂ G) :
    Ψ^n((V.character : G → ℂ)) ∈ R(G) := by
  -- Route correction: isolate the top Adams summand once in a split-last recurrence, then run
  -- strong induction on the predecessor index exactly as in the source Newton recursion.
  have hP : ∀ m : ℕ, ∀ W : FDRep ℂ G, Ψ^(Nat.succPNat m)((W.character : G → ℂ)) ∈ R(G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro W
        cases m with
        | zero =>
            -- The first Adams operator is the identity, so this is the ordinary character case.
            change Ψ^(1 : ℕ+)((W.character : G → ℂ)) ∈ R(G)
            simpa [adamsOperator_one] using
              (Representation.rep_character_mem_characterRing (G := G) (Rep.of W.ρ))
        | succ m =>
            let n : ℕ+ := Nat.succPNat (m + 1)
            have hsplit0 := nthExteriorPowerCharacter_recurrence_split_last (n := n) W
            have hsub0 : (n : ℕ) - (n.natPred + 1) = 0 := by
              simp [n]
            rw [hsub0, nthExteriorPower_zero_character] at hsplit0
            have hsplit :
                (n : ℂ) • (Representation.nthExteriorPower W.ρ n).character =
                  (((-1 : ℂ) ^ n.natPred) • Ψ^n(W.character)) +
                    ∑ x ∈ Finset.range n.natPred,
                      (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) *
                        (Representation.nthExteriorPower W.ρ ((n : ℕ) - (x + 1))).character := by
              -- After the final exterior-power factor becomes `1`, the top term is the desired
              -- signed Adams summand.
              simpa [add_comm, add_left_comm, add_assoc] using hsplit0
            have hexterior_mem : (Representation.nthExteriorPower W.ρ n).character ∈ R(G) := by
              -- Honest exterior-power characters already lie in the character ring.
              simpa [n] using
                (Representation.rep_character_mem_characterRing (G := G)
                  (Rep.of (Representation.nthExteriorPower W.ρ n)))
            have hlhs_mem :
                (n : ℂ) • (Representation.nthExteriorPower W.ρ n).character ∈ R(G) := by
              -- Replace the complex scalar `n` by the corresponding integer `zsmul`.
              rw [show ((n : ℂ) • (Representation.nthExteriorPower W.ρ n).character) =
                  (((n : ℤ) • (Representation.nthExteriorPower W.ρ n).character) : G → ℂ) by
                simpa [n] using intCast_smul_eq_zsmul (G := G) (n : ℤ)
                  ((Representation.nthExteriorPower W.ρ n).character)]
              exact (R(G)).zsmul_mem hexterior_mem (n : ℤ)
            have hlower_mem :
                ∑ x ∈ Finset.range n.natPred,
                  (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) *
                    (Representation.nthExteriorPower W.ρ ((n : ℕ) - (x + 1))).character ∈
                      R(G) := by
              -- Every lower summand is a product of a previously known Adams term with an
              -- exterior-power character.
              refine Submodule.sum_mem (R(G)).toSubmodule ?_
              intro x hx
              have hx' : x ≤ m := by
                simpa [n] using hx
              have hpsi_mem : Ψ^(Nat.succPNat x)((W.character : G → ℂ)) ∈ R(G) := by
                exact ih x (Nat.lt_succ_of_le hx') W
              have hsigned_mem :
                  (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) ∈ R(G) := by
                -- Normalize the sign coefficient to the integral scalar `(-1)^x`.
                rw [show (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) =
                    ((((-1 : ℤ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) : G → ℂ) by
                  ext g
                  simp [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_pow]]
                exact (R(G)).zsmul_mem hpsi_mem (((-1 : ℤ) ^ x))
              have hexterior_tail_mem :
                  (Representation.nthExteriorPower W.ρ ((n : ℕ) - (x + 1))).character ∈ R(G) := by
                simpa using
                  (Representation.rep_character_mem_characterRing (G := G)
                    (Rep.of (Representation.nthExteriorPower W.ρ ((n : ℕ) - (x + 1)))))
              exact (R(G)).mul_mem hsigned_mem hexterior_tail_mem
            have hsigned_mem : (((-1 : ℂ) ^ n.natPred) • Ψ^n(W.character)) ∈ R(G) := by
              have hsigned_eq :
                  (((-1 : ℂ) ^ n.natPred) • Ψ^n(W.character)) =
                    ((n : ℂ) • (Representation.nthExteriorPower W.ρ n).character) -
                      ∑ x ∈ Finset.range n.natPred,
                        (((-1 : ℂ) ^ x) • Ψ^(Nat.succPNat x)(W.character)) *
                          (Representation.nthExteriorPower W.ρ ((n : ℕ) - (x + 1))).character := by
                -- Rearranging the split recurrence isolates the top Adams summand.
                refine (eq_sub_iff_add_eq').2 ?_
                simpa [add_comm, add_left_comm, add_assoc] using hsplit.symm
              rw [hsigned_eq]
              exact (R(G)).sub_mem hlhs_mem hlower_mem
            -- The sign on the isolated term is always `±1`, so it does not change membership in
            -- the integral character ring.
            rw [show (((-1 : ℂ) ^ n.natPred) • Ψ^n(W.character)) =
                ((((-1 : ℤ) ^ n.natPred) • Ψ^n(W.character)) : G → ℂ) by
              ext g
              simp [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_pow]] at hsigned_mem
            rcases neg_one_pow_eq_or ℤ n.natPred with hsign | hsign
            · simpa [hsign] using hsigned_mem
            · have hneg_mem : -(Ψ^n(W.character)) ∈ R(G) := by
                simpa [hsign] using hsigned_mem
              simpa using (R(G)).neg_mem hneg_mem
  simpa [PNat.succPNat_natPred] using hP n.natPred V

/-- Helper for Exercise 9-9.1-4: reindexing the normalized pairing along the coprime power
permutation preserves the normalized pairing of class functions. -/
lemma psiPower_pairing_eq (n : ℕ+) (hn : (Nat.card G).Coprime n) (χ ψ : G → ℂ) :
    ⟪Ψ^n(χ), Ψ^n(ψ)⟫ = ⟪χ, ψ⟫ := by
  -- Reindex the defining average by the bijection `g ↦ g ^ n`.
  rw [Representation.groupFunctionPairingOverField, Representation.groupFunctionPairingOverField]
  congr 1
  simpa [adamsOperator, powCoprime_inv] using
    (Equiv.sum_comp (powCoprime hn) (fun g : G ↦ χ g⁻¹ * ψ g))

/-- Helper for Exercise 9-9.1-4: reindexing the normalized pairing along the coprime power
permutation preserves the self-pairing of a class function. -/
lemma psiPower_self_pairing_eq (n : ℕ+) (hn : (Nat.card G).Coprime n) (χ : G → ℂ) :
    ⟪Ψ^n(χ), Ψ^n(χ)⟫ = ⟪χ, χ⟫ := by
  -- The self-pairing case is the diagonal specialization of the general reindexing lemma.
  simpa using psiPower_pairing_eq n hn χ χ

/-- Helper for Exercise 9-9.1-4: an algebra automorphism of a finite product of copies of `ℂ`
permutes the standard primitive idempotents `Pi.basisFun`. -/
private lemma product_algEquiv_permutes_basisFun {ι : Type*} [Finite ι]
    (e : (ι → ℂ) ≃ₐ[ℂ] (ι → ℂ)) :
    ∃ σ : ι ≃ ι, ∀ i, e.symm (Pi.basisFun ℂ ι i) = Pi.basisFun ℂ ι (σ i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose τ hτ using fun i : ι =>
    AlgHom.eq_piEvalAlgHom
      ((Pi.evalAlgHom ℂ (fun _ : ι => ℂ) i).comp e.symm.toAlgHom)
  have hτ_apply (i : ι) (f : ι → ℂ) : e.symm f i = f (τ i) := by
    -- Evaluate the classified algebra homomorphism on the chosen function `f`.
    exact congrArg (fun φ : (ι → ℂ) →ₐ[ℂ] ℂ => φ f) (hτ i)
  have hτ_surj : Function.Surjective τ := by
    intro j
    by_contra hnot
    have hzero : e.symm (Pi.basisFun ℂ ι j) = 0 := by
      -- If `j` were outside the image of `τ`, every coordinate of the transported basis vector
      -- would vanish.
      ext i
      have hij : τ i ≠ j := by
        intro hij
        exact hnot ⟨i, hij⟩
      simp [hτ_apply, Pi.basisFun_apply, hij]
    have hbasis_nonzero : Pi.basisFun ℂ ι j ≠ 0 := by
      -- The `j`-th standard basis vector is detected by its `j`-th coordinate.
      intro hzero'
      have := congrArg (fun f : ι → ℂ => f j) hzero'
      simp at this
    have hfun_nonzero : e.symm (Pi.basisFun ℂ ι j) ≠ 0 := by
      -- An algebra equivalence cannot send a nonzero basis vector to zero.
      intro hzero'
      apply hbasis_nonzero
      have hzero0 : e.symm (Pi.basisFun ℂ ι j) = e.symm 0 := by
        rw [hzero', map_zero]
      exact e.symm.injective hzero0
    exact hfun_nonzero hzero
  have hτ_bij : Function.Bijective τ :=
    (Finite.surjective_iff_bijective (f := τ)).1 hτ_surj
  let τe : ι ≃ ι := Equiv.ofBijective τ hτ_bij
  refine ⟨τe.symm, ?_⟩
  intro i
  ext j
  -- Compare the `j`-th coordinate using the evaluation description of `e.symm`.
  rw [hτ_apply]
  by_cases h : τe.symm i = j
  · subst h
    have hτj : τ (τe.symm i) = i := by
      change τe (τe.symm i) = i
      exact τe.apply_symm_apply i
    simp [Pi.basisFun_apply, hτj]
  · have h' : i ≠ τ j := by
      intro hij
      apply h
      exact τe.symm_apply_eq.mpr hij
    simp [Pi.basisFun_apply, h, h']

/-- Helper for Exercise 9-9.1-4: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : ℂ) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty linear combination pairs to zero.
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Rewrite the integer multiple as complex scalar multiplication before applying linearity.
      have hzsmul : (a i • χ i : G → ℂ) = (((a i : ℤ) : ℂ) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 9-9.1-4: pairing an element of `R(G)` with an irreducible basis character
recovers the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Finite ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(G)) (i : ι) :
    ⟪(x : G → ℂ), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : G → ℂ) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  have horth : Pairwise fun j k ↦ ⟪(π j).character, (π k).character⟫ = (0 : ℂ) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ j, ⟪(π j).character, (π j).character⟫ = (1 : ℂ) := by
    intro j
    letI : Simple (π j) := hπ_complete.isSimple j
    have hself : Nonempty (π j ≅ π j) := ⟨Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π j) (π j))
  calc
    ⟪(x : G → ℂ), (π i).character⟫ = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
      -- Replace `x` by its irreducible-basis expansion.
      rw [hx]
    _ = ∑ j, ((c j : ℤ) : ℂ) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left
              (s := Finset.univ) (a := c) (χ := fun j ↦ (π j).character)
              (ψ := (π i).character)
    _ = ((c i : ℤ) : ℂ) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            rw [horth hji, mul_zero]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    _ = (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
          simp [b, c, hdiag]

/-- Helper for Exercise 9-9.1-4: self-pairing `1` forces the irreducible-basis coefficients of an
element of `R(G)` to have square sum `1`. -/
lemma repr_square_sum_eq_one_of_self_pairing_eq_one
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(G))
    (hpair : ⟪(x : G → ℂ), x⟫ = (1 : ℂ)) :
    ∑ i, ((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i)^2
      = 1 := by
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : G → ℂ) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  have hcomplex :
      (((∑ i, (c i)^2 : ℤ) : ℂ)) = ⟪(x : G → ℂ), x⟫ := by
    calc
      (((∑ i, (c i)^2 : ℤ) : ℂ))
          = ∑ i, ((c i : ℤ) : ℂ) * (((c i : ℤ) : ℂ)) := by
              -- Convert the integer square sum into the ambient complex sum.
              simp [pow_two]
      _ = ∑ i, ((c i : ℤ) : ℂ) * ⟪(π i).character, (x : G → ℂ)⟫ := by
            -- Each coefficient is recovered by pairing with the corresponding basis character.
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [groupFunctionPairing_comm, basis_coefficient_pairing_eq (π := π) hπ_pairwise
              hπ_complete x i]
      _ = ⟪∑ i, c i • (π i).character, (x : G → ℂ)⟫ := by
            -- Reassemble the coefficient sum into a single pairing.
            symm
            simpa [c] using
              groupFunctionPairing_sum_zsmul_left
                (s := Finset.univ) (a := c) (χ := fun i ↦ (π i).character)
                (ψ := (x : G → ℂ))
      _ = ⟪(x : G → ℂ), x⟫ := by
            rw [hx]
  have hcomplex_one : (((∑ i, (c i)^2 : ℤ) : ℂ)) = (1 : ℂ) := by
    rw [hcomplex, hpair]
  exact_mod_cast hcomplex_one

/-- Helper for Exercise 9-9.1-4: an integral square sum equal to `1` has exactly one nonzero
coefficient, and that coefficient is `1` or `-1`. -/
lemma integer_coefficients_eq_singleton_of_sq_sum_eq_one
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (h : ∑ i, (c i) ^ 2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hnotallzero : ¬ ∀ i, c i = 0 := by
    intro hzero
    have hsum_zero : ∑ i, (c i)^2 = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_sq_le : (c i)^2 ≤ 1 := by
    calc
      (c i)^2 ≤ ∑ j, (c j)^2 := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ sq_nonneg (c j)) (Finset.mem_univ i) :
            (c i)^2 ≤ ∑ j, (c j)^2)
      _ = 1 := h
  have hi_sq_eq : (c i)^2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := by
    exact sq_eq_one_iff.mp hi_sq_eq
  refine ⟨i, hi_sign, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = ∑ k, (c k)^2 := by
        simp
      _ = 1 := h
  have herase_zero : Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) = 0 := by
    linarith
  have hj_sq_le :
      (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (c k)) hj_mem :
        (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2))
  have hj_sq_eq_zero : (c j)^2 = 0 := by
    have hj_sq_nonneg : 0 ≤ (c j)^2 := sq_nonneg (c j)
    linarith
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: a simple finite-dimensional complex representation has positive
degree. -/
theorem simple_fdRep_finrank_pos
    (V : FDRep ℂ G) [Simple V] :
    0 < Module.finrank ℂ V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero V hzero
  letI : Nontrivial V := hV_nontriv
  exact Module.finrank_pos

end

end Representation
