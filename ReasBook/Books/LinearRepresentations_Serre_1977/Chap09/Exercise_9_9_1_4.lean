import Mathlib
import Serre.Chap02.Remark_2_2_1_2
import Serre.Chap02.Remark_2_2_4_4
import Serre.Chap06.Exercise_6_6_3_3
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_3_1
import Serre.GroupTheory.ConjClassesPower
import Serre.Chap06.Exercise_6_6_5_6
import Serre.Chap09.Exercise_9_9_1_3
import Serre.Chap09.Exercise_9_9_1_4.Index
import Serre.Chap11.Theorem_11_11_2_1
import Serre.Chap12.Proposition_12_12_1_1
import Serre.RepresentationTheory.SymmetricExterior

-- Declarations for this item will be appended below by the statement pipeline.

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

-- Source/core/bridge triage:
-- * source-facing: the irreducibility statement for `Ψ^n(χ)` and the induced automorphism of
--   `Subalgebra.center k (k[G])`.
-- * core/canonical: the Chapter 11 owner `Representation.adamsOperator`, the coprime power
--   permutation `powCoprime hn`, and the chapter owner `centerCoeffEquivFun k` for the center of
--   the group algebra.
-- * bridge/view: comparison between the induced center automorphism and the ambient permutation on
--   `k[G]`.

-- Proof sketch: expand the Adams transform in the canonical irreducible-character basis of
-- `R(G)`, use the preserved self-pairing to show only one basis coefficient survives, and then use
-- the value at `1` to rule out the negative sign.
/-- Exercise 9-9.1-4 (1): if `n` is coprime to `|G|` and `χ` is an irreducible complex
character of `G`, then `Ψ^n(χ)` is again an irreducible complex character. -/
theorem exists_irreducible_fdRep_character_eq_psiPower
    (n : ℕ+) (hn : (Nat.card G).Coprime n) (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    ∃ W : FDRep ℂ G, CategoryTheory.Simple W ∧ W.character = Ψ^n(V.character) := by
  let χ : R(G) := ⟨Ψ^n((V.character : G → ℂ)), psiPower_mem_characterRing n V⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  obtain ⟨ι, _, π, _hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := ℂ) (G := G)
  let πfd : ι → FDRep ℂ G := fun i ↦ FDRep.of (π i).ρ
  have hπfd_pairwise : PairwiseNonisomorphic πfd := by
    intro i j hij hIso
    apply hπ_pairwise hij
    rcases hIso with ⟨e⟩
    refine ⟨?_⟩
    simpa [πfd] using (forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e
  have hpair : ⟪(χ : G → ℂ), χ⟫ = (1 : ℂ) := by
    -- Reindex the self-pairing along the coprime power permutation and then invoke the standard
    -- irreducible-character self-pairing criterion.
    change ⟪Ψ^n((V.character : G → ℂ)), Ψ^n((V.character : G → ℂ))⟫ = (1 : ℂ)
    rw [show
      ⟪Ψ^n((V.character : G → ℂ)), Ψ^n((V.character : G → ℂ))⟫ =
        ⟪(V.character : G → ℂ), V.character⟫ by
      simpa using psiPower_self_pairing_eq (G := G) n hn (V.character : G → ℂ)]
    letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
    exact (self_character_pairing_eq_one_iff_isIrreducible V.ρ).2 inferInstance
  have hχ_one_nonneg : 0 ≤ ((χ : G → ℂ) 1).re := by
    -- Evaluating at the identity commutes with the Adams operator because `1 ^ n = 1`.
    change 0 ≤ (Ψ^n((V.character : G → ℂ)) 1).re
    have hdegree_nonneg : 0 ≤ (Module.finrank ℂ V : ℝ) := by
      positivity
    have hV_one_nonneg : 0 ≤ (V.character 1).re := by
      simp
    simp [Representation.adamsOperator]
  let b := irreducible_characters_basis_of_complete_family ℂ πfd hπfd_pairwise hπ_complete
  let c := b.repr χ
  have hsq :
      ∑ i, (c i)^2 = 1 :=
    repr_square_sum_eq_one_of_self_pairing_eq_one
      (π := πfd) hπfd_pairwise hπ_complete χ hpair
  obtain ⟨i, hi_sign, hzero⟩ :=
    integer_coefficients_eq_singleton_of_sq_sum_eq_one c hsq
  have hχ_expansion : ∑ j, c j • (πfd j).character = (χ : G → ℂ) := by
    -- Rewrite the basis expansion of `χ` into the ambient function space.
    simpa [b, c, χ, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr χ)
  have hsum_single : ∑ j, c j • (πfd j).character = c i • (πfd i).character := by
    -- All basis coefficients except one vanish.
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      simp [hzero j hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hχ_single : (χ : G → ℂ) = c i • (πfd i).character := by
    calc
      (χ : G → ℂ) = ∑ j, c j • (πfd j).character := by
        simpa using hχ_expansion.symm
      _ = c i • (πfd i).character := hsum_single
  rcases hi_sign with hi_pos | hi_neg
  · -- The positive sign identifies `χ` itself with one irreducible character.
    refine ⟨πfd i, hπ_complete.isSimple i, ?_⟩
    calc
      (πfd i).character = (1 : ℤ) • (πfd i).character := by
        simp
      _ = (χ : G → ℂ) := by
        simpa [hi_pos] using hχ_single.symm
  · -- The negative sign would force the value at `1` to be strictly negative.
    letI : Simple (πfd i) := hπ_complete.isSimple i
    have hπ_pos : 0 < Module.finrank ℂ (πfd i) :=
      simple_fdRep_finrank_pos (V := πfd i)
    have hχ_neg : (χ : G → ℂ) = (-1 : ℤ) • (πfd i).character := by
      simpa [hi_neg] using hχ_single
    have hχ_one :
        ((χ : G → ℂ) 1).re = -(Module.finrank ℂ (πfd i) : ℝ) := by
      have hzsmul :
          (((-1 : ℤ) • (πfd i).character : G → ℂ)) = ((-1 : ℂ) • (πfd i).character) := by
        ext g
        simp [smul_eq_mul]
      calc
        ((χ : G → ℂ) 1).re = ((((-1 : ℤ) • (πfd i).character : G → ℂ) 1)).re := by
          rw [hχ_neg]
        _ = ((((-1 : ℂ) • (πfd i).character : G → ℂ) 1)).re := by
          rw [hzsmul]
        _ = -(Module.finrank ℂ (πfd i) : ℝ) := by
          simp [FDRep.char_one]
    have hπ_pos_real : 0 < (Module.finrank ℂ (πfd i) : ℝ) := by
      exact_mod_cast hπ_pos
    have hχ_one_neg : ((χ : G → ℂ) 1).re < 0 := by
      rw [hχ_one]
      linarith
    exact (not_lt_of_ge hχ_one_nonneg hχ_one_neg).elim

end

end Representation

namespace Representation

section

variable {k : Type*} [CommSemiring k]
variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the induced automorphism of `Subalgebra.center k (k[G])`.
-- * core/canonical: the chapter owner `centerCoeffEquivFun k :
--   Subalgebra.center k (k[G]) ≃ₗ[k] (ConjClasses G → k)` together with the induced permutation of
--   `ConjClasses G` coming from `ConjClasses.powCoprimeEquiv n hn`.
-- * bridge/view: comparison with the ambient permutation `Finsupp.domLCongr (powCoprime hn)` on
--   `k[G]`.

-- Primitive data: the project owner `ConjClasses.pow n`.
-- Derived API: when `n` is coprime to `|G|`, `ConjClasses.powCoprimeEquiv n hn` is the induced
-- permutation of conjugacy classes.

/-- Helper for Exercise 9-9.1-4: the center automorphism first transported to coefficient
functions on conjugacy classes, before restoring the algebra structure. -/
def centerPowerLinearEquiv (n : ℕ) (hn : (Nat.card G).Coprime n) :
    Subalgebra.center k (k[G]) ≃ₗ[k] Subalgebra.center k (k[G]) :=
  (((centerCoeffEquivFun k).trans
      (LinearEquiv.funCongrLeft k k (ConjClasses.powCoprimeEquiv n hn).symm)).trans
        (centerCoeffEquivFun k).symm)

/-- Helper for Exercise 9-9.1-4: after coercing back to the ambient group algebra, the transported
center map is exactly coefficient transport along the coprime power permutation of `G`. -/
lemma centerPowerLinearEquiv_apply
    (n : ℕ) (hn : (Nat.card G).Coprime n) (z : Subalgebra.center k (k[G])) :
    ((centerPowerLinearEquiv (k := k) n hn) z : k[G]) =
      (Finsupp.domLCongr (powCoprime hn) : k[G] ≃ₗ[k] k[G]) (z : k[G]) := by
  -- Compare both sides coefficientwise and identify the descended conjugacy-class permutation with
  -- the ambient group-level power permutation on representatives.
  ext g
  have hclass :
      (ConjClasses.powCoprimeEquiv n hn).symm (ConjClasses.mk g) =
        ConjClasses.mk ((powCoprime hn).symm g) := by
    apply (ConjClasses.powCoprimeEquiv n hn).symm_apply_eq.mpr
    simpa [ConjClasses.pow_mk] using
      (congrArg ConjClasses.mk ((powCoprime hn).apply_symm_apply g)).symm
  change (centerCoeffEquivFun k ((centerPowerLinearEquiv (k := k) n hn) z)) (ConjClasses.mk g) =
    ((Finsupp.domLCongr (powCoprime hn) : k[G] ≃ₗ[k] k[G]) (z : k[G])) g
  rw [show
      (centerCoeffEquivFun k ((centerPowerLinearEquiv (k := k) n hn) z)) (ConjClasses.mk g) =
        (centerCoeffEquivFun k z) ((ConjClasses.powCoprimeEquiv n hn).symm (ConjClasses.mk g)) by
      rfl]
  simp [Finsupp.domLCongr_apply, hclass]

/-- Helper for Exercise 9-9.1-4: on the conjugacy-class-sum basis of the center,
`centerPowerLinearEquiv` is exactly the permutation induced by `ConjClasses.powCoprimeEquiv`. -/
lemma centerPowerLinearEquiv_conjugacyClassSumInCenter
    (n : ℕ) (hn : (Nat.card G).Coprime n) (c : ConjClasses G) :
    centerPowerLinearEquiv (k := k) n hn (conjugacyClassSumInCenter k c) =
      conjugacyClassSumInCenter k ((ConjClasses.powCoprimeEquiv n hn) c) := by
  -- Compare the two central elements in conjugacy-class coordinates.
  apply (centerCoeffEquivFun k).injective
  ext c'
  simp [centerPowerLinearEquiv]
  by_cases hc' : c' = (ConjClasses.powCoprimeEquiv n hn) c
  · -- On the image class, both sides are the distinguished basis coefficient `1`.
    subst hc'
    simp
  · -- Away from that image class, both basis coefficients vanish.
    have hne : (ConjClasses.powCoprimeEquiv n hn).symm c' ≠ c := by
      intro hEq
      apply hc'
      simpa using congrArg (ConjClasses.powCoprimeEquiv n hn) hEq
    simp [centerCoeffEquivFun_conjugacyClassSumInCenter_of_ne, hc', hne]

/-- Helper for Exercise 9-9.1-4: the transported center map fixes the unit element. -/
lemma centerPowerLinearEquiv_map_one (n : ℕ) (hn : (Nat.card G).Coprime n) :
    centerPowerLinearEquiv (k := k) n hn 1 = 1 := by
  -- After coercing to `k[G]`, the map is `domLCongr` on coefficients, and that permutation fixes
  -- the unit basis vector at `1`.
  apply Subtype.ext
  rw [centerPowerLinearEquiv_apply (k := k) n hn 1]
  ext g
  change (((Finsupp.domLCongr (powCoprime hn) : MonoidAlgebra k G ≃ₗ[k] MonoidAlgebra k G)
      ((1 : Subalgebra.center k (k[G])) : MonoidAlgebra k G)) g) =
    (MonoidAlgebra.single (1 : G) (1 : k)) g
  by_cases hg : g = 1
  · subst hg
    simp [MonoidAlgebra.one_def, Finsupp.domLCongr_apply]
  · simp [MonoidAlgebra.one_def, Finsupp.domLCongr_apply, hg]

omit [Finite G] in
/-- Helper for Exercise 9-9.1-4: a simple finite-dimensional complex representation has positive
dimension. -/
private theorem simple_fdRep_finrank_pos_local
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
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

/-- Helper for Exercise 9-9.1-4: evaluating the transported central primitive idempotent attached
to `V` on an irreducible representation `U` is the same as evaluating the original central
primitive idempotent on any irreducible representation whose character is `Ψ^n(U.character)`. -/
lemma centralCharacter_centerPowerLinearEquiv_characterCentralElement
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (U V W : FDRep ℂ G)
    [CategoryTheory.Simple U] [CategoryTheory.Simple W]
    [Representation.IsIrreducible U.ρ] [Representation.IsIrreducible W.ρ]
    (hW : W.character = Ψ^n(U.character)) :
    ω[U.ρ] (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (Rep.of V.ρ))) =
      ω[W.ρ] (characterCentralElement (Rep.of V.ρ)) := by
  have hUpos : 0 < Module.finrank ℂ U := simple_fdRep_finrank_pos_local (V := U)
  have hUneq : (Module.finrank ℂ U : ℂ) ≠ 0 := by
    exact_mod_cast hUpos.ne'
  have hdim : Module.finrank ℂ W = Module.finrank ℂ U := by
    -- Compare the value at the identity to identify the degrees of `U` and `W`.
    have h1 := congrFun hW 1
    simpa [adamsOperator] using h1
  have hWneq : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (hdim.symm ▸ hUpos).ne'
  -- Route correction: compare the normalized trace sums directly after reindexing the group by
  -- the coprime power permutation `g ↦ g ^ n`.
  let zc : Subalgebra.center ℂ (ℂ[G]) := characterCentralElement (Rep.of V.ρ)
  let z : MonoidAlgebra ℂ G :=
    (zc : MonoidAlgebra ℂ G)
  rw [
    centralCharacter_apply_eq_sum_character
      (ρ := U.ρ)
      (u := centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn zc)
      hUneq
  ]
  rw [centralCharacter_apply_eq_sum_character (ρ := W.ρ) (u := zc) hWneq]
  rw [centerPowerLinearEquiv_apply (k := ℂ) (n : ℕ) hn zc]
  change (Module.finrank ℂ U : ℂ)⁻¹ *
      ∑ s : G, ((Finsupp.domCongr (powCoprime hn) z) s) * U.character s =
    (Module.finrank ℂ W : ℂ)⁻¹ * ∑ s : G, z s * W.character s
  have hsum :
      ∑ s : G, ((Finsupp.domCongr (powCoprime hn) z) s) * U.character s =
        ∑ s : G, z s * W.character s := by
    -- Reindex the left-hand sum by the bijection `powCoprime hn`.
    calc
      ∑ s : G, ((Finsupp.domCongr (powCoprime hn) z) s) * U.character s
          = ∑ s : G, z ((powCoprime hn).symm s) * U.character s := by
              simp [z, Finsupp.domCongr]
      _ = ∑ s : G, z ((powCoprime hn).symm s) *
            U.character (((powCoprime hn).symm s) ^ (n : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro s hs
              congr 1
              simpa using congrArg U.character ((powCoprime hn).apply_symm_apply s).symm
      _ = ∑ s : G, z ((powCoprime hn).symm s) *
            W.character ((powCoprime hn).symm s) := by
              refine Finset.sum_congr rfl ?_
              intro s hs
              simp [hW, adamsOperator]
      _ = ∑ s : G, z s * W.character s := by
              simpa [z] using
                (Equiv.sum_comp (powCoprime hn).symm (fun s : G ↦ z s * W.character s))
  rw [hsum]
  simp [hdim]

/-- Helper for Exercise 9-9.1-4: precomposing functions with a permutation sends the `i`-th
standard basis vector to the basis vector at the inverse image of `i`. -/
private lemma basisFun_funCongrLeft {ι : Type*} [Finite ι]
    (σ : ι ≃ ι) (i : ι) :
    LinearEquiv.funCongrLeft ℂ ℂ σ (Pi.basisFun ℂ ι i) =
      Pi.basisFun ℂ ι (σ.symm i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  ext j
  by_cases h : σ j = i
  · have hj : j = σ.symm i := (σ.apply_eq_iff_eq_symm_apply).mp h
    subst hj
    simpa [LinearEquiv.funCongrLeft_apply, Pi.basisFun_apply] using
      congrArg (fun t : ι => Pi.single i (1 : ℂ) t) h
  · have hj : j ≠ σ.symm i := by
      intro hjEq
      apply h
      rw [hjEq]
      exact σ.apply_symm_apply i
    simp [LinearEquiv.funCongrLeft_apply, Pi.basisFun_apply, h, hj]

/-- Helper for Exercise 9-9.1-4: Adams transport permutes any chosen complete pairwise
nonisomorphic family of irreducible complex representations. -/
private lemma adams_irreducible_family_perm
    {ι : Type*} [Finite ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (n : ℕ+) (hn : (Nat.card G).Coprime n) :
    ∃ σ : ι ≃ ι, ∀ i,
      Ψ^n((FDRep.of (π i).ρ).character) = (FDRep.of (π (σ i)).ρ).character := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let πfd : ι → FDRep ℂ G := fun i ↦ FDRep.of (π i).ρ
  have hπfd_pairwise : PairwiseNonisomorphic πfd := by
    -- Forgetting an isomorphism of `FDRep` objects gives one of the underlying `Rep` objects.
    intro i j hij hIso
    apply hπ_pairwise hij
    rcases hIso with ⟨e⟩
    refine ⟨?_⟩
    simpa [πfd] using (forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e
  have hexists : ∀ i : ι, ∃ j, Ψ^n((πfd i).character) = (πfd j).character := by
    intro i
    letI : Simple (πfd i) := hπ_complete.isSimple i
    -- Part (a) produces an irreducible target for the Adams transform of the `i`-th character.
    rcases exists_irreducible_fdRep_character_eq_psiPower (G := G) n hn (πfd i) with
      ⟨W, hWsimple, hWchar⟩
    have hWsimple' : Simple W := hWsimple
    letI : Simple W := hWsimple'
    obtain ⟨j, hj⟩ := hπ_complete.exists_iso W hWsimple'
    rcases hj with ⟨e⟩
    refine ⟨j, ?_⟩
    calc
      Ψ^n((πfd i).character) = W.character := hWchar.symm
      _ = (πfd j).character := by
          simpa using FDRep.char_iso e
  choose τ hτ using hexists
  have hτ_inj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    letI : Simple (πfd i) := hπ_complete.isSimple i
    letI : Simple (πfd j) := hπ_complete.isSimple j
    letI : Simple (πfd (τ i)) := hπ_complete.isSimple (τ i)
    have hpair : ⟪(πfd i).character, (πfd j).character⟫ = (1 : ℂ) := by
      -- The preserved pairing identifies the source characters once their Adams images coincide.
      calc
        ⟪(πfd i).character, (πfd j).character⟫
            = ⟪Ψ^n((πfd i).character), Ψ^n((πfd j).character)⟫ := by
                symm
                simpa using
                  psiPower_pairing_eq (G := G) n hn (πfd i).character (πfd j).character
        _ = ⟪(πfd (τ i)).character, (πfd (τ i)).character⟫ := by
              simpa [hij] using congrArg₂ (fun a b ↦ ⟪a, b⟫) (hτ i) (hτ j)
        _ = 1 := by
              have hself : Nonempty (πfd (τ i) ≅ πfd (τ i)) := ⟨Iso.refl _⟩
              simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
                hself] using (FDRep.char_orthonormal (πfd (τ i)) (πfd (τ i)))
    have hpair_zero : ⟪(πfd i).character, (πfd j).character⟫ = (0 : ℂ) := by
      have hnoiso : ¬ Nonempty (πfd i ≅ πfd j) := by
        intro hIso
        exact hπfd_pairwise hne hIso
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hnoiso] using
        (FDRep.char_orthonormal (πfd i) (πfd j))
    exact zero_ne_one (hpair_zero.symm.trans hpair)
  have hτ_bij : Function.Bijective τ :=
    (Finite.injective_iff_bijective (f := τ)).mp hτ_inj
  let σ : ι ≃ ι := Equiv.ofBijective τ hτ_bij
  refine ⟨σ, ?_⟩
  intro i
  simpa [σ] using hτ i

/-- Helper for Exercise 9-9.1-4: the forward central-character equivalence sends each primitive
central idempotent to the corresponding standard basis vector. -/
lemma centralCharacterFamilyAlgEquiv_apply_characterCentralElement
    {ι : Type*} [Finite ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (i : ι) :
    (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete) (characterCentralElement (π i)) =
      Pi.basisFun ℂ ι i := by
  letI : Fintype ι := Fintype.ofFinite ι
  -- Apply the equivalence to the known inverse-image description of `Pi.basisFun`.
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  have hsymm :=
    centralCharacterFamilyAlgEquiv_symm_basisFun (k := ℂ) (π := π) hπ_pairwise hπ_complete i
  calc
    e (characterCentralElement (π i)) = e (e.symm (Pi.basisFun ℂ ι i)) := by
      rw [hsymm]
    _ = Pi.basisFun ℂ ι i := e.apply_symm_apply _

/-- Helper for Exercise 9-9.1-4: under the central-character equivalence, Adams transport sends
each central primitive idempotent to the basis vector indexed by the induced Adams permutation. -/
private lemma centerPowerLinearEquiv_characterCentralElement_image
    {ι : Type*} [Finite ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (n : ℕ+) (hn : (Nat.card G).Coprime n) :
    ∃ σ : ι ≃ ι, ∀ i,
      (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete)
        (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) =
          Pi.basisFun ℂ ι (σ.symm i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  obtain ⟨σ, hσ⟩ := adams_irreducible_family_perm π hπ_pairwise hπ_complete n hn
  refine ⟨σ, ?_⟩
  intro i
  ext j
  let U : FDRep ℂ G := FDRep.of (π j).ρ
  let V : FDRep ℂ G := FDRep.of (π i).ρ
  let W : FDRep ℂ G := FDRep.of (π (σ j)).ρ
  letI : CategoryTheory.Simple U := hπ_complete.isSimple j
  letI : CategoryTheory.Simple W := hπ_complete.isSimple (σ j)
  letI : Representation.IsIrreducible U.ρ :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  letI : Representation.IsIrreducible V.ρ :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : Representation.IsIrreducible W.ρ :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete (σ j)
  have hcoord :
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) j =
        ω[W.ρ] (characterCentralElement (π i)) := by
    -- Route correction: first rewrite the transported primitive idempotent in product
    -- coordinates, then compare the resulting scalar with the Adams-permuted irreducible target.
    change ω[U.ρ] (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) =
      ω[W.ρ] (characterCentralElement (π i))
    simpa [U, V, W] using
      centralCharacter_centerPowerLinearEquiv_characterCentralElement
        (G := G) (n := n) (hn := hn) U V W (hσ j).symm
  have hiso_iff : Nonempty (Rep.of W.ρ ≅ Rep.of V.ρ) ↔ j = σ.symm i := by
    constructor
    · intro hWV
      have hσj_eq_i : σ j = i := by
        by_contra hne
        have hrepIso : Nonempty (π (σ j) ≅ π i) := by
          simpa [W, V] using hWV
        exact hπ_pairwise hne hrepIso
      exact (σ.apply_eq_iff_eq_symm_apply).mp hσj_eq_i
    · intro hj
      subst hj
      refine ⟨eqToIso ?_⟩
      change π (σ (σ.symm i)) = π i
      rw [σ.apply_symm_apply]
  have hdelta :
      ω[W.ρ] (characterCentralElement (π i)) = if j = σ.symm i then 1 else 0 := by
    by_cases hj : j = σ.symm i
    · have hnonempty : Nonempty (Rep.of W.ρ ≅ Rep.of V.ρ) := (hiso_iff).2 hj
      change ω[(Rep.of W.ρ).ρ] (characterCentralElement (Rep.of V.ρ)) =
        if j = σ.symm i then 1 else 0
      rw [centralCharacter_characterCentralElement_eq_ite_of_irreducible
        (X := Rep.of W.ρ) (Y := Rep.of V.ρ) inferInstance inferInstance,
        if_pos hnonempty, if_pos hj]
    · have hnone : ¬ Nonempty (Rep.of W.ρ ≅ Rep.of V.ρ) := by
        intro hnonempty
        exact hj ((hiso_iff).1 hnonempty)
      change ω[(Rep.of W.ρ).ρ] (characterCentralElement (Rep.of V.ρ)) =
        if j = σ.symm i then 1 else 0
      rw [centralCharacter_characterCentralElement_eq_ite_of_irreducible
        (X := Rep.of W.ρ) (Y := Rep.of V.ρ) inferInstance inferInstance,
        if_neg hnone, if_neg hj]
  calc
    e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) j =
        ω[W.ρ] (characterCentralElement (π i)) := hcoord
    _ = if j = σ.symm i then 1 else 0 := hdelta
    _ = Pi.basisFun ℂ ι (σ.symm i) j := by
        simp [Pi.basisFun_apply, Pi.single_apply]

/-- Helper for Exercise 9-9.1-4: over `ℂ`, the transported center map permutes the central
primitive idempotents according to the Adams transport of irreducible characters. -/
lemma centerPowerLinearEquiv_characterCentralElement
    {ι : Type*} [Finite ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (n : ℕ+) (hn : (Nat.card G).Coprime n) :
    ∃ σ : ι ≃ ι, ∀ i,
      centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i)) =
        characterCentralElement (π (σ.symm i)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  obtain ⟨σ, hσ⟩ :=
    centerPowerLinearEquiv_characterCentralElement_image π hπ_pairwise hπ_complete n hn
  refine ⟨σ, ?_⟩
  intro i
  apply e.injective
  -- Descend the image theorem in `ℂ^ι` back to the center through injectivity of `e`.
  calc
    e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) =
        Pi.basisFun ℂ ι (σ.symm i) := hσ i
    _ = e (characterCentralElement (π (σ.symm i))) := by
        symm
        exact centralCharacterFamilyAlgEquiv_apply_characterCentralElement
          π hπ_pairwise hπ_complete (σ.symm i)

/-- Helper for Exercise 9-9.1-4: after transporting the center through the central-character
algebra equivalence, the complex power map becomes coordinate permutation. -/
lemma centerPowerLinearEquiv_conjugated_eq_funCongrLeft
    {ι : Type*} [Finite ι] (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    [Invertible (Nat.card G : ℂ)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (σ : ι ≃ ι)
    (hσ : ∀ i,
      centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i)) =
        characterCentralElement (π (σ.symm i))) :
    ((((centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv.symm.trans
        (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn)).trans
      (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).toLinearEquiv)) =
      LinearEquiv.funCongrLeft ℂ ℂ σ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  apply LinearEquiv.toLinearMap_injective
  -- Compare the two linear maps on the standard basis of `ℂ^ι`.
  apply (Pi.basisFun ℂ ι).ext
  intro i
  have hsymm_basis :
      e.symm (Pi.basisFun ℂ ι i) = characterCentralElement (π i) := by
    simpa [e] using
      (centralCharacterFamilyAlgEquiv_symm_basisFun
        (k := ℂ) (π := π) hπ_pairwise hπ_complete i)
  calc
    ((((e.toLinearEquiv.symm.trans (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn)).trans
        e.toLinearEquiv)) (Pi.basisFun ℂ ι i))
        = e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (e.symm (Pi.basisFun ℂ ι i))) := by
            rfl
    _ = e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (characterCentralElement (π i))) := by
          rw [hsymm_basis]
    _ = e (characterCentralElement (π (σ.symm i))) := by
          rw [hσ i]
    _ = Pi.basisFun ℂ ι (σ.symm i) := by
          simpa [e] using
            centralCharacterFamilyAlgEquiv_apply_characterCentralElement
              π hπ_pairwise hπ_complete (σ.symm i)
    _ = LinearEquiv.funCongrLeft ℂ ℂ σ (Pi.basisFun ℂ ι i) := by
          symm
          simpa using basisFun_funCongrLeft (σ := σ) i

/-- Helper for Exercise 9-9.1-4: over `ℂ`, the transported center map is multiplicative because
it becomes coordinate permutation under the central-character algebra equivalence. -/
lemma centerPowerLinearEquiv_map_mul_complex
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (z w : Subalgebra.center ℂ (ℂ[G])) :
    centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (z * w) =
      centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn z *
        centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn w := by
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  obtain ⟨ι, _, π, _hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := ℂ) (G := G)
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  obtain ⟨σ, hσ⟩ :=
    centerPowerLinearEquiv_characterCentralElement π hπ_pairwise hπ_complete n hn
  let T : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
    (((e.toLinearEquiv.symm.trans (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn)).trans
      e.toLinearEquiv))
  have hT :
      T = LinearEquiv.funCongrLeft ℂ ℂ σ :=
    centerPowerLinearEquiv_conjugated_eq_funCongrLeft
      π hπ_pairwise hπ_complete n hn σ hσ
  apply e.injective
  have hzw :
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (z * w)) = T (e (z * w)) := by
    change e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (z * w)) =
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (e.symm (e (z * w))))
    exact congrArg e (by rw [e.symm_apply_apply])
  have hz :
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn z) = T (e z) := by
    change e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn z) =
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (e.symm (e z)))
    exact congrArg e (by rw [e.symm_apply_apply])
  have hw :
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn w) = T (e w) := by
    change e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn w) =
      e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (e.symm (e w)))
    exact congrArg e (by rw [e.symm_apply_apply])
  -- Under `e`, the source-faithful center automorphism becomes coordinate permutation, which
  -- clearly preserves pointwise multiplication.
  calc
    e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (z * w)) = T (e (z * w)) := hzw
    _ = T (e z * e w) := by
          exact congrArg T (e.map_mul z w)
    _ = T (e z) * T (e w) := by
          rw [hT]
          ext i
          simp [Pi.mul_apply, LinearEquiv.funCongrLeft_apply]
    _ = e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn z) *
          e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn w) := by
            rw [← hz, ← hw]
    _ = e (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn z *
          centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn w) := by
            symm
            exact e.map_mul _ _

/-- Helper for Exercise 9-9.1-4: expanding the product of two class sums at a fixed group element
turns the coefficient into a sum of indicator products. -/
lemma conjugacyClassSum_mul_apply_eq_sum_indicator
    (c₁ c₂ : ConjClasses G) (g : G) :
    (conjugacyClassSum k c₁ * conjugacyClassSum k c₂) g =
      ∑ x : G, (c₁.indicator x) * (c₂.indicator (x⁻¹ * g)) := by
  classical
  -- Unfold convolution once, then replace coefficients by the class indicators.
  rw [MonoidAlgebra.mul_apply_left, Finsupp.sum]
  calc
    ∑ x ∈ (conjugacyClassSum k c₁).support,
        conjugacyClassSum k c₁ x * conjugacyClassSum k c₂ (x⁻¹ * g)
      = ∑ x ∈ (conjugacyClassSum k c₁).support,
          c₁.indicator x * c₂.indicator (x⁻¹ * g) := by
            simp [conjugacyClassSum_apply]
    _ = ∑ x : G, c₁.indicator x * c₂.indicator (x⁻¹ * g) := by
          -- Off the support of the first class sum, the indicator contribution vanishes.
          refine Finset.sum_subset (by intro x hx; simp) ?_
          intro x _ hx
          have hx0 : conjugacyClassSum k c₁ x = 0 := by
            contrapose! hx
            simpa [Finsupp.mem_support_iff] using hx
          rw [← conjugacyClassSum_apply (k := k) (c := c₁) (g := x)]
          simp [hx0]

/-- Helper for Exercise 9-9.1-4: the coefficient of a product of two conjugacy-class sums is the
cardinality of the corresponding solution set, viewed through the natural-number cast into the
coefficient semiring. -/
lemma conjugacyClassSumInCenter_mul_coeff_eq_natCast_card
    (c₁ c₂ : ConjClasses G) (g : G)
    [DecidablePred fun x : G ↦ ConjClasses.mk x = c₁ ∧ ConjClasses.mk (x⁻¹ * g) = c₂] :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c₁ * conjugacyClassSumInCenter k c₂)
      (ConjClasses.mk g) =
        ((Finset.univ.filter fun x : G ↦
          ConjClasses.mk x = c₁ ∧ ConjClasses.mk (x⁻¹ * g) = c₂).card : k) := by
  rw [centerCoeffEquivFun_apply_mk]
  -- Pass from center coordinates to the ambient coefficient at `g`, then expand the product.
  change (conjugacyClassSum k c₁ * conjugacyClassSum k c₂) g = _
  rw [conjugacyClassSum_mul_apply_eq_sum_indicator]
  let P : G → Prop := fun x : G ↦ ConjClasses.mk x = c₁ ∧ ConjClasses.mk (x⁻¹ * g) = c₂
  have hterm : ∀ x : G,
      c₁.indicator x * c₂.indicator (x⁻¹ * g) = if P x then (1 : k) else 0 := by
    intro x
    -- Each indicator product is `1` exactly when both class constraints hold.
    by_cases h₁ : ConjClasses.mk x = c₁ <;> by_cases h₂ : ConjClasses.mk (x⁻¹ * g) = c₂
    · simp [P, ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h₁, h₂]
    · simp [P, ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h₁, h₂]
    · simp [P, ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h₁, h₂]
    · simp [P, ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h₁, h₂]
  have hcard :
      Finset.sum (Finset.univ.filter P) (fun _ : G ↦ (1 : k)) =
        ((Finset.univ.filter P).card : k) := by
    -- The filtered sum of ones is exactly the natural-number cardinality.
    have h := congrArg (fun n : ℕ ↦ (n : k)) (Finset.card_eq_sum_ones (Finset.univ.filter P))
    simp
  calc
    ∑ x : G, c₁.indicator x * c₂.indicator (x⁻¹ * g)
      = ∑ x : G, if P x then (1 : k) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact hterm x
    _ = Finset.sum (Finset.univ.filter P) (fun _ : G ↦ (1 : k)) := by
          -- Rewrite the ambient sum as the sum over the filtered solution set.
          symm
          exact Finset.sum_filter P (fun _ : G ↦ (1 : k))
    _ = ((Finset.univ.filter P).card : k) := hcard

/-- Helper for Exercise 9-9.1-4: over `ℂ`, multiplicativity of the transported center map implies
that the class-sum structure constants are invariant under the coprime power permutation. -/
lemma conjugacyClassSum_structure_constants_complex_invariant
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (c₁ c₂ c₃ : ConjClasses G) :
    centerCoeffEquivFun ℂ
      (conjugacyClassSumInCenter ℂ ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₁) *
        conjugacyClassSumInCenter ℂ ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₂))
      ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₃) =
        centerCoeffEquivFun ℂ
          (conjugacyClassSumInCenter ℂ c₁ * conjugacyClassSumInCenter ℂ c₂)
          c₃ := by
  let p := ConjClasses.powCoprimeEquiv (n : ℕ) hn
  -- Specialize the already-proved complex multiplicativity theorem to the class-sum basis.
  calc
    centerCoeffEquivFun ℂ
        (conjugacyClassSumInCenter ℂ (p c₁) * conjugacyClassSumInCenter ℂ (p c₂))
        (p c₃)
      = centerCoeffEquivFun ℂ
          (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (conjugacyClassSumInCenter ℂ c₁) *
            centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn (conjugacyClassSumInCenter ℂ c₂))
          (p c₃) := by
            simp [centerPowerLinearEquiv_conjugacyClassSumInCenter, p]
    _ = centerCoeffEquivFun ℂ
          (centerPowerLinearEquiv (k := ℂ) (n : ℕ) hn
            (conjugacyClassSumInCenter ℂ c₁ * conjugacyClassSumInCenter ℂ c₂))
          (p c₃) := by
            exact congrArg (fun u ↦ centerCoeffEquivFun ℂ u (p c₃))
              (centerPowerLinearEquiv_map_mul_complex (G := G) (n := n) (hn := hn)
                (conjugacyClassSumInCenter ℂ c₁) (conjugacyClassSumInCenter ℂ c₂)).symm
    _ = centerCoeffEquivFun ℂ
          (conjugacyClassSumInCenter ℂ c₁ * conjugacyClassSumInCenter ℂ c₂)
          c₃ := by
            simp [centerPowerLinearEquiv, p]

/-- Helper for Exercise 9-9.1-4: the conjugacy-class-sum structure constants are preserved by the
coprime power permutation on conjugacy classes. -/
lemma conjugacyClassSum_structure_constants_powCoprime_invariant
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (c₁ c₂ c₃ : ConjClasses G) :
    centerCoeffEquivFun k
      (conjugacyClassSumInCenter k ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₁) *
        conjugacyClassSumInCenter k ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₂))
      ((ConjClasses.powCoprimeEquiv (n : ℕ) hn) c₃) =
        centerCoeffEquivFun k
          (conjugacyClassSumInCenter k c₁ * conjugacyClassSumInCenter k c₂)
          c₃ := by
  classical
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c₃
  let p := ConjClasses.powCoprimeEquiv (n : ℕ) hn
  let Npow : ℕ :=
    (Finset.univ.filter fun x : G ↦
      ConjClasses.mk x = p c₁ ∧ ConjClasses.mk (x⁻¹ * (g ^ (n : ℕ))) = p c₂).card
  let Nbase : ℕ :=
    (Finset.univ.filter fun x : G ↦
      ConjClasses.mk x = c₁ ∧ ConjClasses.mk (x⁻¹ * g) = c₂).card
  have hp_mk : p (ConjClasses.mk g) = ConjClasses.mk (g ^ (n : ℕ)) := by
    change ConjClasses.pow (n : ℕ) (ConjClasses.mk g) = ConjClasses.mk (g ^ (n : ℕ))
    exact ConjClasses.pow_mk n g
  -- Route correction: descend the invariant from the already-proved complex automorphism instead
  -- of trying to reindex the defining filter directly.
  have hcomplex :
      centerCoeffEquivFun ℂ
        (conjugacyClassSumInCenter ℂ (p c₁) * conjugacyClassSumInCenter ℂ (p c₂))
        (p (ConjClasses.mk g)) =
          centerCoeffEquivFun ℂ
            (conjugacyClassSumInCenter ℂ c₁ * conjugacyClassSumInCenter ℂ c₂)
            (ConjClasses.mk g) :=
    conjugacyClassSum_structure_constants_complex_invariant (G := G) n hn c₁ c₂ (ConjClasses.mk g)
  have hnat : Npow = Nbase := by
    -- After rewriting both complex coefficients as natural-number casts, injectivity of
    -- `Nat.cast : ℕ → ℂ` identifies the underlying structure constants.
    rw [hp_mk,
      conjugacyClassSumInCenter_mul_coeff_eq_natCast_card (k := ℂ)
        (c₁ := p c₁) (c₂ := p c₂) (g := g ^ (n : ℕ)),
      conjugacyClassSumInCenter_mul_coeff_eq_natCast_card (k := ℂ)
        (c₁ := c₁) (c₂ := c₂) (g := g)] at hcomplex
    exact Nat.cast_injective (R := ℂ) (by simpa [Npow, Nbase] using hcomplex)
  -- The arbitrary-`k` statement is now the same cardinality identity recast into `k`.
  rw [hp_mk,
    conjugacyClassSumInCenter_mul_coeff_eq_natCast_card (k := k)
      (c₁ := p c₁) (c₂ := p c₂) (g := g ^ (n : ℕ)),
    conjugacyClassSumInCenter_mul_coeff_eq_natCast_card (k := k)
      (c₁ := c₁) (c₂ := c₂) (g := g)]
  simp [Npow, Nbase, hnat]

/-- Helper for Exercise 9-9.1-4: multiplicativity of the transported center map holds on each
pair of conjugacy-class-sum basis vectors. -/
lemma centerPowerLinearEquiv_map_mul_conjugacyClassSumInCenter
    (n : ℕ+) (hn : (Nat.card G).Coprime n)
    (c₁ c₂ : ConjClasses G) :
    centerPowerLinearEquiv (k := k) (n : ℕ) hn
      (conjugacyClassSumInCenter k c₁ * conjugacyClassSumInCenter k c₂) =
        centerPowerLinearEquiv (k := k) (n : ℕ) hn (conjugacyClassSumInCenter k c₁) *
          centerPowerLinearEquiv (k := k) (n : ℕ) hn (conjugacyClassSumInCenter k c₂) := by
  apply (centerCoeffEquivFun k).injective
  ext c'
  let p := ConjClasses.powCoprimeEquiv (n : ℕ) hn
  let d : ConjClasses G := p.symm c'
  -- Compare the coefficient at `c'` after transporting with the original coefficient at `d`.
  calc
    centerCoeffEquivFun k
        (centerPowerLinearEquiv (k := k) (n : ℕ) hn
          (conjugacyClassSumInCenter k c₁ * conjugacyClassSumInCenter k c₂)) c'
      = centerCoeffEquivFun k
          (conjugacyClassSumInCenter k c₁ * conjugacyClassSumInCenter k c₂) d := by
            simp [centerPowerLinearEquiv, p, d]
    _ = centerCoeffEquivFun k
          (conjugacyClassSumInCenter k (p c₁) * conjugacyClassSumInCenter k (p c₂)) c' := by
            simpa [p, d] using
              (conjugacyClassSum_structure_constants_powCoprime_invariant
                (k := k) (G := G) n hn c₁ c₂ d).symm
    _ = centerCoeffEquivFun k
          (centerPowerLinearEquiv (k := k) (n : ℕ) hn (conjugacyClassSumInCenter k c₁) *
            centerPowerLinearEquiv (k := k) (n : ℕ) hn (conjugacyClassSumInCenter k c₂)) c' := by
            simp [centerPowerLinearEquiv_conjugacyClassSumInCenter, p]

/-- Exercise 9-9.1-4 (2): the center map induced by the coprime power permutation is
multiplicative, so it upgrades to an algebra automorphism of `Subalgebra.center k (k[G])`. -/
theorem centerPowerLinearEquiv_map_mul
    (n : ℕ) (hn : (Nat.card G).Coprime n)
    (z w : Subalgebra.center k (k[G])) :
    centerPowerLinearEquiv (k := k) n hn (z * w) =
      centerPowerLinearEquiv (k := k) n hn z * centerPowerLinearEquiv (k := k) n hn w := by
  classical
  by_cases h0 : n = 0
  · subst h0
    have hcard : Nat.card G = 1 := by
      simpa [Nat.coprime_zero_right] using hn
    have hsub : Subsingleton G := by
      have hcardF : Fintype.card G = 1 := by
        simpa [Nat.card_eq_fintype_card] using hcard
      exact (Fintype.card_le_one_iff_subsingleton).mp (by omega)
    letI : Subsingleton G := hsub
    have hpow : powCoprime hn = @_root_.Equiv.refl G := by
      ext g
      exact Subsingleton.elim _ _
    -- In the trivial-group case, the power permutation itself is the identity.
    apply Subtype.ext
    rw [show (((centerPowerLinearEquiv (k := k) 0 hn z * centerPowerLinearEquiv (k := k) 0 hn w :
        Subalgebra.center k (k[G])) : k[G])) =
        ((centerPowerLinearEquiv (k := k) 0 hn z : k[G]) *
          (centerPowerLinearEquiv (k := k) 0 hn w : k[G])) by
        rfl]
    rw [centerPowerLinearEquiv_apply (k := k) 0 hn (z * w),
      centerPowerLinearEquiv_apply (k := k) 0 hn z,
      centerPowerLinearEquiv_apply (k := k) 0 hn w,
      hpow]
    ext g
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero h0
    let m : ℕ+ := ⟨n, hpos⟩
    let b := conjugacyClassSumBasis (G := G) (k := k)
    -- Expand both central elements in the class-sum basis and reduce to the basis-vector case.
    rw [← b.sum_repr z, ← b.sum_repr w]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_congr rfl (fun c₁ hc₁ ↦ by
      exact congrArg (fun u ↦ (b.repr w) c₁ • u) (by
        exact Finset.sum_congr rfl (fun c₂ hc₂ ↦ by
          have hb₁ : b c₁ = conjugacyClassSumInCenter k c₁ := by
            dsimp [b]
            simp
          have hb₂ : b c₂ = conjugacyClassSumInCenter k c₂ := by
            dsimp [b]
            simp
          have hbasis :
              centerPowerLinearEquiv (k := k) (m : ℕ) hn (b c₁ * b c₂) =
                centerPowerLinearEquiv (k := k) (m : ℕ) hn (b c₁) *
                  centerPowerLinearEquiv (k := k) (m : ℕ) hn (b c₂) := by
            simpa [m, hb₁, hb₂] using
              (centerPowerLinearEquiv_map_mul_conjugacyClassSumInCenter
                (k := k) (G := G) m hn c₁ c₂)
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun u ↦ (b.repr z) c₂ • u) hbasis)))

end

end Representation
