import Mathlib
import Serre.Chap01.Theorem_1_1_4_2
import Serre.Chap03.Definition_3_3_3_1
import Serre.Chap03.Exercise_3_3_3_6
import Serre.Chap07.Proposition_7_7_1_3
import Serre.Chap07.Remark_7_7_1_4
import Serre.Chap08.Definition_8_8_3_2
import Serre.Chap08.Exercise_8_8_3_9
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap10.MonomialCharacter
import Serre.Chap10.Theorem_10_10_2_1
import Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure
import Serre.Chap10.Theorem_10_10_5_2.BrauerPRegularBridge
import Serre.Chap10.Theorem_10_10_5_2.MonomialLinearCharacter
import Serre.Chap10.Theorem_10_10_5_2.InducedModelEquivalence
import Serre.Chap10.Theorem_10_10_5_2.QuotientMonomialReduction
import Serre.Chap10.Theorem_10_10_5_2.SubrepresentationTransport
import Serre.Chap10.Theorem_10_10_5_2.IsotypicRestrictionBridge
import Serre.Chap10.Theorem_10_10_5_2.SupersolvableInductionBridge

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_target_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_target_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

/-- Helper for Theorem 10-10.5-2: the character of an irreducible finite-dimensional complex
representation of an elementary group is monomial. -/
theorem fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible
    (V : FDRep ℂ G) [CategoryTheory.Simple V] (hG : IsElementary G) :
    fdRepCharacterRing V ∈ monomialCharacterSpan G := by
  -- Reduce the target to the representation-level monomiality bridge isolated just above.
  exact
    fdRepCharacterRing_mem_monomialCharacterSpan_of_isMonomial V
      (fdRep_isMonomial_of_simple_of_isElementary V hG)

/-- Helper for Theorem 10-10.5-2: every honest finite-dimensional character of an elementary
group belongs to the monomial-character span. -/
theorem rep_character_mem_monomialCharacterSpan_of_isElementary
    (V : FDRep ℂ G) (hG : IsElementary G) :
    fdRepCharacterRing V ∈ monomialCharacterSpan G := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation V.ρ),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_isInternal_irreducible_subrepresentations (ρ := V.ρ)
  let hinternal : DirectSum.IsInternal (fun i : κ ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  have hchar :
      V.character = ∑ i : κ, ((σ i).toRepresentation).character := by
    -- Decompose the trace of `V g` along the internal direct sum of irreducible summands.
    ext g
    simpa [Representation.character] using
      (LinearMap.trace_eq_sum_trace_restrict
        (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
        (f := V.ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))
  have hring :
      fdRepCharacterRing V = ∑ i : κ, fdRepCharacterRing (FDRep.of (σ i).toRepresentation) := by
    -- Bundle the character decomposition inside `R(G)`.
    apply Subtype.ext
    ext g
    simpa [fdRepCharacterRing] using congrFun hchar g
  rw [hring]
  -- Each irreducible summand is already monomial on an elementary group, so the finite sum stays
  -- inside the monomial-character span.
  refine Submodule.sum_mem _ ?_
  intro i hi
  let τ : FDRep ℂ G := FDRep.of (σ i).toRepresentation
  letI : Representation.IsIrreducible τ.ρ := by
    simpa [τ] using hσ_irr i
  letI : CategoryTheory.Simple τ := FDRep.simple_of_isIrreducible τ
  simpa [τ] using
    fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible τ hG

/-- Helper for Theorem 10-10.5-2: an elementary finite group has monomial-character span equal to
its full character ring. -/
theorem monomialCharacterSpan_eq_top_of_isElementary
    (hG : IsElementary G) :
    monomialCharacterSpan G = ⊤ := by
  -- Reduce the elementary endpoint to the single honest-character membership statement above.
  refine top_unique ?_
  rw [← rep_character_span_eq_top (G := G)]
  rw [Submodule.span_le]
  intro χ hχ
  rcases hχ with ⟨V, rfl⟩
  exact rep_character_mem_monomialCharacterSpan_of_isElementary V hG

/-- Helper for Theorem 10-10.5-2: inducing a tensor character from any `p`-elementary subgroup
already lands in the realized local scalar span of `V[p](G)`. -/
private theorem induced_tensor_character_on_pElementary_subgroup_mem_local_scalar_span
    (p : Nat.Primes) (H : Subgroup G) (hH : IsPElementary (p : ℕ) H)
    (ψ : pElementaryScalarExtensionRing_local ⊗R(H)) :
    let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
      Submodule.span pElementaryScalarExtensionRing_local
        { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
    Ind[H]((ψ : H → ℂ)) ∈ W := by
  let W : Submodule pElementaryScalarExtensionRing_local (G → ℂ) :=
    Submodule.span pElementaryScalarExtensionRing_local
      { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }
  -- This is exactly the support-file bridge theorem, restated in the local notation of the main
  -- proof.
  simpa [W] using
    induced_tensor_character_mem_pElementary_scalarExtension_local
      (G := G) (p := (p : ℕ)) H hH ψ

-- Proof sketch: rewrite `V[p](G)` as the supremum of the ranges of the subgroup induction maps
-- over the `p`-elementary subgroups of `G`, then use the elementary `= ⊤` theorem and induction
-- closure of `monomialCharacterSpan`.
/-- Helper for Theorem 10-10.5-2: every Brauer submodule `V[p](G)` is contained in the
monomial-character span. -/
theorem pElementaryInducedCharacterSpan_le_monomialCharacterSpan (p : Nat.Primes) :
    V[p](G) ≤ monomialCharacterSpan G := by
  classical
  -- Route correction: the Brauer owner `V[p](G)` is a supremum of full `characterRingInduction`
  -- ranges, so the proof has to use the stronger elementary statement `= ⊤`, not only honest
  -- character membership.
  rw [Representation.pElementaryInducedCharacterSpan]
  simp_rw [Representation.artinInducedCharacterSubmodule]
  refine iSup_le ?_
  intro H
  rcases H with ⟨H, hHmem⟩
  have hH : IsPElementary (p : ℕ) H := by
    simpa using (Finset.mem_filter.mp hHmem).2
  -- Replace the induction range by the image of `⊤`, then apply the elementary `= ⊤` theorem.
  calc
    LinearMap.range (Representation.Subgroup.characterRingInduction H) =
        Submodule.map (Representation.Subgroup.characterRingInduction H) ⊤ := by
      rw [LinearMap.range_eq_map]
    _ ≤ Submodule.map (Representation.Subgroup.characterRingInduction H)
        (monomialCharacterSpan H) := by
      rw [monomialCharacterSpan_eq_top_of_isElementary ⟨p, hH⟩]
    _ ≤ monomialCharacterSpan G :=
        Representation.Subgroup.characterRingInduction_map_monomialCharacterSpan H

/-- Helper for Theorem 10-10.5-2: a submodule of the character ring whose additive index is `1`
is already the whole character ring. -/
private theorem eq_top_of_toAddSubgroup_index_eq_one
    (W : Submodule ℤ (R(G))) (hW_index : W.toAddSubgroup.index = 1) :
    W = ⊤ := by
  -- Translate the additive subgroup criterion back to the ambient `ℤ`-submodule.
  simpa using
    (Submodule.toAddSubgroup_eq_top.1 (AddSubgroup.index_eq_one.1 hW_index))

/-- Helper for Theorem 10-10.5-2: if each Brauer owner `V[q](G)` has additive index coprime to
its defining prime `q`, then their supremum is already the whole character ring. -/
private theorem iSup_pElementaryInducedCharacterSpan_eq_top_of_primewise_index_coprime
    (hcoprime : ∀ q : Nat.Primes, Nat.Coprime q (V[q](G)).toAddSubgroup.index) :
    (⨆ p : Nat.Primes, V[p](G)) = ⊤ := by
  let W : Submodule ℤ (R(G)) := ⨆ p : Nat.Primes, V[p](G)
  have hW_index : W.toAddSubgroup.index = 1 := by
    -- Brauer's standard index argument: `W` sits above each `V[q](G)`, so its index divides every
    -- primewise index and is therefore coprime to every prime.
    refine (Nat.eq_one_iff_not_exists_prime_dvd).2 ?_
    intro p hp hpdvd
    let q : Nat.Primes := ⟨p, hp⟩
    have hVq_le : V[q](G) ≤ W :=
      le_iSup (fun r : Nat.Primes ↦ V[r](G)) q
    have hW_dvd : W.toAddSubgroup.index ∣ (V[q](G)).toAddSubgroup.index :=
      AddSubgroup.index_dvd_of_le hVq_le
    have hW_coprime : Nat.Coprime p W.toAddSubgroup.index :=
      Nat.Coprime.of_dvd_right hW_dvd (by simpa using hcoprime q)
    exact (hp.coprime_iff_not_dvd.1 hW_coprime) hpdvd
  -- Once the additive index is `1`, the supremum submodule must be all of `R(G)`.
  simpa [W] using eq_top_of_toAddSubgroup_index_eq_one (G := G) W hW_index

/-- Helper for Theorem 10-10.5-2: Brauer's theorem places every integral character in the
supremum of the `p`-elementary induction spans. -/
theorem character_mem_iSup_pElementaryInducedCharacterSpan (χ : R(G)) :
    χ ∈ (⨆ p : Nat.Primes, V[p](G)) := by
  have hW_top : (⨆ p : Nat.Primes, V[p](G)) = ⊤ := by
    have hprimewise :
        ∀ q : Nat.Primes, Nat.Coprime q (V[q](G)).toAddSubgroup.index := by
      intro q
      -- The primewise coprimality input is exactly the earlier Brauer finite-index theorem.
      simpa using (pElementaryInducedCharacterSpan_finiteIndex_and_index_coprime (G := G) q).2
    -- The generic index argument is now separated from the primewise Brauer input.
    exact
      iSup_pElementaryInducedCharacterSpan_eq_top_of_primewise_index_coprime
        (G := G) hprimewise
  -- Once the Brauer supremum is identified with `⊤`, membership is immediate.
  simp [hW_top]

/-- Helper for Theorem 10-10.5-2: once Brauer's theorem puts a character in the supremum of the
`p`-elementary induction spans, the already-verified elementary-group argument places it in the
monomial-character span. -/
private theorem brauer_sup_le_monomialCharacterSpan :
    (⨆ p : Nat.Primes, V[p](G)) ≤ monomialCharacterSpan G := by
  -- Each Brauer owner `V[p](G)` is already inside the monomial-character span.
  exact
    iSup_le (fun p ↦
      pElementaryInducedCharacterSpan_le_monomialCharacterSpan (G := G) p)

-- Proof sketch: Theorem `10-10.5-1` reduces every character of `G` to an integral linear
-- combination of characters induced from elementary subgroups. For an elementary subgroup `H`,
-- Definition `10-10.1-3` gives nilpotence, and finite nilpotent groups are supersolvable; apply
-- Theorem `8-8.5-2` to decompose the irreducible constituents on `H` into inductions from
-- one-dimensional characters. Induction in stages then shows that each elementary induced
-- character lies in `monomialCharacterSpan G`, so this span is all of `R(G)`.
/-- Theorem 10-10.5-2: the monomial characters span Serre's integral character ring `R(G)`. -/
theorem monomialCharacterSpan_eq_top :
    monomialCharacterSpan G = ⊤ := by
  -- Brauer's theorem puts each character into the supremum of the elementary induction spans,
  -- and each such span already lies inside the monomial-character span.
  refine top_unique ?_
  intro χ _
  have hχ :
      χ ∈ (⨆ p : Nat.Primes, V[p](G)) := by
    simpa using character_mem_iSup_pElementaryInducedCharacterSpan (G := G) χ
  exact brauer_sup_le_monomialCharacterSpan (G := G) hχ

/-- Every character of `G` belongs to the monomial-character span. -/
theorem character_mem_monomialCharacterSpan (χ : R(G)) :
    χ ∈ monomialCharacterSpan G := by
  simp [monomialCharacterSpan_eq_top]

end

end Representation
