import StacksProject_2024.Chap10.Lemma_10_108_6.RankSupportBridge
import StacksProject_2024.Chap10.Lemma_10_108_6.ExteriorPowerBaseChange

universe u v w z

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.108.6: the support of the `i`th exterior power of a finite flat module is
exactly the upper stalk-rank level set `{p | i ≤ rankAtStalk M p}`. -/
theorem mem_support_exteriorPower_iff_le_rankAtStalk_of_finite_flat
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (p : PrimeSpectrum R) (i : ℕ) :
    p ∈ Module.support R (⋀[R]^i M) ↔ i ≤ Module.rankAtStalk (R := R) M p := by
  -- Move both sides to the residue-field fiber; the remaining comparison is the fixed-degree
  -- exterior-power base-change equivalence isolated above.
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.rankAtStalk_eq]
  let K := p.asIdeal.ResidueField
  let e := residueFieldTensorExteriorPowerEquiv (R := R) (M := M) p i
  exact (Equiv.nontrivial_congr e.toEquiv).trans
    (nontrivial_exteriorPower_iff_le_finrank (K := K)
      (V := TensorProduct R K M) i)

/-- Helper for Lemma 10.108.6: under the openness hypothesis for closed subsets stable under
generalization, a finite flat module is finite locally free. -/
theorem finiteLocallyFree_of_closed_generalizationStable_open
    (hOpen : ∀ Z : Set (PrimeSpectrum R), IsClosed Z →
      StableUnderGeneralization Z → IsOpen Z)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.FiniteLocallyFree R M := by
  have hRankClosed :
      ∀ i : ℕ, IsClosed {p : PrimeSpectrum R | i ≤ Module.rankAtStalk (R := R) M p} := by
    intro i
    -- The support/rank bridge identifies each upper rank level with a finite module support.
    have hEq :
        {p : PrimeSpectrum R | i ≤ Module.rankAtStalk (R := R) M p} =
          Module.support R (⋀[R]^i M) := by
      ext p
      simpa [Set.mem_setOf_eq] using
        (mem_support_exteriorPower_iff_le_rankAtStalk_of_finite_flat
          (R := R) (M := M) p i).symm
    rw [hEq]
    exact Module.isClosed_support (R := R) (M := ⋀[R]^i M)
  have hRankOpen :
      ∀ i : ℕ, IsOpen {p : PrimeSpectrum R | i ≤ Module.rankAtStalk (R := R) M p} := by
    intro i
    -- The global hypothesis opens these closed sets because rank is constant under
    -- generalization for finite flat modules.
    exact hOpen _
      (hRankClosed i)
      (stableUnderGeneralization_upper_rank_level_of_finite_flat (R := R) (N := M) i)
  have hRankLocallyConstant :
      IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)) :=
    isLocallyConstant_int_of_clopen_upper_level
      (fun p : PrimeSpectrum R ↦ Module.rankAtStalk (R := R) M p)
      hRankOpen hRankClosed
  -- Finite flat modules have free stalks everywhere; the clopen rank levels give the remaining
  -- local constancy needed by the finite-locally-free criterion.
  exact
    Module.finiteLocallyFree_of_freeLocus_eq_univ_of_isLocallyConstant_rankAtStalk
      (R := R) (M := M) (Module.freeLocus_eq_univ (R := R) (M := M))
      hRankLocallyConstant

/-- Helper for Lemma 10.108.6: under the openness hypothesis for closed subsets stable under
generalization, the stalk-rank function of a finite flat module is locally constant. -/
theorem isLocallyConstant_rankAtStalk_of_closed_generalizationStable_open
    (hOpen : ∀ Z : Set (PrimeSpectrum R), IsClosed Z →
      StableUnderGeneralization Z → IsOpen Z)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)) := by
  -- Once the source-local argument produces finite local freeness, the chapter TFAE turns it into
  -- local constancy of the stalk-rank function.
  have hFiniteLocallyFree :
      Module.FiniteLocallyFree R M :=
    finiteLocallyFree_of_closed_generalizationStable_open (R := R) (M := M) hOpen
  have hTfae :
      Module.Finite R M ∧
        Module.freeLocus R M = Set.univ ∧
          IsLocallyConstant
            (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk (R := R) M p : ℤ)) :=
    ((module_finite_projective_tfae (R := R) (M := M)).out 6 7).mp hFiniteLocallyFree
  exact hTfae.2.2
end
