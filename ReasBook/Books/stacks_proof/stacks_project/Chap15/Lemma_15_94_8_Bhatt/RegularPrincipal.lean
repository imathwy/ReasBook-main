import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_89_1
import stacks_proof.stacks_project.Chap15.PrincipalIdeal

-- Declarations for this helper file are theorem-local to Lemma 15.94.8 (Bhatt).

universe u

section

variable {A : Type u} [CommRing A]

open CategoryTheory
open scoped IdealPowerTorsion PrincipalIdeal

namespace ModuleCat

/-- Helper for Lemma 15.94.8 (Bhatt): in a short exact row `0 → K → L → M → 0`, the Bhatt
preimage chain `L_n = {x | f^n x ∈ im(ι)}` covers `L` as soon as the quotient `M` is
`(f)`-power torsion. -/
lemma principal_preimage_chain_iUnion_eq_univ
    {K L M : ModuleCat A} (f : A) (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hMtors : Module.IsIdealPowerTorsion ((f) : Ideal A) M) :
    (⋃ n : ℕ, {x : L | (f ^ n) • x ∈ LinearMap.range ι.hom}) = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    rw [Set.mem_iUnion]
    rw [Module.isIdealPowerTorsion_iff] at hMtors
    obtain ⟨n, hn⟩ := hMtors (π.hom x)
    refine ⟨n, ?_⟩
    have hRangeKer :
        LinearMap.range ι.hom = LinearMap.ker π.hom := by
      -- Proof comment: short exactness identifies the image of `ι` with the kernel of `π`.
      let S : ShortComplex (ModuleCat A) := ShortComplex.mk ι π h
      exact (S.moduleCat_exact_iff_range_eq_ker.mp hshort.exact)
    have hPowInIdeal : f ^ (n : ℕ) ∈ (((f) : Ideal A) ^ (n : ℕ)) := by
      -- Proof comment: the canonical generator `f` of `(f)` yields the expected element of the
      -- `n`th ideal power.
      exact Ideal.pow_mem_pow (show f ∈ ((f) : Ideal A) by simpa [principalIdeal]) (n : ℕ)
    have hKill : (f ^ (n : ℕ)) • π.hom x = 0 := by
      -- Proof comment: apply the torsion witness for `π x` to the canonical element `f^n`.
      exact hn ⟨f ^ (n : ℕ), hPowInIdeal⟩
    rw [hRangeKer, LinearMap.mem_ker]
    -- Proof comment: `π` is linear, so vanishing of `(f^n) • π x` is exactly the statement that
    -- `(f^n) • x` lands in `ker π = im ι`.
    simpa using hKill

end ModuleCat

end
