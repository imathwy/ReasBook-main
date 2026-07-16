import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1

noncomputable section

universe u

open CategoryTheory
open scoped Representation

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {A : Type*} [AddCommGroup A]

/-- Helper for Theorem 16-16.1-5: if a fixed natural-number multiple of each simple basis vector
of `R₀[k](G)` lies in the range of an additive map `f`, then the same multiple of every class lies
in the range of `f`. -/
theorem addMonoidHom_nsmul_mem_range_of_simple_basis_preimages
    [Finite G] {ι : Type (u + 1)} [Fintype ι]
    (f : A →+ R₀[k](G))
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (N : ℕ)
    (hπ_range : ∀ i, (N : ℕ) • [π i]₀ ∈ f.range)
    (y : R₀[k](G)) :
    (N : ℕ) • y ∈ f.range := by
  classical
  let b : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hb : ∀ i, (N : ℕ) • b i ∈ f.range := by
    -- Rewrite the canonical basis vector back to the chosen simple class.
    intro i
    simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using hπ_range i
  choose x hx using hb
  refine ⟨(b.repr y).sum fun i a ↦ a • x i, ?_⟩
  -- Expand `y` in the simple basis and lift the chosen multiples termwise.
  calc
    f ((b.repr y).sum fun i a ↦ a • x i)
        = (b.repr y).sum fun i a ↦ a • f (x i) := by
            simp [Finsupp.sum, map_sum, map_zsmul]
    _ = (b.repr y).sum fun i a ↦ a • ((N : ℕ) • b i) := by
          simp [Finsupp.sum, hx]
    _ = (b.repr y).sum fun i a ↦ (N : ℕ) • (a • b i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using (smul_comm (b.repr y i) (N : ℕ) (b i))
    _ = (N : ℕ) • ((b.repr y).sum fun i a ↦ a • b i) := by
          simpa [Finsupp.sum] using
            (Finset.smul_sum
              (s := (b.repr y).support) (f := fun i ↦ (b.repr y i) • b i) (r := (N : ℕ))).symm
    _ = (N : ℕ) • y := by
          rw [show (b.repr y).sum (fun i a ↦ a • b i) = y by
            simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y]

end

end Representation
