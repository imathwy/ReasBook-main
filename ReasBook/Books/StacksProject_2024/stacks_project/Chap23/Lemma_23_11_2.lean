import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Order.Disjoint
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Regular.RegularSequence
import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {r : ℕ}
variable {F : Submodule (R ⧸ I) I.Cotangent}

-- Semantic recall note: the semantic Lean search tool was unavailable in this environment, so the
-- owner choices here were verified against local precedent for `projectiveDimension`,
-- `Ideal.Cotangent`, `IsComplemented`, `Module.FiniteLocallyFreeOfRank`,
-- `fin_pi_finiteLocallyFreeOfRank`, `finiteLocallyFreeOfRank_of_equiv`, and `IsRegular`.

/-- Helper for Lemma 23.11.2: the free-rank part of the source hypothesis on `F` is exposed
through the canonical owner `Module.FiniteLocallyFreeOfRank`, while the direct-summand hypothesis
remains the explicit assumption `hFcompl`. -/
theorem exists_regularSequence_generating_cotangent_directSummand_of_projectiveDimension_ne_top_of_finiteLocallyFreeOfRank
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    [Module.FiniteLocallyFreeOfRank (R ⧸ I) F r] :
    ∃ x : Fin r → I,
      RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) ∧
        Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (x i)) = F := by
  sorry

/-- Lemma 23.11.2: let `R` be a Noetherian local ring and let `I ⊆ R` be an ideal of finite
projective dimension over `R`. If `F ⊆ I / I²` is a direct summand free of rank `r`, then there
exists a regular sequence `x₁, …, xᵣ ∈ I` whose classes in `I / I²` generate `F`. -/
@[stacks 0FJR]
theorem exists_regularSequence_generating_cotangent_directSummand_of_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    (hF : Nonempty (F ≃ₗ[R ⧸ I] (Fin r → R ⧸ I))) :
    ∃ x : Fin r → I,
      RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) ∧
        Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (x i)) = F := by
  sorry

end
