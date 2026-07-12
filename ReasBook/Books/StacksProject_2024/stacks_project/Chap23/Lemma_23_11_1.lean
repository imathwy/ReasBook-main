import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Order.Disjoint
import Mathlib.RingTheory.Ideal.Cotangent

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {F : Submodule (R ⧸ I) I.Cotangent}

-- Semantic recall note: the semantic Lean search tool was unavailable in this environment, so the
-- owner choices here were verified against local precedent for `projectiveDimension`,
-- `Ideal.Cotangent`, `IsComplemented`, and `nonZeroDivisors`.

/-- Lemma 23.11.1: let `R` be a Noetherian local ring and let `I ⊆ R` be an ideal of finite
projective dimension over `R`. If `F ⊆ I / I²` is a direct summand linearly isomorphic to `R / I`,
then there exists a nonzerodivisor `x ∈ I` whose image in `I / I²` generates `F`. -/
@[stacks 0FJQ]
theorem exists_nonzerodivisor_generating_cotangent_directSummand_of_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    (hF : Nonempty (F ≃ₗ[R ⧸ I] (R ⧸ I))) :
    ∃ x : I,
      (x : R) ∈ nonZeroDivisors R ∧
        Submodule.span (R ⧸ I) {I.toCotangent x} = F := by
  sorry

end
