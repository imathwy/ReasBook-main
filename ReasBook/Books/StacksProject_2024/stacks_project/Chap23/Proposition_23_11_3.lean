import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Ideal.Cotangent
import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Ideal R}

-- Semantic recall note: the semantic Lean search tool was unavailable in this environment, so the
-- owner choice here was verified against local precedent for `Ideal.IsRegularIdeal`,
-- `projectiveDimension`, `Module.FiniteLocallyFree`, and `Ideal.Cotangent`.

/-- Proposition 23.11.3: let `R` be a Noetherian ring and let `I ⊆ R` be an ideal of finite
projective dimension over `R`. If the conormal module `I / I² = I.Cotangent` is finite locally
free over `R / I`, then `I` is a regular ideal. -/
@[stacks 0FJS]
theorem Ideal.isRegularIdeal_of_projectiveDimension_ne_top_of_finiteLocallyFree_cotangent
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hcot : Module.FiniteLocallyFree (R ⧸ I) I.Cotangent) :
    I.IsRegularIdeal := sorry

/-- Companion API: the finite-local-freeness hypothesis on the conormal module is often consumed
through the canonical typeclass owner `Module.FiniteLocallyFree`. -/
theorem Ideal.isRegularIdeal_of_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    [Module.FiniteLocallyFree (R ⧸ I) I.Cotangent] :
    I.IsRegularIdeal :=
  Ideal.isRegularIdeal_of_projectiveDimension_ne_top_of_finiteLocallyFree_cotangent
    hpd inferInstance

end
