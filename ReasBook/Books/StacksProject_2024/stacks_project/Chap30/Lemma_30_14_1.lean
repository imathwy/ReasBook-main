import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap30.ProjectiveSpaceCohomology

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical `Proj` owner for projective space
and the additive sheaf cohomology owner `CategoryTheory.Sheaf.H'`. Local Chapter 30 precedent
represents `\mathbf P^n_R` by `projectiveSpaceCohomologyScheme R n`; because the project does not
yet expose a canonical global twist-sheaf owner, the source-facing clauses below take the chosen
owners of `\mathcal O(d)` and `\mathcal F(d)` as explicit parameters. -/

/-- The additive sheaf cohomology group of a module sheaf on the standard `Proj` model of
`\mathbf P^n_R`. -/
abbrev projectiveSpaceCoherentSheafCohomology
    (R : Type u) [CommRing R] (n : ℕ)
    (ℱ : (projectiveSpaceCohomologyScheme R n).Modules) (i : ℕ) : AddCommGrpCat :=
  (((SheafOfModules.toSheaf (projectiveSpaceCohomologyScheme R n).ringCatSheaf).obj ℱ).H' i
    (⊤ : Opens (projectiveSpaceCohomologyScheme R n)))

/-- The defining normal form for projective-space coherent-sheaf cohomology. -/
theorem projectiveSpaceCoherentSheafCohomology_def
    (R : Type u) [CommRing R] (n : ℕ)
    (ℱ : (projectiveSpaceCohomologyScheme R n).Modules) (i : ℕ) :
    projectiveSpaceCoherentSheafCohomology R n ℱ i =
      (((SheafOfModules.toSheaf (projectiveSpaceCohomologyScheme R n).ringCatSheaf).obj ℱ).H' i
        (⊤ : Opens (projectiveSpaceCohomologyScheme R n))) := sorry

/-- The truncated graded group
`\bigoplus_{d \ge k} H^0(\mathbf P^n_R, \mathcal F(d))` for a chosen family of twist owners. -/
abbrev projectiveSpaceCoherentSheafTruncatedGlobalSections
    (R : Type u) [CommRing R] (n : ℕ)
    (twist : ℤ → (projectiveSpaceCohomologyScheme R n).Modules) (k : ℤ) : Type u :=
  DirectSum {d : ℤ // k ≤ d} fun d ↦
    (projectiveSpaceCoherentSheafCohomology R n (twist d.1) 0 : Type u)

/-- The defining normal form for the truncated graded group of global sections. -/
theorem projectiveSpaceCoherentSheafTruncatedGlobalSections_def
    (R : Type u) [CommRing R] (n : ℕ)
    (twist : ℤ → (projectiveSpaceCohomologyScheme R n).Modules) (k : ℤ) :
    projectiveSpaceCoherentSheafTruncatedGlobalSections R n twist k =
      DirectSum {d : ℤ // k ≤ d} fun d ↦
        (projectiveSpaceCoherentSheafCohomology R n (twist d.1) 0 : Type u) := sorry

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
variable (ℱ : (projectiveSpaceCohomologyScheme R n).Modules) [ℱ.IsCoherent]

/-- Lemma 30.14.1 (1): for a coherent sheaf on `\mathbf P^n_R`, there is a finite direct sum of
twisting sheaves mapping epimorphically onto it. The family `twistingSheaf` is the chosen owner of
the sheaves `\mathcal O_{\mathbf P^n_R}(d)` in the current projective-space model. -/
@[stacks 01YS]
theorem projectiveSpaceCoherentSheaf_exists_epi_from_twistingSheaf_coproduct
    (twistingSheaf : ℤ → (projectiveSpaceCohomologyScheme R n).Modules) :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ twistingSheaf (d j)) ⟶ ℱ), Epi π := sorry

/-- Lemma 30.14.1 (2): cohomology of a coherent sheaf on `\mathbf P^n_R` vanishes in all
degrees above `n`. Since cohomological degrees are natural numbers in Lean, this is the
`i > n` form of the source clause `H^i = 0` unless `0 ≤ i ≤ n`. -/
@[stacks 01YS]
theorem projectiveSpaceCoherentSheafCohomology_isZero_of_top_lt
    (i : ℕ) (hi : n < i) :
    IsZero (projectiveSpaceCoherentSheafCohomology R n ℱ i) := sorry

/-- Lemma 30.14.1 (3): every cohomology group of a coherent sheaf on `\mathbf P^n_R` is finite
as an `R`-module, for the source-induced `R`-module structure on cohomology. -/
@[stacks 01YS]
theorem projectiveSpaceCoherentSheafCohomology_finite
    (i : ℕ)
    [Module R (projectiveSpaceCoherentSheafCohomology R n ℱ i)] :
    Module.Finite R (projectiveSpaceCoherentSheafCohomology R n ℱ i) := sorry

/-- Lemma 30.14.1 (4): positive-degree cohomology of sufficiently positive twists of a coherent
sheaf on `\mathbf P^n_R` vanishes. The family `twist` is the chosen owner of
`\mathcal F(d)`. -/
@[stacks 01YS]
theorem projectiveSpaceCoherentSheafTwistCohomology_eventually_isZero
    (twist : ℤ → (projectiveSpaceCohomologyScheme R n).Modules)
    (i : ℕ) (hi : 0 < i) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (projectiveSpaceCoherentSheafCohomology R n (twist d) i) := sorry

/-- Lemma 30.14.1 (5): for every integer `k`, the truncated graded module
`\bigoplus_{d \ge k} H^0(\mathbf P^n_R, \mathcal F(d))` is finite over
`R[T_0,\ldots,T_n]`, for the source-induced graded polynomial action. The family `twist` is the
chosen owner of `\mathcal F(d)`. -/
@[stacks 01YS]
theorem projectiveSpaceCoherentSheafTruncatedGlobalSections_finite
    (twist : ℤ → (projectiveSpaceCohomologyScheme R n).Modules) (k : ℤ)
    [Module (MvPolynomial (Fin (n + 1)) R)
      (projectiveSpaceCoherentSheafTruncatedGlobalSections R n twist k)] :
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (projectiveSpaceCoherentSheafTruncatedGlobalSections R n twist k) := sorry

end

end AlgebraicGeometry
