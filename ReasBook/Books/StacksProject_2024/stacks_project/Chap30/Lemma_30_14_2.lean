import StacksProject_2024.stacks_project.Chap30.Lemma_30_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical owner `AlgebraicGeometry.Proj`,
`Proj.toSpecZero`, and the finite-type/proper API around `Proj.toSpecZero`. Local Chapter 30
precedent represents sheaf cohomology by `CategoryTheory.Sheaf.H'`; since the project does not yet
expose a canonical twist-sheaf owner for arbitrary `Proj`, the source-facing clauses below take the
chosen owners of `\mathcal O_X(d)` and `\mathcal F(d)` as explicit parameters. -/

/-- The additive sheaf cohomology group of a module sheaf on `Proj 𝒜`. -/
abbrev projCoherentSheafCohomology
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (ℱ : (Proj 𝒜).Modules) (i : ℕ) : AddCommGrpCat :=
  (((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).obj ℱ).H' i
    (⊤ : Opens (Proj 𝒜)))

/-- The truncated graded group `\bigoplus_{d \ge k} H^0(Proj 𝒜, \mathcal F(d))`
for a chosen family of twist owners. -/
abbrev projCoherentSheafTruncatedGlobalSections
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (twist : ℤ → (Proj 𝒜).Modules) (k : ℤ) : Type u :=
  DirectSum {d : ℤ // k ≤ d} fun d ↦
    (projCoherentSheafCohomology 𝒜 (twist d.1) 0 : Type u)

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Lemma 30.14.2 (1): if `A₀` is Noetherian and the graded ring `A` is generated over
`A₀` by finitely many degree-one elements, then `Proj(A)` is a Noetherian scheme. -/
@[stacks 0AG6]
theorem proj_isNoetherian_of_degreeOneGenerated_noetherian
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1) :
    IsNoetherian (Proj 𝒜) := sorry

/-- Lemma 30.14.2 (2): for a coherent sheaf on `Proj(A)` under the same finite degree-one
generation hypotheses, there is a finite direct sum of twisting sheaves mapping epimorphically
onto it. The family `twistingSheaf` is the chosen owner of the sheaves `\mathcal O_X(d)`. -/
@[stacks 0AG6]
theorem projCoherentSheaf_exists_epi_from_twistingSheaf_coproduct
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twistingSheaf : ℤ → (Proj 𝒜).Modules) :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ twistingSheaf (d j)) ⟶ ℱ), Epi π := sorry

/-- Lemma 30.14.2 (3): every cohomology group of a coherent sheaf on `Proj(A)` is finite as an
`A₀`-module, for the source-induced `A₀`-module structure on cohomology. -/
@[stacks 0AG6]
theorem projCoherentSheafCohomology_finite
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent] (i : ℕ)
    [Module (𝒜 0) (projCoherentSheafCohomology 𝒜 ℱ i)] :
    Module.Finite (𝒜 0) (projCoherentSheafCohomology 𝒜 ℱ i) := sorry

/-- Lemma 30.14.2 (4): positive-degree cohomology of sufficiently positive twists of a coherent
sheaf on `Proj(A)` vanishes. The family `twist` is the chosen owner of `\mathcal F(d)`. -/
@[stacks 0AG6]
theorem projCoherentSheafTwistCohomology_eventually_isZero
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twist : ℤ → (Proj 𝒜).Modules) (i : ℕ) (hi : 0 < i) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (projCoherentSheafCohomology 𝒜 (twist d) i) := sorry

/-- Lemma 30.14.2 (5): for every integer `k`, the truncated graded module
`\bigoplus_{d \ge k} H^0(Proj(A), \mathcal F(d))` is finite over `A`, for the source-induced
graded `A`-module structure. The family `twist` is the chosen owner of `\mathcal F(d)`. -/
@[stacks 0AG6]
theorem projCoherentSheafTruncatedGlobalSections_finite
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twist : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    [Module A (projCoherentSheafTruncatedGlobalSections 𝒜 twist k)] :
    Module.Finite A (projCoherentSheafTruncatedGlobalSections 𝒜 twist k) := sorry

end

end AlgebraicGeometry
