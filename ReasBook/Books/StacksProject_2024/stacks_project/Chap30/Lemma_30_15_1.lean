import StacksProject_2024.stacks_project.Chap30.Lemma_30_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical `Proj` owner for a graded ring.
Local Chapter 30 precedent, especially Lemma 30.14.2, represents sheaf cohomology by
`projCoherentSheafCohomology` and uses explicit chosen families for the twist sheaves because the
project does not yet expose a canonical arbitrary-`Proj` twist-sheaf owner. -/

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]

/-- Lemma 30.15.1 (1): if `A` is a Noetherian graded ring, then `Proj(A)` is a
Noetherian scheme. -/
@[stacks 0B5Q]
theorem proj_isNoetherian_of_noetherian_gradedRing :
    IsNoetherian (Proj 𝒜) := sorry

/-- Lemma 30.15.1 (2): for a coherent sheaf on `Proj(A)`, there is a finite direct sum of
twisting sheaves mapping epimorphically onto it. The family `twistingSheaf` is the chosen owner of
the sheaves `\mathcal O_X(d)` in the current arbitrary-`Proj` model. -/
@[stacks 0B5Q]
theorem projCoherentSheaf_exists_epi_from_twistingSheaf_coproduct_of_noetherian
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twistingSheaf : ℤ → (Proj 𝒜).Modules) :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ twistingSheaf (d j)) ⟶ ℱ), Epi π := sorry

/-- Lemma 30.15.1 (3): every cohomology group of a coherent sheaf on `Proj(A)` is finite as an
`A₀`-module, for the source-induced `A₀`-module structure on cohomology. -/
@[stacks 0B5Q]
theorem projCoherentSheafCohomology_finite_of_noetherian
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent] (i : ℕ)
    [Module (𝒜 0) (projCoherentSheafCohomology 𝒜 ℱ i)] :
    Module.Finite (𝒜 0) (projCoherentSheafCohomology 𝒜 ℱ i) := sorry

/-- Lemma 30.15.1 (4): positive-degree cohomology of sufficiently positive twists of a coherent
sheaf on `Proj(A)` vanishes. The family `twist` is the chosen owner of `\mathcal F(d)`. -/
@[stacks 0B5Q]
theorem projCoherentSheafTwistCohomology_eventually_isZero_of_noetherian
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twist : ℤ → (Proj 𝒜).Modules) (i : ℕ) (hi : 0 < i) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (projCoherentSheafCohomology 𝒜 (twist d) i) := sorry

/-- Lemma 30.15.1 (5): for every integer `k`, the truncated graded module
`\bigoplus_{d \ge k} H^0(Proj(A), \mathcal F(d))` is finite over `A`, for the source-induced
graded `A`-module structure. The family `twist` is the chosen owner of `\mathcal F(d)`. -/
@[stacks 0B5Q]
theorem projCoherentSheafTruncatedGlobalSections_finite_of_noetherian
    (ℱ : (Proj 𝒜).Modules) [ℱ.IsCoherent]
    (twist : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    [Module A (projCoherentSheafTruncatedGlobalSections 𝒜 twist k)] :
    Module.Finite A (projCoherentSheafTruncatedGlobalSections 𝒜 twist k) := sorry

end

end AlgebraicGeometry
