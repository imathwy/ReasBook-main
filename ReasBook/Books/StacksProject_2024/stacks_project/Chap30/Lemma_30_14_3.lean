import StacksProject_2024.stacks_project.Chap30.Lemma_30_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The degree-shift action of nonnegative ring degrees on integer graded-module degrees. -/
instance instNatVAddInt : VAdd ℕ ℤ where
  vadd n d := (n : ℤ) + d

/- Semantic recall: `lean_leansearch` surfaced the canonical `AlgebraicGeometry.Proj` owner and
local Chapter 30 precedent uses `projCoherentSheafCohomology` for global sections on `Proj`. The
current project does not yet expose the associated sheaf of a graded module on `Proj(A)` or the
Construction 27.10.3 comparison map as concrete declarations, so the source-facing theorem below
takes the chosen twist family `\widetilde M(n)` and the canonical comparison maps as explicit
inputs. -/

/-- Lemma 30.14.3: if `A₀` is Noetherian, the graded ring `A` is generated over `A₀` by finitely
many degree-one elements, and `M` is a finite graded `A`-module, then the canonical maps
`M_n → Γ(Proj(A), \widetilde M(n))` from Constructions, Lemma 27.10.3 are isomorphisms for all
sufficiently large `n`. The family `associatedTwist` is the chosen owner of `\widetilde M(n)`,
and `sectionMap` is the corresponding family of canonical maps. -/
@[stacks 0AG7]
theorem finiteGradedModule_projAssociatedSheaf_sectionMap_eventually_isIso
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (Mpiece : ℤ → Type u) [∀ n, AddCommGroup (Mpiece n)]
    [DirectSum.Gmodule (fun i ↦ 𝒜 i) Mpiece]
    [Module A (DirectSum ℤ Mpiece)] [Module.Finite A (DirectSum ℤ Mpiece)]
    (associatedTwist : ℤ → (Proj 𝒜).Modules)
    (sectionMap : ∀ n : ℤ,
      AddCommGrpCat.of (Mpiece n) ⟶ projCoherentSheafCohomology 𝒜 (associatedTwist n) 0) :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n → IsIso (sectionMap n) := sorry

end AlgebraicGeometry
