import Mathlib
import StacksProject_2024.Chap13.Lemma_13_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex
open HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

noncomputable section

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
variable {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes and their behavior under exact additive
--   functors between abelian categories.
-- * inspected owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `CochainComplex.IsKInjective.homotopyZero`,
--   `Adjunction.homotopy_mapHomologicalComplex_homEquiv`,
--   `Functor.mapHomologicalComplex`,
--   `Adjunction.mapHomologicalComplex`.
-- * layer: `source-facing`; the statement is genuinely about preservation of K-injectivity under a
--   right adjoint, not about introducing a new wrapper around complexes.
-- * core/canonical owner abstraction: `I.IsKInjective` for the mapped complex
--   `((u.mapHomologicalComplex (up ℤ)).obj I)`.
-- * primitive data: the adjunction `v ⊣ u` and exactness of `v`; additivity is derived from
--   these owner hypotheses and should not remain as redundant public input.
-- * derived API: K-injectivity of the image of `I` under `u.mapHomologicalComplex`.

private theorem mapHomologicalComplex_acyclic_of_exact
    (v : ℬ ⥤ 𝒜) (hv : exactFunctor ℬ 𝒜 v)
    (M : CochainComplex ℬ ℤ) (hM : M.Acyclic) :
    by
      letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
      exact ((v.mapHomologicalComplex (up ℤ)).obj M).Acyclic := by
  letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
  let hExact := (exactFunctor_iff v).1 hv
  letI : Limits.PreservesFiniteLimits v := hExact.1
  letI : Limits.PreservesFiniteColimits v := hExact.2
  letI : v.PreservesHomology := inferInstance
  rw [HomologicalComplex.acyclic_iff] at hM ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff]
  have hMn : (M.sc n).Exact := by
    simpa [HomologicalComplex.exactAt_iff] using hM n
  simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
    hMn.map v

-- Proof sketch: let `M` be an acyclic complex of `ℬ`. Exactness of the left adjoint `v` sends
-- `M` to an acyclic complex of `𝒜`. The adjunction `v ⊣ u` induces an identification
-- `Hom_K(v(M), I) ≃ Hom_K(M, u(I))`, and the left-hand side vanishes because `I` is
-- K-injective.
/-- Lemma 13.31.9: if `u : \mathcal A ⥤ \mathcal B` is right adjoint to an exact functor
`v : \mathcal B ⥤ \mathcal A`, then the image of a K-injective cochain complex under `u`
is again K-injective. In abelian categories, the needed additivity of `u` and `v` is derived
internally from exactness and the adjunction. -/
theorem right_adjoint_preserves_isKInjective_of_exact_left_adjoint
    (u : 𝒜 ⥤ ℬ) (v : ℬ ⥤ 𝒜) (adj : v ⊣ u) (hv : exactFunctor ℬ 𝒜 v)
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    by
      letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
      letI : u.Additive := adj.right_adjoint_additive
      exact CochainComplex.IsKInjective ((u.mapHomologicalComplex (up ℤ)).obj I) := by
  letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
  letI : u.Additive := adj.right_adjoint_additive
  let uC := u.mapHomologicalComplex (up ℤ)
  let vC := v.mapHomologicalComplex (up ℤ)
  let adjC := adj.mapHomologicalComplex (up ℤ)
  refine ⟨fun {M} f hM ↦ ?_⟩
  let f' := (adjC.homEquiv M I).symm f
  have hM' : (vC.obj M).Acyclic :=
    mapHomologicalComplex_acyclic_of_exact v hv M hM
  refine ⟨?_⟩
  simpa [uC, vC, adjC, f'] using
    adj.homotopy_mapHomologicalComplex_homEquiv (up ℤ) (IsKInjective.homotopyZero f' hM')

end

end

end CategoryTheory
