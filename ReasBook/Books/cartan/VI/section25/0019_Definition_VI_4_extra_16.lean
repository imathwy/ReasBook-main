import Mathlib
import cartan.III.section11.«0003_Theorem_III_5_extra_2»

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the residue surface was verified directly against Mathlib's circle-integral notation
-- `∮ z in C(c, R), f z`.

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain sampling: the intrinsic mathlib residue owner for meromorphic functions is
`meromorphicTrailingCoeffAt`, while the chapter-local contour owner is `IsolatedLocalResidueCircle`.
The present item is `source-facing`: it keeps the textbook stronger "all sufficiently small
circles" formulation, and the companion bridge below maps it to the chapter-local one-circle owner
used downstream in the residue theorem. -/

/-- Definition VI.4-extra-16: for the local differential form `ω(z) dz`, a complex number
`residue` is the residue at the isolated point `a` when `ω` is holomorphic on a punctured
neighborhood of `a` and every sufficiently small positively oriented circle about `a` has integral
`2π i · residue`. This is the local-coordinate formulation of the textbook coefficient `c₁` of the
`dz / z` term. -/
def HasResidueAt (ω : ℂ → ℂ) (a residue : ℂ) : Prop :=
  ∃ radius > 0,
    DifferentiableOn ℂ ω (Metric.ball a radius \ ({a} : Set ℂ)) ∧
      ∀ ⦃ρ : ℝ⦄, 0 < ρ → ρ ≤ radius →
        (∮ z in C(a, ρ), ω z) = (2 * Real.pi * Complex.I : ℂ) * residue

namespace HasResidueAt

/-- Unpacking `HasResidueAt` gives an explicit punctured radius on which the small-circle integral
formula for the residue holds. -/
theorem exists_radius_spec
    {ω : ℂ → ℂ} {a residue : ℂ} (h : HasResidueAt ω a residue) :
    ∃ radius > 0,
      DifferentiableOn ℂ ω (Metric.ball a radius \ ({a} : Set ℂ)) ∧
        ∀ ⦃ρ : ℝ⦄, 0 < ρ → ρ ≤ radius →
          (∮ z in C(a, ρ), ω z) = (2 * Real.pi * Complex.I : ℂ) * residue :=
  h

/-- The source-facing residue data on a punctured neighborhood yields the chapter-local isolated
residue-circle owner in the whole-plane singleton case. -/
theorem toIsolatedLocalResidueCircle
    {ω : ℂ → ℂ} {a residue : ℂ} (h : HasResidueAt ω a residue) :
    IsolatedLocalResidueCircle (Set.univ : Set ℂ) Set.univ ({a} : Finset ℂ) ω a residue := by
  rcases h with ⟨radius, hradius, hdiff, hcircle⟩
  refine ⟨radius, hradius, ?_, ?_, ?_, hdiff, ?_⟩
  · simp
  · simp
  · intro w hw hwne hwBall
    exact hwne (by simpa [Finset.mem_singleton] using hw)
  · exact hcircle hradius le_rfl

end HasResidueAt
