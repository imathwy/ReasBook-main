import Mathlib
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open Metric Set
open scoped Topology

-- Proof sketch: combine `hess` with the punctured-disc analyticity hypothesis to place `f` in the
-- isolated essential-singularity setting at `o`, then apply the Great Picard theorem to conclude
-- that the image of the punctured disc omits at most one complex value.
/-- Theorem III.4-extra-9: if `o` is an isolated essential singularity of `f`, then the image of
any punctured disc around `o` on which `f` is holomorphic is either all of `ℂ`, or `ℂ` with one
point missing. -/
theorem punctured_ball_image_eq_univ_or_compl_singleton_of_essential_singularity
    {f : ℂ → ℂ} {o : ℂ} {ε : ℝ}
    (hess : HasEssentialSingularityAt f o) (hε : 0 < ε)
    (h_analytic : AnalyticOnNhd ℂ f (ball o ε \ ({o} : Set ℂ))) :
    f '' (ball o ε \ ({o} : Set ℂ)) = univ ∨
      ∃ a : ℂ, f '' (ball o ε \ ({o} : Set ℂ)) = ({a} : Set ℂ)ᶜ := sorry
