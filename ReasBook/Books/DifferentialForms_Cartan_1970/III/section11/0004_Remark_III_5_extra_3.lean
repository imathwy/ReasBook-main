import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-
This remark is a `bridge/view`: its source content is the residue sum on the Riemann sphere, while
the chapter's residue owner is the compact oriented-boundary theorem on a closed disc. The finite
residue data is therefore stated on one explicit enclosing disc `Metric.closedBall 0 R`, and the
residue at infinity is recorded by the chapter's global owner `ResidueAtInfinityCircleEq`, whose
threshold radius guarantees the contour formula on every sufficiently large circle. For rational
functions, the residue owner stays the core/canonical `meromorphicTrailingCoeffAt`, and the
rational theorem below is only a specialization of the generic bridge theorem.
-/

/-- Remark III.5-extra-3 (1): if `f` is holomorphic away from the finite set `s`, and if the
finite residues are realized on the closed disc `Metric.closedBall 0 R` by the chapter's canonical
local residue-circle owner, while the chapter's canonical residue-at-infinity owner holds on all
sufficiently large circles, then the sum of the finite residues together with the residue at
infinity is zero. -/
theorem sum_residue_at_add_residue_at_infinity_eq_zero_of_holomorphic_off_finite_set
    (f : ℂ → ℂ) (s : Finset ℂ) (residue : ℂ → ℂ) (residueAtInfinity : ℂ) (R : ℝ)
    (hhol : DifferentiableOn ℂ f (↑s : Set ℂ)ᶜ)
    (hres :
      ∀ z ∈ s, LocalResidueCircle (Metric.closedBall 0 R) Set.univ f z (residue z))
    (hres_infty : ResidueAtInfinityCircleEq f residueAtInfinity) :
    s.sum residue + residueAtInfinity = 0 := sorry

section Rational

variable (p q : Polynomial ℂ)

local notation "f" => fun w : ℂ ↦ p.eval w / q.eval w

/-- Remark III.5-extra-3 (2): for a rational function, the sum of the canonical finite residues
together with the residue at infinity is zero provided `s` is exactly its finite pole set and the
finite residues are recorded on the chosen closed disc `Metric.closedBall 0 R` by the chapter's
canonical local residue-circle owner specialized to `meromorphicTrailingCoeffAt`, while the
residue at infinity is supplied by the chapter's global owner `ResidueAtInfinityCircleEq` on all
sufficiently large circles. -/
theorem sum_meromorphicTrailingCoeffAt_add_residue_at_infinity_eq_zero_of_rational
    (s : Finset ℂ) (residueAtInfinity : ℂ) (R : ℝ)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hres :
      ∀ z ∈ s,
        LocalResidueCircle
          (Metric.closedBall 0 R)
          Set.univ
          f
          z
          (meromorphicTrailingCoeffAt f z))
    (hres_infty : ResidueAtInfinityCircleEq f residueAtInfinity) :
    s.sum (meromorphicTrailingCoeffAt f) + residueAtInfinity = 0 := by
  have hhol : DifferentiableOn ℂ f (↑s : Set ℂ)ᶜ := by
    sorry
  exact
    sum_residue_at_add_residue_at_infinity_eq_zero_of_holomorphic_off_finite_set
      f s (meromorphicTrailingCoeffAt f) residueAtInfinity R hhol hres hres_infty

end Rational
