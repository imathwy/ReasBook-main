import Mathlib
import stacks_project.Chap10.Definition_10_136_5
import stacks_project.Chap10.Definition_10_137_10
import stacks_project.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

open Presentation

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

section

variable (f : Fin c → MvPolynomial (Fin n) R)

/- Domain-style sampling:
- primary domain: Jacobian criteria for smoothness of explicit polynomial-quotient presentations of
  relative global complete intersections;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.Presentation.naive`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`;
- best owner abstraction: the public source-facing smoothness owner in this chapter is
  `Algebra.SmoothAtPrime`, while the presentation-theoretic primitive data for the displayed
  quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` already live on the canonical owner
  `Algebra.Presentation`; the Jacobian-minor criterion should therefore be exposed as a theorem
  about `SmoothAtPrime`, with `IsSmoothAt` used only as the internal bridge;
- primitive vs. derived:
  the primitive source-facing data are the relations `f` and the induced naive presentation of the
  quotient; the quotient type and the Jacobian minors are derived owner API coming from
  `Algebra.Presentation`, and `IsSmoothAt` is derived bridge API coming from
  `smoothAtPrime_iff_isSmoothAt`.

Source/core/bridge triage:
- `source-facing`: Lemma `10.137.15`, the Jacobian criterion for smoothness at a prime of the
  explicit quotient, stated using `SmoothAtPrime`;
- `core/canonical`: `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`, and `IsSmoothAt`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt`, which passes between the source-facing smoothness
  predicate and the canonical local owner.
-/

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal

/-- Lemma 10.137.15: for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` with `c ≤ n` and a prime `q` of `S`, the map `R → S` is smooth
at `q` in the source-facing Stacks sense if and only if some Jacobian minor
`det(∂f_j / ∂x_i)` indexed by a `c`-element subset of the variables avoids `q`. -/
theorem smoothAtPrime_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    SmoothAtPrime R PresentedAlgebra q ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := sorry

-- Proof sketch: use Lemma `10.136.12` to identify the naive cotangent complex of the quotient
-- presentation with the Jacobian matrix `(∂f_j/∂x_i)`. By Lemma `10.134.13`, smoothness at `q`
-- is equivalent to the localized conormal map becoming split injective. For a map between free
-- modules of ranks `c` and `n`, this happens exactly when some `c × c` minor is invertible in the
-- localization at `q`, i.e. when one Jacobian minor avoids `q`.
/-- Companion bridge for Lemma `10.137.15`: for the canonical naive presentation
`R[x₁, …, xₙ] / (f₁, …, f_c)`, formal smoothness at `q` is equivalent to the existence of a
Jacobian minor indexed by a `c`-element subset of the variables whose image in the quotient avoids
`q`. -/
theorem isSmoothAt_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    IsSmoothAt R q.asIdeal ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := by
  let _ : FinitePresentation R PresentedAlgebra :=
    Presentation.finitePresentation_of_isFinite
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
  rw [← smoothAtPrime_iff_isSmoothAt R PresentedAlgebra q]
  exact smoothAtPrime_iff_exists_jacobian_minor_not_mem f hc hP q

end

end Algebra
