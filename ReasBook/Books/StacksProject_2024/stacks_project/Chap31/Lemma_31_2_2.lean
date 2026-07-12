import Mathlib
import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the affine-local localization/stalk API around
-- `IsAffineOpen.fromSpec` and associated primes. Local Chapter 31 precedent already fixes the
-- affine-point correspondence as `hU.fromSpec p`, while the source-facing owner on sections is
-- `associatedPrimesOfModule` and the sheaf-side owner is `associatedPoints`.

/-- Lemma 31.2.2 (1): for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`,
an affine open `U ⊆ X`, and a prime `\mathfrak p` of the affine section ring `Γ(X, U)`, if
`\mathfrak p` is associated to the section module `Γ(U, \mathcal F)`, then the corresponding
point of `U` is an associated point of `\mathcal F`. -/
@[stacks 02OK]
theorem mem_associatedPoints_of_mem_associatedPrimesOfModule_sections
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hp : p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U))) :
    hU.fromSpec p ∈ associatedPoints ℱ := sorry

/-- Lemma 31.2.2 (2): with the same affine setup, if the corresponding point of `U` is
associated to `\mathcal F` and `\mathfrak p` is finitely generated, then `\mathfrak p` is
associated to the section module `Γ(U, \mathcal F)`. -/
@[stacks 02OK]
theorem mem_associatedPrimesOfModule_sections_of_mem_associatedPoints_of_fg
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hx : hU.fromSpec p ∈ associatedPoints ℱ) (hfg : p.asIdeal.FG) :
    p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- Lemma 31.2.2 (3): if `X` is locally Noetherian, then for every affine open `U ⊆ X` and every
prime `\mathfrak p` of the affine section ring `Γ(X, U)`, the prime `\mathfrak p` is associated
to `Γ(U, \mathcal F)` if and only if the corresponding point of `U` is an associated point of
`\mathcal F`. -/
@[stacks 02OK]
theorem mem_associatedPrimesOfModule_sections_iff_fromSpec_mem_associatedPoints_of_isLocallyNoetherian
    {U : X.Opens} (hU : IsAffineOpen U) [IsLocallyNoetherian X] (p : PrimeSpectrum (Γ(X, U))) :
    p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ associatedPoints ℱ := sorry

/-- Pointwise affine form of Lemma 31.2.2 (1), using the associated-prime predicate on the section
module instead of set membership. -/
theorem fromSpec_mem_associatedPoints_of_isAssociatedToModule_sections
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hp : Ideal.IsAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal) :
    hU.fromSpec p ∈ associatedPoints ℱ := by
  exact mem_associatedPoints_of_mem_associatedPrimesOfModule_sections ℱ hU p <|
    by simpa [mem_associatedPrimesOfModule_iff] using hp

/-- Pointwise affine form of Lemma 31.2.2 (2), using the associated-prime predicate on the section
module instead of set membership. -/
theorem isAssociatedToModule_sections_of_fromSpec_mem_associatedPoints_of_fg
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U)))
    (hx : hU.fromSpec p ∈ associatedPoints ℱ) (hfg : p.asIdeal.FG) :
    Ideal.IsAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal := by
  simpa [mem_associatedPrimesOfModule_iff] using
    mem_associatedPrimesOfModule_sections_of_mem_associatedPoints_of_fg ℱ hU p hx hfg

/-- Pointwise affine form of Lemma 31.2.2 (3), using the associated-prime predicate on the section
module instead of set membership. -/
theorem isAssociatedToModule_sections_iff_fromSpec_mem_associatedPoints_of_isLocallyNoetherian
    {U : X.Opens} (hU : IsAffineOpen U) [IsLocallyNoetherian X] (p : PrimeSpectrum (Γ(X, U))) :
    Ideal.IsAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal ↔
      hU.fromSpec p ∈ associatedPoints ℱ := by
  simpa [mem_associatedPrimesOfModule_iff] using
    mem_associatedPrimesOfModule_sections_iff_fromSpec_mem_associatedPoints_of_isLocallyNoetherian
      ℱ hU p

end AlgebraicGeometry.Scheme.Modules
