import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` returned the canonical
`MvPolynomial.homogeneousSubmodule` API, including
`MvPolynomial.homogeneousSubmodule_mul`, for homogeneous polynomial pieces. Local Chapter 30
precedent represents `\mathbf P^n_R` as `Proj` of the standard `MvPolynomial` grading and states
the twist-cohomology identifications on the additive sheaf cohomology object `H'`. -/

/-- The standard grading on `R[T_0, \ldots, T_n]` used in the compatibility statement for
projective-space twist cohomology. -/
abbrev projectiveSpaceTwistCompatibilityGrading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard `Proj` model of `\mathbf P^n_R` used for projective-space twist compatibility. -/
abbrev projectiveSpaceTwistCompatibilityScheme (R : Type u) [CommRing R] (n : ℕ) :
    Scheme :=
  Proj (projectiveSpaceTwistCompatibilityGrading R n)

/-- The degree-`d` homogeneous piece of `R[T_0, \ldots, T_n]`, with negative degrees interpreted
as the zero submodule. -/
def projectiveSpaceTwistCompatibilityDegreePiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  if 0 ≤ d then
    projectiveSpaceTwistCompatibilityGrading R n d.toNat
  else
    ⊥

/-- In nonnegative degree, the compatibility degree piece is the usual homogeneous submodule. -/
theorem projectiveSpaceTwistCompatibilityDegreePiece_of_nonneg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    projectiveSpaceTwistCompatibilityDegreePiece R n d =
      projectiveSpaceTwistCompatibilityGrading R n d.toNat := sorry

/-- In negative degree, the compatibility degree piece is zero. -/
theorem projectiveSpaceTwistCompatibilityDegreePiece_of_neg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : ¬ 0 ≤ d) :
    projectiveSpaceTwistCompatibilityDegreePiece R n d = ⊥ := sorry

/-- The dual graded piece appearing in top cohomology of
`\mathcal O_{\mathbf P^n_R}(d)`. -/
abbrev projectiveSpaceTwistCompatibilityTopDual
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :=
  projectiveSpaceTwistCompatibilityDegreePiece R n (-((n : ℤ) + 1) - d) →ₗ[R] R

/-- The additive sheaf cohomology group of a chosen module-sheaf owner on the standard
projective space model. -/
abbrev projectiveSpaceTwistCompatibilityCohomologyGroup
    (R : Type u) [CommRing R] (n : ℕ)
    (Od : (projectiveSpaceTwistCompatibilityScheme R n).Modules) (q : ℕ) :
    AddCommGrpCat :=
  (((SheafOfModules.toSheaf (projectiveSpaceTwistCompatibilityScheme R n).ringCatSheaf).obj Od).H'
    q (⊤ : Opens (projectiveSpaceTwistCompatibilityScheme R n)))

/-- The map on additive sheaf cohomology induced by a morphism of the chosen module-sheaf
owners. -/
abbrev projectiveSpaceTwistCompatibilityCohomologyMap
    (R : Type u) [CommRing R] (n : ℕ)
    {Od Od' : (projectiveSpaceTwistCompatibilityScheme R n).Modules}
    (φ : Od ⟶ Od') (q : ℕ) :
    projectiveSpaceTwistCompatibilityCohomologyGroup R n Od q ⟶
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od' q :=
  ((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveSpaceTwistCompatibilityScheme R n)) q).map
    ((SheafOfModules.toSheaf (projectiveSpaceTwistCompatibilityScheme R n).ringCatSheaf).map
      φ)).app (op (⊤ : Opens (projectiveSpaceTwistCompatibilityScheme R n)))

/-- Homogeneous multiplication sends the selected degree piece into the shifted degree piece. -/
theorem projectiveSpaceTwistCompatibility_mul_mem_degreePiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (m : ℕ)
    (f g : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R m)
    (hg : g ∈ projectiveSpaceTwistCompatibilityDegreePiece R n d) :
    f * g ∈ projectiveSpaceTwistCompatibilityDegreePiece R n (d + (m : ℤ)) := sorry

end AlgebraicGeometry
