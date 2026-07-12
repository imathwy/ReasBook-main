import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.Sober
import StacksProject_2024.Chap29.ProjectiveSpaceBasic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/- Semantic recall / owner check:
`lean_leansearch` surfaced the canonical projective-spectrum vanishing-ideal API and the scheme
closed-subscheme owner `Scheme.IdealSheafData.subscheme`. Local Chapter 31 precedent
(`Example_31_31_2`) keeps the currently-unpackaged operation `Z ↦ I(Z)` as an explicit parameter.
The no-embedded-points predicate is likewise passed as the source-facing condition on `Z`, while
the codimension-one condition is stated directly at generic points of irreducible components. -/

/-- Lemma 31.31.3: let `R` be a Noetherian UFD and let `Z ⊆ \mathbf P^n_R` be a closed subscheme
with no embedded points such that every irreducible component of `Z` has codimension `1` in
`\mathbf P^n_R`. Then the homogeneous ideal `I(Z) ⊆ R[T_0,\ldots,T_n]` corresponding to `Z` is
principal.

The parameter `projectiveSpaceClosedSubschemeIdeal` represents the current project surface for
the homogeneous ideal `I(Z)`, and `hasNoEmbeddedPoints` represents the source no-embedded-points
condition on closed subschemes of projective space. -/
@[stacks 0BXL]
theorem projectiveSpace_closedSubschemeIdeal_isPrincipal_of_noEmbeddedPoints_codimOne
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] (n : ℕ)
    (Z : (projectiveSpace R n).IdealSheafData)
    (projectiveSpaceClosedSubschemeIdeal :
      (projectiveSpace R n).IdealSheafData → Ideal (MvPolynomial (Fin (n + 1)) R))
    (hasNoEmbeddedPoints : (projectiveSpace R n).IdealSheafData → Prop)
    (hnoEmbedded : hasNoEmbeddedPoints Z)
    (hcodimOne :
      ∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
        ringKrullDim ((projectiveSpace R n).presheaf.stalk (Z.subschemeι.base ξ)) = 1) :
    (projectiveSpaceClosedSubschemeIdeal Z).IsPrincipal := sorry

end AlgebraicGeometry
