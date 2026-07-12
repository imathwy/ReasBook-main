import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: no semantic Lean search MCP tool was available in this environment, so the
-- owner/API choice was verified locally against the existing project use of `IsAffineHom U.ι`,
-- `irreducibleComponents`, `IsGenericPoint`, `closure (U : Set X)`, and
-- `ringKrullDim (X.presheaf.stalk x)`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 31.16.4 (1): let `X` be a locally Noetherian scheme and let `U ⊆ X` be an open
subscheme whose inclusion `U ⟶ X` is affine. If `ξ` is a generic point of an irreducible
component of the closed complement `X \ U`, viewed as a point of the subspace `((U : Set X)ᶜ)`,
then the local ring `\mathcal O_{X,\xi}` has Krull dimension at most `1`. -/
@[stacks 0BCU]
theorem ringKrullDim_stalk_le_one_of_affineOpenComplement_genericPoint
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) })) :
    ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1 := sorry

/-- Lemma 31.16.4 (2): with the same hypotheses, if the generic point `ξ` of an irreducible
component of `X \ U` lies in the closure of `U`, then the local ring `\mathcal O_{X,\xi}` has
Krull dimension exactly `1`. -/
@[stacks 0BCU]
theorem ringKrullDim_stalk_eq_one_of_affineOpenComplement_genericPoint_of_mem_closure
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) }))
    (hξ_closure : ξ.1 ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

/-- If the affine open `U` is dense, then every generic point of an irreducible component of the
closed complement `X \ U` satisfies the conclusion of
`ringKrullDim_stalk_eq_one_of_affineOpenComplement_genericPoint_of_mem_closure`. -/
theorem ringKrullDim_stalk_eq_one_of_affineOpenComplement_genericPoint_of_dense
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) }))
    (hU_dense : Dense (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

end AlgebraicGeometry.Scheme
