import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the affine-open owner `IsAffineOpen`, the affine
-- morphism bridge `isAffineHom_of_isAffine_of_isSeparated`, and the absolute separated owner
-- `Scheme.IsSeparated`. Nearby Section 31.16 precedent already fixes the generic-point encoding on
-- the closed complement via `irreducibleComponents { x : X // x ∉ (U : Set X) }`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]

/-- Lemma 31.16.5 (1): let `X` be a separated locally Noetherian scheme and let `U ⊆ X` be an
affine open. For every generic point `ξ` of an irreducible component of the closed complement
`X \ U`, the local ring `\mathcal O_{X,\xi}` has Krull dimension at most `1`. -/
@[stacks 0BCV]
theorem ringKrullDim_stalk_le_one_of_affineOpenComplement_genericPoint_of_isSeparated
    {U : X.Opens} (hU : IsAffineOpen U) {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) })) :
    ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1 := sorry

/-- Lemma 31.16.5 (2): with the same hypotheses, if the generic point `ξ` of an irreducible
component of `X \ U` lies in the closure of `U`, then `\dim(\mathcal O_{X,\xi}) = 1`. -/
@[stacks 0BCV]
theorem ringKrullDim_stalk_eq_one_of_affineOpenComplement_genericPoint_of_mem_closure_of_isSeparated
    {U : X.Opens} (hU : IsAffineOpen U) {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) }))
    (hξ_closure : ξ.1 ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

/-- Lemma 31.16.5 (3): with the same hypotheses, if the affine open `U` is dense in `X`, then
the local ring at every generic point of an irreducible component of `X \ U` has dimension `1`. -/
@[stacks 0BCV]
theorem ringKrullDim_stalk_eq_one_of_affineOpenComplement_genericPoint_of_dense_of_isSeparated
    {U : X.Opens} (hU : IsAffineOpen U) {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ∃ Z : irreducibleComponents { x : X // x ∉ (U : Set X) },
      IsGenericPoint ξ (Z : Set { x : X // x ∉ (U : Set X) }))
    (hU_dense : Dense (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

end AlgebraicGeometry.Scheme
