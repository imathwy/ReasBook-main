import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_3 (from Chap03/Sec03_13) -/
noncomputable section

open scoped ContDiff Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so this
-- file uses local repository precedent plus mathlib inspection of `Basis.map`,
-- `EuclideanSpace.basisFun`, and `LinearEquiv.finrank_eq`.

variable {n : ℕ}

local notation "R^n" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "SmoothRn" => C^∞⟮I, EuclideanSpace ℝ (Fin n); ℝ⟯

/-- The derivation `∂/∂xⁱ|ₐ` on smooth functions on `ℝ^n`, realized as directional
differentiation in the `i`-th standard basis direction. -/
def coordinate_point_derivation (a : R^n) (i : Fin n) : PointDerivation I a :=
  directional_point_derivation a (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Evaluating `coordinate_point_derivation a i` differentiates in the `i`-th coordinate
direction. -/
theorem coordinate_point_derivation_apply (a : R^n) (i : Fin n) (f : SmoothRn) :
    coordinate_point_derivation a i f =
      fderiv ℝ f a (EuclideanSpace.basisFun (Fin n) ℝ i) := sorry

/-- Corollary 3.3 (1): for any `a ∈ ℝ^n`, the coordinate derivations
`∂/∂x¹|ₐ, …, ∂/∂xⁿ|ₐ` form a basis of `T_aℝ^n`. -/
noncomputable def coordinate_point_derivation_basis (a : R^n) :
    Module.Basis (Fin n) ℝ (PointDerivation I a) :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).map
    (geometric_to_point_derivation_linear_equiv a)

/-- The `i`-th vector of `coordinate_point_derivation_basis a` is the derivation
`∂/∂xⁱ|ₐ`. -/
theorem coordinate_point_derivation_basis_apply (a : R^n) (i : Fin n) :
    coordinate_point_derivation_basis a i = coordinate_point_derivation a i := sorry

/-- Corollary 3.3 (2): for any `a ∈ ℝ^n`, the tangent space `T_aℝ^n` has dimension `n`. -/
theorem point_derivation_finrank_eq (a : R^n) :
    Module.finrank ℝ (PointDerivation I a) = n := sorry

/-! ### Problem_3_3 (from Chap03/Sec03_20) -/
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (I' : ModelWithCorners 𝕜 E' H')
variable (M' : Type uM') [TopologicalSpace M'] [ChartedSpace H' M']

/- Problem 3-3 (1): the canonical equivalence between the tangent bundle of a product manifold
and the product of the tangent bundles is `equivTangentBundleProd`. -/
recall equivTangentBundleProd :
    TangentBundle (I.prod I') (M × M') ≃ TangentBundle I M × TangentBundle I' M'

/- Problem 3-3 (2): the canonical equivalence `equivTangentBundleProd` is smooth. -/
recall contMDiff_equivTangentBundleProd

/- Problem 3-3 (3): the inverse of `equivTangentBundleProd` is smooth. -/
recall contMDiff_equivTangentBundleProd_symm

/- The pointwise formula is already the canonical `@[simps]` lemma attached to
`equivTangentBundleProd`; this is a bridge/view recall rather than a new local owner. -/
recall equivTangentBundleProd_apply (p : TangentBundle (I.prod I') (M × M')) :
    equivTangentBundleProd I M I' M' p = (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
