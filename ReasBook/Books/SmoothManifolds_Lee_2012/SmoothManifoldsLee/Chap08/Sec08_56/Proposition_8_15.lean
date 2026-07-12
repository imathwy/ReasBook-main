import SmoothManifolds_Lee_2012.Chap03.Sec03_20.Problem_3_7
import SmoothManifolds_Lee_2012.Chap08.Sec08_56.Notation_8_56_extra_3
import SmoothManifolds_Lee_2012.Chap08.Sec08_56.Proposition_8_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯
local notation "SmoothDerivation" => Derivation ℝ SmoothFunction SmoothFunction
local notation "SmoothVectorField" => Cₛ^∞⟮I; E, TangentSpace I⟯

-- Domain sampling pass:
-- * primary domain: smooth vector fields and derivations of the algebra of smooth functions;
-- * source-facing layer: every smooth derivation of `C^∞(M)` is induced by a smooth vector field;
-- * core/canonical owner: `ContMDiffSection.toDerivation`;
-- * bridge/view owners inspected in the local chapter/project API:
--   `Derivation.evalAt`, `smooth_germ_derivation_at.toTangentSpace`, and
--   `roughVectorField_smooth_iff_forall_smooth_apply_smooth`;
-- * owner abstraction choice: the main proposition should be surjectivity of
--   `ContMDiffSection.toDerivation`, while the pointwise tangent-vector reconstruction and the
--   smoothness criterion remain derived bridge steps.
-- Primitive data is only a global derivation `D : SmoothDerivation`; the pointwise tangent vector
-- at `p` is derived from `Derivation.evalAt p D` via
-- `smooth_germ_derivation_at.toTangentSpace`, and smoothness of the resulting rough field is
-- derived from Proposition 8.14. This owner chain is currently formalized only under
-- `[T2Space M] [SigmaCompactSpace M]`, so those hypotheses belong in the public statement.

/-- Proposition 8.15. In the chapter's finite-dimensional Hausdorff sigma-compact manifold setting,
a linear operator on `C^∞(M)` is a derivation if and only if it is given by applying some smooth
vector field to smooth functions. In owner form, the canonical bridge
`ContMDiffSection.toDerivation` from smooth vector fields to derivations of `C^∞(M)` is
surjective. -/
theorem smoothVectorField_toDerivation_surjective :
    Function.Surjective (ContMDiffSection.toDerivation : SmoothVectorField → SmoothDerivation) := by
  intro D
  sorry

/-- Proposition 8.15. In the same formal manifold setting, every derivation of `C^∞(M)` is the
derivation induced by some smooth vector field. -/
theorem exists_smoothVectorField_eq_derivation (D : SmoothDerivation) :
    ∃ X : SmoothVectorField, D = X.toDerivation := by
  rcases smoothVectorField_toDerivation_surjective D with ⟨X, hX⟩
  exact ⟨X, hX.symm⟩

end
