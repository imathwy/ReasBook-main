import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Corollary_8_38
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Definition_8_60_extra_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

universe uH uE uG

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

local instance : LieGroup I (minSmoothness ℝ 3) G := LieGroup.of_le le_top

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯
local notation "LeftInvariantSmoothVectorField" =>
  (smooth_left_invariant_vector_fields.toSubmodule : Submodule ℝ SmoothVectorField)

-- Domain sampling / source-core-bridge triage:
-- * source-facing layer: the real vector space of smooth left-invariant vector fields on `G`;
-- * core/canonical owner: `GroupLieAlgebra I G`;
-- * bridge/view sampled here and upstream in the chapter: `mulInvariantVectorField`, written
--   `vᴸ`, together with the source-facing `Submodule` view of
--   `smooth_left_invariant_vector_fields`.
-- Primitive data is the identity tangent fiber `GroupLieAlgebra I G = TₑG`; the smooth
-- left-invariant Lie-subalgebra structure from Example 8.36 is derived API, while Theorem 8.37
-- only uses the vector-space carrier.

/-- The canonical smooth left-invariant vector field associated to a tangent vector at the
identity. -/
noncomputable def smoothMulInvariantVectorField
    (v : GroupLieAlgebra I G) : LeftInvariantSmoothVectorField := by
  have hvL : VectorField.IsLeftInvariant vᴸ := by
    intro g
    simpa using mpullback_mulInvariantVectorField g v
  exact ⟨⟨vᴸ, by simpa using contMDiff_mulInvariantVectorField v⟩, hvL⟩

/-- Theorem 8.37 (1): the evaluation map sending a smooth left-invariant vector field on a Lie
group `G` to its value at the identity is a real vector-space isomorphism onto the canonical owner
`Lie(G) = GroupLieAlgebra I G = TₑG`. -/
noncomputable def lie_algebra_evaluation_at_identity :
    LeftInvariantSmoothVectorField ≃ₗ[ℝ] GroupLieAlgebra I G :=
  { toFun := fun X ↦ X.1 1
    invFun := smoothMulInvariantVectorField
    map_add' := by
      intro X Y
      rfl
    map_smul' := by
      intro c X
      rfl
    left_inv := by
      intro X
      apply Subtype.ext
      ext g
      exact congrFun
        (left_invariant_rough_vector_field_eq_mulInvariantVectorField
          (X.1 : Π g : G, TangentSpace I g) X.2).symm g
    right_inv := by
      intro v
      change vᴸ 1 = v
      simpa [mulInvariantVectorField] }

/-- Applying `lie_algebra_evaluation_at_identity` to a left-invariant smooth vector field returns
its value at the identity. -/
theorem lie_algebra_evaluation_at_identity_apply
    (X : LeftInvariantSmoothVectorField) :
    lie_algebra_evaluation_at_identity X = X.1 1 :=
  rfl

/-- Theorem 8.37 (2): the Lie algebra of a Lie group, viewed as the space of smooth left-invariant
vector fields, is finite-dimensional over `ℝ`. -/
theorem lie_algebra_finiteDimensional [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ LeftInvariantSmoothVectorField := by
  haveI : FiniteDimensional ℝ (GroupLieAlgebra I G) := by
    simpa [GroupLieAlgebra] using (inferInstance : FiniteDimensional ℝ E)
  exact lie_algebra_evaluation_at_identity.symm.finiteDimensional

/-- Theorem 8.37 (3): the dimension of the space of smooth left-invariant vector fields on `G`
equals the dimension of the manifold model space of `G`, i.e. `dim G`. -/
theorem lie_algebra_finrank_eq_manifold_finrank [FiniteDimensional ℝ E] :
    Module.finrank ℝ LeftInvariantSmoothVectorField = Module.finrank ℝ E := by
  haveI : FiniteDimensional ℝ (GroupLieAlgebra I G) := by
    simpa [GroupLieAlgebra] using (inferInstance : FiniteDimensional ℝ E)
  calc
    Module.finrank ℝ LeftInvariantSmoothVectorField
        = Module.finrank ℝ (GroupLieAlgebra I G) :=
      lie_algebra_evaluation_at_identity.finrank_eq
    _ = Module.finrank ℝ E := by
      simp [GroupLieAlgebra]
