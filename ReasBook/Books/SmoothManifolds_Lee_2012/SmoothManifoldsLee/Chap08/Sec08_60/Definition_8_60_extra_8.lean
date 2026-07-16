import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Example_8_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

universe uH uE uG

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯

-- Domain sampling / source-core-bridge triage:
-- * source-facing item: the real vector-subspace of smooth left-invariant vector fields on `G`;
-- * core/canonical owner in the chapter: `smooth_left_invariant_vector_fields`;
-- * bridge/view used here: its canonical `Submodule` view.
-- Primitive data stays with the Lie-subalgebra owner from Example 8.36; the subspace statement
-- is derived API via the canonical forgetful map to `Submodule`.

/-
Definition 8.60-extra-8: the smooth left-invariant vector fields on a Lie group form a real
subspace of the bundled smooth vector fields. This is the canonical `Submodule` view of the
chapter owner `smooth_left_invariant_vector_fields`.
-/
#check (smooth_left_invariant_vector_fields.toSubmodule : Submodule ℝ SmoothVectorField)
