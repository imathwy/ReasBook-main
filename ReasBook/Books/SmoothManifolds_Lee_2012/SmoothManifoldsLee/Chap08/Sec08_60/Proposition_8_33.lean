import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Corollary_8_38
import SmoothManifolds_Lee_2012.Chap08.Sec08_59.Proposition_8_30

open scoped ContDiff Manifold
open VectorField

noncomputable section

section

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

-- Domain sampling pass:
-- * primary domain: left-invariant vector fields on Lie groups and the manifold Lie bracket;
-- * source-facing owner: `IsLeftInvariant`;
-- * core/canonical owner for left-invariant fields: `mulInvariantVectorField`;
-- * core/canonical bracket owner: `mlieBracket`, exposed via `⁅X, Y⁆`;
-- * derived API used here: `isLeftInvariant_iff_mfderiv`,
--   `left_invariant_rough_vector_field_smooth`,
--   and `f_related_mlieBracket`.
-- Primitive data is only the vector fields `X` and `Y`; smoothness is derived from the owner
-- abstraction for left-invariant fields, so it should not remain primitive public data here.

/-- Proposition 8.33: Let `G` be a Lie group, and suppose `X` and `Y` are smooth left-invariant
vector fields on `G`. Then `[X, Y]` is also left-invariant. -/
theorem isLeftInvariant_mlieBracket
    {X Y : ∀ g : G, TangentSpace I g}
    (hX_left_invariant : IsLeftInvariant X)
    (hY_left_invariant : IsLeftInvariant Y) :
    IsLeftInvariant ⁅X, Y⁆ := by
  have hX_smooth : ContMDiff I I.tangent ∞ (T% X) :=
    left_invariant_rough_vector_field_smooth X hX_left_invariant
  have hY_smooth : ContMDiff I I.tangent ∞ (T% Y) :=
    left_invariant_rough_vector_field_smooth Y hY_left_invariant
  rw [isLeftInvariant_iff_mfderiv]
  intro g g'
  have hX_related : f_related (g * ·) X X := by
    exact ⟨contMDiff_mul_left, (isLeftInvariant_iff_mfderiv X).1 hX_left_invariant g⟩
  have hY_related : f_related (g * ·) Y Y := by
    exact ⟨contMDiff_mul_left, (isLeftInvariant_iff_mfderiv Y).1 hY_left_invariant g⟩
  exact (f_related_mlieBracket hX_smooth hY_smooth hX_smooth hY_smooth
    hX_related hY_related).2 g'

end
