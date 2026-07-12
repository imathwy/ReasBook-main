import SmoothManifolds_Lee_2012.Chap08.Sec08_58.Proposition_8_23
import SmoothManifolds_Lee_2012.Chap08.Sec08_59.Proposition_8_30

open scoped ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uE' uH uH' uM

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I ∞ M]
  {S : Set M} [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

-- Domain sampling pass:
-- * primary domain: smooth vector fields tangent to an immersed submanifold and closure under the
--   manifold Lie bracket;
-- * source-facing tangency owner sampled upstream: `VectorField.IsTangentToSubmanifold`;
-- * source-facing restriction bridge sampled upstream: `existsUnique_restriction_to_submanifold`;
-- * core/canonical bracket owner sampled upstream: `VectorField.mlieBracket`, which already
--   accepts bundled smooth vector fields through the section coercion, so no local wrapper bracket
--   API is needed here.
-- The primitive smooth data here are bundled smooth vector fields; tangency and `f_related`
-- remain derived predicates over those owners.

local notation "SmoothVectorFieldOnM" => Cₛ^∞⟮I; E, TangentSpace I⟯
local notation "SmoothVectorFieldOnS" => Cₛ^∞⟮J; E', TangentSpace J⟯

/-- Corollary 8.32 (Brackets of Vector Fields Tangent to Submanifolds): let `M` be a smooth
manifold and let `S` be an immersed submanifold with or without boundary in `M`. If `Y₁` and `Y₂`
are smooth vector fields on `M` that are tangent to `S`, then `[Y₁, Y₂]` is also tangent to
`S`. -/
theorem isTangentToSubmanifold_mlieBracket
    (hS : IsImmersedSubmanifold I J S)
    (Y₁ Y₂ : SmoothVectorFieldOnM)
    (hY₁_tangent : IsTangentToSubmanifold S J Y₁)
    (hY₂_tangent : IsTangentToSubmanifold S J Y₂) :
    IsTangentToSubmanifold S J (VectorField.mlieBracket I Y₁ Y₂) := by
  rcases existsUnique_restriction_to_submanifold hS Y₁ hY₁_tangent with ⟨X₁, hX₁_related, -⟩
  rcases existsUnique_restriction_to_submanifold hS Y₂ hY₂_tangent with ⟨X₂, hX₂_related, -⟩
  have hBracket_related :
      f_related (Subtype.val : S → M)
        (VectorField.mlieBracket J X₁ X₂) (VectorField.mlieBracket I Y₁ Y₂) :=
    f_related_mlieBracket X₁.contMDiff X₂.contMDiff Y₁.contMDiff Y₂.contMDiff
      hX₁_related hX₂_related
  intro p
  rw [isTangentToSubmanifoldAt_iff_exists]
  exact ⟨VectorField.mlieBracket J X₁ X₂ p, hBracket_related.2 p⟩

end VectorField

end
