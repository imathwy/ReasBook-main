import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling pass:
-- * primary domain: vector fields on smooth manifolds under diffeomorphisms;
-- * relevant owner-style declarations sampled before refinement:
--   `VectorField.mpullback`, `VectorField.mpullback_apply`, `Diffeomorph.symm`,
--   and `ContMDiff.mpullback_vectorField`;
-- * owner abstraction: mathlib's `VectorField.mpullback`;
-- * source/core/bridge split: Lee's pushforward surface is only a bridge/view for the canonical
--   pullback of a vector field along the inverse diffeomorphism.
-- Primitive data is only the diffeomorphism and the source vector field. The pushforward itself
-- is derived API from the canonical pullback owner, with only a thin bridge abbreviation for a
-- notation-stable source-facing surface.

universe u𝕜 uE uE' uH uH' uM uN

noncomputable section

section

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

/- Definition 8.57-extra-2 is recall-only at the owner level: for a diffeomorphism `F`, Lee's
pushforward vector field `F_* X` is the canonical manifold pullback `VectorField.mpullback` of
`X` along `F.symm`. -/
recall VectorField.mpullback

namespace Diffeomorph

/- Thin bridge/view for Lee's pushforward of a vector field along a diffeomorphism. The canonical
owner remains `VectorField.mpullback`. -/
abbrev pushforward
    (F : M ≃ₘ⟮I, J⟯ N)
    (X : ∀ p : M, TangentSpace I p) :
    ∀ q : N, TangentSpace J q :=
  VectorField.mpullback J I F.symm X

end Diffeomorph

namespace Manifold

/- Source-facing textbook notation for the pushforward of a vector field along a diffeomorphism.
Lean writes this as `F _* X`. -/
scoped notation:max F " _* " X => Diffeomorph.pushforward F X

end Manifold

end
