import Mathlib.AlgebraicGeometry.PullbackCarrier

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall:
-- - `AlgebraicGeometry.IsDominant` is the canonical dominant-morphism owner.
-- - `Scheme.Pullback.range_snd` is the canonical description of the pullback projection image.
-- - `Dense.preimage` is the topological bridge from the source's open-map hypothesis to density of
--   preimages.

/-- Lemma 29.8.5: if `f : X ⟶ S` is dominant and `g : S' ⟶ S` is an open morphism of schemes,
then the base change of `f` by `g` is dominant. -/
@[stacks 0H8F]
theorem isDominant_pullbackSnd_of_isDominant_of_isOpenMap
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsDominant f]
    (hg : IsOpenMap g.base) :
    IsDominant (pullback.snd f g) := by
  have hf : Dense (Set.range f) := by
    simpa [DenseRange] using f.denseRange
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_snd]
  exact hf.preimage hg

end AlgebraicGeometry
