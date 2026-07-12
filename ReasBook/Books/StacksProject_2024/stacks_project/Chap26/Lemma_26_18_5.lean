import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Topology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Hom.fiber`,
-- `Scheme.Hom.fiberι`, and `Scheme.fromSpecStalk`; the two source arrows are the
-- canonical projections from these pullback schemes to `X`.

/-- Lemma 26.18.5 (1): for a morphism of schemes `f : X ⟶ S` and a point `s : S`,
the top arrow `X_s ⟶ X` in the residue-field fibre square is a homeomorphism onto its
image. In mathlib this is the topological embedding of the canonical fibre inclusion. -/
@[stacks 01K1]
theorem fiberι_isEmbedding (f : X ⟶ S) (s : S) :
    IsEmbedding (f.fiberι s) := sorry

/-- Lemma 26.18.5 (2): for a morphism of schemes `f : X ⟶ S` and a point `s : S`,
the top arrow `Spec(\mathcal O_{S,s}) ×_S X ⟶ X` in the stalk-base-change square is a
homeomorphism onto its image. In mathlib this is the topological embedding of the
second projection from the pullback along `S.fromSpecStalk s`. -/
@[stacks 01K1]
theorem pullbackSnd_fromSpecStalk_isEmbedding (f : X ⟶ S) (s : S) :
    IsEmbedding
      (pullback.snd (S.fromSpecStalk s) f : pullback (S.fromSpecStalk s) f ⟶ X) := sorry

end AlgebraicGeometry
