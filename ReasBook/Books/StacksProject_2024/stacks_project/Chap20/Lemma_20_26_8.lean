import StacksProject_2024.Chap06.Lemma_6_26_4
import StacksProject_2024.Chap15.Lemma_15_59_3
import StacksProject_2024.Chap20.Lemma_20_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open scoped RingedSpace.Hom

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules Y)] [MonoidalPreadditive (RingedSpace.Modules Y)]

/- Domain-style sampling for Lemma 20.26.8:
- primary domain: pullback of cochain complexes of module sheaves on ringed spaces and the owner
  predicate `K.IsKFlat`;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `AlgebraicGeometry.RingedSpace.isKFlat_iff_stalkwise_isKFlat`,
  `AlgebraicGeometry.RingedSpace.Hom.pullbackStalkIso`,
  `CategoryTheory.extendScalarsComplex_isKFlat`;
- best owner abstraction: the main owner remains the predicate `K.IsKFlat` on the cochain complex
  itself, while the pulled-back complex is the canonical image of `K` under the ambient pullback
  functor `f^*` on module sheaves, extended to complexes by `mapHomologicalComplex`;
- primitive vs derived: the primitive data are only the morphism `f`, the source complex `K`, and
  the hypothesis `hK : K.IsKFlat`; the stalk comparison and extension-of-scalars preservation are
  bridge/view ingredients for the proof, not extra public data.

Source/core/bridge triage:
- `source-facing`: pullback along a morphism of ringed spaces preserves K-flatness of complexes;
- `core/canonical`: `K.IsKFlat` and the canonical pullback functor `f^*`;
- `bridge/view`: `isKFlat_iff_stalkwise_isKFlat`, `RingedSpace.Hom.pullbackStalkIso`, and
  `extendScalarsComplex_isKFlat`, which witness the stalkwise reduction and the ring-level base
  change step.
-/

section

local notation "ModY" => RingedSpace.Modules Y

-- Proof sketch: by Lemma `20.26.4`, it suffices to check K-flatness on stalk complexes. For
-- `x : X`, Lemma `6.26.4` identifies the stalk of the pullback complex with extension of scalars
-- of the stalk complex of `K` along `𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}`. Then Lemma
-- `15.59.3` shows that extension of scalars preserves K-flatness.
/-- For each `x : X`, the stalk complex of the pulled-back complex `f^* K` is K-flat whenever
`K` is K-flat. -/
lemma stalkComplex_pullback_isKFlat
    (f : X ⟶ Y) (K : CochainComplex ModY ℤ) (hK : K.IsKFlat) (x : X) :
    (stalkComplex (((f^*).mapHomologicalComplex (up ℤ)).obj K) x).IsKFlat :=
  sorry

/-- Lemma 20.26.8: for a morphism of ringed spaces
`f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, the pullback of a K-flat complex of `𝒪_Y`-modules is a
K-flat complex of `𝒪_X`-modules. -/
@[stacks 06YC]
lemma pullback_isKFlat (f : X ⟶ Y) (K : CochainComplex ModY ℤ) (hK : K.IsKFlat) :
    (((f^*).mapHomologicalComplex (up ℤ)).obj K).IsKFlat :=
  isKFlat_of_stalkComplex_isKFlat _ (stalkComplex_pullback_isKFlat f K hK)

end

end AlgebraicGeometry.RingedSpace
