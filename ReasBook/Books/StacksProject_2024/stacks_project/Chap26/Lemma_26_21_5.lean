import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found `IsImmersion.instιScheme`,
-- `isClosedImmersion_equalizer_ι_left`, and the canonical equalizer universal property
-- `equalizerIsEqualizer`.  The source-facing statements below keep the object in `Over S` and
-- expose the underlying subscheme inclusion as `(equalizer.ι a b).left`.

variable {S : Scheme.{u}} {X Y : Over S} (a b : X ⟶ Y)

/-- Lemma 26.21.5 (1): for two morphisms of schemes over `S`, the canonical equalizer inclusion
is an immersion, hence represents the locally closed subscheme of `X` where the two morphisms
agree. -/
@[stacks 01KM]
theorem isImmersion_equalizer_ι_left :
    IsImmersion (equalizer.ι a b).left := sorry

/-- Lemma 26.21.5 (2): the locally closed subscheme from part (1) is the categorical equalizer of
the two morphisms over `S`, hence has the largest-subscheme universal property. -/
@[stacks 01KM]
def equalizer_ι_isLimit_over :
    IsLimit (Fork.ofι (equalizer.ι a b) (equalizer.condition a b)) :=
  equalizerIsEqualizer a b

/-- Companion API for the equalizer in `Over S`: the limiting-fork witness supplies the
canonical factorization of any morphism on which the two maps agree. -/
theorem equalizer_ι_isLimit_over_lift_ι {Z : Over S}
    (k : Z ⟶ X) (hk : k ≫ a = k ≫ b) :
    Fork.IsLimit.lift (equalizer_ι_isLimit_over a b) k hk ≫ equalizer.ι a b = k := sorry

/-- Lemma 26.21.5 (3): if the target is separated over `S`, then the equalizer subscheme is a
closed subscheme of `X`. -/
@[stacks 01KM]
theorem isClosedImmersion_equalizer_ι_left_of_isSeparated [IsSeparated Y.hom] :
    IsClosedImmersion (equalizer.ι a b).left := sorry

end AlgebraicGeometry
