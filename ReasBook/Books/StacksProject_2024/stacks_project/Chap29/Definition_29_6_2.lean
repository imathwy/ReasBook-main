import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-
Definition 29.6.2: for a morphism of schemes `f : X \to Y`, the scheme theoretic
image is the canonical closed subscheme `Scheme.Hom.image f` of `Y`, with factorization maps
`Scheme.Hom.toImage f` and `Scheme.Hom.imageι f`. This records the canonical mathlib owner
rather than introducing a redundant alias.

Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.Scheme.Hom.image`,
`AlgebraicGeometry.Scheme.Hom.toImage`, and `AlgebraicGeometry.Scheme.Hom.imageι`; local
Lemma 29.6.1 already records the closed-immersion, factorization, and minimality API. The Stacks
tag evidence is consistent: item tag `01R7` matches the source URL `/tag/01R7`.
-/
recall AlgebraicGeometry.Scheme.Hom.image
recall AlgebraicGeometry.Scheme.Hom.toImage
recall AlgebraicGeometry.Scheme.Hom.imageι
recall AlgebraicGeometry.Scheme.Hom.toImage_imageι

end

end AlgebraicGeometry
