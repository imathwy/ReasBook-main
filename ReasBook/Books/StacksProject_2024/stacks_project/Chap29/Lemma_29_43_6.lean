import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / dependency-closure note:
- Local Chapter 29 precedent fixes `RelativelyAmple f L` for an `f`-ample invertible sheaf,
  `IsProper f` for properness, and `LocallyProjective f` for the conclusion.
- The Stacks tag evidence is consistent: item tag `0B5N` agrees with the source URL ending in
  `/tag/0B5N`.
- Importing the checked-in `RelativelyAmple`/`LocallyProjective` owners currently forces Lake to
  rebuild `Definition_29_37_1.lean`, which fails before this target elaborates. This file therefore
  records the source lemma as a labeled `#check` block rather than introducing fake local
  replacements for relative ampleness or local projectivity.
-/

/- Lemma 29.43.6 (Stacks tag `0B5N`): let `f : X ⟶ S` be a proper morphism of schemes. If
there exists an `f`-ample invertible sheaf on `X`, then `f` is locally projective.

When the Chapter 29 relative-ampleness and locally-projective owners are dependency-closed, the
intended source-facing statement is:
`theorem locallyProjective_of_isProper_exists_relativelyAmple
  {X S : Scheme} (f : X ⟶ S) [IsProper f]
  (h : ∃ L : X.Modules, RelativelyAmple f L) :
  LocallyProjective f := sorry`.
-/
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ IsProper f

end AlgebraicGeometry
