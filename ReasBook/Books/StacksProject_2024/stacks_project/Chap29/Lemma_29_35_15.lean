import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_35_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_14

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the ring-level owner `Algebra.unramifiedLocus`, the scheme-side
  owner `FormallyUnramified`, and base-change stability for unramified morphisms.
- Local Section 29.35 precedent fixes the pointwise scheme owners as `Scheme.Hom.UnramifiedAt`
  and `Scheme.Hom.GUnramifiedAt`, while Chapter 29 base-change locus statements use the
  canonical pullback projection `pullback.fst f g` and base-changed morphism `pullback.snd f g`.
- The Stacks tag evidence is consistent: item tag `0475` and source URL tag `0475`.
-/

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- Lemma 29.35.15 (1): for a locally finite type morphism `f : X ⟶ S`, formation of
the open set of points where `f` is unramified commutes with arbitrary base change. Equivalently,
using Lemma 29.35.14, this is the set of points where the fiber over `f x` is unramified at the
corresponding point. -/
@[stacks 0475]
theorem unramifiedAt_locus_pullback_snd [LocallyOfFiniteType f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).UnramifiedAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.UnramifiedAt x} := sorry

/-- Lemma 29.35.15 (2): for a locally finite presentation morphism `f : X ⟶ S`, formation of
the open set of points where `f` is G-unramified commutes with arbitrary base change. -/
@[stacks 0475]
theorem gUnramifiedAt_locus_pullback_snd [LocallyOfFinitePresentation f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).GUnramifiedAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.GUnramifiedAt x} := sorry

end

end AlgebraicGeometry
