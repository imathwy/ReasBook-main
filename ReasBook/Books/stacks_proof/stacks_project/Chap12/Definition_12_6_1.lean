import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

/-
Domain-style sampling for Definition 12.6.1:
- primary domain: extensions in homological algebra, formalized as short exact sequences in a
  category with zero morphisms;
- sampled owner declarations:
  `ShortComplex`,
  `ShortComplex.ShortExact`,
  `ShortComplex.ShortExact.mk'`,
  `ShortComplex.ShortExact.extClass`;
- best owner abstraction: `ShortComplex C` with the owner predicate `S.ShortExact`;
- primitive source-facing data: the middle object `E` and the two structure maps
  `A ⟶ E ⟶ B` whose composite is zero;
- derived API: the associated short complex `toShortComplex`, the short exactness proof, and the
  induced `Mono`/`Epi` instances on the structure maps;
- source/core/bridge triage:
  `source-facing`: an extension of `B` by `A`, i.e. a short exact sequence
    `0 ⟶ A ⟶ E ⟶ B ⟶ 0` with fixed endpoints;
  `core/canonical`: `ShortComplex C` together with `ShortComplex.ShortExact`;
  `bridge/view`: `toShortComplex`.

The fixed-endpoint source-facing structure is kept here because replacing it by a raw subtype of
`ShortComplex C` would force endpoint transports into the public API. The refinement should
therefore reuse the `ShortComplex` owner through a thin bridge, not collapse the source-facing
notion into a transport-heavy wrapper.
-/
/-- Definition 12.6.1: an extension of `B` by `A` in an abelian category is a short exact
sequence `0 ⟶ A ⟶ E ⟶ B ⟶ 0`. The owner abstraction is `ShortComplex C`; a source-facing
extension is a short exact short complex whose endpoints are fixed to `A` and `B`. -/
@[stacks 010J]
structure Extension (A B : C) where
  E : C
  f : A ⟶ E
  g : E ⟶ B
  zero : f ≫ g = 0
  shortExact : (ShortComplex.mk f g zero).ShortExact

namespace Extension

abbrev toShortComplex (S : Extension A B) : ShortComplex C :=
  ShortComplex.mk S.f S.g S.zero

instance : CoeOut (Extension A B) (ShortComplex C) where
  coe := toShortComplex

instance (S : Extension A B) : Mono S.f :=
  S.shortExact.mono_f

instance (S : Extension A B) : Epi S.g :=
  S.shortExact.epi_g

end Extension

end

end CategoryTheory
