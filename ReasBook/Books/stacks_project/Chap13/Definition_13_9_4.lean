import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {A B C : CochainComplex V ℤ}
variable (α : A ⟶ B) (β : B ⟶ C)

/- Source/core/bridge triage for Definition 13.9.4:
- primary domain: morphisms of cochain complexes and the split mono/epi structure on their
  components;
- inspected owner declarations:
  `HomologicalComplex.Hom.f`,
  `CategoryTheory.IsSplitMono`,
  `CategoryTheory.retraction`,
  `CategoryTheory.IsSplitEpi`,
  `CategoryTheory.section_`;
- best owner abstraction: the per-component owner classes `IsSplitMono` and `IsSplitEpi`; there
  is no separate canonical project/mathlib owner for the extra word “termwise”, so the correct
  public surface is the direct componentwise predicate on a complex morphism;
- layer: `bridge/view`; the numbered item only translates the textbook phrase “termwise split
  injection/surjection” into the canonical upstream owner classes, and should not introduce a new
  wrapper predicate.

Primitive data lives upstream inside `IsSplitMono (α.f n)` and `IsSplitEpi (β.f n)` for each
degree `n`. The chosen retractions/sections are derived API through `retraction` and `section_`,
while the component maps themselves come from the canonical owner projection `HomologicalComplex.Hom.f`.
Accordingly, the file only needs `[HasZeroMorphisms V]`: neither the component map projection nor
the split mono/epi owners use the stronger additive structure. This file should therefore reuse
those owners directly instead of packaging a parallel “termwise split” structure.
-/

/- Companion recalls: the relevant owner classes and their canonical chosen splitting maps. -/
recall IsSplitMono
recall retraction
recall IsSplitEpi
recall section_

/- Definition 13.9.4 (1): the source phrases this for cochain complexes in an additive category,
but the recalled componentwise split-monomorphism predicate already lives canonically in any
category with zero morphisms. Thus a morphism `α : A^• ⟶ B^•` is termwise split injective exactly
when each component `α.f n : A.X n ⟶ B.X n` is a split monomorphism. The canonical Lean
expression is the direct componentwise predicate below. -/
#check (∀ n : ℤ, IsSplitMono (α.f n))

/- Definition 13.9.4 (2): likewise, the componentwise split-epimorphism predicate only needs zero
morphisms. A morphism `β : B^• ⟶ C^•` is termwise split surjective exactly when each component
`β.f n : B.X n ⟶ C.X n` is a split epimorphism. The canonical Lean expression is the direct
componentwise predicate below. -/
#check (∀ n : ℤ, IsSplitEpi (β.f n))

end

end CochainComplex
