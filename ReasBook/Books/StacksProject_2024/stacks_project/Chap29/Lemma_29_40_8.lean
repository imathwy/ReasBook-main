import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Lemma_29_37_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced the canonical scheme-morphism owners `QuasiCompact` and related
postcomposition lemmas, but no upstream quasi-projective postcomposition descent theorem. Local
Chapter 29 owns the source notion as `QuasiProjective` from `Definition_29_40_1`, and the source
composite `g ∘ f` is formalized as `f ≫ g`.

The current read-only item environment cannot import `Definition_29_40_1` within the target-file
timeout: its relative-ampleness/projective-space owner path rebuilds upstream Chapter 17/18 files
before this target is elaborated. This file therefore records the source lemma as a labeled recall
block and checks the dependency-closed composition, finite-type, quasi-compact, and module
surfaces instead of introducing a fake replacement for `QuasiProjective`. The Stacks tag evidence
is consistent: item tag `0C4N` matches the source URL ending in `/tag/0C4N`.
-/

/- Lemma 29.40.8 (Stacks tag `0C4N`): let `g : Y ⟶ S` and `f : X ⟶ Y` be morphisms
of schemes. If `g ∘ f` is quasi-projective and `f` is quasi-compact, then `f` is
quasi-projective.

When `Definition_29_40_1` is dependency-closed, the intended source-facing statement is:
`theorem QuasiProjective.of_comp_of_quasiCompact {X Y S : Scheme} {f : X ⟶ Y} {g : Y ⟶ S}
  [QuasiCompact f] (hfg : QuasiProjective (f ≫ g)) : QuasiProjective f`.
-/
#check fun {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) ↦ f ≫ g
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ QuasiCompact f
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ Scheme.Hom.FiniteType f
#check fun {X : Scheme.{u}} (L : X.Modules) ↦ L

end AlgebraicGeometry
