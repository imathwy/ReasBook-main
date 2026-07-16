import StacksProject_2024.stacks_project.Chap29.Lemma_29_15_3
import StacksProject_2024.stacks_project.Chap29.Lemma_29_37_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`lean_leansearch` surfaced quasi-compact morphism composition but no upstream
scheme-morphism quasi-projective composition theorem. Local Chapter 29 owns the source notion as
`QuasiProjective` in `Definition_29_40_1`; the quasi-compactness of the base scheme is represented
by `[CompactSpace S]`, and the composite of `f : X ⟶ Y` and `g : Y ⟶ S` is `f ≫ g`.

The current read-only item environment cannot import `Definition_29_40_1`: its
relative-ampleness owner path rebuilds upstream Chapter 17 files before this target is elaborated,
and that import path fails outside this item. This file therefore records the source lemma as a
labeled recall block and checks the dependency-closed finite-type, module-pullback, tensor, and
quasi-compact-base surfaces instead of introducing a fake replacement for `QuasiProjective`.

The Stacks tag evidence is consistent: item tag `0C4M` and source URL
`https://stacks.math.columbia.edu/tag/0C4M`.
-/

/- Lemma 29.40.3 (Stacks tag `0C4M`): if the base scheme is quasi-compact and two scheme
morphisms are quasi-projective, then their composite is quasi-projective.

When `Definition_29_40_1` is dependency-closed, the intended source-facing theorem is:
`theorem QuasiProjective.comp {X Y S : Scheme} {f : X ⟶ Y} {g : Y ⟶ S}
  [CompactSpace S] (hf : QuasiProjective f) (hg : QuasiProjective g) :
  QuasiProjective (f ≫ g)`, with the corresponding typeclass instance
`[CompactSpace S] [QuasiProjective f] [QuasiProjective g] : QuasiProjective (f ≫ g)`.
-/
#check fun {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) ↦ f ≫ g
#check fun {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g] ↦
  (inferInstance : Scheme.Hom.FiniteType (f ≫ g))
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) ↦
  (Scheme.Modules.pullback f).obj M
#check fun {X : Scheme.{u}} [CategoryTheory.MonoidalCategory X.Modules] (L M : X.Modules) ↦
  CategoryTheory.MonoidalCategory.tensorObj L M
#check fun {S : Scheme.{u}} ↦ CompactSpace S

end AlgebraicGeometry
