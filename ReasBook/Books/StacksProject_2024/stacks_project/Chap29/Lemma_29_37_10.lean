import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced `AlgebraicGeometry.QuasiCompact.of_comp` and the canonical
morphism predicate `QuasiCompact`. Local Chapter 29 uses `RelativelyAmple f L` from
Definition 29.37.1 for an invertible sheaf `L` being `f`-ample, but importing that owner
currently forces Lake through the upstream Chapter 28/17 ampleness path before this item is
elaborated. This file therefore records the source lemma as a labeled recall block and checks
the dependency-closed morphism and module surfaces. The Stacks tag evidence is consistent:
item tag `0C4L` and source URL `https://stacks.math.columbia.edu/tag/0C4L`.
-/

/- Lemma 29.37.10 (Stacks tag `0C4L`): if an invertible `\mathcal O_X`-module
`\mathcal L` is `(g \circ f)`-ample and `f : X ⟶ Y` is quasi-compact, then
`\mathcal L` is `f`-ample.

When the Chapter 28/29 ampleness owners are dependency-closed, the intended source-facing
statement is the theorem skeleton with hypotheses `[QuasiCompact f]`,
`[Scheme.Modules.Invertible L]`, and `RelativelyAmple (f ≫ g) L`, and conclusion
`RelativelyAmple f L`.
-/
#check fun {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) ↦ f ≫ g
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ QuasiCompact f
#check fun {X : Scheme.{u}} (L : X.Modules) ↦ L

end AlgebraicGeometry
