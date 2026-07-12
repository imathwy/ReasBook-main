import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` did not find a packaged relative-ampleness tensor theorem. Local Chapter 29
owns the source notion as `RelativelyAmple`, and Chapter 28 owns absolute ampleness and tensor
powers for invertible modules. Importing that local owner currently forces a long upstream replay
in the read-only item runner; the dependency item Lemma 29.37.7 records the same blocker. This
file therefore keeps Lemma 29.37.8 as a labeled recall block and checks the dependency-closed
morphism, module-pullback, tensor, and quasi-compactness surfaces instead of introducing a fake
replacement for relative ampleness.

The Stacks tag evidence is consistent: item tag `0C4K` and source URL
`https://stacks.math.columbia.edu/tag/0C4K`.
-/

/- Lemma 29.37.8 (Stacks tag `0C4K`): let `g : Y ⟶ S` and `f : X ⟶ Y` be morphisms
of schemes. Let `M` be an invertible `\mathcal O_Y`-module and let `L` be an invertible
`\mathcal O_X`-module. If `S` is quasi-compact, `M` is `g`-ample, and `L` is `f`-ample, then
`L ⊗ f^*(M^{\otimes a})` is `(g \circ f)`-ample for all sufficiently large `a`.

When the Chapter 28/29 ampleness owners are dependency-closed, the intended source-facing theorem
has hypotheses `[CompactSpace S]`, `RelativelyAmple g M`, and `RelativelyAmple f L`, and conclusion
`∀ᶠ a : ℕ in atTop, RelativelyAmple (f ≫ g)
  (L ⊗ (Scheme.Modules.pullback f).obj (M^{\otimes a}))`.
-/
#check fun {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) ↦ f ≫ g
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) ↦
  (Scheme.Modules.pullback f).obj M
#check fun {X : Scheme.{u}} [MonoidalCategory X.Modules] (L M : X.Modules) ↦ tensorObj L M
#check fun {S : Scheme.{u}} ↦ CompactSpace S

end AlgebraicGeometry
