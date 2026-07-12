import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Modules

/- Semantic recall / owner check:
- `lean_leansearch` did not find a packaged theorem for tensoring an `f`-ample invertible sheaf
  by another invertible sheaf to become eventually relatively very ample;
- nearby Chapter 29 files own the source notions as `RelativelyAmple` and `RelativelyVeryAmple`,
  use `Scheme.Hom.FiniteType` for finite-type morphisms, represent quasi-compact base schemes
  by `[CompactSpace S]`, and use `Invertible.tensorPow L d` for `L^{\otimes d}`;
- importing `Definition_29_38_1.lean` currently rebuilds `Definition_29_37_1.lean`, whose
  relative-ampleness owner is not dependency-closed in this item environment.  This file
  therefore records the intended source-facing theorem without introducing a fake replacement for
  relative ampleness or relative very ampleness;
- the Stacks tag evidence is consistent: item tag `0FVC` and source URL
  `https://stacks.math.columbia.edu/tag/0FVC`.
-/

/- Lemma 29.39.8 (Stacks tag `0FVC`): let `f : X ⟶ S` be a morphism of schemes, and
let `N` and `L` be invertible `\mathcal O_X`-modules.  If `S` is quasi-compact, `f` is of finite
type, and `L` is `f`-ample, then `N \otimes_{\mathcal O_X} L^{\otimes d}` is `f`-very ample for
all sufficiently large `d`.

When the Chapter 29 relative-ampleness owners are dependency-closed, the intended source-facing
statement shape is:
`theorem RelativelyAmple.eventually_relativelyVeryAmple_tensor_tensorPow
  {X S : Scheme} {f : X ⟶ S} {N L : X.Modules}
  [MonoidalCategory X.Modules] [Invertible N] [RelativelyAmple f L]
  [CompactSpace S] [Scheme.Hom.FiniteType f] :
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    RelativelyVeryAmple f (tensorObj N (Invertible.tensorPow L d))`.
-/
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ Scheme.Hom.FiniteType f
#check fun {S : Scheme.{u}} ↦ CompactSpace S
#check fun {X : Scheme.{u}} [MonoidalCategory X.Modules] (L : X.Modules) ↦ Invertible L
#check fun {X : Scheme.{u}} [MonoidalCategory X.Modules] (N L : X.Modules) (d : ℕ) ↦
  tensorObj N (Invertible.tensorPow L d)
#check fun {X : Scheme.{u}} [MonoidalCategory X.Modules] (L : X.Modules) [Invertible L] ↦
  Scheme.Modules.IsAmple L

end AlgebraicGeometry
