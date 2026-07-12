import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

/- Semantic recall hits used for this setup item:
- `CategoryTheory.IsPullback`,
- `AlgebraicGeometry.Scheme.Modules.pullback`,
- `AlgebraicGeometry.Scheme.Modules.pushforward`,
- `CategoryTheory.Functor.rightDerived`. -/

namespace AlgebraicGeometry.Scheme

variable {X X' S S' : Scheme.{u}}

/- 30.5.0.1: this displayed base-change diagram is setup, not a new theorem. Its geometric square
is expressed by `CategoryTheory.IsPullback`; the sheaf in the upper-left corner is the canonical
pullback `(g')^* ℱ`, formalized by `AlgebraicGeometry.Scheme.Modules.pullback`; and the lower row
is handled in the current environment by the degreewise right-derived owner
`CategoryTheory.Functor.rightDerived` applied to the pushforward functors
`AlgebraicGeometry.Scheme.Modules.pushforward` along `f'` and `f`. -/
#check IsPullback
#check (Scheme.Modules.pullback : (X' ⟶ X) → X.Modules ⥤ X'.Modules)
#check (Scheme.Modules.pushforward : (X ⟶ S) → X.Modules ⥤ S.Modules)
#check (fun (g' : X' ⟶ X) (ℱ : X.Modules) ↦ (Scheme.Modules.pullback g').obj ℱ)

section

variable [HasInjectiveResolutions X.Modules]

#check (fun (f : X ⟶ S) (i : ℕ) ↦ (Scheme.Modules.pushforward f).rightDerived i)

end

end AlgebraicGeometry.Scheme
