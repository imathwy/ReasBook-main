import StacksProject_2024.stacks_project.Chap17.Definition_17_20_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open RingedSpace.Hom
open SheafOfModules
noncomputable section

universe u

namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Definition 29.25.1 (1): a morphism of schemes `f : X ⟶ S` is flat at `x : X` if the local
ring `\mathcal O_{X, x}` is flat over the local ring `\mathcal O_{S, f(x)}`. -/
@[stacks 01U3]
abbrev flatAt (f : X ⟶ S) (x : X) : Prop :=
  RingedSpace.Hom.FlatAt f.toLRSHom.toShHom x

/-- Definition 29.25.1 (3): a morphism of schemes is flat if it is flat at every point of `X`.
This source wording is expressed by the canonical mathlib owner `AlgebraicGeometry.Flat f`. -/
@[stacks 01U3]
theorem flat_iff_forall_flatAt (f : X ⟶ S) :
    Flat f ↔ ∀ x : X, flatAt f x := by
  constructor
  · intro hf x
    exact ((Scheme.Hom.isFlat_iff_flat f).2 hf).flatAt x
  · intro h
    exact (Scheme.Hom.isFlat_iff_flat f).1 ⟨h⟩

end Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- Definition 29.25.1 (2): a quasi-coherent `\mathcal O_X`-module `ℱ` is flat over `S` at
`x : X` if the stalk `\mathcal F_x` is a flat `\mathcal O_{S, f(x)}`-module. -/
@[stacks 01U3]
abbrev flatOverAt
    (ℱ : X.Modules) (f : X ⟶ S) (x : X) : Prop :=
  flat_over_at ℱ f.toShHom x

/-- Definition 29.25.1 (4): a quasi-coherent `\mathcal O_X`-module `ℱ` is flat over `S` if it
is flat over `S` at every point of `X`. Equivalently, the restricted
`f^{-1}\mathcal O_S`-module is flat in the canonical Chapter 17 owner. -/
@[stacks 01U3]
abbrev flatOver
    (ℱ : X.Modules) (f : X ⟶ S) : Prop :=
  (relativeModule ℱ f.toShHom).IsFlat

/-- The global flat-over-base predicate is exactly the corresponding stalkwise condition. -/
@[stacks 01U3]
theorem flatOver_iff_forall_flatOverAt
    (ℱ : X.Modules) (f : X ⟶ S) :
    flatOver ℱ f ↔ ∀ x : X, flatOverAt ℱ f x := by
  simpa [flatOver, flatOverAt] using
    (flat_over_iff_stalkwise ℱ f.toShHom)

end AlgebraicGeometry.Scheme.Modules
