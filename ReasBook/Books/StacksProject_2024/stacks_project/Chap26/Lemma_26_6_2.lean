import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical owner-side API
-- `RingedSpace.basicOpen`, `RingedSpace.mem_top_basicOpen`, and
-- `RingedSpace.isUnit_res_basicOpen`, while `IsLocalRing.notMem_maximalIdeal` gives the
-- locally-ringed-space translation from stalkwise invertibility to nonmembership in the maximal
-- ideal.
recall AlgebraicGeometry.RingedSpace.basicOpen

/-- The basic open `D(f)` of a global section on a locally ringed space, viewed through the
underlying ringed space. -/
abbrev basicOpen (X : LocallyRingedSpace.{u}) (f : X.presheaf.obj (op ⊤)) :
    TopologicalSpace.Opens X :=
  X.toRingedSpace.basicOpen f

/-- Membership in `D(f)` is equivalent to invertibility of the germ of `f`. -/
@[simp] theorem mem_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.Γgerm x f) := by
  exact X.toRingedSpace.mem_top_basicOpen f x

/-- The basic open `D(f)` is an open subset of `X`. -/
theorem basicOpen_le (f : X.presheaf.obj (op ⊤)) :
    X.basicOpen f ≤ ⊤ :=
  X.toRingedSpace.basicOpen_le f

/-- Lemma 26.6.2 (1): for a global section `f`, a point `x` lies in the Stacks set
`D(f) = {x | image f ∉ 𝔪_x}` exactly when it lies in the canonical basic open cut out by `f`. -/
@[stacks 01HZ]
theorem mem_basicOpen_iff_notMem_maximalIdeal (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔
      X.presheaf.Γgerm x f ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  exact (X.mem_basicOpen f x).trans IsLocalRing.notMem_maximalIdeal.symm

/-- Lemma 26.6.2 (2): the restriction of `f` to its basic open is invertible. This is exactly the
canonical ringed-space theorem specialized to the underlying ringed space of `X`. -/
@[stacks 01HZ]
theorem isUnit_res_basicOpen (f : X.presheaf.obj (op ⊤)) :
    IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) := by
  simpa [basicOpen, basicOpen_le] using X.toRingedSpace.isUnit_res_basicOpen f

end AlgebraicGeometry.LocallyRingedSpace
