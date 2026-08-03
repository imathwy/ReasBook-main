module

public import Topology_Munkres_2000.Book.Definition_29_2.Compactification
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

universe u v w

/- Definition 38.1 (1): A compactification of `X` is a compact Hausdorff target equipped with a
dense topological embedding of `X`. -/
#check Compactification

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Definition 38.1: a concrete equivalence of compactifications is a homeomorphism
over `X`. -/
structure Equiv (C : Compactification.{u, v} X) (D : Compactification.{u, w} X) where
  toHomeomorph : C ≃ₜ D
  commutes (x : X) : toHomeomorph (C x) = D x

/-- Helper for Definition 38.1: a compactification equivalence acts by its homeomorphism. -/
instance Equiv.instCoeFun {C : Compactification.{u, v} X} {D : Compactification.{u, w} X} :
    CoeFun (Equiv C D) (fun _ ↦ C → D) where
  coe e := e.toHomeomorph

/-- Helper for Definition 38.1: applying an equivalence applies its underlying homeomorphism. -/
theorem Equiv.toHomeomorph_apply {C : Compactification.{u, v} X}
    {D : Compactification.{u, w} X} (e : Equiv C D) (y : C) :
    e.toHomeomorph y = e y := by
  -- The function coercion is definitionally the underlying homeomorphism.
  rfl

/-- Definition 38.1 (2): Two compactifications are equivalent when a homeomorphism over `X`
exists between them. -/
def Equivalent (C : Compactification.{u, v} X) (D : Compactification.{u, w} X) : Prop :=
  Nonempty (Equiv C D)

end Compactification

end
