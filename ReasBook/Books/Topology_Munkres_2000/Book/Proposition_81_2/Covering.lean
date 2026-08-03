module

public import Topology_Munkres_2000.Book.Definition_79_1.Equiv
public import Mathlib.Topology.Homotopy.Lifting

public section

universe u v

/-- A connected covering of `B`, including the chapter convention that its projection is
surjective and its total space is path connected and locally path connected. -/
structure ConnectedCovering (B : Type v) [TopologicalSpace B] where
  Total : TopCat.{u}
  proj : Total → B
  isCoveringMap : IsCoveringMap proj
  surjective : Function.Surjective proj
  pathConnected : PathConnectedSpace Total
  locallyPathConnected : LocallyPathConnectedSpace Total

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B]

/-- Build a connected covering from a covering projection satisfying the chapter's standing
connectedness and surjectivity conventions. -/
@[expose]
def of {E : Type u} [TopologicalSpace E] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (proj : E → B) (isCoveringMap : IsCoveringMap proj)
    (surjective : Function.Surjective proj) : ConnectedCovering B where
  Total := TopCat.of E
  proj := proj
  isCoveringMap := isCoveringMap
  surjective := surjective
  pathConnected := inferInstance
  locallyPathConnected := inferInstance

/-- The path-connectedness carried by a connected covering. -/
theorem pathConnectedSpace (C : ConnectedCovering.{u} B) : PathConnectedSpace C.Total :=
  C.pathConnected

/-- The local path-connectedness carried by a connected covering. -/
theorem locallyPathConnectedSpace (C : ConnectedCovering.{u} B) :
    LocallyPathConnectedSpace C.Total :=
  C.locallyPathConnected

/-- Two connected coverings are equivalent when their projections are equivalent maps over the
base. -/
def Equivalent (C D : ConnectedCovering.{u} B) : Prop :=
  CoveringMap.Equivalent C.proj D.proj

/-- Equivalence of connected coverings is exactly existence of a homeomorphism commuting with
their projections. -/
theorem equivalent_iff {C D : ConnectedCovering.{u} B} :
    Equivalent C D ↔ ∃ h : C.Total ≃ₜ D.Total, C.proj = D.proj ∘ h :=
  CoveringMap.equivalent_iff

/-- The covering-equivalence relation is reflexive. -/
theorem Equivalent.refl (C : ConnectedCovering.{u} B) : Equivalent C C :=
  CoveringMap.Equivalent.refl C.proj

/-- The covering-equivalence relation is symmetric. -/
theorem Equivalent.symm {C D : ConnectedCovering.{u} B} (h : Equivalent C D) : Equivalent D C :=
  CoveringMap.Equivalent.symm h

/-- The covering-equivalence relation is transitive. -/
theorem Equivalent.trans {C D F : ConnectedCovering.{u} B}
    (h : Equivalent C D) (k : Equivalent D F) : Equivalent C F :=
  CoveringMap.Equivalent.trans h k

/-- Covering equivalence as the setoid used to form equivalence classes. -/
def equivalentSetoid (B : Type v) [TopologicalSpace B] : Setoid (ConnectedCovering.{u} B) where
  r := Equivalent
  iseqv := ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

/-- The relation underlying connected-covering classes is precisely covering equivalence. -/
theorem equivalentSetoid_iff {C D : ConnectedCovering.{u} B} :
    (equivalentSetoid B).r C D ↔ Equivalent C D :=
  Iff.rfl

/-- Equivalence classes of connected coverings of `B`. -/
abbrev Class (B : Type v) [TopologicalSpace B] :=
  Quotient (equivalentSetoid B)

/-- Two connected coverings define the same class exactly when they are equivalent. -/
theorem class_mk_eq_mk_iff {C D : ConnectedCovering.{u} B} :
    Quotient.mk (equivalentSetoid B) C =
        Quotient.mk (equivalentSetoid B) D ↔
      Equivalent C D :=
  Quotient.eq''

end ConnectedCovering
