import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: mathlib already provides `Scheme.local_affine` and the subtype
-- `X.affineOpens`; the source notion is therefore best exposed as a scheme predicate ranging over
-- affine open neighborhoods and testing the bundled section ring `Γ(X, U)`.

-- Allow source-facing point-membership notation on bundled affine opens.
instance instMembershipAffineOpens (X : Scheme.{u}) : Membership X X.affineOpens where
  mem U x := x ∈ (U : X.Opens)

/-- Definition 28.4.2: a scheme has ring property `P` locally if every point lies in an affine
open whose ring of sections has property `P`. -/
@[stacks 01OQ]
class HasRingPropertyLocally (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) : Prop where
  /-- Every point admits an affine open neighborhood whose section ring has property `P`. -/
  out : ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U))

namespace HasRingPropertyLocally

/-- A scheme with ring property `P` locally has, at each point, an affine open neighborhood whose
section ring satisfies `P`. -/
theorem exists_affineOpen (X : Scheme.{u}) (P : CommRingCat.{u} → Prop)
    [h : X.HasRingPropertyLocally P] (x : X) :
    ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)) :=
  h.out x

end HasRingPropertyLocally

/-- Helper for Definition 28.4.2: unfold `HasRingPropertyLocally` as the affine-open neighborhood
witness condition on points. -/
theorem hasRingPropertyLocally_iff (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) :
    X.HasRingPropertyLocally P ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)) := by
  constructor
  · intro h x
    exact h.out x
  · intro h
    exact ⟨h⟩

end Scheme
end AlgebraicGeometry
