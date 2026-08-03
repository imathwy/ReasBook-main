module

public import Topology_Munkres_2000.Book.Definition_52_6.BasepointChange

public section

universe u

namespace FundamentalGroup.LeftToRight

/-- Helper for Exercise 52.2: the path-class representation of an element of
`π₁(X, x₀)` is injective. -/
private lemma toPath_injective {X : Type u} [TopologicalSpace X] {x₀ : X}
    (a b : π₁(X, x₀)) (h : toPath a = toPath b) : a = b := by
  -- Apply the inverse representation map to recover the original group elements.
  calc
    a = fromPath (toPath a) := (fromPath_toPath a).symm
    _ = fromPath (toPath b) := congrArg fromPath h
    _ = b := fromPath_toPath b

/-- Helper for Exercise 52.2: reversing a composite of path-homotopy classes
reverses the order of its factors. -/
private lemma quotientSymm_trans {X : Type u} [TopologicalSpace X]
    {x₀ x₁ x₂ : X} (γ : Path.Homotopic.Quotient x₀ x₁)
    (δ : Path.Homotopic.Quotient x₁ x₂) :
    (γ.trans δ).symm = δ.symm.trans γ.symm := by
  -- Reduce to represented paths, where reversal of concatenation is a path equality.
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      induction δ using Path.Homotopic.Quotient.ind with
      | mk δ =>
          simp only [← Path.Homotopic.Quotient.mk_trans,
            ← Path.Homotopic.Quotient.mk_symm, Path.trans_symm]

/-- Exercise 52.2: Basepoint change along `α.trans β` is the composite of basepoint
change along `α` followed by basepoint change along `β`. -/
theorem hat_trans {X : Type u} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (α : Path x₀ x₁) (β : Path x₁ x₂) :
    (α.trans β)̂ = β̂ ∘ α̂ := by
  -- Compare both functions pointwise through their injective path-class representation.
  funext p
  apply toPath_injective
  -- Expand basepoint change, reverse the composite, and reassociate concatenations.
  simp only [toPath_hat_apply, Function.comp_apply,
    Path.Homotopic.Quotient.mk_trans, quotientSymm_trans,
    Path.Homotopic.Quotient.trans_assoc]

/-- Helper for Exercise 52.2: the bundled multiplicative equivalence for a composite
path is the composite of the equivalences for its factors. -/
theorem mulEquivOfPath_trans {X : Type u} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (α : Path x₀ x₁) (β : Path x₁ x₂) :
    mulEquivOfPath (α.trans β) = (mulEquivOfPath α).trans (mulEquivOfPath β) := by
  ext p
  exact congrFun (hat_trans α β) p

end FundamentalGroup.LeftToRight
