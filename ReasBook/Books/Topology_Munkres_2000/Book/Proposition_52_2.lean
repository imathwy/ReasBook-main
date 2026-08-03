module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention

public section

universe u

namespace FundamentalGroup

namespace LeftToRight

/-- Helper for Proposition 52.2: the path-class representation of an element of
`π₁(X, x₀)` is injective. -/
private lemma toPath_injective {X : Type u} [TopologicalSpace X] {x₀ : X}
    (a b : π₁(X, x₀)) (h : toPath a = toPath b) : a = b := by
  -- Apply the inverse representation map to recover the original group elements.
  calc
    a = fromPath (toPath a) := (fromPath_toPath a).symm
    _ = fromPath (toPath b) := congrArg fromPath h
    _ = b := fromPath_toPath b

/-- Helper for Proposition 52.2: homotopic connecting paths induce the same
basepoint-change equivalence. -/
private lemma mulEquivOfPath_eq_of_mk_eq {X : Type u} [TopologicalSpace X]
    {x₀ x₁ : X} (p q : Path x₀ x₁)
    (h : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q) :
    mulEquivOfPath p = mulEquivOfPath q := by
  -- Compare values after passing to path classes, where the hypothesis rewrites directly.
  apply MulEquiv.ext
  intro a
  apply toPath_injective
  rw [toPath_mulEquivOfPath_apply, toPath_mulEquivOfPath_apply, h]

/-- Helper for Proposition 52.2: reversing a composite of path-homotopy classes
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

/-- Helper for Proposition 52.2: prepending a loop to a connecting path changes
basepoint change by conjugation with that loop. -/
private lemma mulEquivOfPath_prependLoop_apply {X : Type u} [TopologicalSpace X]
    {x₀ x₁ : X} (β : Path x₀ x₀) (p : Path x₀ x₁) (a : π₁(X, x₀)) :
    mulEquivOfPath (β.trans p) a =
      mulEquivOfPath p
        ((fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
          fromPath (Path.Homotopic.Quotient.mk β)) := by
  -- After applying `toPath`, both sides are the same fivefold path concatenation.
  apply toPath_injective
  simp only [toPath_mulEquivOfPath_apply, mul_def, inv_def, toPath_fromPath,
    Path.Homotopic.Quotient.mk_trans, quotientSymm_trans,
    Path.Homotopic.Quotient.trans_assoc]

/-- Proposition 52.2. For fixed basepoints in a path-connected space, the basepoint-change
multiplicative equivalence is independent of the connecting path if and only if the
fundamental group is abelian. -/
theorem mulEquivOfPath_independent_iff {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ x₁ : X) :
    (∀ p q : Path x₀ x₁, mulEquivOfPath p = mulEquivOfPath q) ↔
      IsMulCommutative π₁(X, x₀) := by
  constructor
  · intro hindependent
    apply isMulCommutative_iff.mpr
    intro a b
    let p : Path x₀ x₁ := PathConnectedSpace.somePath x₀ x₁
    obtain ⟨β, hβ⟩ := Path.Homotopic.Quotient.mk_surjective (toPath b)
    have hrepresent : fromPath (Path.Homotopic.Quotient.mk β) = b := by
      -- The chosen loop represents exactly `b` under `fromPath`.
      rw [hβ, fromPath_toPath]
    have hconjugate : b⁻¹ * a * b = a := by
      -- Path independence identifies change along `β.trans p` with change along `p`.
      apply (mulEquivOfPath p).injective
      rw [← hrepresent]
      calc
        mulEquivOfPath p
            ((fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
              fromPath (Path.Homotopic.Quotient.mk β)) =
            mulEquivOfPath (β.trans p) a :=
          (mulEquivOfPath_prependLoop_apply β p a).symm
        _ = mulEquivOfPath p a :=
          congrArg (fun e : π₁(X, x₀) ≃* π₁(X, x₁) ↦ e a)
            (hindependent (β.trans p) p)
    -- Triviality of conjugation is precisely the desired commutation relation.
    apply inv_mul_eq_iff_eq_mul.mp
    simpa only [mul_assoc] using hconjugate
  · intro hcommutative p q
    let β : Path x₀ x₀ := q.trans p.symm
    have hclass : Path.Homotopic.Quotient.mk (β.trans p) =
        Path.Homotopic.Quotient.mk q := by
      -- In the path quotient, the inserted `p.symm.trans p` cancels.
      simp only [β, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    have hconjugate (a : π₁(X, x₀)) :
        (fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
            fromPath (Path.Homotopic.Quotient.mk β) = a := by
      -- Commutativity moves `a` past the inverse, after which the inverse pair cancels.
      rw [(isMulCommutative_iff.mp hcommutative)
        (fromPath (Path.Homotopic.Quotient.mk β))⁻¹ a, mul_assoc, inv_mul_cancel,
        mul_one]
    -- Rewrite `q` as a loop prepended to `p`, then remove its trivial conjugation.
    apply MulEquiv.ext
    intro a
    calc
      mulEquivOfPath p a =
          mulEquivOfPath p
            ((fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
              fromPath (Path.Homotopic.Quotient.mk β)) :=
        congrArg (mulEquivOfPath p) (hconjugate a).symm
      _ = mulEquivOfPath (β.trans p) a :=
        (mulEquivOfPath_prependLoop_apply β p a).symm
      _ = mulEquivOfPath q a :=
        congrArg (fun e : π₁(X, x₀) ≃* π₁(X, x₁) ↦ e a)
          (mulEquivOfPath_eq_of_mk_eq (β.trans p) q hclass)

end LeftToRight

end FundamentalGroup
