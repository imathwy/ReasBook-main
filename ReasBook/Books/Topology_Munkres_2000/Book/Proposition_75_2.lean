module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Mathlib.GroupTheory.Abelianization.Defs

public section

universe u

namespace FundamentalGroup.LeftToRight

/-- Helper for Proposition 75.2: the path-class representation of an element of
`π₁(X, x₀)` is injective. -/
private lemma toPath_injective {X : Type u} [TopologicalSpace X] {x₀ : X}
    (a b : π₁(X, x₀)) (h : toPath a = toPath b) : a = b := by
  -- Apply the inverse representation map to recover the original group elements.
  calc
    a = fromPath (toPath a) := (fromPath_toPath a).symm
    _ = fromPath (toPath b) := congrArg fromPath h
    _ = b := fromPath_toPath b

/-- Helper for Proposition 75.2: homotopic connecting paths induce the same
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

/-- Helper for Proposition 75.2: reversing a composite of path-homotopy classes
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

/-- Helper for Proposition 75.2: prepending a loop to a connecting path changes
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

/-- Proposition 75.2. The equivalence between abelianized fundamental groups induced by a path
is independent of the chosen path. -/
theorem abelianizationEquivOfPath_independent {X : Type u} [TopologicalSpace X]
    (x₀ x₁ : X) (p q : Path x₀ x₁) :
    (mulEquivOfPath p).abelianizationCongr =
      (mulEquivOfPath q).abelianizationCongr := by
  let β : Path x₀ x₀ := q.trans p.symm
  have hclass : Path.Homotopic.Quotient.mk (β.trans p) =
      Path.Homotopic.Quotient.mk q := by
    -- In the path quotient, the inserted `p.symm.trans p` cancels.
    simp only [β, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  -- It suffices to compare the induced homomorphisms on generators of the abelianization.
  apply MulEquiv.toMonoidHom_injective
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply]
  have hconjugate : IsConj a
      ((fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
        fromPath (Path.Homotopic.Quotient.mk β)) := by
    -- The second element is conjugation by the inverse of the represented loop.
    apply isConj_iff.mpr
    refine ⟨(fromPath (Path.Homotopic.Quotient.mk β))⁻¹, ?_⟩
    rw [inv_inv]
  have habelianized :=
    (Abelianization.of.comp (mulEquivOfPath p).toMonoidHom).map_isConj hconjugate
  have habelianized_eq := isConj_iff_eq.mp habelianized
  -- Replace the conjugated value by change along `β.trans p`, then identify that path with `q`.
  calc
    Abelianization.of (mulEquivOfPath p a) =
        Abelianization.of
          (mulEquivOfPath p
            ((fromPath (Path.Homotopic.Quotient.mk β))⁻¹ * a *
              fromPath (Path.Homotopic.Quotient.mk β))) := habelianized_eq
    _ = Abelianization.of (mulEquivOfPath (β.trans p) a) :=
      congrArg Abelianization.of (mulEquivOfPath_prependLoop_apply β p a).symm
    _ = Abelianization.of (mulEquivOfPath q a) :=
      congrArg (fun e : π₁(X, x₀) ≃* π₁(X, x₁) ↦ Abelianization.of (e a))
        (mulEquivOfPath_eq_of_mk_eq (β.trans p) q hclass)

end FundamentalGroup.LeftToRight

end
