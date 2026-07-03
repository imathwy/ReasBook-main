import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_14_1 (from Chap03) -/
noncomputable section

universe u v

section

open scoped PolarCone

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 14.1 states three facts about the polar `Kᵒ` of a nonempty closed
  convex cone `K`: `Kᵒ` is again a nonempty closed convex cone, `Kᵒᵒ = K`, and the indicator
  functions of `K` and `Kᵒ` are mutual Fenchel conjugates. The source phrases this in `R^n`,
  but the owner APIs here already live on the pairing layer for the structural and indicator
  clauses and on the real continuous perfect self-pairing layer for the bipolar clause.
- `core/canonical`: the owner declarations already present in the project are the source-facing
  set polar `polarCone`, the owner facts `zero_mem_polarCone`, `isClosed_polarCone`,
  `convex_polarCone`, `isCone_polarCone`, the chapter owner predicate `Set.IsConvexCone ℝ K`,
  the owner hull `ConvexCone.hull ℝ K` together with `Set.IsConvexCone.hull_eq`, the bipolar
  owner `polarCone_polarCone_eq_closure`, the indicator bridge `indicatorFunction`, and the
  Fenchel conjugate `convexConjugate`.
- `bridge/view`: the theorem keeps Rockafellar's polar-cone notation as the main object. The
  already-established nonemptiness, closedness, and convexity clauses are recalled directly, while
  the bipolar clause is reduced to the earlier closure theorem by passing to the canonical bundled
  cone owner `ConvexCone.hull ℝ K`.

Domain-style sampling used here:
- the source-facing polar-cone inequality from Text 14.0.1;
- `zero_mem_polarCone`, `isClosed_polarCone`, `convex_polarCone`, and `isCone_polarCone` from
  Text 14.0.7;
- `Set.IsConvexCone` and `Set.IsConvexCone.hull_eq` from Definition 2.5.10;
- `ConvexCone.hull` from Definition 2.5.10;
- `polarCone_polarCone_eq_closure` from Text 14.0.4;
- `convexConjugate_indicatorFunction_eq_supportFunction`;
- `convexConjugate_indicatorFunction_eq_supportFunction_of_pairing_symm`;
- `convexConjugate_supportFunction_eq_indicatorFunction_closure_of_pairing_symm`.

Primitive data vs derived API:
- primitive datum: the set `K : Set E`;
- derived API: the recalled owner facts for `Kᵒ`, the bipolar identity, and the two conjugacy
  equalities for indicator functions.

The source sentence is split into atomic declarations. Redundant hypotheses are removed from the
polar-side structural clauses because those facts hold for every set `K`.
-/

/- The nonemptiness, closedness, convexity, and cone clauses of Theorem 14.1 are already the owner
facts `zero_mem_polarCone`, `isClosed_polarCone`, `convex_polarCone`, and `isCone_polarCone`. -/
recall zero_mem_polarCone
recall isClosed_polarCone
recall convex_polarCone
recall isCone_polarCone

end

section

open scoped PolarCone

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
variable [((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)).IsContPerfPair]

-- Proof sketch: the polar cone is always closed and convex by the previous clauses, and for a
-- nonempty closed convex cone `K` the bipolar identity identifies `Kᵒᵒ` with `K`.
/-- Theorem 14.1 (4): a nonempty closed convex cone is equal to its bipolar at the real
continuous perfect self-pairing layer. The source's `R^n` statement is a concrete specialization. -/
theorem polarCone_polarCone_eq
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK : Set.IsConvexCone ℝ K) :
    ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) = K := by
  let C : ConvexCone ℝ E := ConvexCone.hull ℝ K
  have hC_eq : (C : Set E) = K := by
    simpa [C] using (Set.IsConvexCone.hull_eq hK)
  have hC_nonempty : (C : Set E).Nonempty := by
    simpa [hC_eq] using hK_nonempty
  have hdouble_closure :
      ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) = closure K := by
    simpa [hC_eq] using
      (polarCone_polarCone_eq_closure_of_nonempty (K := C) hC_nonempty)
  simpa [hK_closed.closure_eq] using hdouble_closure

end

section

open scoped Pointwise PolarCone Rockafellar

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable [HasPairing Y X 𝕜]

-- Proof sketch: for `xStar ∈ Kᵒ`, every pairing `⟪x, xStar⟫` with `x ∈ K` is nonpositive, and
-- conic scaling forces the support supremum to be exactly `0`; for `xStar ∉ Kᵒ`, a violating
-- `x ∈ K` can be scaled by arbitrary positive integers, so the support value is `⊤`.
/-- Theorem 14.1 (5): for a nonempty cone `K`, the support function
`δᵛ[WithTopBot 𝕜](· | K)` is the indicator `δ(· | Kᵒ[𝕜])` of the polar cone. -/
theorem supportFunction_eq_indicatorFunction_polarCone
    (K : Set X) (hK_nonempty : K.Nonempty) (hK_cone : Set.IsCone 𝕜 K) :
    (δᵛ[WithTopBot 𝕜](· | K) : Y → WithTopBot 𝕜) = (δ[𝕜](· | Kᵒ[𝕜]) : Y → WithTopBot 𝕜) := by
  sorry

section

variable [HasPairingSwap X Y 𝕜]

-- Proof sketch: combine the source-facing support-function identity above with the owner theorem
-- `convexConjugate_indicatorFunction_eq_supportFunction`.
/-- Theorem 14.1 (5): the indicator function of a nonempty cone has the indicator function of its
polar cone as Fenchel conjugate. The source states this on `R^n`, but the owner objects involved
already live at the pairing layer. -/
theorem convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
    (K : Set X) (hK_nonempty : K.Nonempty) (hK_cone : Set.IsCone 𝕜 K) :
    ((δ[𝕜](· | K) : X → WithTopBot 𝕜)⋆) = (δ[𝕜](· | Kᵒ[𝕜]) : Y → WithTopBot 𝕜) := by
  sorry

end

end

section

open scoped PolarCone Rockafellar

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]

-- Proof sketch: clause (5) rewrites `indicatorFunction Kᵒ[ℝ]` as `supportFunction K`, and the
-- support-function biconjugacy theorem from Text 13.1.5 identifies the conjugate of that support
-- function with `indicatorFunction (intrinsicClosure ℝ K)`.
/-- Theorem 14.1 (6), intrinsic form: for a nonempty convex cone `K`, the indicator function of
`Kᵒ[ℝ]` has as Fenchel conjugate the indicator of the intrinsic closure `intrinsicClosure ℝ K`. -/
theorem convexConjugate_indicatorFunction_polarCone_eq_indicatorFunction
    (K : Set E) (hK_nonempty : K.Nonempty)
    (hK : Set.IsConvexCone ℝ K) :
    ((δ[ℝ](· | Kᵒ[ℝ]) : E → WithTopBot ℝ)⋆) =
      (δ[ℝ](· | intrinsicClosure ℝ K) : E → WithTopBot ℝ) := by
  sorry

/-- Closed-set bridge for Theorem 14.1 (6): if `K` is closed, the intrinsic closure collapses to
`K`, recovering the textbook ambient statement. -/
theorem convexConjugate_indicatorFunction_polarCone_eq_indicatorFunction_of_isClosed
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK : Set.IsConvexCone ℝ K) :
    ((δ[ℝ](· | Kᵒ[ℝ]) : E → WithTopBot ℝ)⋆) = (δ[ℝ](· | K) : E → WithTopBot ℝ) := by
  sorry

end

end
