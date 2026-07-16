import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.1 identifies closedness of a concave function with the fixed-point
  equation `concaveClosure g = g`, equivalently `cl(-g) = -g` on the convex side.
- `core/canonical`: the chapter closure owner is `concaveClosure`, and convex-side closedness is
  the standard lower-semicontinuity/fixed-point API for `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: negation converts the concave closure fixed-point equation into the convex closure
  fixed-point equation for `-g`.

Primary mathematical domain:
- closedness and closure operators for extended-real-valued concave functions on topological
  spaces.

Domain-style sampling used here:
- `concaveClosure`;
- `concaveClosure_eq_neg_lowerSemicontinuousHull_neg`;
- `lowerSemicontinuousHull_eq_self`;
- `lowerSemicontinuous_lowerSemicontinuousHull`.

Primitive data vs derived API:
- primitive owner: `concaveClosure g`;
- derived API: the source-facing fixed-point equivalence
  `concaveClosure g = g ↔ cl(-g) = -g`, and its thin lower-semicontinuity companion obtained from
  the Chapter 2 owner theorem for `cl(·)`.

Layer target: `source-facing` for the fixed-point theorem, with a `bridge/view` companion to
`LowerSemicontinuous (-g)`.
-/

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: unfold `concaveClosure g = - cl(-g)` pointwise and negate the resulting equality.
-- This turns the fixed-point equation for `concaveClosure` into the fixed-point equation
-- `cl(-g) = -g` for the convex-side closure of the negated function.
/-- Theorem 6.30.1: a concave extended-real-valued function is closed exactly when its concave
closure fixes it; equivalently, the convex-side closure of the negated function is already `-g`. -/
theorem concaveClosure_eq_self_iff_cl_neg_eq_neg
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ cl(-g) = -g := by
  rw [concaveClosure_eq_neg_lowerSemicontinuousHull_neg g]
  constructor
  · intro h
    ext x
    have hx : -(cl(-g) x) = g x := congrArg (fun f ↦ f x) h
    simpa using congrArg Neg.neg hx
  · intro h
    ext x
    have hx : cl(-g) x = -g x := congrArg (fun f ↦ f x) h
    simpa using congrArg Neg.neg hx

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]

-- Proof sketch: combine the source-facing fixed-point equivalence above with the Chapter 2 owner
-- theorem `LowerSemicontinuous f ↔ cl(f) = f`, applied to `f := -g`.
/-- Companion bridge: the source-facing closedness equation from Theorem 6.30.1 is equivalent to
lower semicontinuity of the negated function. -/
theorem concaveClosure_eq_self_iff_lowerSemicontinuous_neg
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ LowerSemicontinuous (-g) := by
  rw [concaveClosure_eq_self_iff_cl_neg_eq_neg]
  constructor
  · intro hg
    simpa [hg] using lowerSemicontinuous_lowerSemicontinuousHull (-g)
  · intro hg
    exact lowerSemicontinuousHull_eq_self hg

/-- Symmetric bridge form of Theorem 6.30.1 used by downstream fixed-point proofs. -/
theorem lowerSemicontinuous_neg_iff_concaveClosure_eq_self
    (g : E → WithBotTop 𝕜) :
    LowerSemicontinuous (-g) ↔ concaveClosure g = g :=
  (concaveClosure_eq_self_iff_lowerSemicontinuous_neg g).symm

end

end
