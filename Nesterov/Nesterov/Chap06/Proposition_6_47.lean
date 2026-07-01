import Nesterov.Chap03.Definition_3_1_1_2
import Nesterov.Chap06.Proposition_6_25
import Nesterov.Chap06.Definition_6_61

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConvexAnalysis Gradient WeightSequenceNotation

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- Proposition 6.47 lies in the Chapter 6 accuracy-certificate / averaged-dual domain.

Mandatory domain-style sampling before refinement:
- `Finset.centerMass` and `ConvexOn.map_centerMass_le`, the canonical owners for normalized finite
  weighted averages and Jensen's inequality on those averages;
- `A[a](t)` in `Chap06/Definition_6_53`, the chapter owner for accumulated weights;
- `localModelAccuracyCertificate` in `Chap06/Definition_6_61`, the source-facing owner `ℓ_t`;
- `smoothedDualObjective` in `Chap06/Proposition_6_25`, whose zero-smoothing specialization is the
  chapter owner for the dual objective `ν ↦ inf_{x ∈ Q} (ψ(x) + A x ν) - g(ν)`;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from the
  `EReal`-valued dual objective to its displayed real-valued form.

Best owner abstraction:
- source-facing: Proposition 6.47's certificate `ℓ_t`, averaged dual point `ν_t`, and final
  primal-dual gap estimate;
- core/canonical: `localModelAccuracyCertificate`, `A[a](t)`, and the zero-smoothing
  `smoothedDualObjective`;
- bridge/view: the `Finset.centerMass` realization of `ν_t` and the center-mass scalar correction
  term for the sampled dual values.

Primitive data:
- the feasible set `Q`, the regularizer `ψ`, the iterate sequence `xSeq`, and the weights `a`;
- the dual representation data `A`, `g`, and `u`;
- the dualized local-linearization hypothesis along the sampled iterates.

Derived API:
- the canonical certificate value `localModelAccuracyCertificate Q f ψ xSeq a t`;
- the averaged dual point
  `ν_t = (Finset.range (t + 1)).centerMass a (fun k ↦ u (x_k))`;
- the Chapter 6 dual objective
  `extendedRealRealPart (smoothedDualObjective A Q (Function.extend Subtype.val ψ 0) g 0 0)`;
- the scalar center-mass correction term
  `(Finset.range (t + 1)).centerMass a (fun k ↦ g (u (x_k)))`.

Source/core/bridge triage:
- source-facing: the proposition below;
- core/canonical: `localModelAccuracyCertificate` and `smoothedDualObjective`;
- bridge/view: the normalized finite weighted sum defining `ν_t`.

The previous version rebuilt a raw normalized-sum dual iterate and packaged the final result as
one large conjunction. This refinement deletes that duplicate weighted-average surface, exposes
the averaged dual point through `Finset.centerMass`, removes the now-redundant explicit
average-membership hypothesis, and restores the main source-facing conclusion as an
upper-gap theorem plus an interval-valued companion whose left endpoint is supplied by an explicit
weak-duality hypothesis.
-/

/-- If the affine models entering the Chapter 6 certificate `ℓ_t` can be rewritten through the
selected dual values `u(x_k)` and the accumulated weight `A_t = A[a](t)` is positive, then `ℓ_t`
equals the zero-smoothing dual objective at the center-mass dual average, corrected by the
center mass of the sampled dual values `g(u(x_k))`. -/
-- Proof sketch: unfold `localModelAccuracyCertificate`, rewrite the weighted affine models with
-- `hlocal`, and identify the resulting normalized finite sum with the zero-smoothing dual
-- objective evaluated at the center-mass dual average.
theorem localModelAccuracyCertificate_eq_dual_average_correction
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (t : ℕ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (hAt : 0 < A[a](t))
    (hν_dom :
      (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)) ∈
        dom
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0)) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    localModelAccuracyCertificate Q f ψ xSeq a t =
      dualObj νt + g νt -
        (Finset.range (t + 1)).centerMass a (fun k ↦ g (u (xSeq k : E))) := sorry

/-- Under the convexity of the sampled dual term `g` on the feasible dual set `U`, the
center-mass formula for `ℓ_t` yields the lower bound `ℓ_t ≤ \bar g(ν_t)` at the averaged dual
point `ν_t = (Finset.range (t + 1)).centerMass a (fun k ↦ u (x_k))`. -/
-- Proof sketch: combine
-- `localModelAccuracyCertificate_eq_dual_average_correction` with Jensen's inequality in the
-- `Finset.centerMass` form for `g` on `U`.
theorem localModelAccuracyCertificate_le_dualObjective_of_dual_average
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g)
    (hν_dom :
      (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)) ∈
        dom
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0)) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    localModelAccuracyCertificate Q f ψ xSeq a t ≤ dualObj νt := sorry

/-- Proposition 6.47: let
`ν_t = (Finset.range (t + 1)).centerMass a (fun k ↦ u (x_k))`.
If the affine models entering the Chapter 6 certificate `ℓ_t` can be rewritten through the dual
representation `A x (u(x_k)) - g(u(x_k))`, then the certificate is bounded above by the
zero-smoothing dual objective at `ν_t`. Consequently, any estimate
`\bar f(x_t) - ℓ_t ≤ B_{v,t} / A_t` yields the upper bound
`\bar f(x_t) - \bar g(ν_t) ≤ B_{v,t} / A_t`. -/
-- Proof sketch: subtract the lower bound
-- `localModelAccuracyCertificate Q f ψ xSeq a t ≤ dualObj νt` from the assumed certificate-gap
-- estimate and simplify the resulting inequality.
theorem localModelAccuracyCertificate_gap_upper_bound_of_dual_average
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (Bvt : ℝ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g)
    (hν_dom :
      (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)) ∈
        dom
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0))
    (hcertificate :
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barf (xSeq t) - localModelAccuracyCertificate Q f ψ xSeq a t ≤ Bvt / A[a](t)) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
    barf (xSeq t) - dualObj νt ≤ Bvt / A[a](t) := sorry

/-- Proposition 6.47 in interval form: if, in addition to the upper-gap hypotheses above, the
averaged dual point `ν_t` satisfies the weak-duality lower bound
`\bar g(ν_t) ≤ \bar f(x_t)`, then the resulting primal-dual gap belongs to the canonical interval
`[0, B_{v,t} / A_t]`. -/
-- Proof sketch: use `hweak` for the left endpoint `0 ≤ barf (xSeq t) - dualObj νt` and
-- `localModelAccuracyCertificate_gap_upper_bound_of_dual_average` for the right endpoint.
theorem localModelAccuracyCertificate_gap_bound_of_dual_average
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ F) (g : F → ℝ) (u : E → F) (U : Set F) (t : ℕ)
    (Bvt : ℝ)
    (hlocal :
      ∀ (k : ℕ) (x : Q),
        f (xSeq k) + inner ℝ (∇ f (xSeq k : E)) ((x : E) - (xSeq k : E)) =
          A (x : E) (u (xSeq k : E)) - g (u (xSeq k : E)))
    (ha_nonneg : ∀ k ∈ Finset.range (t + 1), 0 ≤ a k)
    (hAt : 0 < A[a](t))
    (hu_mapsTo : Set.MapsTo u Q U)
    (hg_convex : ConvexOn ℝ U g)
    (hν_dom :
      (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E)) ∈
        dom
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0))
    (hweak :
      let dualObj :=
        extendedRealRealPart
          (smoothedDualObjective
            A
            Q
            (Function.extend Subtype.val ψ 0)
            g
            (fun _ : E ↦ 0)
            0)
      let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      dualObj νt ≤ barf (xSeq t))
    (hcertificate :
      let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
      barf (xSeq t) - localModelAccuracyCertificate Q f ψ xSeq a t ≤ Bvt / A[a](t)) :
    let dualObj :=
      extendedRealRealPart
        (smoothedDualObjective
          A
          Q
          (Function.extend Subtype.val ψ 0)
          g
          (fun _ : E ↦ 0)
          0)
    let νt := (Finset.range (t + 1)).centerMass a (fun k ↦ u (xSeq k : E))
    let barf : Q → ℝ := fun x ↦ ψ x + g (u x)
    barf (xSeq t) - dualObj νt ∈ Set.Icc 0 (Bvt / A[a](t)) := sorry

end
