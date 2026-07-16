import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_2

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.4 introduces the two one-variable closure operators of a
  bifunction: concave closure in the first variable and convex closure in the second variable.
- `core/canonical`: the owner constructions are Chapter 6's `concaveClosure` and Chapter 2's
  lower-semicontinuous hull `cl(·)`.
- `bridge/view`: later Chapter 7 files use slice-wise `UpperSemicontinuous` and
  `LowerSemicontinuous` owners; this file keeps only the whole-space fixed-point bridges from
  those owners to `cl₁` and `cl₂`.

Domain-style sampling used here:
- `concaveClosure`;
- `lowerSemicontinuous_neg_iff_concaveClosure_eq_self`;
- `concaveClosure_eq_self_iff_upperSemicontinuous`;
- `UpperSemicontinuous`;
- `lowerSemicontinuousHull`, written `cl(·)`;
- `lowerSemicontinuousHull_eq_self`;
- `lowerSemicontinuous_lowerSemicontinuousHull`;
- `LowerSemicontinuous`.

Layer target: the source-facing partial closure operators, together with the thin fixed-point
bridges needed downstream in Chapter 7.
-/

section ConcaveClosure

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace U]

/-- Definition33.0.4: the first-variable partial closure `cl₁ K` is obtained by applying the
Chapter 6 concave closure to each slice `u ↦ K u x`; the second-variable closure `cl₂ K` is
introduced below. -/
def closure1 [ConditionallyCompleteLattice 𝕜] [Neg 𝕜]
    (K : U → X → WithTopBot 𝕜) : U → X → WithTopBot 𝕜 :=
  fun u x ↦ concaveClosure (fun u' ↦ K u' x) u

scoped[Rockafellar] prefix:max "cl₁ " => Bifunction.closure1

-- Proof sketch: unfold `closure1`; this is just the defining equation of the first-variable
-- closure operator.
/-- Evaluating `cl₁ K` at `(u, x)` is evaluating the concave closure of the first-variable slice
at `u`. -/
@[simp] theorem closure1_apply [ConditionallyCompleteLattice 𝕜] [Neg 𝕜]
    (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    cl₁ K u x = concaveClosure (fun u' ↦ K u' x) u :=
  rfl

/-- First-variable closedness owner: every first-variable slice is upper semicontinuous. -/
def IsConcaveClosed {L : Type w} [Preorder L] (K : U → X → L) : Prop :=
  ∀ x : X, UpperSemicontinuous (fun u : U ↦ K u x)

/-- First-variable closedness is exactly slice-wise upper semicontinuity. -/
@[simp] theorem isConcaveClosed_iff {L : Type w} [Preorder L] (K : U → X → L) :
    IsConcaveClosed K ↔ ∀ x : X, UpperSemicontinuous (fun u : U ↦ K u x) :=
  Iff.rfl

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜]
variable [AddGroup 𝕜]

-- Proof sketch: for each fixed `x`, write `g u = K u x`. The lower-semicontinuity hypothesis on
-- `-g` gives `cl(-g) = -g` by the Chapter 2 fixed-point theorem, and Theorem 6.30.1 turns this
-- into `concaveClosure g = g`.
/-- Forward primitive fixed-point bridge for `cl₁`: if every negated first-variable slice is lower
semicontinuous, then `cl₁` fixes the bifunction. -/
theorem closure1_eq_of_lowerSemicontinuousNegSlices (K : U → X → WithTopBot 𝕜)
    (hK : ∀ x : X, LowerSemicontinuous (fun u : U ↦ -K u x)) :
    cl₁ K = K := by
  ext u x
  let g : U → WithTopBot 𝕜 := fun u' ↦ K u' x
  have hg_lsc : LowerSemicontinuous (-g) := by
    simpa [g] using hK x
  have hg_fix : cl(-g) = -g :=
    lowerSemicontinuousHull_eq_self hg_lsc
  have hfix : concaveClosure g = g :=
    (concaveClosure_eq_self_iff_cl_neg_eq_neg g).2 hg_fix
  simpa [closure1, g] using congrFun hfix u

end

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [NoBotOrder 𝕜]
variable [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddGroup 𝕜]

-- Proof sketch: fix `x` and write `g u = K u x`. Then `cl₁ (cl₁ K)` is the concave closure of
-- `concaveClosure g`. Negating this slice gives `cl(-g)`, which is lower semicontinuous by the
-- Chapter 2 owner theorem for `cl(·)`, so the Chapter 6 sign-dual fixed-point bridge yields
-- `concaveClosure (concaveClosure g) = concaveClosure g`.
/-- The first-variable closure operator `cl₁` is idempotent. -/
@[simp] theorem closure1_idem (K : U → X → WithTopBot 𝕜) :
    cl₁ (cl₁ K) = cl₁ K := by
  ext u x
  let g : U → WithTopBot 𝕜 := fun u' ↦ K u' x
  have hneg : -concaveClosure g = cl(-g) := by
    ext u'
    simp [g, concaveClosure_eq_neg_lowerSemicontinuousHull_neg]
  have hg_lsc : LowerSemicontinuous (-concaveClosure g) := by
    rw [hneg]
    exact lowerSemicontinuous_lowerSemicontinuousHull (-g)
  have hcl_fix : cl(-concaveClosure g) = -concaveClosure g :=
    lowerSemicontinuousHull_eq_self hg_lsc
  have hfix : concaveClosure (concaveClosure g) = concaveClosure g :=
    (concaveClosure_eq_self_iff_cl_neg_eq_neg (concaveClosure g)).2 hcl_fix
  simpa [closure1, g] using congrFun hfix u

-- Proof sketch: this is the primitive fixed-point bridge for `cl₁`: each first-variable slice is
-- fixed by `concaveClosure` exactly when the negated slice is lower semicontinuous (Theorem
-- 6.30.1). This avoids using the stronger upper-semicontinuity bridge.
/-- Primitive fixed-point bridge for `cl₁`: a bifunction is fixed by `cl₁` exactly when every
negated first-variable slice is lower semicontinuous. -/
theorem lowerSemicontinuousNegSlices_of_closure1_eq (K : U → X → WithTopBot 𝕜)
    (hK : cl₁ K = K) :
    ∀ x : X, LowerSemicontinuous (fun u : U ↦ -K u x) := by
  intro x
  let g : U → WithTopBot 𝕜 := fun u' ↦ K u' x
  have hfix : concaveClosure g = g := by
    ext u
    simpa [closure1, g] using congrFun (congrFun hK u) x
  have hcl_fix : cl(-g) = -g :=
    (concaveClosure_eq_self_iff_cl_neg_eq_neg g).1 hfix
  have hg_lsc : LowerSemicontinuous (cl(-g)) :=
    lowerSemicontinuous_lowerSemicontinuousHull (-g)
  have hg_lsc' : LowerSemicontinuous (-g) := hcl_fix ▸ hg_lsc
  simpa [g] using hg_lsc'

/-- Primitive fixed-point bridge for `cl₁`: a bifunction is fixed by `cl₁` exactly when every
negated first-variable slice is lower semicontinuous. -/
theorem lowerSemicontinuousNegSlices_iff_closure1_eq (K : U → X → WithTopBot 𝕜) :
    (∀ x : X, LowerSemicontinuous (fun u : U ↦ -K u x)) ↔ cl₁ K = K := by
  constructor
  · intro hK
    exact closure1_eq_of_lowerSemicontinuousNegSlices K hK
  · intro hK
    exact lowerSemicontinuousNegSlices_of_closure1_eq K hK

section

variable [AddCommGroup 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [IsOrderedAddMonoid 𝕜]

/-- Source-facing bridge: first-variable closedness via upper semicontinuity is equivalent to the
primitive neg-slice lower-semicontinuity formulation. -/
theorem isConcaveClosed_iff_lowerSemicontinuousNegSlices (K : U → X → WithTopBot 𝕜) :
    IsConcaveClosed K ↔ ∀ x : X, LowerSemicontinuous (fun u : U ↦ -K u x) := by
  constructor
  · intro hK x
    let g : U → WithTopBot 𝕜 := fun u ↦ K u x
    have hfix : concaveClosure g = g :=
      (concaveClosure_eq_self_iff_upperSemicontinuous g).2 (hK x)
    have hg_lsc : LowerSemicontinuous (-g) :=
      (lowerSemicontinuous_neg_iff_concaveClosure_eq_self g).2 hfix
    simpa [g] using hg_lsc
  · intro hK x
    let g : U → WithTopBot 𝕜 := fun u ↦ K u x
    have hg_lsc : LowerSemicontinuous (-g) := by
      simpa [g] using hK x
    have hfix : concaveClosure g = g :=
      (lowerSemicontinuous_neg_iff_concaveClosure_eq_self g).1 hg_lsc
    exact (concaveClosure_eq_self_iff_upperSemicontinuous g).1 hfix

/-! Symmetric owner-style fixed-point bridges for `cl₁`, parallel to the `cl₂` API. -/
/-- If a bifunction is concave-closed, then the first-variable closure `cl₁` fixes it. -/
theorem IsConcaveClosed.closure1_eq {K : U → X → WithTopBot 𝕜}
    (hK : IsConcaveClosed K) :
    cl₁ K = K := by
  exact closure1_eq_of_lowerSemicontinuousNegSlices K
    ((isConcaveClosed_iff_lowerSemicontinuousNegSlices K).1 hK)

/-- Reverse fixed-point bridge for `cl₁`: fixedness under `cl₁` implies concave-closedness. -/
theorem isConcaveClosed_of_closure1_eq {K : U → X → WithTopBot 𝕜}
    (hK : cl₁ K = K) :
    IsConcaveClosed K := by
  exact (isConcaveClosed_iff_lowerSemicontinuousNegSlices K).2
    (lowerSemicontinuousNegSlices_of_closure1_eq K hK)

-- Proof sketch: combine the source-facing bridge above with the primitive fixed-point bridge
-- `lowerSemicontinuousNegSlices_iff_closure1_eq`.
/-- A bifunction is concave-closed exactly when it is fixed by the first-variable closure
operator `cl₁`. -/
theorem isConcaveClosed_iff_closure1_eq (K : U → X → WithTopBot 𝕜) :
    IsConcaveClosed K ↔ cl₁ K = K := by
  constructor
  · intro hK
    exact hK.closure1_eq
  · intro hK
    exact isConcaveClosed_of_closure1_eq hK

end

end

end ConcaveClosure

section ConvexClosure

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace X]

/-- The second-variable partial closure `cl₂ K` is obtained by applying Rockafellar's closure
operator `cl(·)` to each slice `x ↦ K u x`. -/
def closure2 [ConditionallyCompleteLattice 𝕜]
    (K : U → X → WithTopBot 𝕜) : U → X → WithTopBot 𝕜 :=
  fun u ↦ cl(K u)

scoped[Rockafellar] prefix:max "cl₂ " => Bifunction.closure2

-- Proof sketch: unfold `closure2`; this is just the defining equation of the second-variable
-- closure operator.
/-- Evaluating `cl₂ K` at `(u, x)` is evaluating the lower-semicontinuous hull of the
second-variable slice `K u` at `x`. -/
@[simp] theorem closure2_apply [ConditionallyCompleteLattice 𝕜]
    (K : U → X → WithTopBot 𝕜) (u : U) (x : X) :
    cl₂ K u x = cl(K u) x :=
  rfl

/-- Second-variable closedness owner: every second-variable slice is lower semicontinuous. -/
def IsConvexClosed {L : Type w} [Preorder L] (K : U → X → L) : Prop :=
  ∀ u : U, LowerSemicontinuous (K u)

/-- Second-variable closedness is exactly slice-wise lower semicontinuity. -/
@[simp] theorem isConvexClosed_iff {L : Type w} [Preorder L] (K : U → X → L) :
    IsConvexClosed K ↔ ∀ u : U, LowerSemicontinuous (K u) :=
  Iff.rfl

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜] [NoBotOrder 𝕜]

-- Proof sketch: apply the Chapter 2 one-variable fixed-point theorem for `cl(·)` to each
-- second-variable slice `K u`.
/-- Primitive fixed-point bridge for `cl₂`: slice-wise lower semicontinuity implies fixedness
under the second-variable closure operator. -/
theorem IsConvexClosed.closure2_eq {K : U → X → WithTopBot 𝕜}
    (hK : IsConvexClosed K) :
    cl₂ K = K := by
  ext u x
  have hu : cl(K u) = K u :=
    lowerSemicontinuousHull_eq_self (hK u)
  simpa [closure2] using congrFun hu x

end

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

-- Proof sketch: rewrite each slice from the fixed-point equation and transport lower
-- semicontinuity from the canonical closed slice `cl(K u)`.
/-- Reverse fixed-point bridge for `cl₂`: fixedness under `cl₂` implies slice-wise lower
semicontinuity. -/
theorem isConvexClosed_of_closure2_eq {K : U → X → WithTopBot 𝕜}
    (hK : cl₂ K = K) :
    IsConvexClosed K := by
  intro u
  have hu : cl(K u) = K u := by
    ext x
    simpa [closure2] using congrFun (congrFun hK u) x
  exact hu ▸
    (lowerSemicontinuous_lowerSemicontinuousHull (K u) :
      LowerSemicontinuous (cl(K u)))

section

variable [NoBotOrder 𝕜]

-- Proof sketch: fix `u`; then `x ↦ cl₂ K u x` is the lower-semicontinuous hull of the already
-- lower-semicontinuous slice `cl(K u)`, so the Chapter 2 fixed-point theorem for `cl(·)` gives
-- idempotence pointwise.
/-- The second-variable closure operator `cl₂` is idempotent. -/
@[simp] theorem closure2_idem (K : U → X → WithTopBot 𝕜) :
    cl₂ (cl₂ K) = cl₂ K := by
  have hclosed : IsConvexClosed (cl₂ K) := by
    intro u
    simpa [closure2] using
      (lowerSemicontinuous_lowerSemicontinuousHull (K u) :
        LowerSemicontinuous (cl(K u)))
  exact hclosed.closure2_eq

-- Proof sketch: combine the primitive forward bridge `IsConvexClosed.closure2_eq` with the
-- reverse bridge `isConvexClosed_of_closure2_eq`.
/-- A bifunction is convex-closed exactly when it is fixed by the second-variable closure
operator `cl₂`. -/
theorem isConvexClosed_iff_closure2_eq (K : U → X → WithTopBot 𝕜) :
    IsConvexClosed K ↔ cl₂ K = K := by
  constructor
  · intro hK
    exact hK.closure2_eq
  · intro hK
    exact isConvexClosed_of_closure2_eq hK

end

end

end ConvexClosure

end Bifunction
