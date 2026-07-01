import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4

noncomputable section

universe u v w

namespace Bifunction

variable {U : Type u} {X : Type v} {L : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.38 names the condition that a bifunction is fully closed.
- `core/canonical`: the one-sided owners are convex-side closedness (closed in the second
  variable) and concave-side closedness (closed in the first variable).
- `bridge/view`: the slice-wise `UpperSemicontinuous` / `LowerSemicontinuous` clauses are
  recovered as thin projection lemmas, so the raw semicontinuity surface remains available
  without being the primary owner.

Domain-style sampling used here:
- `Bifunction.IsConcaveClosed` and `Bifunction.IsConvexClosed` from Definition33.0.4;
- `UpperSemicontinuous` and `LowerSemicontinuous` as the slice-wise bridge views.

Layer target: `source-facing`, reusing the canonical Chapter 33 one-sided closedness owners.
-/

section FullyClosed

variable [TopologicalSpace U] [TopologicalSpace X]
variable [Preorder L]

/-- Definition33.0.38: a bifunction is fully closed when it is closed in the second variable
for each fixed first argument and upper semicontinuous in the first variable for each fixed second
argument. -/
def IsFullyClosed (K : U → X → L) : Prop :=
  IsConvexClosed K ∧ IsConcaveClosed K

-- Proof sketch: `IsFullyClosed` is defined as this conjunction.
@[simp] theorem isFullyClosed_iff (K : U → X → L) :
    IsFullyClosed K ↔ IsConvexClosed K ∧ IsConcaveClosed K := Iff.rfl

/-- Bridge view: `IsFullyClosed` is equivalent to lower semicontinuity in the second variable
and upper semicontinuity in the first variable. -/
theorem isFullyClosed_iff_lowerSemicontinuous_second_and_upperSemicontinuous_first
    (K : U → X → L) :
    IsFullyClosed K ↔
      (∀ u : U, LowerSemicontinuous (K u)) ∧
        (∀ x : X, UpperSemicontinuous (fun u : U ↦ K u x)) :=
  Iff.rfl

-- Proof sketch: apply the first conjunct of `IsFullyClosed`.
/-- A fully closed bifunction is convex-side closed in the canonical Chapter 7 owner sense. -/
theorem IsFullyClosed.convexClosed {K : U → X → L} (hK : IsFullyClosed K) :
    IsConvexClosed K :=
  hK.1

-- Proof sketch: apply the second conjunct of `IsFullyClosed`.
/-- A fully closed bifunction is concave-side closed in the canonical Chapter 7 owner sense. -/
theorem IsFullyClosed.concaveClosed {K : U → X → L} (hK : IsFullyClosed K) :
    IsConcaveClosed K :=
  hK.2

-- Proof sketch: evaluate `IsFullyClosed.convexClosed` at the chosen first-variable point.
theorem IsFullyClosed.lowerSemicontinuous_second {K : U → X → L}
    (hK : IsFullyClosed K) (u : U) :
    LowerSemicontinuous (K u) :=
  hK.convexClosed u

-- Proof sketch: evaluate `IsFullyClosed.concaveClosed` at the chosen second-variable point.
theorem IsFullyClosed.upperSemicontinuous_first {K : U → X → L}
    (hK : IsFullyClosed K) (x : X) :
    UpperSemicontinuous (fun u : U ↦ K u x) :=
  hK.concaveClosed x

end FullyClosed

section FullyClosedClosure2Bridge

open scoped Rockafellar

variable {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [NoBotOrder 𝕜]

/-- Owner-level bridge with the primitive first-variable owner kept explicit: full closedness is
equivalent to simultaneous fixedness under the second-variable closure operator `cl₂` and
first-variable concave-side closedness. -/
theorem isFullyClosed_iff_closure2_eq_and_concaveClosed
    (K : U → X → WithTopBot 𝕜) :
    IsFullyClosed K ↔ cl₂ K = K ∧ IsConcaveClosed K := by
  rw [isFullyClosed_iff, isConvexClosed_iff_closure2_eq]

end FullyClosedClosure2Bridge

section FullyClosedFixedPoint

open scoped Rockafellar

variable {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [TopologicalSpace U] [TopologicalSpace X]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddCommGroup 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [NoBotOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]

/-- Owner-level fixed-point characterization: full closedness is exactly simultaneous fixedness
under the two one-sided closure operators `cl₂` and `cl₁`. -/
theorem isFullyClosed_iff_closure2_eq_and_closure1_eq
    (K : U → X → WithTopBot 𝕜) :
    IsFullyClosed K ↔ cl₂ K = K ∧ cl₁ K = K := by
  rw [isFullyClosed_iff_closure2_eq_and_concaveClosed, isConcaveClosed_iff_closure1_eq]

end FullyClosedFixedPoint

end Bifunction
