import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_8

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped PolarCone

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
variable [((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)).IsContPerfPair]

local notation "pairingLinearMap" => (HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.4 states that the polar of the polar of a nonempty convex cone `K`
  is the closure of `K`.
- `core/canonical`: the owner abstractions are mathlib's bundled `ConvexCone ℝ E`, the bundled
  closure `ConvexCone.closure`, the set-duality owner `PointedCone.dual`, and its proper-cone
  closed owner `ProperCone.dual` for a continuous perfect pairing.
- `bridge/view`: `polarCone` is Rockafellar's nonpositive-sign-convention view of
  `PointedCone.dual (-(HasLinearPairing.pairingLinear))`, so the theorem remains source-facing
  while its proof factors through closure invariance of `polarCone`, the sign bridge between
  `polarCone` and `ProperCone.dual`, and the canonical proper-cone bipolar owner theorem
  `ProperCone.dual_flip_dual`.

Domain-style sampling used here:
- `ConvexCone ℝ E` as the canonical owner for convex-cone structure;
- `ConvexCone.closure` as the canonical closed-cone completion;
- `PointedCone.dual` as the owner/set bridge behind the source-facing sign convention;
- `polarCone_closure` as closure invariance at the source-facing owner;
- `ProperCone.dual_flip_dual` as the canonical bipolar theorem for proper cones.

Primitive data vs derived API:
- primitive input: a bundled pointed cone `K : PointedCone ℝ E`;
- derived API: the source-facing bipolar equality
  `((K : Set E)ᵒ[ℝ] : Set E)ᵒ[ℝ] = closure (K : Set E)`.

Scalar-layer note:
- this file remains specialized to `ℝ` because the upstream owner theorem
  `ProperCone.dual_flip_dual` used in the proof is currently available in mathlib only at the
  real locally convex layer.
-/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ] in
private theorem polarCone_eq_neg_dual (K : Set E) :
    (((Kᵒ[ℝ] : PointedCone ℝ E) : Set E)) = (-(ProperCone.dual pairingLinearMap K : Set E)) := by
  ext y
  change y ∈ Kᵒ[ℝ] ↔ y ∈ (-(ProperCone.dual pairingLinearMap K : Set E))
  rw [mem_polarCone_iff]
  constructor
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K
    rw [ProperCone.mem_dual]
    intro x hx
    have hxle : (pairingLinearMap x) y ≤ (0 : ℝ) := hy x hx
    simpa [LinearMap.map_neg] using (neg_nonneg.mpr hxle)
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K at hy
    rw [ProperCone.mem_dual] at hy
    intro x hx
    have hxnonneg : (0 : ℝ) ≤ (pairingLinearMap x) (-y) := hy (x := x) hx
    have hxneg : (0 : ℝ) ≤ -((pairingLinearMap x) y) := by
      simpa [LinearMap.map_neg] using hxnonneg
    exact neg_nonneg.mp hxneg

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ] in
private theorem dual_neg_eq_neg_dual (K : Set E) :
    ProperCone.dual pairingLinearMap (-K) = (-(ProperCone.dual pairingLinearMap K : Set E)) := by
  ext y
  constructor
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K
    have hy' : ∀ ⦃x : E⦄, x ∈ -K → 0 ≤ (pairingLinearMap x) y := by
      simpa [ProperCone.mem_dual] using hy
    rw [ProperCone.mem_dual]
    intro x hx
    have hneg : (0 : ℝ) ≤ (pairingLinearMap (-x)) y := hy' (x := -x) (by simpa using hx)
    have hxle : (pairingLinearMap x) y ≤ (0 : ℝ) := by
      have hxneg : (0 : ℝ) ≤ -((pairingLinearMap x) y) := by
        simpa [LinearMap.map_neg] using hneg
      exact neg_nonneg.mp hxneg
    simpa [LinearMap.map_neg] using (neg_nonneg.mpr hxle)
  · intro hy
    change -y ∈ ProperCone.dual pairingLinearMap K at hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) (-y) := by
      simpa [ProperCone.mem_dual] using hy
    have hdual : ∀ ⦃x : E⦄, x ∈ -K → 0 ≤ (pairingLinearMap x) y := by
      intro x hx
      have hxK : -x ∈ K := by simpa using hx
      have hneg : (0 : ℝ) ≤ (pairingLinearMap (-x)) (-y) := hy' (x := -x) hxK
      simpa [LinearMap.map_neg] using hneg
    exact (by simpa [ProperCone.mem_dual] using hdual)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [HasContinuousPairing E E ℝ] in
private theorem dual_eq_dual_flip (K : Set E) :
    (ProperCone.dual pairingLinearMap K : Set E) =
      (ProperCone.dual
        ((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) K : Set E) := by
  ext y
  constructor
  · intro hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) y := by
      simpa [ProperCone.mem_dual] using hy
    have hyflip : ∀ ⦃x : E⦄, x ∈ K →
        0 ≤ (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := by
      intro x hx
      change (0 : ℝ) ≤ (pairingLinearMap y) x
      have hxy : (0 : ℝ) ≤ (pairingLinearMap x) y := hy' hx
      have hswap : (pairingLinearMap y) x = (pairingLinearMap x) y := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using
          (HasPairingSwap.pairing_swap (x := y) (y := x))
      simpa [hswap] using hxy
    simpa [ProperCone.mem_dual] using hyflip
  · intro hy
    have hy' : ∀ ⦃x : E⦄, x ∈ K →
        0 ≤ (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := by
      simpa [ProperCone.mem_dual] using hy
    have hyorig : ∀ ⦃x : E⦄, x ∈ K → 0 ≤ (pairingLinearMap x) y := by
      intro x hx
      have hyx : (0 : ℝ) ≤
          (((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip) x) y := hy' hx
      change (0 : ℝ) ≤ (pairingLinearMap y) x at hyx
      have hswap : (pairingLinearMap y) x = (pairingLinearMap x) y := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using
          (HasPairingSwap.pairing_swap (x := y) (y := x))
      simpa [hswap] using hyx
    simpa [ProperCone.mem_dual] using hyorig

-- Proof sketch: first replace `K` by its closure using the owner closure-invariance theorem for
-- `polarCone`. For the closed cone `K.closure`, the double source-facing polar is rewritten
-- through the sign bridge to `ProperCone.dual`, then reduced to the proper-cone bipolar owner
-- theorem `ProperCone.dual_flip_dual`.
/-- Text 14.0.4: the polar of the polar of a nonempty convex cone `K` is the closure of the
carrier of `K`. -/
private theorem polarCone_polarCone_eq_closure_of_nonempty_convexCone
    (K : ConvexCone ℝ E) (hK_nonempty : (K : Set E).Nonempty) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) := by
  have hpolarClosure :
      (((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) := by
    exact congrArg (fun P : PointedCone ℝ E => (P : Set E))
      (polarCone_closure (𝕜 := ℝ) (K := (K : Set E)))
  have hdoubleClosure :
      (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) :=
      by
    exact (congrArg (fun S : Set E ↦ ((Sᵒ[ℝ] : PointedCone ℝ E) : Set E)) hpolarClosure).symm
  have hKcl : (K.closure : Set E).Nonempty ∧ IsClosed (K.closure : Set E) := by
    constructor
    · exact Set.Nonempty.mono subset_closure hK_nonempty
    · simp [ConvexCone.coe_closure]
  let Kc : ProperCone ℝ E :=
    { toSubmodule :=
        (K.closure).toPointedCone (ConvexCone.Pointed.of_nonempty_of_isClosed hKcl.1 hKcl.2)
      isClosed' := hKcl.2 }
  have hKc_set : (Kc : Set E) = closure (K : Set E) := by
    change (K.closure : Set E) = closure (K : Set E)
    rfl
  calc
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
        (((((closure (K : Set E))ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) :=
        hdoubleClosure
    _ = (((((Kc : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) := by
          simp [hKc_set]
    _ = (-(ProperCone.dual pairingLinearMap
            (((Kc : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) : Set E)) := by
      rw [polarCone_eq_neg_dual]
    _ = (-(ProperCone.dual pairingLinearMap
            (-(ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E)) := by
      rw [polarCone_eq_neg_dual]
    _ = (-(-(ProperCone.dual pairingLinearMap
            ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E)) :
          Set E) := by
      rw [dual_neg_eq_neg_dual]
    _ = (ProperCone.dual pairingLinearMap
          ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E) := by
      rw [neg_neg]
    _ = (ProperCone.dual
          ((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ).flip)
          ((ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)) : Set E) := by
      simpa using
        (dual_eq_dual_flip
          (K := (ProperCone.dual pairingLinearMap (Kc : Set E) : Set E)))
    _ = (Kc : Set E) := by
      exact congrArg ((↑) : ProperCone ℝ E → Set E)
        (ProperCone.dual_flip_dual pairingLinearMap Kc)
    _ = closure (K : Set E) := hKc_set

-- Proof sketch: apply the nonempty-convex-cone bridge theorem to the canonical pointed-cone
-- owner `(K : ConvexCone ℝ E)`, using `0 ∈ K` from pointedness.
/-- Text 14.0.4: for a pointed convex cone `K`, the polar of the polar of `K` is the closure of
its carrier. This owner form keeps nonemptiness in the cone owner (`PointedCone`) rather than as
an extra theorem argument. -/
theorem polarCone_polarCone_eq_closure
    (K : PointedCone ℝ E) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) := by
  exact polarCone_polarCone_eq_closure_of_nonempty_convexCone
    (K := (K : ConvexCone ℝ E))
    ⟨0, K.zero_mem⟩

/-- Nonempty-convex-cone bridge for Text 14.0.4. This keeps the source hypothesis form available
when an upstream declaration still packages the cone as `ConvexCone` plus explicit nonemptiness. -/
theorem polarCone_polarCone_eq_closure_of_nonempty
    (K : ConvexCone ℝ E) (hK_nonempty : (K : Set E).Nonempty) :
    (((((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) =
      closure (K : Set E) :=
  polarCone_polarCone_eq_closure_of_nonempty_convexCone K hK_nonempty

end
