import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_16_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y]
variable [Module 𝕜 Y] [ContinuousConstSMul 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜]

variable {I : Sort*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.2.2 identifies the polar of the intersection of the closures
  `closure (C i)` with the closure of the convex hull of the individual polars.
- `core/canonical`: the owner layer is scalar/pairing-generic, with the closed-convex bipolar
  bridge used internally.
--/

-- Proof sketch: apply Corollary 16.5.2.1 in the dual orientation to the family `(K i)ᵒ[𝕜]`
-- to compute the dual polar of `closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜]))`. Then rewrite each
-- double polar by the closed-convex bipolar bridges on `X` and `Y`, and apply the `Y`-side bridge
-- once more to the closed convex set `closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜]))`, which contains
-- `0` because the family is nonempty and every polar set contains `0`.
/-- Corollary 16.5.2.2 at the scalar/pairing owner layer: for a nonempty family of closed convex
sets containing `0`, the polar of their intersection equals the closure of the convex hull of
their individual polars. -/
theorem polar_iInter_eq_closure_convexHull_iUnion_polar
    (hbipolarX : ∀ {S : Set X}, IsClosed S → Convex 𝕜 S → (0 : X) ∈ S →
      (((Sᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = S))
    (hbipolarY : ∀ {S : Set Y}, IsClosed S → Convex 𝕜 S → (0 : Y) ∈ S →
      (((Sᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = S))
    (hpolar_closureY : ∀ S : Set Y,
      (((closure S)ᵒ[𝕜] : Set X) = (Sᵒ[𝕜] : Set X)))
    (K : I → Set X) (hI : Nonempty I) (hK_closed : ∀ i, IsClosed (K i))
    (hK_convex : ∀ i, Convex 𝕜 (K i)) (h0K : ∀ i, (0 : X) ∈ K i) :
    ((⋂ i, K i)ᵒ[𝕜] : Set Y) = closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜])) := by
  let U : Set Y := ⋃ i, (K i)ᵒ[𝕜]
  let Q : Set Y := convexHull 𝕜 U
  let P : Set Y := closure Q
  letI : HasPairingSwap Y X 𝕜 :=
    ⟨fun y x => (HasPairingSwap.pairing_swap (x := x) (y := y)).symm⟩
  have hdouble : ∀ i,
      (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = K i :=
    fun i ↦ hbipolarX (hK_closed i) (hK_convex i) (h0K i)
  have hQ_polar :
      (Qᵒ[𝕜] : Set X) = ⋂ i, (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) := by
    unfold Q U
    simpa using
      (polar_convexHull_iUnion_eq_iInter_polar (𝕜 := 𝕜)
        (C := fun i ↦ ((K i)ᵒ[𝕜] : Set Y)))
  have hP_polar : (Pᵒ[𝕜] : Set X) = ⋂ i, K i := by
    have hP_closure :
        (Pᵒ[𝕜] : Set X) = (Qᵒ[𝕜] : Set X) := by
      unfold P
      exact hpolar_closureY Q
    calc
      (Pᵒ[𝕜] : Set X) = (Qᵒ[𝕜] : Set X) := hP_closure
      _ = ⋂ i, (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) := hQ_polar
      _ = ⋂ i, K i := by
        simp [hdouble]
  have h0polar : ∀ i, (0 : Y) ∈ (K i)ᵒ[𝕜] := by
    intro i
    refine (Set.mem_polar_iff (C := K i) (xStar := (0 : Y))).2 ?_
    intro x hx
    simp [zero_le_one]
  have hP_zero : (0 : Y) ∈ P := by
    rcases hI with ⟨i0⟩
    have h0U : (0 : Y) ∈ U := Set.mem_iUnion.2 ⟨i0, h0polar i0⟩
    have h0Q : (0 : Y) ∈ Q := subset_convexHull 𝕜 U h0U
    simpa [P] using (subset_closure h0Q)
  have hQ_convex : Convex 𝕜 Q := by
    simpa [Q] using (convex_convexHull 𝕜 U)
  have hP_convex : Convex 𝕜 P := by
    simpa [P] using hQ_convex.closure
  have hPP : (((Pᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = P) :=
    hbipolarY isClosed_closure hP_convex hP_zero
  calc
    ((⋂ i, K i)ᵒ[𝕜] : Set Y) = (((Pᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y)) := by
          rw [hP_polar]
    _ = P := hPP
    _ = closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜])) := by rfl

-- Proof sketch: apply the owner theorem above to the closed family `fun i ↦ closure (C i)` and
-- use `hpolar_closureX` to remove the redundant closure inside each primal polar.
/-- Corollary 16.5.2.2, source-facing closure form: for a nonempty family of convex sets whose
closures contain `0`, the polar of `⋂ i, closure (C i)` equals
`closure (convexHull 𝕜 (⋃ i, (C i)ᵒ[𝕜]))`. -/
theorem polar_iInter_closure_eq_closure_convexHull_iUnion_polar_of_convex
    [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
    (hbipolarX : ∀ {S : Set X}, IsClosed S → Convex 𝕜 S → (0 : X) ∈ S →
      (((Sᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = S))
    (hbipolarY : ∀ {S : Set Y}, IsClosed S → Convex 𝕜 S → (0 : Y) ∈ S →
      (((Sᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = S))
    (hpolar_closureX : ∀ S : Set X,
      (((closure S)ᵒ[𝕜] : Set Y) = (Sᵒ[𝕜] : Set Y)))
    (hpolar_closureY : ∀ S : Set Y,
      (((closure S)ᵒ[𝕜] : Set X) = (Sᵒ[𝕜] : Set X)))
    (C : I → Set X) (hI : Nonempty I) (hC_convex : ∀ i, Convex 𝕜 (C i))
    (h0C : ∀ i, (0 : X) ∈ closure (C i)) :
    ((⋂ i, closure (C i))ᵒ[𝕜] : Set Y) = closure (convexHull 𝕜 (⋃ i, (C i)ᵒ[𝕜])) := by
  simpa [hpolar_closureX] using
    polar_iInter_eq_closure_convexHull_iUnion_polar
      hbipolarX hbipolarY hpolar_closureY
      (fun i ↦ closure (C i)) hI (fun _ ↦ isClosed_closure)
      (fun i ↦ (hC_convex i).closure) h0C

end
