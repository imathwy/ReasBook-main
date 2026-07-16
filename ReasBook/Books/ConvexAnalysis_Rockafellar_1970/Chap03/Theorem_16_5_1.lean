import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

open Function
open scoped Rockafellar

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.1 identifies the conjugate of the convex hull of an arbitrary
  family of functions with the pointwise supremum of the individual conjugates.
- `core/canonical`: the owner constructions already present in the project are
  `conv(⨅ i, f i)` for `conv {f_i | i ∈ I}` and `convexConjugate` for Fenchel conjugation.
- `bridge/view`: the proof uses the maximal-minorant characterization
  `Function.isGreatest_conv_iInf_minorant` together with a direct pointwise bridge between
  affine-defect upper bounds and conjugate upper bounds.

Domain-style sampling used here:
- `conv`;
- `Function.isGreatest_conv_iInf_minorant`;
- `convexConjugate`;
- `convexConjugate_le_convexConjugate_of_le`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the complete-lattice pointwise supremum `⨆ i, ...`.

Primitive data vs derived API:
- primitive input: the family `f : I → X → WithTopBot 𝕜`;
- derived API: the conjugacy identity between the family convex hull and the supremum of the
  individual conjugates as functions on the dual owner `Y`.

Layer target: `source-facing`, stated directly in terms of the already-canonical family hull owner
`conv(⨅ i, f i)` and the conjugate owner. The source proper-convex hypotheses are redundant for
this identity, so they are omitted from the public statement.
-/

-- Proof sketch: rewrite `f⋆ y⋆` as `⨆ x, (⟪x, y⋆⟫ - f x)` and solve the inequality
-- `(fun x ↦ (⟪x, y⋆⟫ - μ⋆ : 𝕜)).toWithTopBot ≤ f` pointwise using
-- `WithTopBot.sub_le_iff_le_add` in both directions.
private theorem pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
    (f : X → WithTopBot 𝕜) (yStar : Y) (μStar : 𝕜) :
    (fun x : X ↦ (⟪x, yStar⟫ₚ - μStar : 𝕜)).toWithTopBot ≤ f ↔
      f⋆ yStar ≤ (μStar : WithTopBot 𝕜) := by
  rw [show f⋆ yStar =
      ⨆ x : X, (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) by
    simpa using convexConjugate_eq_iSup_pairing_sub f yStar]
  constructor
  · intro h
    refine iSup_le fun x ↦ ?_
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μStar : WithTopBot 𝕜)) ≤ f x := by
      simpa [Function.toWithTopBot, sub_eq_add_neg, WithTopBot.sub_eq_add_neg] using h x
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤ f x + (μStar : WithTopBot 𝕜) :=
      (WithTopBot.sub_le_iff_le_add
        (b := (μStar : WithTopBot 𝕜))
        (c := f x)
        (.inl (WithTopBot.coe_ne_bot μStar))
        (.inl (WithTopBot.coe_ne_top μStar))).1 hx'
    exact
      (WithTopBot.sub_le_iff_le_add
        (b := f x)
        (c := (μStar : WithTopBot 𝕜))
        (.inr (WithTopBot.coe_ne_top μStar))
        (.inr (WithTopBot.coe_ne_bot μStar))).2
        (by simpa [add_comm] using hx'')
  · intro h x
    have hx : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) ≤ (μStar : WithTopBot 𝕜) :=
      (le_iSup_of_le x le_rfl).trans h
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤ (μStar : WithTopBot 𝕜) + f x := by
      exact
        (WithTopBot.sub_le_iff_le_add
          (b := f x)
          (c := (μStar : WithTopBot 𝕜))
          (.inr (WithTopBot.coe_ne_top μStar))
          (.inr (WithTopBot.coe_ne_bot μStar))).1 hx
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μStar : WithTopBot 𝕜)) ≤ f x := by
      exact
        (WithTopBot.sub_le_iff_le_add
          (b := (μStar : WithTopBot 𝕜))
          (c := f x)
          (.inl (WithTopBot.coe_ne_bot μStar))
          (.inl (WithTopBot.coe_ne_top μStar))).2
          (by simpa [add_comm] using hx')
    simpa [Function.toWithTopBot, sub_eq_add_neg, WithTopBot.sub_eq_add_neg] using hx''

/-- Theorem 16.5.1: the Fenchel conjugate of `conv {f_i | i ∈ I}`, represented by
`conv(⨅ i, f i)`, is the pointwise supremum of the individual conjugates. The source assumption
that each `f_i` is proper convex is redundant for this identity. -/
theorem convexConjugate_conv_iInf_eq_iSup (f : I → X → WithTopBot 𝕜) :
    (conv(⨅ i : I, f i))⋆ = (⨆ i : I, (f i)⋆) := by
  classical
  let hHull := Function.isGreatest_conv_iInf_minorant f
  have hHull_le_iInf : conv(⨅ i : I, f i) ≤ ⨅ i : I, f i := hHull.1.2
  have hHull_le : ∀ i : I, conv(⨅ i : I, f i) ≤ f i := le_iInf_iff.mp hHull_le_iInf
  have hHull_greatest :
      ∀ {g : X → WithTopBot 𝕜},
        Function.IsConvex 𝕜 g → (∀ i : I, g ≤ f i) → g ≤ conv(⨅ i : I, f i) :=
    fun hg_convex hg_le ↦ hHull.2 ⟨hg_convex, le_iInf_iff.mpr hg_le⟩
  funext xStar
  rw [iSup_apply]
  simpa using
    (iSup_eq_of_forall_le_of_forall_lt_exists_gt
      (fun i ↦
        (convexConjugate_le_convexConjugate_of_le (hHull_le i)) xStar)
      (fun w hw ↦ by
        rcases WithTopBot.exists_between_coe_of_lt hw with ⟨μStar, hwμ, hμhull⟩
        by_contra h_exists
        have hno_gt : ∀ i : I, (f i)⋆ xStar ≤ w := by
          intro i
          by_contra hi
          exact h_exists ⟨i, lt_of_not_ge hi⟩
        have hfamily_le : ∀ i : I, (f i)⋆ xStar ≤ (μStar : WithTopBot 𝕜) :=
          fun i ↦ (hno_gt i).trans hwμ.le
        have h_affine_convex :
            Function.IsConvex 𝕜
              (fun x : X ↦ ((⟪x, xStar⟫ₚ - μStar : 𝕜) : WithTopBot 𝕜)) := by
          simpa [Function.IsConvex, convexOn_iff_convex_epigraph, Set.mem_univ] using
            (LinearMap.convexOn (HasLinearPairing.pairingLinear.flip xStar) convex_univ).sub
              (convexOn_const μStar convex_univ)
        have hminorant :
            (fun x : X ↦ ((⟪x, xStar⟫ₚ - μStar : 𝕜) : WithTopBot 𝕜)) ≤
              conv(⨅ i : I, f i) := by
          exact hHull_greatest h_affine_convex fun i ↦
            (pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
              (f i) xStar μStar).2
              (hfamily_le i)
        have hconj_le : (conv(⨅ i : I, f i))⋆ xStar ≤ (μStar : WithTopBot 𝕜) :=
          (pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
            (conv(⨅ i : I, f i)) xStar μStar).1 hminorant
        exact (not_le_of_gt hμhull) hconj_le)).symm

end
