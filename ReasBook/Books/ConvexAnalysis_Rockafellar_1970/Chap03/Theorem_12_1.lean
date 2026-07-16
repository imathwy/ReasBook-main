import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_5_0
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Pairing-side representation bridge for affine minorants of `f` on a paired module. -/
abbrev AffineMinorant.IsPairingSubConstRepresentable (f : X → WithTopBot 𝕜) : Prop :=
  ∀ h : AffineMinorant f, ∃ y : Y, ∃ μ : 𝕜, h.1 = pairingSubConstAffineMap y μ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.1 says that a closed convex function is recovered as the pointwise
  supremum of all affine functions lying below it.
- `core/canonical`: the chapter owner constructions are `convexConjugate` and the dual biconjugate
  `f⋆⋆`, while convexity and closedness are rendered by
  `Function.IsConvex` and
  `LowerSemicontinuous`.
- `bridge/view`: the family of affine maps `h ≤ f` is organized as the subtype `AffineMinorant f`,
  and the textbook affine-minorant supremum is exposed by the pointwise bridge theorem
  `biconjugate_apply_eq_iSup_affineMinorant`.

Domain-style sampling used here:
- `AffineMinorant` and `affineMinorant_le` from `Text_12_1_2`;
- `Function.IsConvex` from `Theorem_4_2`;
- `convexConjugate`, `convexConjugate_eq_iSup_pairing_sub`, and
  `convexConjugate_convexConjugate_eq_iSup_pairing_sub` from `Defn_12_2`;
- `AffineMinorant.IsPairingSubConstRepresentable` and the source-facing normal-form owner
  `pairingSubConstAffineMap` from
  `Text_12_1_2`;
- the complete-lattice pointwise supremum on `WithTopBot 𝕜`-valued functions.
- Primitive data vs derived API: the primitive input is the function `f : X → WithTopBot 𝕜`; the
  canonical owner is the dual biconjugate `f⋆⋆`, while
  `AffineMinorant f`, the explicit affine-representation hypothesis, and the pointwise
  supremum-over-minorants formula are bridge-level API.
- Layer target: `source-facing`; the theorem keeps the affine-minorant wording of the source, but
  the implementation-facing owner is the canonical biconjugate rather than a parallel local
  supremum function. The bridge layer `AffineMinorant f` itself is stated on the primitive
  scalar/pairing owner ambient already required by `AffineMap 𝕜 X 𝕜`; concrete realizations such
  as finite-dimensional inner-product spaces can be used downstream as bridges to discharge the
  explicit representation hypothesis.
-/

-- Proof sketch: the biconjugate is the supremum of the affine functions
-- `x ↦ ⟪x, x⋆⟫ - convexConjugate f x⋆`. The explicit affine-representation hypothesis below says
-- every affine minorant has this form, and Text 12.1.2 identifies the admissible constants
-- precisely as those dominating `convexConjugate f x⋆`. Therefore the biconjugate is exactly the
-- supremum over all affine minorants.
variable [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-- Evaluating the Fenchel biconjugate `f**` at `x` gives the textbook supremum of the values of
all affine minorants of `f` at `x`. The ambient model layer is exposed through the explicit
representation hypothesis `h_affine`, so this theorem is stated on the pairing owner rather than
on a concrete inner-product model. -/
theorem biconjugate_apply_eq_iSup_affineMinorant
    (f : X → WithTopBot 𝕜) (x : X)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f) :
    (f⋆⋆) x =
      ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  apply le_antisymm
  · rw [convexConjugate_convexConjugate_eq_iSup_pairing_sub (f := f) (x := x)]
    refine iSup_le ?_
    intro y
    by_cases hy_top : f⋆ y = (⊤ : WithTopBot 𝕜)
    · have hbot :
        ((⟪y, x⟫ₚ : WithTopBot 𝕜) - f⋆ y) = (⊥ : WithTopBot 𝕜) := by
        rw [hy_top]
        exact WithBotTop.sub_top (⟪y, x⟫ₚ : WithTopBot 𝕜)
      rw [hbot]
      exact bot_le
    · by_cases hy_bot : f⋆ y = (⊥ : WithTopBot 𝕜)
      · have h_all_ge :
          ∀ a : 𝕜, (a : WithTopBot 𝕜) ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x := by
          intro a
          let μ : 𝕜 := (⟪x, y⟫ₚ : 𝕜) - a
          have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by simp [hy_bot]
          let hminor : AffineMinorant f := pairingSubConstAffineMinorant f y μ hμ
          have ha : (a : WithTopBot 𝕜) = hminor.toWithBotTop x := by
            change (a : WithTopBot 𝕜) = ((hminor x : 𝕜) : WithTopBot 𝕜)
            rw [show hminor x = (⟪x, y⟫ₚ : 𝕜) - μ by
              simp [hminor, pairingSubConstAffineMinorant_apply]]
            have h𝕜 : (⟪x, y⟫ₚ : 𝕜) - μ = a := by
              dsimp [μ]
              ring
            rw [h𝕜]
          simpa [ha] using
            (le_iSup_of_le hminor le_rfl :
              hminor.toWithBotTop x ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x)
        have hsup_top : (⨆ h : AffineMinorant f, h.toWithBotTop x) = (⊤ : WithTopBot 𝕜) := by
          refine
            (WithBot.eq_top_iff_forall_ge
              (x := (⨆ h : AffineMinorant f, h.toWithBotTop x))).2 ?_
          intro a
          simpa using h_all_ge a
        have htop :
            ((⟪y, x⟫ₚ : WithTopBot 𝕜) - f⋆ y) = (⊤ : WithTopBot 𝕜) := by
          have hpair_ne_bot : ((⟪y, x⟫ₚ : WithTopBot 𝕜) ≠ (⊥ : WithTopBot 𝕜)) :=
            WithBotTop.coe_ne_bot _
          rw [hy_bot]
          exact WithBotTop.sub_bot (x := (⟪y, x⟫ₚ : WithTopBot 𝕜)) hpair_ne_bot
        rw [htop, hsup_top]
      · rcases WithBot.ne_bot_iff_exists.mp hy_bot with ⟨rTop, hrTop⟩
        have hrTop_ne_top : rTop ≠ (⊤ : WithTop 𝕜) := by
          intro htop
          apply hy_top
          calc
            f⋆ y = ((rTop : WithTop 𝕜) : WithTopBot 𝕜) := hrTop.symm
            _ = ((⊤ : WithTop 𝕜) : WithTopBot 𝕜) := by simp [htop]
            _ = (⊤ : WithTopBot 𝕜) := rfl
        rcases WithTop.ne_top_iff_exists.mp hrTop_ne_top with ⟨μ, hμrTop⟩
        have hfstar_eq : f⋆ y = (μ : WithTopBot 𝕜) := by
          calc
            f⋆ y = ((rTop : WithTop 𝕜) : WithTopBot 𝕜) := hrTop.symm
            _ = ((μ : WithTop 𝕜) : WithTopBot 𝕜) := by simp [hμrTop]
            _ = (μ : WithTopBot 𝕜) := rfl
        have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by simp [hfstar_eq]
        let hminor : AffineMinorant f := pairingSubConstAffineMinorant f y μ hμ
        have hminor_val :
            hminor.toWithBotTop x =
              (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
          change ((hminor x : 𝕜) : WithTopBot 𝕜) = _
          rw [show hminor x = (⟪x, y⟫ₚ : 𝕜) - μ by
            simp [hminor, pairingSubConstAffineMinorant_apply]]
          simp [coe_sub]
        have hminor_le :
            hminor.toWithBotTop x ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x :=
          le_iSup_of_le hminor le_rfl
        have hswap :
            (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) =
              (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
          exact
            congrArg
              (fun t : 𝕜 ↦ ((t : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)))
              (HasPairingSwap.pairing_swap (x := x) (y := y)).symm
        calc
          (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y)
              = (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
                simp [hfstar_eq]
          _ = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := hswap
          _ = hminor.toWithBotTop x := hminor_val.symm
          _ ≤ ⨆ h : AffineMinorant f, h.toWithBotTop x := hminor_le
  · refine iSup_le ?_
    intro h
    rcases h_affine h with ⟨y, μ, hrepr⟩
    have hminorant : (pairingSubConstAffineMap y μ).toWithBotTop ≤ f := by
      simpa [hrepr] using h.property
    have hμ : f⋆ y ≤ (μ : WithTopBot 𝕜) := by
      exact
        (pairingSubConstAffineMap_le_iff_convexConjugate_le (f := f) y μ).1 hminorant
    have hy :
        (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) ≤
          (f⋆⋆) x := by
      have hy' :
          (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) ≤
            (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - f⋆ y) := by
        exact WithBotTop.sub_le_sub le_rfl hμ
      exact le_trans hy' (le_iSup_of_le y le_rfl)
    have hx :
        h.toWithBotTop x = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
      change ((h x : 𝕜) : WithTopBot 𝕜) = _
      rw [show h x = (⟪x, y⟫ₚ : 𝕜) - μ by simp [hrepr, pairingSubConstAffineMap_apply]]
      simp [coe_sub]
    calc
      h.toWithBotTop x = (((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := hx
      _ = (((⟪y, x⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)) := by
        exact
          congrArg
            (fun t : 𝕜 ↦ ((t : WithTopBot 𝕜) - (μ : WithTopBot 𝕜)))
            (HasPairingSwap.pairing_swap (x := x) (y := y))
      _ ≤ (f⋆⋆) x := hy

/-- If `f` is recovered pointwise by its biconjugate, then the value at `x` is the supremum of
its affine minorants at `x`. This is the source-facing bridge from the canonical owner equation
`f⋆⋆ = f` to the affine-minorant formula. -/
theorem eq_iSup_affineMinorant_of_eq_biconjugate
    (f : X → WithTopBot 𝕜)
    (hf_biconj : f⋆⋆ = f) (x : X)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f) :
    f x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  have hf_biconj_x : (f⋆⋆) x = f x := by
    simpa using congrArg (fun g : X → WithTopBot 𝕜 ↦ g x) hf_biconj
  calc
    f x = (f⋆⋆) x := hf_biconj_x.symm
    _ = ⨆ h : AffineMinorant f, h.toWithBotTop x :=
      biconjugate_apply_eq_iSup_affineMinorant
        f x h_affine

end

section

variable {X : Type u} {Y : Type v} {L : Type*}
variable [CompleteLattice L] [AddCommGroup L] [AddRightMono L]
variable [HasPairing X Y L] [HasPairing Y X L] [HasPairingSwap X Y L]

/-- The Fenchel dual biconjugate lies pointwise below `f` on any swap-compatible paired ambient.
-/
-- Proof sketch: for each `y`, the point `x` is one candidate in the supremum defining `f⋆ y`,
-- so `⟪x, y⟫ₚ - f⋆ y ≤ f x`. Symmetry rewrites the biconjugate summands
-- `⟪y, x⟫ₚ - f⋆ y` to the same form, and then taking the supremum over `y` yields `f** x ≤ f x`.
theorem biconjugate_le
    (f : X → L) :
    f⋆⋆ ≤ f := by
  intro x
  change (⨆ y : Y, (((⟪y, x⟫ₚ : L) - (f⋆ y)) : L)) ≤ f x
  refine iSup_le ?_
  intro y
  have hy : (((⟪x, y⟫ₚ : L) - f x) : L) ≤ f⋆ y := by
    exact le_iSup_of_le x le_rfl
  have hy' : (⟪x, y⟫ₚ : L) ≤ f⋆ y + f x := (sub_le_iff_le_add).1 hy
  have hy'' : (((⟪x, y⟫ₚ : L) - (f⋆ y)) : L) ≤ f x := by
    exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hy')
  simpa [HasPairingSwap.pairing_swap (x := y) (y := x)] using hy''

end

section

variable {𝕜 : Type w} {E : Type u}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: this is the closed-case biconjugacy theorem on the finite-dimensional real
-- pairing layer. The upstream owner theorem gives `f⋆⋆ = cl(f)` under convexity; lower
-- semicontinuity identifies `cl(f) = f`, yielding `f⋆⋆ = f`.
/-- Theorem 12.1 on the canonical owner: on a finite-dimensional scalar-field space with a
continuous linear self-pairing, a closed convex function (expressed by
`LowerSemicontinuous f` and `f.IsConvex`) equals its Fenchel biconjugate `f**`. -/
theorem biconjugate_eq_of_isConvex_of_lowerSemicontinuous
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f) :
    f⋆⋆ = f := by
  simpa [lowerSemicontinuousHull_eq_self hf_closed] using
    (hf_convex.biconjugate_eq_lowerSemicontinuousHull : f⋆⋆ = cl(f))

/-- Theorem 12.1 in the source-facing affine-minorant form: a closed convex function on a
finite-dimensional scalar-field space with a continuous linear self-pairing is the pointwise
supremum of its affine minorants once affine functionals are represented through the pairing. -/
theorem eq_iSup_affineMinorant_of_isConvex_of_lowerSemicontinuous
    [IsStrictOrderedRing 𝕜] [HasPairingSwap E E 𝕜]
    (f : E → WithTopBot 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable f)
    (x : E) :
    f x = ⨆ h : AffineMinorant f, h.toWithBotTop x := by
  exact eq_iSup_affineMinorant_of_eq_biconjugate f
    (biconjugate_eq_of_isConvex_of_lowerSemicontinuous
      f hf_convex hf_closed)
    x h_affine

end
