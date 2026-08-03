import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u}

private noncomputable def zeroIoi : Set.Ioi (⊥ : EReal) := ⟨0, by simp⟩

/-- The source-facing function attached to `h : C → ℝ`, viewed as finite on `C` and equal to `+∞`
outside `C`. -/
noncomputable def extendWithTopOutside
    (C : Set H) (h : C → ℝ) : H → Set.Ioi (⊥ : EReal) :=
  pointwiseAdd (Function.extend Subtype.val h.toEReal (fun _ ↦ zeroIoi)) (ι[C])

/-- Restricting `extendWithTopOutside C h` back to `C` recovers `h`. -/
theorem extendWithTopOutside_comp_subtype
    (C : Set H) (h : C → ℝ) :
    extendWithTopOutside C h ∘ Subtype.val = h.toEReal := by
  funext x
  apply Subtype.ext
  change (extendWithTopOutside C h x : EReal) = (h.toEReal x : EReal)
  have hextend :
      Function.extend Subtype.val h.toEReal (fun _ ↦ zeroIoi) x = h.toEReal x := by
    exact congrArg (fun k : C → Set.Ioi (⊥ : EReal) ↦ k x)
      (Function.extend_comp Subtype.val_injective h.toEReal (fun _ ↦ zeroIoi))
  rw [extendWithTopOutside, pointwiseAdd_apply, hextend]
  simp [ERealFunction.indicator, x.2]

/-- On `C`, `extendWithTopOutside C h` evaluates to the original value `h`. -/
@[simp] theorem extendWithTopOutside_apply_of_mem
    {C : Set H} (h : C → ℝ) {x : H} (hx : x ∈ C) :
    (extendWithTopOutside C h x : EReal) = h ⟨x, hx⟩ := by
  simpa using
    congrArg
      (fun k : C → Set.Ioi (⊥ : EReal) ↦ (k ⟨x, hx⟩ : EReal))
      (extendWithTopOutside_comp_subtype C h)

/-- Outside `C`, `extendWithTopOutside C h` takes the value `+∞`. -/
-- Proof sketch: `x ∉ C` means `x` is not in the range of `Subtype.val : C → H`, so
-- `Function.extend` falls back to the default branch.
theorem extendWithTopOutside_apply_of_not_mem
    {C : Set H} (h : C → ℝ) {x : H} (hx : x ∉ C) :
    (extendWithTopOutside C h x : EReal) = (⊤ : EReal) := by
  rw [extendWithTopOutside, pointwiseAdd_apply]
  simp [ERealFunction.indicator, hx, zeroIoi]

-- Proof sketch: let `f := extendWithTopOutside C h`. For each `x : C`, evaluating the defining
-- infimal convolution at `y = x` gives `(paschHausdorffEnvelope f β x) ≤ h x`, while the
-- `β`-Lipschitz property of `h` on `C` gives the reverse inequality against every admissible
-- `y ∈ C`; hence the envelope agrees with `h` on `C`. The nonemptiness of `C` yields a finite
-- point of `f`, so Proposition 12.17 gives a real-valued greatest `β`-Lipschitz minorant whose
-- `EReal` coercion is the envelope.
/-- Helper for Corollary 12 19: `extendWithTopOutside C h` has a finite value at any point of the
nonempty set `C`. -/
theorem extendWithTopOutside_has_finite_point
    (C : Set H) (hC : C.Nonempty) (h : C → ℝ) :
    ∃ x : H, (extendWithTopOutside C h x : EReal) < ⊤ := by
  rcases hC with ⟨x, hx⟩
  -- Evaluate the extension on a point of `C`, where it coincides with the real datum `h`.
  refine ⟨x, ?_⟩
  rw [extendWithTopOutside_apply_of_mem h hx]
  exact EReal.coe_lt_top _

variable [NormedAddCommGroup H]

/-- Helper for Corollary 12 19: the scaled norm kernel `x ↦ β ‖x‖` as an `]-∞,+∞]`-valued
function. -/
noncomputable def scaledNormKernel (β : NNReal) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (β : ℝ) * ‖x‖).toEReal

/-- Helper for Corollary 12 19: coercing the scaled norm kernel to `EReal` yields the expected
formula `x ↦ β ‖x‖`. -/
@[simp] theorem scaledNormKernel_apply (β : NNReal) (x : H) :
    (scaledNormKernel β x : EReal) = (((β : ℝ) * ‖x‖ : ℝ) : EReal) := by
  simp [scaledNormKernel]

/-- Helper for Corollary 12 19: the `β`-Pasch--Hausdorff envelope is the infimal convolution with
the scaled norm kernel. -/
noncomputable def paschHausdorffEnvelope {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) :
    H → EReal :=
  f □ scaledNormKernel β

/-- Helper for Corollary 12 19: the `β`-Pasch--Hausdorff envelope is computed by infimizing the
translated sums `f y + β ‖x - y‖`. -/
theorem paschHausdorffEnvelope_apply
    {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) (x : H) :
    paschHausdorffEnvelope f β x =
      ⨅ y : H, (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
  simp [paschHausdorffEnvelope, infimalConvolution_apply]

/-- Helper for Corollary 12 19: on `C`, the Pasch--Hausdorff envelope of `extendWithTopOutside C h`
recovers the original value `h`. -/
theorem paschHausdorffEnvelope_extendWithTopOutside_apply_of_mem
    {C : Set H} (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) {x : H} (hx : x ∈ C) :
    paschHausdorffEnvelope (extendWithTopOutside C h) β x = ((h ⟨x, hx⟩ : ℝ) : EReal) := by
  apply le_antisymm
  · -- Test the defining infimum at `y = x` to get the upper bound.
    rw [paschHausdorffEnvelope_apply]
    refine le_trans (iInf_le _ x) ?_
    change (extendWithTopOutside C h x : EReal) + ((((β : ℝ) * ‖x - x‖ : ℝ) : EReal)) ≤
      ((h ⟨x, hx⟩ : ℝ) : EReal)
    rw [extendWithTopOutside_apply_of_mem h hx]
    simp
  · -- Compare against every admissible point `y`; the Lipschitz bound controls the finite branch.
    rw [paschHausdorffEnvelope_apply]
    refine le_iInf ?_
    intro y
    by_cases hy : y ∈ C
    · have hdist :
          |h ⟨x, hx⟩ - h ⟨y, hy⟩| ≤ (β : ℝ) * ‖x - y‖ := by
        -- Rewrite the subtype Lipschitz estimate into the ambient norm form used by the envelope.
        simpa [Real.dist_eq, Subtype.dist_eq, dist_eq_norm] using
          hh.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
      have hle :
          h ⟨x, hx⟩ ≤ h ⟨y, hy⟩ + (β : ℝ) * ‖x - y‖ := by
        -- Extract the forward inequality from the absolute-value control.
        have hright := (abs_le.mp hdist).2
        linarith
      calc
        ((h ⟨x, hx⟩ : ℝ) : EReal) ≤ (((h ⟨y, hy⟩ + (β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
          exact_mod_cast hle
        _ = ((h ⟨y, hy⟩ : ℝ) : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
          simp [EReal.coe_add, EReal.coe_mul]
        _ = (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
          rw [extendWithTopOutside_apply_of_mem h hy]
    · have hkernel_ne_bot :
          ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) ≠ ⊥ :=
        EReal.coe_ne_bot _
      -- Outside `C`, the extension value is `⊤`, so this summand dominates every finite real.
      calc
        ((h ⟨x, hx⟩ : ℝ) : EReal) ≤ (⊤ : EReal) := le_top
        _ = (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
          rw [extendWithTopOutside_apply_of_not_mem h hy,
            EReal.top_add_of_ne_bot hkernel_ne_bot]

/-- Helper for Corollary 12 19: restricting the Pasch--Hausdorff envelope of
`extendWithTopOutside C h` back to `C` recovers `h`. -/
theorem paschHausdorffEnvelope_extendWithTopOutside_comp_subtype
    (C : Set H) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    paschHausdorffEnvelope (extendWithTopOutside C h) β ∘ Subtype.val = h.toEReal.asEReal := by
  funext x
  -- Evaluate the pointwise identity on the subtype element `x : C`.
  simpa [Function.comp_apply, Function.asEReal_apply, Function.toEReal_apply] using
    paschHausdorffEnvelope_extendWithTopOutside_apply_of_mem β h hh x.2

/-- Helper for Corollary 12 19: the real-valued Pasch--Hausdorff inf-extension over `C` is the
infimum of the affine upper barriers `y ↦ h y + β dist x y`. -/
noncomputable def paschHausdorffInfExtension
    (C : Set H) (β : NNReal) (h : C → ℝ) : H → ℝ :=
  fun x ↦ ⨅ y : C, h y + (β : ℝ) * dist x y

/-- Helper for Corollary 12 19: the family defining the inf-extension is bounded below. -/
theorem paschHausdorffInfExtension_bddBelow
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) (x : H) :
    BddBelow (Set.range fun y : C => h y + (β : ℝ) * dist x y) := by
  rcases hC with ⟨z, hz⟩
  refine ⟨h ⟨z, hz⟩ - (β : ℝ) * dist x z, ?_⟩
  rintro w ⟨t, rfl⟩
  rw [sub_le_iff_le_add, add_assoc, ← mul_add]
  calc
    h ⟨z, hz⟩ ≤ h t + (β : ℝ) * dist z t := by
      simpa [Subtype.dist_eq] using hh.le_add_mul ⟨z, hz⟩ t
    _ ≤ h t + (β : ℝ) * (dist x z + dist x t) := by
      gcongr
      simpa [add_comm] using dist_triangle_left z (t : H) x
    _ = h t + (β : ℝ) * (dist x t + dist x z) := by
      simp [add_comm]

/-- Helper for Corollary 12 19: restricting the inf-extension to `C` recovers the original
function `h`. -/
theorem paschHausdorffInfExtension_comp_subtype
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    paschHausdorffInfExtension C β h ∘ Subtype.val = h := by
  letI : Nonempty C := hC.to_subtype
  funext x
  have hB := paschHausdorffInfExtension_bddBelow C hC β h hh x
  refine le_antisymm ?_ ?_
  · -- Evaluate the defining infimum at `y = x`.
    simpa [paschHausdorffInfExtension, Function.comp_apply] using ciInf_le hB x
  · -- Every admissible `y ∈ C` bounds the inf-extension from above by Lipschitz control.
    refine le_ciInf ?_
    intro y
    simpa [paschHausdorffInfExtension, Function.comp_apply, Subtype.dist_eq] using
      hh.le_add_mul x y

/-- Helper for Corollary 12 19: the inf-extension is globally `β`-Lipschitz. -/
theorem paschHausdorffInfExtension_lipschitz
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    LipschitzWith β (paschHausdorffInfExtension C β h) := by
  letI : Nonempty C := hC.to_subtype
  refine LipschitzWith.of_le_add_mul β ?_
  intro x y
  have hB := paschHausdorffInfExtension_bddBelow C hC β h hh x
  rw [← sub_le_iff_le_add]
  refine le_ciInf ?_
  intro z
  rw [sub_le_iff_le_add]
  calc
    paschHausdorffInfExtension C β h x ≤ h z + (β : ℝ) * dist x z := by
      simpa [paschHausdorffInfExtension] using ciInf_le hB z
    _ ≤ h z + (β : ℝ) * dist y z + (β : ℝ) * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      exact dist_triangle x y z

/-- Helper for Corollary 12 19: the Pasch--Hausdorff envelope of `extendWithTopOutside C h`
coincides with the canonical real-valued inf-extension. -/
theorem paschHausdorffEnvelope_eq_paschHausdorffInfExtension
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    paschHausdorffEnvelope (extendWithTopOutside C h) β =
      (paschHausdorffInfExtension C β h).toEReal.asEReal := by
  letI : Nonempty C := hC.to_subtype
  funext x
  have hB := paschHausdorffInfExtension_bddBelow C hC β h hh x
  have hBTop :
      BddBelow (Set.range fun y : C => ((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ)) := by
    rcases hB with ⟨m, hm⟩
    refine ⟨(m : WithTop ℝ), ?_⟩
    rintro z ⟨y, rfl⟩
    have hm' : m ≤ h y + (β : ℝ) * dist x y := hm ⟨y, rfl⟩
    exact WithTop.coe_le_coe.mpr hm'
  have hcast :
      (((paschHausdorffInfExtension C β h x : ℝ) : EReal)) =
        ⨅ y : C, (((h y + (β : ℝ) * dist x y : ℝ) : EReal)) := by
    have hcastWithTop :
        (((paschHausdorffInfExtension C β h x : ℝ) : WithTop ℝ)) =
          ⨅ y : C, ((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ) := by
      simpa [paschHausdorffInfExtension] using
        (WithTop.coe_iInf
          (f := fun y : C => h y + (β : ℝ) * dist x y)
          hB)
    have hcastEReal :
        (((paschHausdorffInfExtension C β h x : ℝ) : WithBot (WithTop ℝ))) =
          ⨅ y : C, ((((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ))) := by
      calc
        (((paschHausdorffInfExtension C β h x : ℝ) : WithBot (WithTop ℝ)))
            = (((⨅ y : C, ((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ)) : WithTop ℝ) :
              WithBot (WithTop ℝ)) := by
                exact congrArg (fun t : WithTop ℝ => (t : WithBot (WithTop ℝ))) hcastWithTop
        _ = ⨅ y : C, ((((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ) :
          WithBot (WithTop ℝ))) := by
              simpa using
                (WithBot.coe_iInf
                  (f := fun y : C => ((h y + (β : ℝ) * dist x y : ℝ) : WithTop ℝ))
                  hBTop)
    simpa using hcastEReal
  have hreduce :
      (⨅ y : H,
          (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal))) =
        ⨅ y : C, (((h y + (β : ℝ) * dist x y : ℝ) : EReal)) := by
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro y
      calc
        (⨅ z : H,
            (extendWithTopOutside C h z : EReal) + ((((β : ℝ) * ‖x - z‖ : ℝ) : EReal))) ≤
            (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
              exact iInf_le (fun z : H =>
                (extendWithTopOutside C h z : EReal) + ((((β : ℝ) * ‖x - z‖ : ℝ) : EReal))) y
        _ = (((h y + (β : ℝ) * dist x y : ℝ) : EReal)) := by
              rw [extendWithTopOutside_apply_of_mem h y.2]
              simp [dist_eq_norm, EReal.coe_add, EReal.coe_mul]
    · refine le_iInf ?_
      intro y
      by_cases hy : y ∈ C
      · calc
          (⨅ z : C, (((h z + (β : ℝ) * dist x z : ℝ) : EReal))) ≤
              (((h ⟨y, hy⟩ + (β : ℝ) * dist x y : ℝ) : EReal)) := by
                exact iInf_le
                  (fun z : C => (((h z + (β : ℝ) * dist x z : ℝ) : EReal)))
                  ⟨y, hy⟩
          _ = (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
                rw [extendWithTopOutside_apply_of_mem h hy]
                simp [dist_eq_norm, EReal.coe_add, EReal.coe_mul]
      · calc
          (⨅ z : C, (((h z + (β : ℝ) * dist x z : ℝ) : EReal))) ≤ (⊤ : EReal) := le_top
          _ = (extendWithTopOutside C h y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
                rw [extendWithTopOutside_apply_of_not_mem h hy,
                  EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  calc
    paschHausdorffEnvelope (extendWithTopOutside C h) β x
        = ⨅ y : C, (((h y + (β : ℝ) * dist x y : ℝ) : EReal)) := by
            simpa [paschHausdorffEnvelope_apply] using hreduce
    _ = (((paschHausdorffInfExtension C β h x : ℝ) : EReal)) := hcast.symm
    _ = (paschHausdorffInfExtension C β h).toEReal.asEReal x := by
          simp [Function.asEReal_apply, Function.toEReal_apply]

/-- Corollary 12 19: if `h : C → ℝ` is `β`-Lipschitz, then the Pasch--Hausdorff envelope of the
function equal to `h` on `C` and `+∞` outside `C` is realized by a real-valued `β`-Lipschitz
extension of `h`. -/
theorem paschHausdorffEnvelope_realizes_lipschitz_extension
    (C : Set H) (hC : C.Nonempty) (β : NNReal) (h : C → ℝ) (hh : LipschitzWith β h) :
    ∃ g : H → ℝ,
      paschHausdorffEnvelope (extendWithTopOutside C h) β = g.toEReal.asEReal ∧
      LipschitzWith β g ∧
      g ∘ Subtype.val = h := by
  refine ⟨paschHausdorffInfExtension C β h,
    paschHausdorffEnvelope_eq_paschHausdorffInfExtension C hC β h hh,
    paschHausdorffInfExtension_lipschitz C hC β h hh,
    paschHausdorffInfExtension_comp_subtype C hC β h hh⟩

end ERealFunction
