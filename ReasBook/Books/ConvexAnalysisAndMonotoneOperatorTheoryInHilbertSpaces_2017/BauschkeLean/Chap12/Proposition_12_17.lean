import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The scaled norm kernel `x ↦ β ‖x‖` as an `]-∞,+∞]`-valued function. -/
noncomputable def scaledNormKernel (β : NNReal) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (β : ℝ) * ‖x‖).toEReal

/-- Coercing the scaled norm kernel to `EReal` recovers the formula `x ↦ β ‖x‖`. -/
@[simp]
theorem scaledNormKernel_apply (β : NNReal) (x : H) :
    (scaledNormKernel β x : EReal) = (((β : ℝ) * ‖x‖ : ℝ) : EReal) := by
  simp [scaledNormKernel]

/-- The `β`-Pasch--Hausdorff envelope of `f` is the infimal convolution of `f` with the scaled
norm `x ↦ β ‖x‖`. -/
noncomputable def paschHausdorffEnvelope {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) :
    H → EReal :=
  f □ scaledNormKernel β

/-- The `β`-Pasch--Hausdorff envelope is computed by infimizing the translated sums
`f y + β ‖x - y‖`. -/
theorem paschHausdorffEnvelope_apply
    {α : Type*} [CoeTC α EReal] (f : H → α) (β : NNReal) (x : H) :
    paschHausdorffEnvelope f β x =
      ⨅ y : H, (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
  simp [paschHausdorffEnvelope, infimalConvolution_apply]

/-- The real-valued `β`-Lipschitz minorants of an `]-∞,+∞]`-valued function. -/
def betaLipschitzMinorants
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) : Set (H → ℝ) :=
  {h | LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal}

/-- Membership in `betaLipschitzMinorants f β` is exactly the `β`-Lipschitz minorant condition:
`h` is `β`-Lipschitz and its canonical `EReal` coercion lies below `f`. -/
theorem mem_betaLipschitzMinorants_iff
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) (h : H → ℝ) :
    h ∈ betaLipschitzMinorants f β ↔
      LipschitzWith β h ∧ h.toEReal.asEReal ≤ f.asEReal :=
  Iff.rfl

/-- Helper for Proposition 12 17: evaluating the defining infimum at a test point `z` bounds the
envelope at `x` by the translated value `f z + β dist x z`. -/
theorem paschHausdorffEnvelope_le_value_add_scaled_dist
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) (x z : H) :
    paschHausdorffEnvelope f β x ≤
      (f z : EReal) + ((((β : ℝ) * dist x z : ℝ) : EReal)) := by
  -- Evaluate the defining infimum at the chosen comparison point `z`.
  rw [paschHausdorffEnvelope_apply]
  simpa [dist_eq_norm] using
    (iInf_le (fun y : H ↦ (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal))) z)

/-- Helper for Proposition 12 17: one finite value of `f` rules out the `⊤` case for the whole
Pasch--Hausdorff envelope. -/
theorem paschHausdorffEnvelope_lt_top_of_exists_finite_point
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal)
    (hf : ∃ x : H, (f x : EReal) < ⊤) (x : H) :
    paschHausdorffEnvelope f β x < ⊤ := by
  rcases hf with ⟨x₀, hx₀⟩
  -- Compare the envelope with the finite translated value at the witness point `x₀`.
  have hle := paschHausdorffEnvelope_le_value_add_scaled_dist f β x x₀
  exact lt_of_le_of_lt hle <| EReal.add_lt_top hx₀.ne (EReal.coe_ne_top _)

/-- Helper for Proposition 12 17: every `β`-Lipschitz minorant lies below the
Pasch--Hausdorff envelope. -/
theorem le_paschHausdorffEnvelope_of_mem_betaLipschitzMinorants
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) {h : H → ℝ}
    (hh : h ∈ betaLipschitzMinorants f β) :
    h.toEReal.asEReal ≤ paschHausdorffEnvelope f β := by
  rw [mem_betaLipschitzMinorants_iff] at hh
  rcases hh with ⟨hh_lipschitz, hh_le⟩
  intro x
  simp only [Function.asEReal_apply, Function.toEReal_apply]
  rw [paschHausdorffEnvelope_apply]
  apply le_iInf
  intro y
  -- Combine the Lipschitz estimate for `h` with the minorant inequality `h ≤ f`.
  have hxy :
      ((h x : ℝ) : EReal) ≤
        ((h y : ℝ) : EReal) + ((((β : ℝ) * dist x y : ℝ) : EReal)) := by
    exact_mod_cast hh_lipschitz.le_add_mul x y
  have hyf : ((h y : ℝ) : EReal) ≤ (f y : EReal) := by
    simpa [Function.asEReal_apply, Function.toEReal_apply] using hh_le y
  calc
    ((h x : ℝ) : EReal) ≤
        ((h y : ℝ) : EReal) + ((((β : ℝ) * dist x y : ℝ) : EReal)) := hxy
    _ ≤ (f y : EReal) + ((((β : ℝ) * dist x y : ℝ) : EReal)) :=
      add_le_add hyf le_rfl
    _ = (f y : EReal) + ((((β : ℝ) * ‖x - y‖ : ℝ) : EReal)) := by
      simp [dist_eq_norm]

/-- Helper for Proposition 12 17: the Pasch--Hausdorff envelope satisfies the one-sided
`β`-Lipschitz estimate `env x ≤ env z + β dist x z`. -/
theorem paschHausdorffEnvelope_le_add_scaled_dist
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) (x z : H) :
    paschHausdorffEnvelope f β x ≤
      paschHausdorffEnvelope f β z + ((((β : ℝ) * dist x z : ℝ) : EReal)) := by
  let c : ℝ := (β : ℝ) * dist x z
  have hsub :
      paschHausdorffEnvelope f β x - (c : EReal) ≤ paschHausdorffEnvelope f β z := by
    rw [paschHausdorffEnvelope_apply]
    apply le_iInf
    intro y
    -- Compare the `y`-summand at `x` with the `y`-summand at `z` via the triangle inequality.
    have hbase := paschHausdorffEnvelope_le_value_add_scaled_dist f β x y
    have hdist0 : dist x y ≤ dist x z + dist z y := by
      simpa [dist_comm] using dist_triangle_right x y z
    have hdist :
        (β : ℝ) * dist x y ≤ (β : ℝ) * dist z y + c := by
      dsimp [c]
      nlinarith [NNReal.coe_nonneg β, hdist0]
    have hdist' :
        ((((β : ℝ) * dist x y : ℝ) : EReal)) ≤
          ((((β : ℝ) * dist z y + c : ℝ) : EReal)) := by
      exact_mod_cast hdist
    have hcompare :
        paschHausdorffEnvelope f β x ≤
          ((f y : EReal) + ((((β : ℝ) * dist z y : ℝ) : EReal))) + (c : EReal) := by
      calc
        paschHausdorffEnvelope f β x ≤
            (f y : EReal) + ((((β : ℝ) * dist x y : ℝ) : EReal)) := hbase
        _ ≤ (f y : EReal) + ((((β : ℝ) * dist z y + c : ℝ) : EReal)) :=
          add_le_add le_rfl hdist'
        _ = ((f y : EReal) + ((((β : ℝ) * dist z y : ℝ) : EReal))) + (c : EReal) := by
          rw [EReal.coe_add, add_assoc]
    simpa [c, dist_eq_norm] using EReal.sub_le_of_le_add hcompare
  -- Move the finite constant back to the right-hand side.
  exact
    (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))).1 hsub

/-- Helper for Proposition 12 17: a finite envelope value generates the standard norm-cone
`β`-Lipschitz minorant. -/
theorem norm_cone_mem_betaLipschitzMinorants_of_envelope_finite
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal) {x₀ : H}
    (hx_top : paschHausdorffEnvelope f β x₀ < ⊤)
    (hx_bot : paschHausdorffEnvelope f β x₀ ≠ ⊥) :
    (fun z : H ↦ (paschHausdorffEnvelope f β x₀).toReal - (β : ℝ) * dist z x₀) ∈
      betaLipschitzMinorants f β := by
  rw [mem_betaLipschitzMinorants_iff]
  constructor
  · -- The cone function inherits the Lipschitz constant from the distance map.
    refine LipschitzWith.of_le_add_mul β ?_
    intro z w
    nlinarith [NNReal.coe_nonneg β, dist_triangle_left w x₀ z]
  · intro z
    simp only [Function.asEReal_apply, Function.toEReal_apply]
    -- Rewrite the envelope estimate at `x₀` as a cone inequality below `f z`.
    have henv :
        paschHausdorffEnvelope f β x₀ ≤
          (f z : EReal) + ((((β : ℝ) * dist x₀ z : ℝ) : EReal)) :=
      paschHausdorffEnvelope_le_value_add_scaled_dist f β x₀ z
    have henv' :
        (((paschHausdorffEnvelope f β x₀).toReal : ℝ) : EReal) ≤
          (f z : EReal) + ((((β : ℝ) * dist z x₀ : ℝ) : EReal)) := by
      rw [EReal.coe_toReal hx_top.ne hx_bot]
      simpa [dist_comm] using henv
    have hcone :
        (((paschHausdorffEnvelope f β x₀).toReal : ℝ) : EReal) -
            ((((β : ℝ) * dist z x₀ : ℝ) : EReal)) ≤
          (f z : EReal) := by
      exact
        (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2
          henv'
    simpa using hcone

/-- Helper for Proposition 12 17: if the minorant set is nonempty, then the envelope is the
canonical `EReal` lift of the greatest `β`-Lipschitz minorant. -/
theorem isGreatest_betaLipschitzMinorants_of_nonempty
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal)
    (hf : ∃ x : H, (f x : EReal) < ⊤)
    (hne : (betaLipschitzMinorants f β).Nonempty) :
    ∃ h : H → ℝ,
      paschHausdorffEnvelope f β = h.toEReal.asEReal ∧
        IsGreatest (betaLipschitzMinorants f β) h := by
  rcases hne with ⟨h₀, h₀mem⟩
  let h : H → ℝ := fun x ↦ (paschHausdorffEnvelope f β x).toReal
  have hlt_top : ∀ x : H, paschHausdorffEnvelope f β x < ⊤ :=
    paschHausdorffEnvelope_lt_top_of_exists_finite_point f β hf
  have h₀_le_env :
      h₀.toEReal.asEReal ≤ paschHausdorffEnvelope f β :=
    le_paschHausdorffEnvelope_of_mem_betaLipschitzMinorants f β h₀mem
  have hne_bot : ∀ x : H, paschHausdorffEnvelope f β x ≠ ⊥ := by
    intro x
    -- A real-valued minorant prevents the envelope from dropping to `⊥`.
    have hx :
        ((h₀ x : ℝ) : EReal) ≤ paschHausdorffEnvelope f β x := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using h₀_le_env x
    intro hx_bot
    have hfalse : False := by
      simpa [hx_bot] using hx
    exact hfalse.elim
  have h_eq : paschHausdorffEnvelope f β = h.toEReal.asEReal := by
    funext x
    -- Each envelope value is finite, so `toReal` recovers it exactly.
    simpa [h, Function.asEReal_apply, Function.toEReal_apply] using
      (EReal.coe_toReal (hlt_top x).ne (hne_bot x)).symm
  have h_lipschitz : LipschitzWith β h := by
    refine LipschitzWith.of_le_add_mul β ?_
    intro x y
    -- Push the envelope-side `EReal` inequality down to `ℝ`.
    have hxy := paschHausdorffEnvelope_le_add_scaled_dist f β x y
    have hright_top :
        paschHausdorffEnvelope f β y + ((((β : ℝ) * dist x y : ℝ) : EReal)) ≠ ⊤ :=
      EReal.add_ne_top (hlt_top y).ne (EReal.coe_ne_top _)
    have hxy_real :
        (paschHausdorffEnvelope f β x).toReal ≤
          (paschHausdorffEnvelope f β y + ((((β : ℝ) * dist x y : ℝ) : EReal))).toReal :=
      EReal.toReal_le_toReal hxy (hne_bot x) hright_top
    rw [EReal.toReal_add (hlt_top y).ne (hne_bot y) (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hxy_real
    simpa [h] using hxy_real
  have h_le_f : h.toEReal.asEReal ≤ f.asEReal := by
    intro x
    -- Test the envelope formula at `y = x` to recover the minorant inequality `env x ≤ f x`.
    have henv : paschHausdorffEnvelope f β x ≤ (f x : EReal) := by
      simpa using paschHausdorffEnvelope_le_value_add_scaled_dist f β x x
    have henv' : (((paschHausdorffEnvelope f β x).toReal : ℝ) : EReal) ≤ (f x : EReal) := by
      rw [EReal.coe_toReal (hlt_top x).ne (hne_bot x)]
      exact henv
    simpa [h, Function.asEReal_apply, Function.toEReal_apply] using henv'
  have hmem : h ∈ betaLipschitzMinorants f β := by
    rw [mem_betaLipschitzMinorants_iff]
    exact ⟨h_lipschitz, h_le_f⟩
  have hgreatest : IsGreatest (betaLipschitzMinorants f β) h := by
    refine ⟨hmem, ?_⟩
    intro g hg
    -- Any other minorant lies below the envelope, hence below the realized function `h`.
    have hg_le_env := le_paschHausdorffEnvelope_of_mem_betaLipschitzMinorants f β hg
    intro x
    have h_eq_x :
        paschHausdorffEnvelope f β x = ((h x : ℝ) : EReal) := by
      simpa [h, Function.asEReal_apply, Function.toEReal_apply] using congrFun h_eq x
    have hgx :
        ((g x : ℝ) : EReal) ≤ paschHausdorffEnvelope f β x := by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using hg_le_env x
    have hgx' : ((g x : ℝ) : EReal) ≤ ((h x : ℝ) : EReal) := by
      simpa [h_eq_x] using hgx
    exact EReal.coe_le_coe_iff.mp hgx'
  exact ⟨h, h_eq, hgreatest⟩

-- Proof sketch: specialize the Pasch--Hausdorff envelope formula to the norm kernel
-- `x ↦ β ‖x‖`. If `f` admits a `β`-Lipschitz minorant, compare that minorant with the defining
-- infimum to show the envelope is real-valued, `β`-Lipschitz, and maximal among such minorants.
-- If no such minorant exists, any finite envelope value would itself produce one, so the envelope
-- must be identically `-∞`. The hypothesis `hf` is the properness assumption specialized to
-- `f : H → ]-∞,+∞]`, where only the existence of a finite point remains nonredundant.
/-- Proposition 12 17: for the `β`-Pasch--Hausdorff envelope of a proper `]-∞,+∞]`-valued
function, exactly one of the following holds: (i) the envelope is the greatest `β`-Lipschitz
continuous minorant, or (ii) there is no `β`-Lipschitz continuous minorant and the envelope is
identically `-∞`. -/
theorem paschHausdorffEnvelope_greatestBetaLipschitzMinorant_or_eq_bot
    (f : H → Set.Ioi (⊥ : EReal)) (β : NNReal)
    (hf : ∃ x : H, (f x : EReal) < ⊤) :
    Xor'
      (∃ h : H → ℝ,
        paschHausdorffEnvelope f β = h.toEReal.asEReal ∧
          IsGreatest (betaLipschitzMinorants f β) h)
      (¬ (betaLipschitzMinorants f β).Nonempty ∧
        paschHausdorffEnvelope f β = (⊥ : H → EReal)) := by
  by_cases hne : (betaLipschitzMinorants f β).Nonempty
  · -- In the nonempty branch, package the realized envelope as the greatest minorant.
    rcases isGreatest_betaLipschitzMinorants_of_nonempty f β hf hne with ⟨h, h_eq, hgreatest⟩
    refine Or.inl ?_
    constructor
    · exact ⟨h, h_eq, hgreatest⟩
    · intro hbot_branch
      exact hbot_branch.1 hne
  · -- Route correction: when no minorant exists, any finite envelope value would generate the
    -- cone minorant from the source proof, so the envelope must be identically `⊥`.
    have hbot : paschHausdorffEnvelope f β = (⊥ : H → EReal) := by
      funext x
      have hx_top := paschHausdorffEnvelope_lt_top_of_exists_finite_point f β hf x
      by_cases hx_bot : paschHausdorffEnvelope f β x = ⊥
      · exact hx_bot
      · exact
          (hne ⟨_,
            norm_cone_mem_betaLipschitzMinorants_of_envelope_finite f β
              (x₀ := x) hx_top hx_bot⟩).elim
    refine Or.inr ?_
    constructor
    · exact ⟨hne, hbot⟩
    · intro hgreat_branch
      rcases hgreat_branch with ⟨h, _, hgreatest⟩
      exact hne ⟨h, hgreatest.1⟩

end ERealFunction
