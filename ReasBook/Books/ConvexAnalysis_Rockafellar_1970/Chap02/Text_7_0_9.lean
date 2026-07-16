import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap02.HyperbolaEpigraph
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1_WithBotTopBridge

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 7.0.9 is the concrete example `f(x) = 1 / x` for `x > 0` and `f(x) = +∞`
  for `x ≤ 0`, asserted to be closed.
- `core/canonical`: Chapter 7 uses `LowerSemicontinuous` as the owner for closed extended-real
  functions, and Chapter 1 uses `f.toWithBotTopOn C` as the owner for extension by `+∞`
  outside a set.
- `bridge/view`: the source branch formulas on `(0, ∞)` and `(-∞, 0]` are kept as specialized
  lemmas for the canonical owner `(fun x : 𝕜 ↦ x⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))`;
  no parallel wrapper definition is introduced.

Domain-style sampling used here:
- `LowerSemicontinuous`;
- `lowerSemicontinuous_iff_isClosed_sublevel`;
- `epi`;
- `Function.toWithBotTopOn` / dot-notation `f.toWithBotTopOn C`;
- `Function.toWithBotTopOn_of_mem` / `Function.toWithBotTopOn_of_notMem`;
- the source-facing bridge `epi_reciprocal_Ioi_extension_eq_hyperbolaEpigraph`.

Layer target: `core/canonical` with a source-facing pointwise bridge.
-/

section

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Inv 𝕜]

private theorem withTopBot_coe_le_coe {a b : 𝕜} :
    (a : WithTopBot 𝕜) ≤ (b : WithTopBot 𝕜) ↔ a ≤ b := by
  change
    (((a : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) ≤
        (((b : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) ↔ a ≤ b
  rw [WithTop.coe_le_coe, WithBot.coe_le_coe]

private theorem withTopBot_coe_ne_bot (a : 𝕜) :
    (a : WithTopBot 𝕜) ≠ (⊥ : WithTopBot 𝕜) := by
  intro h
  change
    (((a : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) =
      ((⊥ : WithBot 𝕜) : WithTop (WithBot 𝕜)) at h
  cases h

-- Proof sketch: unfold `Function.toWithBotTopOn` and split on whether `x ∈ Set.Ioi (0 : 𝕜)`. On
-- the positive branch the extension agrees with `x ↦ x⁻¹`, while outside that set it is `+∞`.
/-- On the positive half-line, the canonical extension of `x ↦ x⁻¹` to `WithTopBot 𝕜` agrees with
the finite reciprocal branch. -/
@[simp] theorem reciprocal_Ioi_extension_of_pos {x : 𝕜} (hx : 0 < x) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x = (x⁻¹ : 𝕜) := by
  simpa using
    (Function.toWithBotTopOn_of_mem
      (f := fun y : 𝕜 ↦ y⁻¹) (C := Set.Ioi (0 : 𝕜)) hx)

/-- Outside the positive half-line, the canonical extension of `x ↦ x⁻¹` to `WithTopBot 𝕜`
takes value `+∞`. -/
@[simp] theorem reciprocal_Ioi_extension_of_not_pos {x : 𝕜} (hx : ¬ 0 < x) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x = (⊤ : WithTopBot 𝕜) := by
  exact
    Function.toWithBotTopOn_of_notMem
      (f := fun y : 𝕜 ↦ y⁻¹) (C := Set.Ioi (0 : 𝕜))
      (by simpa [Set.mem_Ioi] using hx)

/-- The effective domain of the reciprocal extension is exactly the positive half-line. -/
theorem effectiveDomain_reciprocal_Ioi_extension :
    dom((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) = Set.Ioi (0 : 𝕜) := by
  ext x
  rw [mem_effectiveDomain]
  by_cases hx : x ∈ Set.Ioi (0 : 𝕜)
  · have hx' : 0 < x := hx
    simpa [hx, reciprocal_Ioi_extension_of_pos hx']
      using (WithTop.coe_lt_top ((x⁻¹ : 𝕜) : WithBot 𝕜))
  · simp [Function.toWithBotTopOn, hx]

/-- The reciprocal extension never takes the value `-∞`. -/
theorem reciprocal_Ioi_extension_ne_bot (x : 𝕜) :
    ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≠ (⊥ : WithTopBot 𝕜) := by
  by_cases hx : x ∈ Set.Ioi (0 : 𝕜)
  · have hx' : 0 < x := hx
    rw [reciprocal_Ioi_extension_of_pos hx']
    exact withTopBot_coe_ne_bot (x⁻¹)
  · rw [Function.toWithBotTopOn_of_notMem
      (f := fun y : 𝕜 ↦ y⁻¹) (C := Set.Ioi (0 : 𝕜)) hx]
    intro h
    cases h

end

section

variable {𝕜 : Type*}
variable [GroupWithZero 𝕜] [Preorder 𝕜]

-- Proof sketch: unfold membership in `epi` and use the two branch lemmas for the extension. The
-- `x ≤ 0` branch is impossible in the global epigraph because it would force `⊤ ≤ r`.
/-- The scalar epigraph of the reciprocal extension is exactly the source-facing owner
`hyperbolaEpigraph`. -/
theorem epi_reciprocal_Ioi_extension_eq_hyperbolaEpigraph :
    epi ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) = hyperbolaEpigraph := by
  ext p
  rcases p with ⟨x, r⟩
  constructor
  · intro hp
    rw [mem_epi_iff] at hp
    by_cases hx_pos : 0 < x
    · have hxr : x⁻¹ ≤ r := by
        exact withTopBot_coe_le_coe.mp
          (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hp)
      exact (mem_hyperbolaEpigraph_iff).2 ⟨hx_pos, hxr⟩
    · have htop : (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
        simpa [reciprocal_Ioi_extension_of_not_pos hx_pos] using hp
      exact (lt_irrefl (⊤ : WithTopBot 𝕜)
        (lt_of_le_of_lt htop (WithTop.coe_lt_top (r : WithBot 𝕜)))).elim
  · intro hp
    rw [mem_epi_iff]
    rcases (mem_hyperbolaEpigraph_iff).1 hp with ⟨hx_pos, hxr⟩
    exact by
      simpa [reciprocal_Ioi_extension_of_pos hx_pos] using
        (withTopBot_coe_le_coe.mpr hxr : ((x⁻¹ : 𝕜) : WithTopBot 𝕜) ≤ r)

end

section

variable {𝕜 : Type*}
variable [DivisionRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [NoMinOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- Text 7.0.9: the function `f(x) = 1 / x` for `x > 0` and `f(x) = +∞` for `x ≤ 0`, written
canonically as `(fun x ↦ x⁻¹).toWithBotTopOn (Set.Ioi 0)`, is closed; that is, it is
lower semicontinuous.

Assumption layer note: this theorem uses the Chapter 7 scalar-sublevel characterization
`lowerSemicontinuous_iff_isClosed_sublevel` directly, so it does not rely on any deferred
closed-epigraph lemma in the hyperbola owner file. -/
theorem lowerSemicontinuous_reciprocal_Ioi_extension :
    LowerSemicontinuous ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) := by
  refine (lowerSemicontinuous_iff_isClosed_sublevel
    (f := (fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜)))).2 ?_
  intro r
  by_cases hr : 0 < r
  · have hsublevel :
      {x : 𝕜 |
          ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≤ r} =
        Set.Ici (r⁻¹) := by
      ext x
      constructor
      · intro hx
        by_cases hx_pos : 0 < x
        · have hxr : x⁻¹ ≤ r := by
            exact withTopBot_coe_le_coe.mp
              (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hx)
          refine (inv_le_inv₀ (a := x) (b := r⁻¹) hx_pos (inv_pos.2 hr)).1 ?_
          simpa [inv_inv] using hxr
        · have htop : (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
            have htop' := hx
            simp [reciprocal_Ioi_extension_of_not_pos hx_pos] at htop'
          simp at htop
      · intro hx
        have hx_pos : 0 < x := lt_of_lt_of_le (inv_pos.2 hr) hx
        have hxr : x⁻¹ ≤ r := by
          simpa [inv_inv] using
            ((inv_le_inv₀ (a := x) (b := r⁻¹) hx_pos (inv_pos.2 hr)).2 hx)
        exact by
          simpa [reciprocal_Ioi_extension_of_pos hx_pos] using
            (withTopBot_coe_le_coe.mpr hxr :
              ((x⁻¹ : 𝕜) : WithTopBot 𝕜) ≤ r)
    simpa [hsublevel] using (isClosed_Ici : IsClosed (Set.Ici (r⁻¹ : 𝕜)))
  · have hr_nonpos : r ≤ 0 := le_of_not_gt hr
    have hsublevel :
        {x : 𝕜 |
            ((fun y : 𝕜 ↦ y⁻¹).toWithBotTopOn (Set.Ioi (0 : 𝕜))) x ≤ r} = ∅ := by
      ext x
      constructor
      · intro hx
        by_cases hx_pos : 0 < x
        · have hxr : x⁻¹ ≤ r := by
            exact withTopBot_coe_le_coe.mp
              (by simpa [reciprocal_Ioi_extension_of_pos hx_pos] using hx)
          have h0lt_r : (0 : 𝕜) < r := lt_of_lt_of_le (inv_pos.2 hx_pos) hxr
          exact (False.elim (not_lt_of_ge hr_nonpos h0lt_r))
        · have htop : (⊤ : WithTopBot 𝕜) ≤ (r : WithTopBot 𝕜) := by
            have htop' := hx
            simp [reciprocal_Ioi_extension_of_not_pos hx_pos] at htop'
          simp at htop
      · simp
    rw [hsublevel]
    exact isClosed_empty

end
