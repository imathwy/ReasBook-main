import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Pointwise

variable {E : Type*} {α : Type*} (R : Type*)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.0.4 forms the intersection `K₁ ∩ K₂` of the two scaled epigraph
  families attached to `f₁` and `f₂`, then takes its unit slice
  `F = {(x, μ) | (1, x, μ) ∈ K₁ ∩ K₂}`.
- `core/canonical`: the chapter owner abstractions are the imported three-variable family
  `rightScalarMulEpigraphFamily`, its unit-slice membership theorem
  `mem_rightScalarMulEpigraphFamily_one`, the epigraph owner `epi`, the pointwise supremum owner
  `f₁ ⊔ f₂` on `E → WithTopBot α`, and the function-level owner
  `Function.verticalInfimum` from `Theorem_5_3`.
- `bridge/view`: the unit slice of the intersection of the two owner families
  `rightScalarMulEpigraphFamily f₁` and `rightScalarMulEpigraphFamily f₂` is exactly the
  epigraph `epi (f₁ ⊔ f₂)`, so the attached function is obtained canonically by applying
  `Function.verticalInfimum` to that slice.
- Primitive data vs derived API: the only primitive set retained here is the source-facing unit
  slice `F` built from the imported owner family; the fiberwise membership criterion and the
  resulting `Function.verticalInfimum = f₁ ⊔ f₂` statement are derived API, while the raw
  `sInf = (f₁ ⊔ f₂) x` formula is only a companion specification.

Domain-style sampling used here:
- `rightScalarMulEpigraphFamily`;
- `mem_rightScalarMulEpigraphFamily_one`;
- the source-facing unit-slice set expression
  `{p | ((1 : R), p.1, p.2) ∈ rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂}`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_epi`;
- `sup_le_iff` in the lattice `WithTopBot α`.

The source phrases the proposition for proper convex functions, but the displayed unit-slice
identity depends only on the canonical scaled-epigraph owner API already established earlier in the
chapter, so the properness and convexity hypotheses are redundant and omitted.
- Ambient minimization: the primitive source-facing slice expression
  `{p | ((1 : R), p.1, p.2) ∈ rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂}`
  only needs the scalar data needed to form the imported family
  `rightScalarMulEpigraphFamily` together with a distinguished unit scalar `1`; stronger action
  laws are only required by the derived `λ = 1` simplification theorems. The file uses no
  additive, module, coordinate, finite-dimensional, or `Fin`-specific structure.

Layer target: `bridge/view`; this file exposes the textbook unit slice directly as a source-facing
set expression and states the bridge theorems on the canonical owners `epi` and
`Function.verticalInfimum`.
-/

section

variable [Monoid R] [Zero R] [Preorder R]
variable [ConditionallyCompleteLattice α]
variable [MulAction R α] [MulAction R E]
variable [ZeroLEOneClass R] [NoBotOrder α]

@[simp] theorem mem_unit_slice_right_scalar_epigraph_inter
    (f₁ f₂ : E → WithTopBot α) (x : E) (μ : α) :
    (x, μ) ∈ ({p : E × α |
      ((1 : R), p.1, p.2) ∈
        (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)} : Set (E × α)) ↔
      f₁ x ≤ μ ∧ f₂ x ≤ μ := by
  simp

-- Proof sketch: membership in the unit slice means simultaneous membership in the two canonical
-- scaled epigraphs at `λ = 1`. Rewrite each side with
-- `mem_rightScalarMulEpigraphFamily_one`, then package the two inequalities through
-- the canonical pointwise supremum owner `f₁ ⊔ f₂`.
/-- The unit slice of the two scaled epigraph families is exactly the epigraph of the pointwise
maximum, expressed through the canonical binary supremum owner `f₁ ⊔ f₂`. -/
theorem unit_slice_right_scalar_epigraph_inter_eq_epi_sup
    (f₁ f₂ : E → WithTopBot α) :
    ({p : E × α |
      ((1 : R), p.1, p.2) ∈
        (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)} : Set (E × α)) =
      epi (f₁ ⊔ f₂) := by
  ext p
  rcases p with ⟨x, μ⟩
  simp [sup_le_iff]

/-- Helper for Text 5.8.0.4: the vertical infimum of the global epigraph of `g` recovers `g`
itself. -/
private theorem withTopBot_coe_le_coe_iff {β : Type*} [Preorder β] {a b : β} :
    ((a : WithTopBot β) ≤ (b : WithTopBot β)) ↔ a ≤ b := by
  constructor
  · intro h
    exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp h)
  · intro h
    simp [h]

/-- Helper for Text 5.8.0.4: the vertical infimum of the global epigraph of `g` recovers `g`
itself. -/
private theorem verticalInfimum_epi_eq
    (g : E → WithTopBot α) :
    Function.verticalInfimum (epi g) = g := by
  apply le_antisymm
  · intro x
    by_cases htop : g x = (⊤ : WithTopBot α)
    · simp [Function.verticalInfimum, Function.verticalHeights, epi, htop]
    · by_cases hbot : g x = (⊥ : WithTopBot α)
      · have hle_all : ∀ μ : α, Function.verticalInfimum (epi g) x ≤ μ := by
          intro μ
          exact Function.verticalInfimum_le_of_mem
            ((mem_epi_restrict_iff).2 ⟨by simp, by simp [hbot]⟩)
        have hbot' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot α) := by
          classical
          by_contra hne
          cases hvi : Function.verticalInfimum (epi g) x with
          | none =>
              have htop' : Function.verticalInfimum (epi g) x = (⊤ : WithTopBot α) := by
                simpa [WithTopBot] using hvi
              let μ0 : α := Classical.choice inferInstance
              have : (⊤ : WithTopBot α) ≤ μ0 := by
                simpa [htop'] using hle_all μ0
              have hnot : ¬ ((⊤ : WithTopBot α) ≤ μ0) := by simp
              exact (hnot this).elim
          | some z =>
              cases hz : z with
              | bot =>
                  have hbot'' : Function.verticalInfimum (epi g) x = (⊥ : WithTopBot α) := by
                    simpa [WithTopBot, hz] using hvi
                  exact hne hbot''
              | coe a =>
                  have hcoe : Function.verticalInfimum (epi g) x = (a : WithTopBot α) := by
                    simpa [WithTopBot, hz] using hvi
                  rcases exists_not_ge a with ⟨μ, hnaμ⟩
                  have haμ : (a : WithTopBot α) ≤ μ := by
                    simpa [hcoe] using hle_all μ
                  exact hnaμ (withTopBot_coe_le_coe_iff.mp haμ)
        simp [hbot, hbot']
      · cases h : g x with
        | none => contradiction
        | some z =>
            cases hz : z with
            | bot =>
                have : g x = (⊥ : WithTopBot α) := by
                  simpa [WithTopBot, hz] using h
                exact (hbot this).elim
            | coe a =>
                have ha : g x = (a : WithTopBot α) := by
                  simpa [WithTopBot, hz] using h
                have hxepi : (x, a) ∈ epi g := by
                  exact (mem_epi_restrict_iff).2 ⟨by simp, by simp [ha]⟩
                have hle : Function.verticalInfimum (epi g) x ≤ a :=
                  Function.verticalInfimum_le_of_mem hxepi
                simpa [ha] using hle
  · exact Function.le_verticalInfimum_of_subset_epi (subset_rfl : epi g ⊆ epi g)

-- Proof sketch: rewrite the source-facing unit slice as the intrinsic scalar epigraph of
-- `f₁ ⊔ f₂` using `unit_slice_right_scalar_epigraph_inter_eq_epi_sup`, then apply the owner
-- theorem `verticalInfimum_epi`.
/-- Text 5.8.0.4: the vertical infimum function of the unit slice
`F = {(x, μ) | (1, x, μ) ∈ K₁ ∩ K₂}` is the pointwise maximum of `f₁` and `f₂`,
expressed through the canonical pointwise supremum owner `f₁ ⊔ f₂`. -/
theorem unit_slice_right_scalar_epigraph_inter_infimum_eq_sup
    (f₁ f₂ : E → WithTopBot α) :
    Function.verticalInfimum
      ({p : E × α |
        ((1 : R), p.1, p.2) ∈
          (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)}) =
      f₁ ⊔ f₂ := by
  rw [unit_slice_right_scalar_epigraph_inter_eq_epi_sup R f₁ f₂]
  exact verticalInfimum_epi_eq (g := f₁ ⊔ f₂)

/-- The intrinsic height-set owner `verticalHeights` of the unit slice above `x` has
infimum equal to the pointwise supremum `(f₁ ⊔ f₂) x`. -/
theorem sInf_unit_slice_right_scalar_epigraph_inter_eq_sup
    (f₁ f₂ : E → WithTopBot α) (x : E) :
    sInf
        (Function.verticalHeights
          ({p : E × α |
            ((1 : R), p.1, p.2) ∈
              (rightScalarMulEpigraphFamily f₁ ∩ rightScalarMulEpigraphFamily f₂)})
          x) =
      (f₁ ⊔ f₂) x := by
  simpa [Function.verticalInfimum] using
    congrFun (unit_slice_right_scalar_epigraph_inter_infimum_eq_sup R f₁ f₂) x

end

end
