import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 16 26: the raw extended-real coordinate supremum before packaging the
codomain as `]-∞,+∞]`. -/
private noncomputable def affineInnerSupremumEReal (u : ℕ → H) (α : ℕ → ℝ) : H → EReal :=
  fun x ↦ ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)

/-- Helper for Example 16 26: every value of the raw coordinate supremum lies strictly above
`⊥`. -/
private theorem affineInnerSupremum_value_mem_Ioi_bot
    (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    affineInnerSupremumEReal u α x ∈ Set.Ioi (⊥ : EReal) := by
  -- Every branch is a finite real number, so the supremum is still strictly above `⊥`.
  rw [affineInnerSupremumEReal]
  refine lt_of_lt_of_le ?_ (le_iSup (fun n : ℕ ↦ ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) 0)
  exact EReal.bot_lt_coe _

/-- Helper for Example 16 26: the affine coordinate supremum used in the textbook example. -/
noncomputable def affineInnerSupremum (u : ℕ → H) (α : ℕ → ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨affineInnerSupremumEReal u α x, affineInnerSupremum_value_mem_Ioi_bot u α x⟩

/-- Helper for Example 16 26: coercing the packaged coordinate supremum to `EReal` recovers its
defining pointwise supremum formula. -/
@[simp] theorem affineInnerSupremum_apply
    (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    (affineInnerSupremum u α x : EReal) =
      ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal) :=
  rfl

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Coercing the Example 16.26 function to `EReal` recovers the supremum of the coordinate ratios.
-/
@[simp] theorem hilbertBasisCoordinateSupremum_apply
    (b : HilbertBasis ℕ ℝ H) (α : ℕ → ℝ) (x : H) :
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 x : EReal) =
      ⨆ n : ℕ, (((⟪x, b n⟫_ℝ) / α n : ℝ) : EReal) := by
  rw [affineInnerSupremum_apply]
  refine iSup_congr fun n ↦ ?_
  have hratio : ⟪x, (α n)⁻¹ • b n⟫_ℝ - 0 = ⟪x, b n⟫_ℝ / α n := by
    rw [sub_zero, inner_smul_right, div_eq_mul_inv, mul_comm]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hratio

/-- The witness `z = -∑ α_n e_n` from Example 16.26, encoded through the Hilbert-basis
identification with `ℓ²(ℕ, ℝ)`. -/
noncomputable def hilbertBasisCoordinateSupremumWitness
    (b : HilbertBasis ℕ ℝ H) (α : ℓ²(ℕ, ℝ)) : H :=
  -(b.repr.symm α)

-- Proof sketch: each coordinate map `x ↦ ⟪x, b n⟫ / α_n` is a continuous affine functional. The
-- supremum of continuous affine minorants is lower semicontinuous and convex, and the origin
-- belongs to the effective domain because every coordinate ratio vanishes there.
omit [CompleteSpace H] in
/-- The Example 16.26 function belongs to `Γ₀(H)`. -/
theorem hilbertBasisCoordinateSupremum_mem_gammaZero
    (b : HilbertBasis ℕ ℝ H) (α : ℕ → ℝ) :
    affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 ∈ Γ₀(H) := by
  have hbranch :
      ∀ n : ℕ,
        (fun x : H ↦ ((⟪x, (α n)⁻¹ • b n⟫_ℝ : ℝ) : EReal)) ∈ Γ(H) := by
    intro n
    -- Commute the inner product so each branch is the standard continuous inner functional.
    have hrewrite :
        (fun x : H ↦ ((⟪x, (α n)⁻¹ • b n⟫_ℝ : ℝ) : EReal)) =
          fun x : H ↦ ((⟪(α n)⁻¹ • b n, x⟫_ℝ : ℝ) : EReal) := by
      funext x
      rw [real_inner_comm]
    rw [hrewrite]
    exact inner_functional_mem_gamma ((α n)⁻¹ • b n)
  have hgamma :
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal ∈ Γ(H) := by
    have hsup :
        (fun x : H ↦ ⨆ n : ℕ, ((⟪x, (α n)⁻¹ • b n⟫_ℝ : ℝ) : EReal)) ∈ Γ(H) :=
      iSup_mem_gamma
        (fun n : ℕ ↦ fun x : H ↦ ((⟪x, (α n)⁻¹ • b n⟫_ℝ : ℝ) : EReal))
        hbranch
    have hfun :
        (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal =
          fun x : H ↦ ⨆ n : ℕ, ((⟪x, (α n)⁻¹ • b n⟫_ℝ : ℝ) : EReal) := by
      funext x
      rw [Function.asEReal_apply, affineInnerSupremum_apply]
      simp [sub_zero]
    -- Rewrite the function as the countable supremum of the branch functionals in `Γ(H)`.
    rw [hfun]
    exact hsup
  have hproper :
      IsProper (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal := by
    constructor
    · intro x
      -- The bundled codomain excludes `⊥`, so the raw `EReal` representative is proper below.
      exact ne_of_gt ((affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 x).2)
    · refine ⟨0, ?_⟩
      -- At the origin every coordinate ratio vanishes, so the value is finite.
      rw [mem_dom_iff, Function.asEReal_apply, hilbertBasisCoordinateSupremum_apply]
      simp
  have hproperIoi :
      properIoi ((affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal) hproper =
        affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0 := by
    funext x
    apply Subtype.ext
    rfl
  -- Upgrade the proper `Γ(H)` owner to `Γ₀(H)` through `properIoi`.
  rw [← hproperIoi]
  exact properIoi_mem_gammaZero_of_mem_gamma hproper hgamma

section

variable (b : HilbertBasis ℕ ℝ H)
local notation "Cₛ" => (Submodule.span ℝ (Set.range b) : Submodule ℝ H)
local notation "C" => (Cₛ : Set H)

/-- Helper for Example 16 26: every finite subset of `ℕ` misses some natural number. -/
theorem exists_nat_not_mem_finset
    (s : Finset ℕ) :
    ∃ n : ℕ, n ∉ s := by
  have hs : s.card < ENat.card ℕ := by
    simp
  exact Finset.exists_not_mem_of_card_lt_enatCard hs

omit [CompleteSpace H] in
/-- Helper for Example 16 26: a finite linear combination of Hilbert-basis vectors has basis
coordinates equal to its coefficients. -/
theorem hilbertBasis_coordinate_of_finsupp_linearCombination
    (c : ℕ →₀ ℝ) (n : ℕ) :
    ⟪Finsupp.linearCombination ℝ b c, b n⟫_ℝ = c n := by
  -- Orthonormality makes the inner product pick out the `n`th coefficient.
  simpa using b.orthonormal.inner_left_finsupp c n

omit [CompleteSpace H] in
/-- Helper for Example 16 26: outside the support of a finite coefficient family, the corresponding
Hilbert-basis coordinate vanishes. -/
theorem hilbertBasis_coordinate_eq_zero_of_not_mem_support
    (c : ℕ →₀ ℝ) {n : ℕ} (hn : n ∉ c.support) :
    ⟪Finsupp.linearCombination ℝ b c, b n⟫_ℝ = 0 := by
  -- The coefficient formula collapses to `0` away from the support.
  have hcn : c n = 0 := by
    simpa [Finsupp.mem_support_iff] using hn
  simpa [hcn] using hilbertBasis_coordinate_of_finsupp_linearCombination (b := b) c n

omit [CompleteSpace H] in
/-- Helper for Example 16 26: evaluating the coordinate supremum on a finite linear combination
replaces the basis coordinates by the coefficient family. -/
theorem hilbertBasisCoordinateSupremum_apply_linearCombination
    (α : ℕ → ℝ) (c : ℕ →₀ ℝ) :
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal
        (Finsupp.linearCombination ℝ b c) =
      ⨆ n : ℕ, (((c n / α n : ℝ) : EReal)) := by
  -- Expand the coordinate supremum and read off the basis coefficients of the finite sum.
  rw [Function.asEReal_apply, hilbertBasisCoordinateSupremum_apply]
  refine iSup_congr fun n ↦ ?_
  rw [hilbertBasis_coordinate_of_finsupp_linearCombination (b := b) c n]

/-- Helper for Example 16 26: the supremum of finitely supported coordinate ratios is bounded above
by the support-sum of their absolute values. -/
theorem finite_coordinate_supremum_le_sum_abs
    (α : ℕ → ℝ) (c : ℕ →₀ ℝ) :
    (⨆ n : ℕ, (((c n / α n : ℝ) : EReal))) ≤
      (↑(c.support.sum fun i ↦ |c i / α i|) : EReal) := by
  have hsum_nonneg : 0 ≤ c.support.sum (fun i ↦ |c i / α i|) := by
    exact Finset.sum_nonneg fun i hi ↦ abs_nonneg (c i / α i)
  refine iSup_le fun n ↦ ?_
  by_cases hn : n ∈ c.support
  · -- Inside the support, the chosen term is dominated by its absolute value and then by the sum.
    have habs_le :
        |c n / α n| ≤ c.support.sum (fun i ↦ |c i / α i|) := by
      exact Finset.single_le_sum (fun i hi ↦ abs_nonneg (c i / α i)) hn
    have hreal :
        c n / α n ≤ c.support.sum (fun i ↦ |c i / α i|) := by
      exact (le_abs_self (c n / α n)).trans habs_le
    exact_mod_cast hreal
  · -- Outside the support the coefficient vanishes, so the branch is `0`.
    have hcn : c n = 0 := by
      simpa [Finsupp.mem_support_iff] using hn
    have hreal :
        c n / α n ≤ c.support.sum (fun i ↦ |c i / α i|) := by
      simpa [hcn] using hsum_nonneg
    exact_mod_cast hreal

/-- Helper for Example 16 26: the supremum of finitely supported coordinate ratios is
nonnegative because a tail coordinate outside the support contributes `0`. -/
theorem finite_coordinate_supremum_nonneg
    (α : ℕ → ℝ) (c : ℕ →₀ ℝ) :
    (0 : EReal) ≤ ⨆ n : ℕ, (((c n / α n : ℝ) : EReal)) := by
  obtain ⟨n, hn⟩ := exists_nat_not_mem_finset c.support
  have hcn : c n = 0 := by
    simpa [Finsupp.mem_support_iff] using hn
  -- Evaluate the supremum at a coordinate where the finite family vanishes.
  calc
    (0 : EReal) = (((c n / α n : ℝ) : EReal)) := by simp [hcn]
    _ ≤ ⨆ m : ℕ, (((c m / α m : ℝ) : EReal)) := by
      exact le_iSup (fun m : ℕ ↦ (((c m / α m : ℝ) : EReal))) n

-- Proof sketch: a vector in the span of the basis has only finitely many nonzero basis
-- coordinates, so the supremum of the coordinate ratios is finite there.
omit [CompleteSpace H] in
/-- The span `C = span{e_n}` lies in the effective domain of the Example 16.26 function. -/
theorem hilbertBasisCoordinateSupremumSpan_subset_effectiveDomain
    (α : ℕ → ℝ) :
    C ⊆ effectiveDomain (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0) :=
  by
    intro x hx
    rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hx with ⟨c, hc⟩
    have hc_lin : Finsupp.linearCombination ℝ b c = x := by
      simpa [Finsupp.linearCombination_apply] using hc
    -- Rewrite the span element as a finite linear combination and bound the resulting coefficient
    -- supremum by a finite real sum.
    rw [mem_effectiveDomain_iff, ← hc_lin]
    have hfinite :
        (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal
            (Finsupp.linearCombination ℝ b c) < ⊤ := by
      calc
        (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal
            (Finsupp.linearCombination ℝ b c)
            = ⨆ n : ℕ, (((c n / α n : ℝ) : EReal)) := by
                rw [hilbertBasisCoordinateSupremum_apply_linearCombination (b := b) (α := α) c]
        _ ≤ (↑(c.support.sum fun i ↦ |c i / α i|) : EReal) :=
              finite_coordinate_supremum_le_sum_abs (α := α) c
        _ < ⊤ := EReal.coe_lt_top _
    simpa [Function.asEReal_apply] using hfinite

/- The span `C = span{e_n}` is convex by the canonical submodule convexity theorem. -/
#check Submodule.convex Cₛ

/- The span `C = span{e_n}` is dense by the canonical Hilbert-basis span theorem. -/
#check b.dense_span

-- Proof sketch: on the span `C`, the coordinate ratios include the zero tail and therefore have
-- nonnegative supremum; off `C`, the indicator contributes `⊤`. Thus `f + ι_C` is pointwise
-- nonnegative.
omit [CompleteSpace H] in
/-- The indicator-augmented Example 16.26 function satisfies `0 ≤ f + ι_C` pointwise. -/
theorem zero_le_hilbertBasisCoordinateSupremumWithIndicator
    (α : ℕ → ℝ) :
    (fun _ : H ↦ (0 : EReal)) ≤
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal +
        (ι[C]).asEReal := by
  intro x
  by_cases hx : x ∈ C
  · rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hx with ⟨c, hc⟩
    have hc_lin : Finsupp.linearCombination ℝ b c = x := by
      simpa [Finsupp.linearCombination_apply] using hc
    have hnonneg :
        (0 : EReal) ≤ (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal x := by
      -- On the span, rewrite to the finitely supported coefficient family and choose a zero tail
      -- coordinate.
      rw [← hc_lin, hilbertBasisCoordinateSupremum_apply_linearCombination (b := b) (α := α) c]
      exact finite_coordinate_supremum_nonneg (α := α) c
    simpa [indicator_apply, hx] using hnonneg
  · -- Off the span, the indicator contributes `⊤`, so the lower bound is immediate.
    simp [indicator_apply, hx]

omit [CompleteSpace H] in
/-- Helper for Example 16 26: the witness has basis coordinates `-α n`. -/
theorem hilbertBasisCoordinateSupremumWitness_coordinate
    (α : ℓ²(ℕ, ℝ)) (n : ℕ) :
    ⟪hilbertBasisCoordinateSupremumWitness b α, b n⟫_ℝ = -α n := by
  -- Apply `b.repr` to the witness and read off the `n`th coordinate.
  have hcoord :
      ⟪b n, hilbertBasisCoordinateSupremumWitness b α⟫_ℝ = (-α) n := by
    calc
      ⟪b n, hilbertBasisCoordinateSupremumWitness b α⟫_ℝ
          = b.repr (hilbertBasisCoordinateSupremumWitness b α) n := by
              rw [b.repr_apply_apply]
      _ = (-α) n := by
        simp [hilbertBasisCoordinateSupremumWitness]
      _ = -α n := by
        rfl
  simpa [real_inner_comm] using hcoord

-- Proof sketch: the basis coefficients of `z = -∑ α_n e_n` are exactly `-α_n`, so every ratio
-- `⟪z, e_n⟫ / α_n` equals `-1` because `α_n ≠ 0`; taking the supremum gives `f(z) = -1`.
omit [CompleteSpace H] in
/-- The Example 16.26 witness `z = -∑ α_n e_n` satisfies `f(z) = -1`. -/
theorem hilbertBasisCoordinateSupremum_apply_witness
    (α : ℓ²(ℕ, ℝ)) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal
        (hilbertBasisCoordinateSupremumWitness b α) =
      (-1 : EReal) := by
  have hconst :
      (fun n : ℕ ↦
        (((⟪hilbertBasisCoordinateSupremumWitness b α, b n⟫_ℝ) / α n : ℝ) : EReal)) =
        fun _ : ℕ ↦ (-1 : EReal) := by
    funext n
    have hratio : ⟪hilbertBasisCoordinateSupremumWitness b α, b n⟫_ℝ / α n = (-1 : ℝ) := by
      rw [hilbertBasisCoordinateSupremumWitness_coordinate (b := b) α n]
      field_simp [hα_ne n]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hratio
  -- Every coordinate ratio is exactly `-1`, so the supremum is constant.
  rw [Function.asEReal_apply, hilbertBasisCoordinateSupremum_apply]
  rw [hconst]
  simp

-- Proof sketch: every vector in `span{e_n}` has finite support in its basis coordinates, whereas
-- the witness `z = -∑ α_n e_n` has every coordinate equal to `-α_n ≠ 0` because `α_n ≠ 0`.
omit [CompleteSpace H] in
/-- The Example 16.26 witness does not belong to the span `C = span{e_n}`. -/
theorem hilbertBasisCoordinateSupremumWitness_not_mem_span
    (α : ℓ²(ℕ, ℝ)) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    hilbertBasisCoordinateSupremumWitness b α ∉ C := by
  intro hzC
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hzC with ⟨c, hc⟩
  obtain ⟨n, hn⟩ := exists_nat_not_mem_finset c.support
  have hspan_coord :
      ⟪hilbertBasisCoordinateSupremumWitness b α, b n⟫_ℝ = 0 := by
    -- The chosen tail coordinate of a finite span representation vanishes.
    have hc_lin : Finsupp.linearCombination ℝ b c = hilbertBasisCoordinateSupremumWitness b α := by
      simpa [Finsupp.linearCombination_apply] using hc
    rw [← hc_lin]
    exact hilbertBasis_coordinate_eq_zero_of_not_mem_support (b := b) c hn
  have hwitness_coord :
      ⟪hilbertBasisCoordinateSupremumWitness b α, b n⟫_ℝ ≠ 0 := by
    rw [hilbertBasisCoordinateSupremumWitness_coordinate (b := b) α n]
    exact neg_ne_zero.mpr (hα_ne n)
  exact hwitness_coord hspan_coord

-- Proof sketch: the previous helper theorem gives `0 ≤ f + ι_C`, so Proposition 13.16(ii)
-- yields `0 = 0** ≤ (f + ι_C)**`. Evaluating at the witness `z = -∑ α_n e_n`, the function value
-- is `f(z) = -1`, so `(f + ι_C)** z ≠ f z`; hence the two functions are not equal.
omit [CompleteSpace H] in
/-- Example 16 26: for the Hilbert-basis coefficient supremum `f(x) = sup_n ⟪x,e_n⟫ / α_n` and
the span `C = span{e_n}`, the Fenchel biconjugate of `f + ι_C` does not coincide with `f`. -/
theorem hilbertBasisCoordinateSupremumWithIndicator_biconjugate_ne
    (α : ℓ²(ℕ, ℝ)) (hα_ne : ∀ n : ℕ, α n ≠ 0) :
    ((affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal +
        (ι[C]).asEReal)∗∗ ≠
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal := by
  -- Route correction: stay inside the current import closure by proving `F∗ 0 = 0` directly from
  -- the pointwise nonnegativity of `F`, then evaluate `F∗∗` at the witness using the `u = 0`
  -- branch of the defining supremum.
  intro hEq
  let F : H → EReal :=
    (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal + (ι[C]).asEReal
  let z : H := hilbertBasisCoordinateSupremumWitness b α
  have hF_nonneg : (fun _ : H ↦ (0 : EReal)) ≤ F := by
    simpa [F] using zero_le_hilbertBasisCoordinateSupremumWithIndicator (b := b) (α := α)
  have hF_zero : F 0 = 0 := by
    -- At the origin both the coordinate supremum and the indicator of the span vanish.
    simp [F, indicator_apply]
  have hconj_zero_nonneg : (0 : EReal) ≤ F∗ 0 := by
    -- Evaluate the conjugate supremum at the primal point `0`.
    rw [conjugate_apply]
    simpa [F, hF_zero] using
      (le_iSup (fun x : H ↦ (((⟪x, (0 : H)⟫_ℝ : ℝ) : EReal) - F x)) (0 : H))
  have hconj_zero_nonpos : F∗ 0 ≤ 0 := by
    -- Every affine defect at `u = 0` is nonpositive because `F` is pointwise nonnegative.
    rw [conjugate_apply]
    refine iSup_le fun x ↦ ?_
    have hx_nonneg : (0 : EReal) ≤ F x := hF_nonneg x
    have hx_neg : -F x ≤ (0 : EReal) := by
      simpa using (EReal.neg_le_zero (a := F x)).2 hx_nonneg
    simpa using hx_neg
  have hconj_zero : F∗ 0 = 0 := le_antisymm hconj_zero_nonpos hconj_zero_nonneg
  have hnonneg : (0 : EReal) ≤ F∗∗ z := by
    -- In the biconjugate supremum, the branch `u = 0` contributes exactly `0`.
    rw [conjugate_apply]
    have hbranch :
        (0 : EReal) ≤ (((⟪(0 : H), z⟫_ℝ : ℝ) : EReal) - F∗ (0 : H)) := by
      rw [hconj_zero]
      simp
    exact hbranch.trans
      (le_iSup (fun u : H ↦ (((⟪u, z⟫_ℝ : ℝ) : EReal) - F∗ u)) (0 : H))
  have hwitness :
      (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal z = (-1 : EReal) := by
    simpa [z] using hilbertBasisCoordinateSupremum_apply_witness (b := b) α hα_ne
  have hzero_le_neg_one : (0 : EReal) ≤ (-1 : EReal) := by
    -- The assumed equality would force the nonnegative biconjugate value to equal `-1`.
    calc
      (0 : EReal) ≤ F∗∗ z := hnonneg
      _ = (affineInnerSupremum (fun n ↦ (α n)⁻¹ • b n) 0).asEReal z := by
            simpa [F] using congrFun hEq z
      _ = (-1 : EReal) := hwitness
  have hlt : (-1 : EReal) < 0 := by
    norm_num
  exact (not_le_of_gt hlt) hzero_le_neg_one

end

end

end ERealFunction
