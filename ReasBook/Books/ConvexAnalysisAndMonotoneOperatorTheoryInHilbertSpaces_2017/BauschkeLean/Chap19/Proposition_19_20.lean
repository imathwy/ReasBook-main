import Mathlib
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Definition_19_16
import BauschkeLean.Chap19.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace translate

universe u v

namespace ERealFunction

noncomputable section

section Basic

variable {H : Type u} {K : Type v}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup K] [NormedSpace ℝ K]
variable (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)

/-
Source/core/bridge triage:
- `source-facing`: `compositePerturbationFunction` is the textbook perturbation
  `F (x, y) = f x + g (L x + y)`.
- `core/canonical`: the surrounding owner declarations are `perturbationPrimalObjective`,
  `perturbationDualObjective`, `lagrangian`, `compositePrimalObjective`, and
  `compositeDualObjective`.
- `bridge/view`: the proposition below keeps the perturbation as the owner and records the
  canonical rewrites from perturbation-level objectives and saddle points back to the source
  composite primal-dual formulas.
-/

/-- The perturbation function `F(x,y) = f(x) + g(Lx + y)` attached to the composite objective
`x ↦ f(x) + g(Lx)`, expressed as the canonical pointwise sum of the pullback of `f` along
`Prod.fst` and the pullback of `g` along `(x, y) ↦ Lx + y`. -/
abbrev compositePerturbationFunction
    :
    H × K → Set.Ioi (⊥ : EReal) :=
  (f ∘ Prod.fst) + (g ∘ fun p ↦ L p.1 + p.2)

/-- Evaluating `compositePerturbationFunction f g L` gives the formula
`f(x) + g(Lx + y)`. -/
@[simp] theorem compositePerturbationFunction_apply
    (x : H) (y : K) :
    (compositePerturbationFunction f g L (x, y) : EReal) =
      (f x : EReal) + (g (L x + y) : EReal) :=
  rfl

-- Proof sketch: evaluate the perturbation function at `(x, 0)` and simplify the resulting
-- formula `g (L x + 0)` to `g (L x)`.
/-- Proposition 19.20 (2): the primal problem associated with the perturbation
`F(x,y) = f(x) + g(Lx + y)` is the minimization of `x ↦ f(x) + g(Lx)`. -/
@[simp] theorem perturbationPrimalObjective_compositePerturbationFunction
    :
    perturbationPrimalObjective (compositePerturbationFunction f g L) =
      compositePrimalObjective f g L := by
  funext x
  simp [compositePrimalObjective_apply]

end Basic

section ProductL2Ambient

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2
attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 19 20: the shear map `(x, y) ↦ (x, Lx + y)` on `H × K`. -/
abbrev compositePerturbationShear :
    (H × K) →L[ℝ] (H × K) :=
  (ContinuousLinearMap.fst ℝ H K).prod
    (L.comp (ContinuousLinearMap.fst ℝ H K) + ContinuousLinearMap.snd ℝ H K)

/-- Helper for Proposition 19 20: evaluating the shear map gives `(x, Lx + y)`. -/
@[simp] theorem compositePerturbationShear_apply
    (p : H × K) :
    compositePerturbationShear L p = (p.1, L p.1 + p.2) := by
  rfl

/-- Helper for Proposition 19 20: the composite perturbation is the separable sum
`(x, z) ↦ f x + g z` precomposed with the shear `(x, y) ↦ (x, Lx + y)`. -/
theorem compositePerturbationFunction_eq_separable_sum_comp_shear :
    compositePerturbationFunction f g L =
      (((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) ∘ compositePerturbationShear L) := by
  -- Both sides evaluate to the same textbook formula `f x + g (Lx + y)`.
  funext p
  rfl

/-- Helper for Proposition 19 20: fixing `x`, the second-variable slice is the translate of `g`
by `-Lx`, plus the constant value `f x`. -/
theorem secondSlice_compositePerturbationFunction_eq_translate_add_const
    (x : H) :
    (fun y : K ↦ (compositePerturbationFunction f g L (x, y) : EReal)) =
      (τ (-(L x)) g.asEReal) + fun _ : K ↦ (f x : EReal) := by
  funext y
  simp [translate_apply, sub_eq_add_neg, add_comm]

/-- Helper for Proposition 19 20: precomposing a `Γ₀(K)` function with a continuous linear map
preserves `Γ₀(H)` membership when the range of the map meets the effective domain. -/
theorem comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty_local
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K))
    (hdom : (Set.range (compositePerturbationShear L) ∩ effectiveDomain
      ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2)).Nonempty) :
    (((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) ∘ compositePerturbationShear L) ∈ Γ₀(H × K) := by
  have hfst : (fun p : H × K ↦ f p.1) ∈ Γ₀(H × K) := by
    rw [mem_gammaZero_iff]
    constructor
    · simpa using hf.1.comp continuous_fst
    · refine ⟨?_, fun _ hp ↦ hp, ?_⟩
      · rcases hf.2.nonempty with ⟨x, hx⟩
        refine ⟨(x, 0), ?_⟩
        simpa [mem_effectiveDomain_iff] using hx
      · intro p hp q hq a ha0 ha1
        have hp' : p.1 ∈ effectiveDomain f := by
          simpa [mem_effectiveDomain_iff] using hp
        have hq' : q.1 ∈ effectiveDomain f := by
          simpa [mem_effectiveDomain_iff] using hq
        simpa using hf.2.ineq hp' hq' ha0 ha1
  have hsnd : (fun p : H × K ↦ g p.2) ∈ Γ₀(H × K) := by
    rw [mem_gammaZero_iff]
    constructor
    · simpa using hg.1.comp continuous_snd
    · refine ⟨?_, fun _ hp ↦ hp, ?_⟩
      · rcases hg.2.nonempty with ⟨y, hy⟩
        refine ⟨(0, y), ?_⟩
        simpa [mem_effectiveDomain_iff] using hy
      · intro p hp q hq a ha0 ha1
        have hp' : p.2 ∈ effectiveDomain g := by
          simpa [mem_effectiveDomain_iff] using hp
        have hq' : q.2 ∈ effectiveDomain g := by
          simpa [mem_effectiveDomain_iff] using hq
        simpa using hg.2.ineq hp' hq' ha0 ha1
  rcases hf.2.nonempty with ⟨x, hx⟩
  rcases hg.2.nonempty with ⟨y, hy⟩
  have hsum : ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) ∈ Γ₀(H × K) :=
    pointwiseAdd_mem_gammaZero
      (fun p : H × K ↦ f p.1)
      (fun p ↦ g p.2)
      hfst
      hsnd
      ⟨(x, y), by simpa [mem_effectiveDomain_iff] using hx,
        by simpa [mem_effectiveDomain_iff] using hy⟩
  rw [mem_gammaZero_iff] at hsum ⊢
  refine ⟨?_, ?_⟩
  · simpa using hsum.1.comp (compositePerturbationShear L).continuous
  · refine
      ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty
          ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2)
          (compositePerturbationShear L) hdom,
        subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hx' :
        compositePerturbationShear L x ∈
          effectiveDomain ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' :
        compositePerturbationShear L y ∈
          effectiveDomain ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2) := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hsum.2.ineq hx' hy' ha0 ha1

-- Proof sketch: the map `(x, y) ↦ Lx + y` is continuous and affine on `H × K`, so composing `g`
-- with it preserves lower semicontinuity and convexity; adding the pullback of `f` preserves
-- both properties. Properness is automatic because `hf` and `hg` give points `x ∈ dom f` and
-- `z ∈ dom g`, and then choosing `y := z - Lx` makes the perturbation finite at `(x, y)`.
/-- Proposition 19 20 (1): if `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, then the perturbation
`F(x,y) = f(x) + g(Lx + y)` belongs to `Γ₀(ℋ ⊕ 𝒦)`. -/
theorem compositePerturbationFunction_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) :
    compositePerturbationFunction f g L ∈ Γ₀(H × K) := by
  have hdom :
      (Set.range (compositePerturbationShear L) ∩ effectiveDomain
        ((fun p : H × K ↦ f p.1) + fun p ↦ g p.2)).Nonempty := by
    rcases hf.2.nonempty with ⟨x, hx⟩
    rcases hg.2.nonempty with ⟨z, hz⟩
    refine ⟨(x, z), ?_, ?_⟩
    · refine ⟨(x, z - L x), ?_⟩
      simp
    · rw [mem_effectiveDomain_iff]
      have hx' : (f x : EReal) < ⊤ := mem_effectiveDomain_iff.mp hx
      have hz' : (g z : EReal) < ⊤ := mem_effectiveDomain_iff.mp hz
      simpa using EReal.add_lt_top (ne_of_lt hx') (ne_of_lt hz')
  have hcomp :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty_local
      (f := f) (g := g) (L := L) hf hg hdom
  simpa [compositePerturbationFunction_eq_separable_sum_comp_shear] using hcomp

/-- Helper for Proposition 19 20: after the substitution `z = Lx + y`, the affine defect of the
composite perturbation splits into the separate `f`- and `g`-defects. -/
theorem compositePerturbation_affine_defect_split
    [CompleteSpace H] [CompleteSpace K]
    (x : H) (z : K) (v : K) :
    (((⟪z - L x, v⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g z : EReal))) =
      ((((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
        (((⟪z, v⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hgz_bot : (g z : EReal) ≠ ⊥ := ne_of_gt (g z).2
  have hadj : ⟪x, -(L.adjoint v)⟫_ℝ = -⟪L x, v⟫_ℝ := by
    simpa [inner_neg_right] using
      congrArg Neg.neg (ContinuousLinearMap.adjoint_inner_right (A := L) x v)
  have hinner :
      (((⟪z - L x, v⟫_ℝ : ℝ) : EReal)) =
        (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) +
          ((⟪z, v⟫_ℝ : ℝ) : EReal)) := by
    have hreal :
        ⟪z - L x, v⟫_ℝ = ⟪x, -(L.adjoint v)⟫_ℝ + ⟪z, v⟫_ℝ := by
      calc
        ⟪z - L x, v⟫_ℝ = ⟪z, v⟫_ℝ - ⟪L x, v⟫_ℝ := by
          simp [inner_sub_left]
        _ = ⟪z, v⟫_ℝ + ⟪x, -(L.adjoint v)⟫_ℝ := by
          rw [sub_eq_add_neg, hadj]
        _ = ⟪x, -(L.adjoint v)⟫_ℝ + ⟪z, v⟫_ℝ := by
          simp [add_comm]
    rw [hreal, EReal.coe_add]
  rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hfx_bot) (.inr hgz_bot), sub_eq_add_neg,
    sub_eq_add_neg]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 19 20: negating `a - b - c` with finite real terms `b` and `c`
reverses the order into `c + b - a`. -/
theorem ereal_neg_sub_sub_eq_add_add_neg
    {a : EReal} {b c : ℝ} (ha_bot : a ≠ ⊥) (_ha_top : a ≠ ⊤) :
    -(a - (b : EReal) - (c : EReal)) = ((c : EReal) + (b : EReal) - a) := by
  have hb_bot : (b : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hb_top : (b : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hc_bot : (c : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hc_top : (c : EReal) ≠ ⊤ := EReal.coe_ne_top _
  calc
    -(a - (b : EReal) - (c : EReal)) = -((a - (b : EReal)) - (c : EReal)) := by
      rfl
    _ = -((a - (b : EReal))) + (c : EReal) := by
      simpa using
        (EReal.neg_sub (x := a - (b : EReal)) (y := (c : EReal)) (.inr hc_bot) (.inr hc_top))
    _ = (-a + (b : EReal)) + (c : EReal) := by
      rw [EReal.neg_sub (x := a) (y := (b : EReal)) (.inl ha_bot) (.inr hb_top)]
    _ = ((c : EReal) + (b : EReal) - a) := by
      simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Proposition 19 20: the infimum of the pointwise negatives is the negative of the
corresponding supremum. -/
theorem ereal_iInf_neg_eq_neg_iSup
    {ι : Sort*} (φ : ι → EReal) :
    (⨅ i, -φ i) = -(⨆ i, φ i) := by
  have hmap : -(⨅ i, -φ i) = ⨆ i, -(-φ i) := by
    exact OrderIso.map_iInf EReal.negOrderIso (fun i : ι ↦ -φ i)
  have hmap' : -(⨅ i, -φ i) = (⨆ i, φ i) := by
    simpa using hmap
  rw [← hmap']
  simp

-- Proof sketch: unfold `perturbationDualObjective` for the perturbation,
-- `z = Lx + y`,
-- and recognize the remaining supremum as `f^*(-L^* v) + g^*(v)`.
/-- Proposition 19.20 (3): the dual problem associated with the perturbation
`F(x,y) = f(x) + g(Lx + y)` is the minimization of
`v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem perturbationDualObjective_compositePerturbationFunction
    [CompleteSpace H] [CompleteSpace K]
    :
    perturbationDualObjective (compositePerturbationFunction f g L) =
      compositeDualObjective f g L := by
  funext v
  rw [perturbationDualObjective_apply, compositeDualObjective_apply, conjugate_apply,
    conjugate_apply]
  calc
    (⨆ p : H × K,
        (((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
          (compositePerturbationFunction f g L p : EReal))) =
        ⨆ x : H, ⨆ y : K,
          (((⟪y, v⟫_ℝ : ℝ) : EReal) -
            (compositePerturbationFunction f g L (x, y) : EReal)) := by
          rw [iSup_prod']
    _ = ⨆ x : H, ⨆ y : K,
          (((⟪y, v⟫_ℝ : ℝ) : EReal) -
            ((f x : EReal) + (g (L x + y) : EReal))) := by
          refine iSup_congr fun x => ?_
          refine iSup_congr fun y => ?_
          rw [compositePerturbationFunction_apply]
    _ = ⨆ x : H, ⨆ z : K,
          (((⟪z - L x, v⟫_ℝ : ℝ) : EReal) -
            ((f x : EReal) + (g z : EReal))) := by
          refine iSup_congr fun x => ?_
          show
            (⨆ y : K,
              (((⟪y, v⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g (L x + y) : EReal)))) =
              ⨆ z : K,
                (((⟪z - L x, v⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g z : EReal)))
          exact
            ((Equiv.addRight (-(L x))).surjective.iSup_congr (Equiv.addRight (-(L x))) fun z => by
              simp [sub_eq_add_neg, add_left_comm, add_comm]).symm
    _ = ⨆ x : H, ⨆ z : K,
          ((((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
            (((⟪z, v⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
          refine iSup_congr fun x => ?_
          refine iSup_congr fun z => ?_
          simpa using compositePerturbation_affine_defect_split
            (f := f) (g := g) (L := L) x z v
    _ = (⨆ x : H, (((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) - (f x : EReal))) +
          (⨆ z : K, (((⟪z, v⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
          exact iSup_iSup_add_eq_add_iSup _ _

-- Proof sketch: unfold `lagrangian` for the perturbation function, change variables
-- `z = Lx + y`, and identify the remaining infimum with `-g^*(v)`. The cases `x ∉ dom f` and
-- `v ∉ dom g^*` produce the values `+∞` and `-∞`, respectively.
/-- Proposition 19.20 (4): the Lagrangian of the perturbation `F(x,y) = f(x) + g(Lx + y)` is the
piecewise function from formula `(19.34)`. -/
theorem lagrangian_compositePerturbationFunction
    (hg : g ∈ Γ₀(K)) (x : H) (v : K) :
    ℒ[compositePerturbationFunction f g L] x v =
      if _hx : x ∈ effectiveDomain f then
        if _hv : v ∈ effectiveDomain (g∗[hg]) then
          (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
        else
          ⊥
      else
        ⊤ := by
  by_cases hx : x ∈ effectiveDomain f
  · have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hlag_neg_conj :
        ℒ[compositePerturbationFunction f g L] x v =
          -((fun y : K ↦
              (compositePerturbationFunction f g L (x, y) : EReal))∗ v) := by
      calc
        ℒ[compositePerturbationFunction f g L] x v =
            ⨅ y : K,
              (compositePerturbationFunction f g L (x, y) : EReal) -
                (⟪y, v⟫_ℝ : EReal) := by
              rw [lagrangian_apply]
        _ = ⨅ y : K,
              -((((⟪y, v⟫_ℝ : ℝ) : EReal) -
                (compositePerturbationFunction f g L (x, y) : EReal))) := by
              refine iInf_congr fun y => ?_
              have hFy_bot :
                  (compositePerturbationFunction f g L (x, y) : EReal) ≠ ⊥ :=
                ne_of_gt (compositePerturbationFunction f g L (x, y)).2
              simpa [sub_eq_add_neg, add_comm] using
                (EReal.neg_sub
                  (x := (((⟪y, v⟫_ℝ : ℝ) : EReal)))
                  (y := (compositePerturbationFunction f g L (x, y) : EReal))
                  (.inl (EReal.coe_ne_bot _))
                  (.inl (EReal.coe_ne_top _))).symm
        _ = -(⨆ y : K,
              (((⟪y, v⟫_ℝ : ℝ) : EReal) -
                (compositePerturbationFunction f g L (x, y) : EReal))) := by
              let ψ : K → EReal := fun y : K ↦
                (((⟪y, v⟫_ℝ : ℝ) : EReal) -
                  (compositePerturbationFunction f g L (x, y) : EReal))
              simpa [ψ] using ereal_iInf_neg_eq_neg_iSup ψ
        _ = -((fun y : K ↦
              (compositePerturbationFunction f g L (x, y) : EReal))∗ v) := by
              rw [conjugate_apply]
    let β : ℝ := (f x : EReal).toReal
    have hβ : ((β : ℝ) : EReal) = (f x : EReal) := by
      simp [β, EReal.coe_toReal hfx_top hfx_bot]
    have hslice :
        (fun y : K ↦ (compositePerturbationFunction f g L (x, y) : EReal)) =
          (τ (-(L x)) g.asEReal) + fun _ : K ↦ ((β : ℝ) : EReal) := by
      calc
        (fun y : K ↦ (compositePerturbationFunction f g L (x, y) : EReal)) =
            (τ (-(L x)) g.asEReal) + fun _ : K ↦ (f x : EReal) :=
              secondSlice_compositePerturbationFunction_eq_translate_add_const
                (f := f) (g := g) (L := L) x
        _ = (τ (-(L x)) g.asEReal) + fun _ : K ↦ ((β : ℝ) : EReal) := by
              simp [hβ]
    have hconj :
        (((τ (-(L x)) g.asEReal) + fun _ : K ↦ ((β : ℝ) : EReal))∗ v) =
          (g∗[hg] v : EReal) - (⟪L x, v⟫_ℝ : EReal) - ((β : ℝ) : EReal) := by
      simpa [gammaZeroConjugate_apply, translate_apply, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, inner_neg_left] using
        (congrFun
          (conjugate_translate_add_inner_add_const
            (f := g.asEReal) (y := -(L x)) (v := (0 : K)) (β := β))
          v)
    by_cases hv : v ∈ effectiveDomain (g∗[hg])
    · have hgv_bot : (g∗[hg] v : EReal) ≠ ⊥ := ne_of_gt (g∗[hg] v).2
      have hgv_top : (g∗[hg] v : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hv)
      have hlag_value :
          ℒ[compositePerturbationFunction f g L] x v =
            ((β : ℝ) : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) := by
        calc
          ℒ[compositePerturbationFunction f g L] x v =
              -((g∗[hg] v : EReal) - (⟪L x, v⟫_ℝ : EReal) - ((β : ℝ) : EReal)) := by
                rw [hlag_neg_conj, hslice, hconj]
          _ = ((β : ℝ) : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) := by
                simpa using
                  ereal_neg_sub_sub_eq_add_add_neg
                    (a := (g∗[hg] v : EReal)) (b := ⟪L x, v⟫_ℝ) (c := β) hgv_bot hgv_top
      simpa [hx, hv, hβ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlag_value
    · have hgv_top : (g∗[hg] v : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hv))
      have hconj_top :
          (((τ (-(L x)) g.asEReal) + fun _ : K ↦ ((β : ℝ) : EReal))∗ v) = ⊤ := by
        rw [hconj, hgv_top]
        simp [sub_eq_add_neg]
      have hlag_bot : ℒ[compositePerturbationFunction f g L] x v = ⊥ := by
        rw [hlag_neg_conj, hslice, hconj_top]
        simp
      simpa [hx, hv] using hlag_bot
  · have hfx_top : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [lagrangian_apply]
    have hfiber :
        (fun y : K ↦
          (compositePerturbationFunction f g L (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal)) =
          fun _ : K ↦ (⊤ : EReal) := by
      funext y
      rw [compositePerturbationFunction_apply, hfx_top]
      simp [EReal.top_add_of_ne_bot (ne_of_gt (g (L x + y)).2)]
    rw [hfiber]
    simp [hx]

/-- Helper for Proposition 19 20: for fixed `x`, the supremum of the Lagrangian fiber in the
multiplier variable recovers the composite primal objective. -/
theorem lagrangian_sSup_eq_compositePrimalObjective
    [CompleteSpace K]
    (hg : g ∈ Γ₀(K)) (x : H) :
    sSup (Set.range fun w : K ↦ ℒ[compositePerturbationFunction f g L] x w) =
      compositePrimalObjective f g L x := by
  rw [sSup_range, compositePrimalObjective_apply]
  by_cases hx : x ∈ effectiveDomain f
  · have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    let β : ℝ := (f x : EReal).toReal
    have hβ : ((β : ℝ) : EReal) = (f x : EReal) := by
      simp [β, EReal.coe_toReal hfx_top hfx_bot]
    have hlag (w : K) :
        ℒ[compositePerturbationFunction f g L] x w =
          ((((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal)) +
            ((β : ℝ) : EReal)) := by
      by_cases hw : w ∈ effectiveDomain (g∗[hg])
      · have hlag_base :
            ℒ[compositePerturbationFunction f g L] x w =
              (f x : EReal) + (⟪L x, w⟫_ℝ : EReal) - (g∗[hg] w : EReal) := by
          simpa [hx, hw] using
            lagrangian_compositePerturbationFunction (f := f) (g := g) (L := L) hg x w
        rw [hlag_base, hβ]
        simp [sub_eq_add_neg, add_assoc, add_comm]
      · have hgw_top : (g∗[hg] w : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hw))
        have hlag_bot :
            ℒ[compositePerturbationFunction f g L] x w = ⊥ := by
          simpa [hx, hw] using
            lagrangian_compositePerturbationFunction (f := f) (g := g) (L := L) hg x w
        rw [hlag_bot, hgw_top]
        simp [hβ, sub_eq_add_neg]
    have hsup_conj :
        (⨆ w : K, (((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal))) =
          (g (L x) : EReal) := by
      calc
        (⨆ w : K, (((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal))) =
            (⨆ w : K, (((⟪w, L x⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal))) := by
              refine iSup_congr fun w => ?_
              simp [real_inner_comm]
        _ =
            ((g∗[hg]).asEReal∗) (L x) := by
              rw [conjugate_apply]
        _ = (g.asEReal∗∗) (L x) := by
              have hconj_eq : (g∗[hg]).asEReal = g.asEReal∗ := by
                funext u
                exact gammaZeroConjugate_apply g hg u
              rw [hconj_eq]
        _ = (g (L x) : EReal) := by
              simpa using congrFun (biconjugate_eq_of_mem_gammaZero hg) (L x)
    calc
      (⨆ w : K, ℒ[compositePerturbationFunction f g L] x w) =
          (⨆ w : K, (((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal)) +
            ((β : ℝ) : EReal)) := by
              refine iSup_congr fun w => hlag w
      _ =
          (⨆ w : K, (((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal))) +
            ((β : ℝ) : EReal) := by
              simpa using
                ereal_iSup_add_of_real_shift β
                  (fun w : K ↦ (((⟪L x, w⟫_ℝ : ℝ) : EReal) - (g∗[hg] w : EReal)))
      _ = (g (L x) : EReal) + ((β : ℝ) : EReal) := by
            rw [hsup_conj]
      _ = (f x : EReal) + (g (L x) : EReal) := by
            simp [hβ, add_comm]
  · have hfx_top : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have htop : ∀ w : K, ℒ[compositePerturbationFunction f g L] x w = ⊤ := by
      intro w
      simpa [hx] using lagrangian_compositePerturbationFunction
        (f := f) (g := g) (L := L) hg x w
    have hsup_top :
        (⨆ w : K, ℒ[compositePerturbationFunction f g L] x w) = (⨆ _ : K, (⊤ : EReal)) := by
      refine iSup_congr fun w => htop w
    calc
      (⨆ w : K, ℒ[compositePerturbationFunction f g L] x w) = (⨆ _ : K, (⊤ : EReal)) := hsup_top
      _ = (⊤ : EReal) := by
        simp
      _ = compositePrimalObjective f g L x := by
        rw [compositePrimalObjective_apply, hfx_top]
        exact (EReal.top_add_of_ne_bot (ne_of_gt (g (L x)).2)).symm

/-- Helper for Proposition 19 20: for fixed `v`, the infimum of the Lagrangian fiber in the
primal variable is the negative composite dual objective. -/
theorem lagrangian_sInf_eq_neg_compositeDualObjective
    [CompleteSpace H] [CompleteSpace K]
    (v : K) :
    sInf (Set.range fun z : H ↦ ℒ[compositePerturbationFunction f g L] z v) =
      -compositeDualObjective f g L v := by
  calc
    sInf (Set.range fun z : H ↦ ℒ[compositePerturbationFunction f g L] z v) =
        ⨅ z : H, ℒ[compositePerturbationFunction f g L] z v := by
          rw [sInf_range]
    _ = ⨅ z : H, ⨅ y : K,
          (compositePerturbationFunction f g L (z, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
          simp [lagrangian_apply]
    _ = ⨅ p : H × K,
          (compositePerturbationFunction f g L p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
          rw [iInf_prod]
    _ = ⨅ p : H × K,
          -((((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
            (compositePerturbationFunction f g L p : EReal))) := by
          refine iInf_congr fun p => ?_
          have hFp_bot : (compositePerturbationFunction f g L p : EReal) ≠ ⊥ :=
            ne_of_gt (compositePerturbationFunction f g L p).2
          simpa [sub_eq_add_neg, add_comm] using
            (EReal.neg_sub
              (x := (((⟪p.2, v⟫_ℝ : ℝ) : EReal)))
              (y := (compositePerturbationFunction f g L p : EReal))
              (.inl (EReal.coe_ne_bot _))
              (.inl (EReal.coe_ne_top _))).symm
    _ = -(⨆ p : H × K,
          (((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
            (compositePerturbationFunction f g L p : EReal))) := by
          let ψ : H × K → EReal := fun p : H × K ↦
            (((⟪p.2, v⟫_ℝ : ℝ) : EReal) -
              (compositePerturbationFunction f g L p : EReal))
          simpa [ψ] using ereal_iInf_neg_eq_neg_iSup ψ
    _ = -perturbationDualObjective (compositePerturbationFunction f g L) v := by
          rw [perturbationDualObjective_apply]
    _ = -compositeDualObjective f g L v := by
          rw [perturbationDualObjective_compositePerturbationFunction]

section ParametricDuality

variable [CompleteSpace H] [CompleteSpace K]

-- Proof sketch: Proposition 19.20 (1) places the perturbation in `Γ₀(H × K)`. Corollary 19.19
-- then identifies saddle points of its Lagrangian with primal-dual solution pairs. The bridge
-- clauses above rewrite those primal and dual objectives into the composite formulas, and the
-- resulting optimality system reduces to `-L^* v ∈ ∂ f(x)` and `Lx ∈ ∂ g^*(v)`.
/-- Proposition 19.20 (5): assuming the primal and dual optimal values satisfy
`μ = -μ* ∈ ℝ`, a pair `(x, v)` is a saddle point of the Lagrangian if and only if
`-L^* v ∈ ∂ f(x)` and `Lx ∈ ∂ g^*(v)`. -/
theorem isSaddlePointOn_lagrangian_compositePerturbationFunction_iff
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K))
    (hμ :
      ∃ μ : ℝ,
        compositePrimalOptimalValue f g L = μ ∧
          compositeDualOptimalValue f g L = -μ)
    (x : H) (v : K) :
    IsSaddlePointOn (univ : Set H) (univ : Set K)
        (ℒ[compositePerturbationFunction f g L]) x v ↔
      -L.adjoint v ∈ (∂ f) x ∧
        L x ∈ (∂ (g∗[hg])) v := by
  obtain ⟨μ, hprimal, hdual⟩ := hμ
  have hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
    rw [hprimal, hdual]
    simp
  let F : H × K → Set.Ioi (⊥ : EReal) := compositePerturbationFunction f g L
  constructor
  · intro hsaddle
    have hs := (lagrangian_isSaddlePointOn_iff F x v).mp (by simpa [F] using hsaddle)
    have hcontact :
        compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
      calc
        compositePrimalObjective f g L x =
            sSup (Set.range fun w : K ↦ ℒ[F] x w) := by
              simpa [F] using
                (lagrangian_sSup_eq_compositePrimalObjective
                  (f := f) (g := g) (L := L) hg x).symm
        _ = ℒ[F] x v := hs.1
        _ = sInf (Set.range fun z : H ↦ ℒ[F] z v) := hs.2.symm
        _ = -compositeDualObjective f g L v := by
              simpa [F] using
                lagrangian_sInf_eq_neg_compositeDualObjective
                  (f := f) (g := g) (L := L) v
    have hf_proper : IsProper f.asEReal := by
      refine ⟨?_, ?_⟩
      · intro z
        exact ne_of_gt (f z).2
      · simpa [effectiveDomain, dom] using hf.2.nonempty
    have hg_proper : IsProper g.asEReal := by
      refine ⟨?_, ?_⟩
      · intro z
        exact ne_of_gt (g z).2
      · simpa [effectiveDomain, dom] using hg.2.nonempty
    have hzero :
        ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 := by
      let lhs : EReal := (f x : EReal) + (g (L x) : EReal)
      let rhs : EReal := f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v
      have hcontact' : lhs = -rhs := by
        simpa [lhs, rhs, compositePrimalObjective_apply, compositeDualObjective_apply,
          add_assoc, add_left_comm, add_comm] using hcontact
      have hlhs_ne_bot : lhs ≠ ⊥ := by
        rw [show lhs = (f x : EReal) + (g (L x) : EReal) by rfl, EReal.add_ne_bot_iff]
        exact ⟨ne_of_gt (f x).2, ne_of_gt (g (L x)).2⟩
      have hrhs_ne_bot : rhs ≠ ⊥ := by
        rw [show rhs = f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v by rfl, EReal.add_ne_bot_iff]
        exact ⟨conjugate_ne_bot_of_isProper hf_proper (-(L.adjoint v)),
          conjugate_ne_bot_of_isProper hg_proper v⟩
      have hlhs_ne_top : lhs ≠ ⊤ := by
        intro hlhs_top
        have hrhs_bot : rhs = ⊥ := by
          exact EReal.neg_eq_top_iff.mp (by simpa [hlhs_top] using hcontact'.symm)
        exact hrhs_ne_bot hrhs_bot
      have hrhs_ne_top : rhs ≠ ⊤ := by
        intro hrhs_top
        have hlhs_bot : lhs = ⊥ := by
          simpa [hrhs_top] using hcontact'
        exact hlhs_ne_bot hlhs_bot
      simpa [lhs, rhs] using
        (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
          hlhs_ne_top hlhs_ne_bot hrhs_ne_top hrhs_ne_bot).1 hcontact'
    have hsub :=
      (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).mp hzero
    exact
      ⟨hsub.1,
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
          g hg (L x) v).mp hsub.2⟩
  · rintro ⟨hfx, hgv⟩
    have hsub :
        -L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x) := by
      exact
        ⟨hfx,
          (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
            g hg (L x) v).mpr hgv⟩
    have hf_proper : IsProper f.asEReal := by
      refine ⟨?_, ?_⟩
      · intro z
        exact ne_of_gt (f z).2
      · simpa [effectiveDomain, dom] using hf.2.nonempty
    have hg_proper : IsProper g.asEReal := by
      refine ⟨?_, ?_⟩
      · intro z
        exact ne_of_gt (g z).2
      · simpa [effectiveDomain, dom] using hg.2.nonempty
    have hzero :
        ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 :=
      (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).mpr hsub
    have hcontact :
        compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
      let lhs : EReal := (f x : EReal) + (g (L x) : EReal)
      let rhs : EReal := f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v
      have hlhs_ne_bot : lhs ≠ ⊥ := by
        rw [show lhs = (f x : EReal) + (g (L x) : EReal) by rfl, EReal.add_ne_bot_iff]
        exact ⟨ne_of_gt (f x).2, ne_of_gt (g (L x)).2⟩
      have hrhs_ne_bot : rhs ≠ ⊥ := by
        rw [show rhs = f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v by rfl, EReal.add_ne_bot_iff]
        exact ⟨conjugate_ne_bot_of_isProper hf_proper (-(L.adjoint v)),
          conjugate_ne_bot_of_isProper hg_proper v⟩
      have hlhs_ne_top : lhs ≠ ⊤ := by
        intro hlhs_top
        have htop : lhs + rhs = ⊤ := by
          rw [hlhs_top]
          exact EReal.top_add_of_ne_bot hrhs_ne_bot
        exact EReal.zero_ne_top (hzero.symm.trans htop)
      have hrhs_ne_top : rhs ≠ ⊤ := by
        intro hrhs_top
        have htop : lhs + rhs = ⊤ := by
          rw [hrhs_top]
          exact EReal.add_top_of_ne_bot hlhs_ne_bot
        exact EReal.zero_ne_top (hzero.symm.trans htop)
      have hcontact' :
          lhs = -rhs :=
        (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
          hlhs_ne_top hlhs_ne_bot hrhs_ne_top hrhs_ne_bot).2 (by simpa [lhs, rhs] using hzero)
      simpa [lhs, rhs, compositePrimalObjective_apply, compositeDualObjective_apply, add_assoc,
        add_left_comm, add_comm] using hcontact'
    have hfy_g :
        (g (L x) : EReal) + g.asEReal∗ v = ((⟪L x, v⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := g) hg.2.nonempty (L x) v).1 hsub.2
    have hxdom : x ∈ effectiveDomain f := by
      exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf <| by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨-(L.adjoint v), hsub.1⟩
    have hvdom : v ∈ effectiveDomain (g∗[hg]) := by
      exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
        (gammaZeroConjugate_mem_gammaZero hg) <| by
          rw [SetValuedOperator.mem_dom_iff]
          exact ⟨L x, hgv⟩
    have hlag :
        ℒ[F] x v = compositePrimalObjective f g L x := by
      have hLxdom : L x ∈ effectiveDomain g := by
        exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hg <| by
          rw [SetValuedOperator.mem_dom_iff]
          exact ⟨v, hsub.2⟩
      have hgx_bot : (g (L x) : EReal) ≠ ⊥ := ne_of_gt (g (L x)).2
      have hgx_top : (g (L x) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hLxdom)
      have hgv_bot : (g∗[hg] v : EReal) ≠ ⊥ := ne_of_gt (g∗[hg] v).2
      have hgv_top : (g∗[hg] v : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hvdom)
      have hbranch :
          (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) = (g (L x) : EReal) := by
        have hsum : (g (L x) : EReal) + (g∗[hg] v : EReal) = (⟪L x, v⟫_ℝ : EReal) := by
          simpa [gammaZeroConjugate_apply] using hfy_g
        apply le_antisymm
        · exact
            (EReal.sub_le_iff_le_add (.inl hgv_bot) (.inl hgv_top)).2
              (by simpa [add_comm] using hsum.symm.le)
        · exact
            (EReal.le_sub_iff_add_le (.inl hgv_bot) (.inl hgv_top)).2
              (by simpa using hsum.le)
      have hconj_eval :
          (g∗[hg] v : EReal) =
            ⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (g y : EReal)) := by
        rw [gammaZeroConjugate_apply, conjugate_apply]
      have hlag_if :
          (if hx : x ∈ effectiveDomain f then
              if hv : v ∈ effectiveDomain (g∗[hg]) then
                (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
              else
                ⊥
            else
              ⊤) =
            (f x : EReal) + (g (L x) : EReal) := by
        have hsum_branch :
            (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) =
              (f x : EReal) + (g (L x) : EReal) := by
          calc
            (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) =
                (f x : EReal) + ((⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)) := by
                  simp [sub_eq_add_neg, add_assoc]
            _ = (f x : EReal) + (g (L x) : EReal) := by
                  rw [hbranch]
        calc
          (if hx : x ∈ effectiveDomain f then
              if hv : v ∈ effectiveDomain (g∗[hg]) then
                (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
              else
                ⊥
            else
              ⊤) =
              (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal) := by
                simp [hxdom, hvdom]
          _ = (f x : EReal) + (g (L x) : EReal) := hsum_branch
      rw [lagrangian_compositePerturbationFunction (f := f) (g := g) (L := L) hg x v]
      rw [compositePrimalObjective_apply]
      exact hlag_if
    refine (lagrangian_isSaddlePointOn_iff F x v).2 ?_
    constructor
    · calc
        sSup (Set.range fun w : K ↦ ℒ[F] x w) = compositePrimalObjective f g L x := by
            change sSup (Set.range fun w : K ↦
              ℒ[compositePerturbationFunction f g L] x w) = compositePrimalObjective f g L x
            exact lagrangian_sSup_eq_compositePrimalObjective (f := f) (g := g) (L := L) hg x
        _ = ℒ[F] x v := hlag.symm
    · calc
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = -compositeDualObjective f g L v := by
            change sInf (Set.range fun z : H ↦
              ℒ[compositePerturbationFunction f g L] z v) = -compositeDualObjective f g L v
            exact lagrangian_sInf_eq_neg_compositeDualObjective (f := f) (g := g) (L := L) v
        _ = compositePrimalObjective f g L x := hcontact.symm
        _ = ℒ[F] x v := hlag.symm

end ParametricDuality

end ProductL2Ambient

end

end ERealFunction
