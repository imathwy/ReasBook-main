import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_5
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_18
import LecturesConvexOptimization_Nesterov_2018.Chap03.Lemma_3_1_14
import LecturesConvexOptimization_Nesterov_2018.Chap03.Remark_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise PolarSet
open scoped MinkowskiFunctional
open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.18 lies in the chapter's Minkowski-functional / polar-subdifferential domain.

Sampled owner-style declarations:
- `dom`, `IsSubgradientAt`, and `subdifferential` from `Definition_3_1_5`, the chapter owners
  for extended-valued convex analysis;
- `polarSet` and `mem_polarSet_iff` from `Definition_3_18`, the chapter owner for the polar set;
- `pointwiseSupremumOn` from `Theorem_3_1_8` and `activePointwiseSupremumOnIndices` from
  `Lemma_3_1_14`, the chapter owners for active parameter sets of pointwise suprema;
- `minkowskiFunctional` and `minkowskiFunctional_eq_gauge` from `Remark_3_1_2_1`, the chapter
  owner for the source-facing `WithTop ℝ`-valued Minkowski functional and its bridge to mathlib
  `gauge`.

Best owner abstraction:
- source-facing owner reused from the chapter Minkowski/gauge file: `minkowskiFunctional`;
- core/canonical owners: `dom`, `subdifferential`, `polarSet`, `pointwiseSupremumOn`,
  `activePointwiseSupremumOnIndices`, and `gauge`.

Primitive data:
- a set `Q : Set E`;
- for the active-pointwise-supremum owner, a point `x : E`.

Derived API:
- the active polar set
  `activePointwiseSupremumOnIndices Qᵒ (fun x g ↦ ((inner ℝ g x : ℝ) : WithTop ℝ)) x`;
- the three proposition statements on `∂ ψ[Q](x)` and `Qᵒ`.

Source/core/bridge triage:
- source-facing: the Proposition 3.18 statements phrased using the chapter owner
  `minkowskiFunctional`;
- core/canonical: `dom`, `subdifferential`, `polarSet`, `pointwiseSupremumOn`,
  `activePointwiseSupremumOnIndices`, and `gauge`;
- bridge/view: the specialization of `activePointwiseSupremumOnIndices` to the polar-pairing
  slices `fun x g ↦ ((inner ℝ g x : ℝ) : WithTop ℝ)`, together with the upstream bridge
  `minkowskiFunctional_eq_gauge`.

This refinement removes the proposition-local argmax-set wrapper. The file now routes the active
polar-vector statements through the chapter owner `activePointwiseSupremumOnIndices` instead of
keeping a parallel local set definition.
-/

section Subdifferential

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (Q : Set E)

local notation "polarPairingFamily" =>
  (fun y : E ↦ fun g ↦ ((inner ℝ g y : ℝ) : WithTop ℝ))

/-- Helper for Proposition 3.18: if the extended gauge is finite, then the source-facing
Minkowski functional is also finite. -/
-- Proof sketch: unfold the source wrapper to the explicit `if` on the extended gauge and
-- simplify using the hypothesis that the gauge is not `⊤`.
lemma minkowskiFunctional_lt_top_of_egauge_ne_top
    {x : E} (hx : egauge NNReal Q x ≠ ⊤) :
    ψ[Q] x < ⊤ := by
  change
    (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) < ⊤
  simp [hx]

/-- Helper for Proposition 3.18: on finite extended-gauge values, the source-facing Minkowski
wrapper is exactly the coerced real part of the extended gauge. -/
-- Proof sketch: unfold the wrapper and simplify the defining `if` using the non-`⊤` hypothesis.
lemma minkowskiFunctional_eq_coe_toReal_of_egauge_ne_top
    {x : E} (hx : egauge NNReal Q x ≠ ⊤) :
    ψ[Q] x = (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ) := by
  change
    (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) =
      (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)
  simp [hx]

/-- Helper for Proposition 3.18: every point of `Q` has Minkowski functional at most `1`. -/
-- Proof sketch: membership in `Q` gives an immediate `egauge ≤ 1` witness, hence `ψ[Q] z` is
-- finite and agrees with the real-valued gauge. The standard gauge bound on points of `Q` then
-- gives the stated `WithTop` inequality.
lemma minkowskiFunctional_le_one_of_mem
    {z : E} (hz : z ∈ Q) :
    ψ[Q] z ≤ (1 : WithTop ℝ) := by
  -- First show that `z` is a finite point of the source-facing Minkowski functional.
  have hz_mem_one_smul : z ∈ (1 : NNReal) • Q := by
    simpa using hz
  have hz_dom : z ∈ dom (ψ[Q]) := by
    rw [mem_withTopEffectiveDomain_iff]
    have hEgauge : egauge NNReal Q z ≤ (1 : ENNReal) :=
      egauge_le_of_mem_smul (𝕜 := NNReal) (x := z) (s := Q) (c := (1 : NNReal))
        hz_mem_one_smul
    have hNotTop : egauge NNReal Q z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hEgauge
    exact minkowskiFunctional_lt_top_of_egauge_ne_top (Q := Q) hNotTop
  -- On finite points the chapter wrapper agrees with the canonical real-valued gauge.
  rw [minkowskiFunctional_eq_gauge hz_dom]
  exact_mod_cast gauge_le_one_of_mem hz

/-- Helper for Proposition 3.18: every polar vector is bounded above by the Minkowski functional
on the effective domain. -/
-- Proof sketch: after rewriting `ψ[Q] y` as the real-valued gauge, choose a nonzero scaling
-- witness `y ∈ c • Q` coming from finiteness of `ψ[Q] y`. The polar inequalities on `Q` then
-- show `⟪g, y⟫ ≤ c` for every admissible scale `c`, so `⟪g, y⟫` is bounded by the infimum that
-- defines the gauge.
lemma polarPairing_le_minkowskiFunctional_of_mem_polarSet
    {g y : E} (hg : g ∈ Qᵒ) (hy : y ∈ dom (ψ[Q])) :
    polarPairingFamily y g ≤ ψ[Q] y := by
  -- Rewrite the source-facing value through the canonical real-valued gauge.
  rw [minkowskiFunctional_eq_gauge hy]
  -- Rewrite the polar condition as the pointwise pairing bound on `Q`.
  rw [mem_polarSet_iff] at hg
  have hreal : inner ℝ g y ≤ gauge Q y := by
    -- Approximate the infimum defining the gauge by an actual scaling witness.
    let e : ENNReal := egauge NNReal Q y
    have he_ne_top : e ≠ ⊤ := by
      intro he_top
      have hpsi_lt_top : ψ[Q] y < ⊤ := by
        simpa [mem_withTopEffectiveDomain_iff] using hy
      have hpsi_top : ψ[Q] y = ⊤ := by
        change
          (if egauge NNReal Q y = ⊤ then ⊤ else (((egauge NNReal Q y).toReal : ℝ) : WithTop ℝ)) =
            ⊤
        simp [e, he_top]
      simpa [hpsi_top] using hpsi_lt_top
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    let r : NNReal := ⟨e.toReal + ε, add_nonneg ENNReal.toReal_nonneg hε.le⟩
    have htoReal_lt : e.toReal < (r : ℝ) := by
      change e.toReal < e.toReal + ε
      linarith
    have hr_ne_top : (r : ENNReal) ≠ ⊤ := by
      simp
    have he_lt : e < (r : ENNReal) := by
      exact (ENNReal.toReal_lt_toReal he_ne_top hr_ne_top).1 (by simpa [r] using htoReal_lt)
    rcases (egauge_lt_iff.1 he_lt) with ⟨c, hyc, hc_lt⟩
    rcases hyc with ⟨z, hz, hyz⟩
    have hz_pair : inner ℝ g z ≤ 1 := hg z hz
    have hinner_le_c : inner ℝ g ((c : NNReal) • z) ≤ c := by
      calc
        inner ℝ g ((c : NNReal) • z) = (c : ℝ) * inner ℝ g z := by
          simpa [NNReal.smul_def, mul_comm] using (real_inner_smul_right g z (c : ℝ))
        _ ≤ (c : ℝ) * 1 := by gcongr
        _ = c := by simp
    have he_toReal_eq_gauge : e.toReal = gauge Q y := by
      have hy_eq_toReal :
          ψ[Q] y = ((e.toReal : ℝ) : WithTop ℝ) := by
        simpa [e] using minkowskiFunctional_eq_coe_toReal_of_egauge_ne_top (Q := Q) he_ne_top
      have hy_eq_gauge :
          ψ[Q] y = ((gauge Q y : ℝ) : WithTop ℝ) := by
        rw [minkowskiFunctional_eq_gauge hy]
      have hcoe : ((e.toReal : ℝ) : WithTop ℝ) = ((gauge Q y : ℝ) : WithTop ℝ) := by
        exact hy_eq_toReal.symm.trans hy_eq_gauge
      exact WithTop.coe_injective hcoe
    have hy_lt : inner ℝ g y < e.toReal + ε := by
      calc
        inner ℝ g y = inner ℝ g ((c : NNReal) • z) := by
          simpa [hyz]
        _ < e.toReal + ε := hinner_le_c.trans_lt (by simpa [r] using hc_lt)
    simpa [he_toReal_eq_gauge] using hy_lt
  change (((inner ℝ g y : ℝ) : WithTop ℝ)) ≤ ((gauge Q y : ℝ) : WithTop ℝ)
  exact_mod_cast hreal

/-- Helper for Proposition 3.18: at every finite point, the subdifferential of the Minkowski
functional is the set of polar vectors that touch the function value. -/
-- Proof sketch: for `g ∈ ∂ ψ[Q](x)`, first test the subgradient inequality at `0` to obtain
-- `ψ[Q] x ≤ ⟪g, x⟫`, then test it on points of `Q` to prove `g ∈ Qᵒ`. The reverse direction uses
-- the polar upper bound from `polarPairing_le_minkowskiFunctional_of_mem_polarSet` and rewrites
-- the touching equality into the affine support inequality at `x`.
lemma subdifferential_minkowskiFunctional_eq_polar_touching
    {x : E} (hx : x ∈ dom (ψ[Q])) :
    ∂ ψ[Q](x) = Qᵒ ∩ {g | polarPairingFamily x g = ψ[Q] x} := by
  ext g
  constructor
  · intro hg
    have hsub : IsSubgradientAt (ψ[Q]) x g := mem_subdifferential_iff.mp hg
    -- Extract one scaling witness from finiteness of `ψ[Q] x`; this gives the nonemptiness of `Q`.
    have hx_witness : ∃ c : NNReal, x ∈ c • Q := by
      by_contra hfalse
      have he_top : egauge NNReal Q x = ⊤ := by
        rw [egauge_eq_top]
        intro c
        exact fun hxc ↦ hfalse ⟨c, hxc⟩
      have hpsi_lt_top : ψ[Q] x < ⊤ := by
        simpa [mem_withTopEffectiveDomain_iff] using hx
      have hxtop : ψ[Q] x = ⊤ := by
        change
          (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) =
            ⊤
        simp [he_top]
      simpa [hxtop] using hpsi_lt_top
    have hQ_nonempty : Q.Nonempty := by
      rcases hx_witness with ⟨c, z, hz, _⟩
      exact ⟨z, hz⟩
    -- The origin is finite because a nonempty set always contains `0` in its zero scaling.
    have hzero_dom : (0 : E) ∈ dom (ψ[Q]) := by
      rw [mem_withTopEffectiveDomain_iff]
      rcases hQ_nonempty with ⟨z, hz⟩
      have hzero_mem : (0 : E) ∈ (0 : NNReal) • Q := by
        refine ⟨z, hz, ?_⟩
        simp
      have hEgauge : egauge NNReal Q (0 : E) ≤ (0 : ENNReal) :=
        egauge_le_of_mem_smul (𝕜 := NNReal) (x := (0 : E)) (s := Q) (c := (0 : NNReal))
          hzero_mem
      have hNotTop : egauge NNReal Q (0 : E) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) hEgauge
      exact minkowskiFunctional_lt_top_of_egauge_ne_top (Q := Q) hNotTop
    have hx_scaled_dom : ∀ {t : ℝ}, 0 ≤ t → t • x ∈ dom (ψ[Q]) := by
      intro t ht
      rw [mem_withTopEffectiveDomain_iff]
      rcases hx_witness with ⟨c, z, hz, hxc⟩
      let tc : NNReal := ⟨t, ht⟩ * c
      have hscaled_mem : t • ((c : NNReal) • z) ∈ tc • Q := by
        refine ⟨z, hz, ?_⟩
        change (((tc : NNReal) : ℝ) • z) = t • ((c : NNReal) • z)
        rw [NNReal.smul_def, smul_smul]
        have htc : ((tc : NNReal) : ℝ) = t * (c : ℝ) := by
          rw [show ((tc : NNReal) : ℝ) = ((⟨t, ht⟩ : NNReal) : ℝ) * (c : ℝ) by rfl]
        rw [htc]
      have hEgauge : egauge NNReal Q (t • ((c : NNReal) • z)) ≤ (tc : ENNReal) :=
        egauge_le_of_mem_smul (𝕜 := NNReal) (x := t • ((c : NNReal) • z)) (s := Q) (c := tc)
          hscaled_mem
      have hx_eq : x = (c : ℝ) • z := by
        simpa [NNReal.smul_def] using hxc.symm
      have hEgauge_tx : egauge NNReal Q (t • x) ≤ (tc : ENNReal) := by
        calc
          egauge NNReal Q (t • x) = egauge NNReal Q (t • ((c : ℝ) • z)) := by rw [hx_eq]
          _ = egauge NNReal Q (t • ((c : NNReal) • z)) := by simp [NNReal.smul_def]
          _ ≤ (tc : ENNReal) := hEgauge
      have hNotTop : egauge NNReal Q (t • x) ≠ ⊤ := by
        exact ne_top_of_le_ne_top (by simp) hEgauge_tx
      exact minkowskiFunctional_lt_top_of_egauge_ne_top (Q := Q) hNotTop
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hzero_dom]
      simp [gauge_zero]
    -- Test the subgradient inequality at `0` and at `2x` to pin down the touching equality.
    have hineq_zero := hsub.2 hzero_dom
    have hpair_ge_real : gauge Q x ≤ inner ℝ g x := by
      have hineq_zero' : (((0 : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g (-x) : ℝ) : WithTop ℝ)) := by
        simpa [hpsi_zero, minkowskiFunctional_eq_gauge hx] using hineq_zero
      have hineq_zero_real : 0 ≥ gauge Q x + inner ℝ g (-x) := by
        exact_mod_cast hineq_zero'
      have haux : gauge Q x - inner ℝ g x ≤ 0 := by
        simpa using hineq_zero_real
      linarith
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have htwo_dom : (2 : ℝ) • x ∈ dom (ψ[Q]) := hx_scaled_dom htwo_nonneg
    have hineq_two := hsub.2 htwo_dom
    have htwo_sub : (2 : ℝ) • x - x = x := by
      simp [two_smul]
    rw [htwo_sub] at hineq_two
    have hpair_le_real : inner ℝ g x ≤ gauge Q x := by
      have hineq_two' :
          (((2 * gauge Q x : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g x : ℝ) : WithTop ℝ)) := by
        simpa [minkowskiFunctional_eq_gauge hx, minkowskiFunctional_eq_gauge htwo_dom,
          gauge_smul_of_nonneg htwo_nonneg, smul_eq_mul] using hineq_two
      have hineq_two_real : 2 * gauge Q x ≥ gauge Q x + inner ℝ g x := by
        exact_mod_cast hineq_two'
      linarith
    have hpair_eq_real : inner ℝ g x = gauge Q x := by
      linarith
    -- Once the touching value is known, the `y ∈ Q` test yields the polar inequalities.
    have hg_polar : g ∈ Qᵒ := by
      rw [mem_polarSet_iff]
      intro z hz
      have hz_dom : z ∈ dom (ψ[Q]) := by
        rw [mem_withTopEffectiveDomain_iff]
        have hz_lt_top : ψ[Q] z < ⊤ := by
          exact lt_of_le_of_lt (minkowskiFunctional_le_one_of_mem (Q := Q) hz) (by norm_num)
        exact hz_lt_top
      have hineq_z := hsub.2 hz_dom
      have hineq_z' :
          (((gauge Q z : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g (z - x) : ℝ) : WithTop ℝ)) := by
        simpa [minkowskiFunctional_eq_gauge hz_dom, minkowskiFunctional_eq_gauge hx] using hineq_z
      have hineq_z_real : gauge Q z ≥ gauge Q x + inner ℝ g (z - x) := by
        exact_mod_cast hineq_z'
      have hz_le_one : gauge Q z ≤ 1 := by
        exact gauge_le_one_of_mem hz
      have hz_pair : inner ℝ g z ≤ gauge Q z := by
        calc
          inner ℝ g z = inner ℝ g x + inner ℝ g (z - x) := by
            simp [inner_sub_right]
          _ = gauge Q x + inner ℝ g (z - x) := by
            rw [hpair_eq_real]
          _ ≤ gauge Q z := hineq_z_real
      exact hz_pair.trans hz_le_one
    have hpair_eq : polarPairingFamily x g = ψ[Q] x := by
      rw [minkowskiFunctional_eq_gauge hx]
      change (((inner ℝ g x : ℝ) : WithTop ℝ)) = ((gauge Q x : ℝ) : WithTop ℝ)
      exact_mod_cast hpair_eq_real
    exact ⟨hg_polar, hpair_eq⟩
  · rintro ⟨hg_polar, hpair_eq⟩
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨hx, ?_⟩
    intro y hy
    -- Replace the target affine support inequality by the polar upper bound at `y`.
    have hineq :=
      polarPairing_le_minkowskiFunctional_of_mem_polarSet (Q := Q) hg_polar hy
    have hsum_real : inner ℝ g x + inner ℝ g (y - x) = inner ℝ g y := by
      simp [inner_sub_right]
    have hsum :
        polarPairingFamily x g + (inner ℝ g (y - x) : WithTop ℝ) = polarPairingFamily y g := by
      change
        (((inner ℝ g x : ℝ) : WithTop ℝ) + ((inner ℝ g (y - x) : ℝ) : WithTop ℝ)) =
          (((inner ℝ g y : ℝ) : WithTop ℝ))
      exact_mod_cast hsum_real
    calc
      ψ[Q] y ≥ polarPairingFamily y g := hineq
      _ = polarPairingFamily x g + (inner ℝ g (y - x) : WithTop ℝ) := by
        rw [hsum.symm]
      _ = ψ[Q] x + (inner ℝ g (y - x) : WithTop ℝ) := by
        rw [hpair_eq]

/-- Helper for Proposition 3.18: at finite points, the supremum of the polar pairings equals the
Minkowski functional. -/
-- Route correction: the earlier easy inequalities and touching characterization are now proved.
-- The remaining gap is the source-faithful support-value identity, which needs the structural
-- lower-bound/separation argument converting the polar support supremum back to `ψ[Q] x`.
-- TODO: prove the lower-bound/support step, or replace it with the attained-active specialization
-- if the generalized ambient assumptions are too weak without an earlier Hilbert-space owner.
lemma minkowskiFunctional_eq_pointwiseSupremumOn_polarSet
    (hQ_convex : Convex ℝ Q) {x : E} (hx : x ∈ dom (ψ[Q])) :
    pointwiseSupremumOn Qᵒ polarPairingFamily x = ψ[Q] x := sorry

/-- Proposition 3.18 (1): if the Minkowski functional of `Q` is finite at `0`, then its
subdifferential at `0` is the polar set `Qᵒ`. -/
-- Proof sketch: unfold the owner subgradient inequality at `x = 0`. The finiteness hypothesis
-- gives `ψ[Q] 0 < ⊤`, so the base point is admissible for `∂ ψ[Q](0)`. A vector belongs to
-- `∂ ψ[Q](0)` exactly when its pairing with every point of `Q` is bounded by `1`, which is the
-- defining membership condition for `Qᵒ`.
theorem subdifferential_minkowskiFunctional_zero_eq_polarSet
    (hQ_dom_zero : (0 : E) ∈ dom (ψ[Q])) :
    ∂ ψ[Q](0) = Qᵒ := by
  ext g
  constructor
  · intro hg
    have hsub : IsSubgradientAt (ψ[Q]) 0 g := mem_subdifferential_iff.mp hg
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hQ_dom_zero]
      simp [gauge_zero]
    rw [mem_polarSet_iff]
    intro z hz
    have hz_dom : z ∈ dom (ψ[Q]) := by
      rw [mem_withTopEffectiveDomain_iff]
      exact lt_of_le_of_lt (minkowskiFunctional_le_one_of_mem (Q := Q) hz) (by norm_num)
    have hineq := hsub.2 hz_dom
    rw [hpsi_zero, zero_add, sub_zero] at hineq
    have hpsi_le : ψ[Q] z ≤ (1 : WithTop ℝ) :=
      minkowskiFunctional_le_one_of_mem (Q := Q) hz
    exact_mod_cast (hineq.trans hpsi_le)
  · intro hg
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨hQ_dom_zero, ?_⟩
    intro y hy
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hQ_dom_zero]
      simp [gauge_zero]
    have hineq :=
      polarPairing_le_minkowskiFunctional_of_mem_polarSet (Q := Q) hg hy
    simpa [hpsi_zero, sub_zero] using hineq

section PolarSupport

variable (hQ_convex : Convex ℝ Q)
variable {x : E}

/-- Proposition 3.18 (2): for a convex set `Q` in a real inner-product space, the subdifferential
of the Minkowski functional at a finite point `x` is the active parameter set for the
polar-pairing pointwise supremum over `Qᵒ`. -/
-- Proof sketch: write the gauge as the supremum of the linear functionals `g ↦ ⟪g, x⟫` over
-- `Qᵒ`. On `dom (ψ[Q])`, the general subdifferential rule for such suprema identifies `∂ ψ[Q](x)`
-- with the active maximizers.
theorem subdifferential_minkowskiFunctional_eq_activePolarIndices
    (hx : x ∈ dom (ψ[Q])) :
    ∂ ψ[Q](x) =
      activePointwiseSupremumOnIndices Qᵒ polarPairingFamily x := by
  -- TODO: finish Proposition 3.18 by combining the touching characterization above with the
  -- support-value identity `minkowskiFunctional_eq_pointwiseSupremumOn_polarSet`. The current
  -- theorem header does not expose the convexity hypothesis needed to invoke that bridge.
  sorry

/-- Proposition 3.18 (3): for a convex set `Q` in a real inner-product space, the active polar
indices at a finite point `x` are exactly the polar vectors satisfying
`⟪g, x⟫ = ψ_Q(x)`. -/
-- Proof sketch: combine the max formula for the gauge with the defining equality in
-- `activePointwiseSupremumOnIndices`. On `dom (ψ[Q])`, activity means the pairing reaches the
-- value `ψ[Q] x`.
theorem activePolarIndices_eq_activePolarVectors_of_minkowskiFunctional
    (hx : x ∈ dom (ψ[Q])) :
    activePointwiseSupremumOnIndices Qᵒ polarPairingFamily x =
      Qᵒ ∩ {g | polarPairingFamily x g = ψ[Q] x} := by
  -- TODO: after the support-value identity is available in a theorem-local way, rewrite
  -- `activePointwiseSupremumOnIndices` by `mem_activePointwiseSupremumOnIndices_iff` and compare
  -- the attained supremum value with `ψ[Q] x`.
  sorry

end PolarSupport

end Subdifferential

end
