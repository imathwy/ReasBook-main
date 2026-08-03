import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Proposition_15_18
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Theorem 19.1 is the textbook primal-dual optimality system for the composite
  objective `x ↦ f x + g (L x)`.
- `core/canonical`: the owner ingredients are the composite primal and dual objectives from
  Chapter 15 together with the Chapter 16 Fenchel--Young equality criterion.
- `bridge/view`: Proposition 13.49 packages the canonical Fenchel conjugate on `Γ₀`, and the
  remaining bridge rewrites the paired contact conditions into the conjugate-subdifferential form.
-/

-- Proof sketch: Chapter 16 turns each subgradient condition into Fenchel--Young equality.
-- The pair of equalities collapses exactly to the composite zero-gap identity because the adjoint
-- pairings cancel. Proposition 13.49 packages the conjugates back into `Γ₀` so the second clause
-- can be restated as the intersection/preimage condition in item (iii).
omit [CompleteSpace H] in
/-- Helper for Theorem 19 1: for an `]-∞,+∞]`-valued function with nonempty effective domain,
subgradient membership is equivalent to Fenchel--Young equality. -/
theorem mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  simpa using
    ERealFunction.mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u

/-- Helper for Theorem 19 1: a subgradient relation for `f` is equivalent to the corresponding
conjugate subgradient relation for `f∗[hf]`. -/
theorem mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x u : H) :
    u ∈ (∂ f) x ↔ x ∈ (∂ (f∗[hf])) u := by
  constructor
  · intro hu
    simpa [gammaZeroConjugate] using
      (mem_subdifferential_properConjugateIoi_of_mem_subdifferential
        (f := f) hf.2.nonempty x u) hu
  · intro hu
    let hconj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
    have hdouble : gammaZeroConjugate (f∗[hf]) hconj = f := by
      ext y
      simpa [gammaZeroConjugate, properConjugateIoi_apply, Function.asEReal] using
        congrFun (biconjugate_eq_of_mem_gammaZero hf) y
    have hu' :
        u ∈ (∂ (gammaZeroConjugate (f∗[hf]) hconj)) x := by
      simpa [gammaZeroConjugate] using
        (mem_subdifferential_properConjugateIoi_of_mem_subdifferential
          (f := f∗[hf]) hconj.2.nonempty u x) hu
    simpa [hdouble] using hu'

/-- Helper for Theorem 19 1: for finite extended-real values, the contact identity `a = -b` is
equivalent to the zero-gap identity `a + b = 0`. -/
theorem ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
    {a b : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) :
    a = -b ↔ a + b = 0 := by
  constructor
  · intro hab
    have hab_real : a.toReal = -b.toReal := by
      apply_fun EReal.toReal at hab
      simpa [EReal.toReal_neg_eq] using hab
    have hsum_real : a.toReal + b.toReal = 0 := by
      linarith
    calc
      a + b = (((a.toReal : ℝ) : EReal)) + (((b.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
      _ = (((a.toReal + b.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_add]
      _ = 0 := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hsum_real
  · intro hsum
    have hsum_real : a.toReal + b.toReal = 0 := by
      apply EReal.coe_eq_coe_iff.mp
      calc
        (((a.toReal + b.toReal : ℝ) : EReal)) =
            (((a.toReal : ℝ) : EReal)) + (((b.toReal : ℝ) : EReal)) := by
              rw [EReal.coe_add]
        _ = a + b := by
          rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
        _ = 0 := hsum
    have hab_real : a.toReal = -b.toReal := by
      linarith
    calc
      a = (((a.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal ha_top ha_bot]
      _ = (((-b.toReal : ℝ) : EReal)) := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hab_real
      _ = -b := by
        rw [EReal.coe_neg, EReal.coe_toReal hb_top hb_bot]

/-- Companion bridge for Theorem 19.1: the contact condition
`-L^* v ∈ ∂ f(x)` and `v ∈ ∂ g(Lx)` is equivalent to the conjugate-subdifferential clause
`x ∈ ∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, with `f^*` and `g^*` represented by `f∗[hf]`
and `g∗[hg]`. -/
theorem subgradient_pair_iff_mem_conjugateSubdifferential_inter_preimage
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    (-L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x)) ↔
      x ∈ (∂ (f∗[hf])) (-L.adjoint v) ∩
        L ⁻¹' ((∂ (g∗[hg])) v) := by
  constructor
  · rintro ⟨hf_sub, hg_sub⟩
    refine ⟨?_, ?_⟩
    · exact
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate f hf x
          (-L.adjoint v)).mp hf_sub
    · change L x ∈ (∂ (g∗[hg])) v
      exact
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate g hg (L x) v).mp hg_sub
  · rintro ⟨hf_sub, hg_sub⟩
    refine ⟨?_, ?_⟩
    · exact
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate f hf x
          (-L.adjoint v)).mpr hf_sub
    · change L x ∈ (∂ (g∗[hg])) v at hg_sub
      exact
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate g hg (L x) v).mpr hg_sub

/-- Helper for Theorem 19 1: equality in the composite Fenchel--Young gap is equivalent to the
paired subgradient conditions for `f` and `g`. -/
theorem composite_fenchel_young_zero_iff_subgradient_pair
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    ((f x : EReal) + (g (L x) : EReal)) +
        (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 ↔
      -L.adjoint v ∈ (∂ f) x ∧
        v ∈ (∂ g) (L x) := by
  let u : H := -(L.adjoint v)
  constructor
  · intro hzero
    -- Convert the `Γ₀` hypotheses into the properness facts needed to control conjugate values.
    have hf_proper : IsProper f.asEReal := isProper_of_mem_gammaZero hf
    have hg_proper : IsProper g.asEReal := isProper_of_mem_gammaZero hg
    let A : EReal := (f x : EReal) + f.asEReal∗ (-(L.adjoint v))
    let B : EReal := (g (L x) : EReal) + g.asEReal∗ v
    have hABzero : A + B = 0 := by
      simpa [A, B, add_assoc, add_left_comm, add_comm] using hzero
    have hA_ge : ((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) ≤ A := by
      simpa [A, u] using fenchel_young_inequality hf_proper x u
    have hB_ge : ((⟪L x, v⟫_ℝ : ℝ) : EReal) ≤ B := by
      simpa [B] using fenchel_young_inequality hg_proper (L x) v
    have hA_ne_bot : A ≠ ⊥ := by
      simpa [A, EReal.add_ne_bot_iff] using
        show (f x : EReal) ≠ ⊥ ∧ f.asEReal∗ (-(L.adjoint v)) ≠ ⊥ from
          ⟨ne_of_gt (f x).2, conjugate_ne_bot_of_isProper hf_proper _⟩
    have hB_ne_bot : B ≠ ⊥ := by
      simpa [B, EReal.add_ne_bot_iff] using
        show (g (L x) : EReal) ≠ ⊥ ∧ g.asEReal∗ v ≠ ⊥ from
          ⟨ne_of_gt (g (L x)).2, conjugate_ne_bot_of_isProper hg_proper _⟩
    have hA_ne_top : A ≠ ⊤ := by
      intro hA_top
      have htop : A + B = ⊤ := by
        rw [hA_top]
        exact EReal.top_add_of_ne_bot hB_ne_bot
      exact EReal.zero_ne_top (hABzero.symm.trans htop)
    have hB_ne_top : B ≠ ⊤ := by
      intro hB_top
      have htop : A + B = ⊤ := by
        rw [hB_top]
        exact EReal.add_top_of_ne_bot hA_ne_bot
      exact EReal.zero_ne_top (hABzero.symm.trans htop)
    have hsum_real : A.toReal + B.toReal = 0 := by
      have hsum_ereal : (((A.toReal + B.toReal : ℝ) : EReal)) = 0 := by
        rw [EReal.coe_add, EReal.coe_toReal hA_ne_top hA_ne_bot,
          EReal.coe_toReal hB_ne_top hB_ne_bot, hABzero]
      exact EReal.coe_eq_coe_iff.mp hsum_ereal
    have hA_ge_real : ⟪x, -(L.adjoint v)⟫_ℝ ≤ A.toReal := by
      exact EReal.toReal_le_toReal hA_ge (EReal.coe_ne_bot _) hA_ne_top
    have hB_ge_real : ⟪L x, v⟫_ℝ ≤ B.toReal := by
      exact EReal.toReal_le_toReal hB_ge (EReal.coe_ne_bot _) hB_ne_top
    have hpair_real :
        ⟪x, -(L.adjoint v)⟫_ℝ + ⟪L x, v⟫_ℝ = 0 := by
      rw [inner_neg_right, ContinuousLinearMap.adjoint_inner_right]
      ring
    have hA_eq_real : A.toReal = ⟪x, -(L.adjoint v)⟫_ℝ := by
      linarith
    have hB_eq_real : B.toReal = ⟪L x, v⟫_ℝ := by
      linarith
    have hfy_f :
        (f x : EReal) + f.asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      calc
        (f x : EReal) + f.asEReal∗ u = A := by
          rfl
        _ = (((A.toReal : ℝ) : EReal)) := by
          rw [EReal.coe_toReal hA_ne_top hA_ne_bot]
        _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal)) hA_eq_real
    have hfy_g :
        (g (L x) : EReal) + g.asEReal∗ v =
          ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
      calc
        (g (L x) : EReal) + g.asEReal∗ v = B := by
          rfl
        _ = (((B.toReal : ℝ) : EReal)) := by
          rw [EReal.coe_toReal hB_ne_top hB_ne_bot]
        _ = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal)) hB_eq_real
    exact
      ⟨(mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
          f hf.2.nonempty x u).2 (by simpa [u] using hfy_f),
        (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
          g hg.2.nonempty (L x) v).2 hfy_g⟩
  · rintro ⟨hf_sub, hg_sub⟩
    have hfy_f :
        (f x : EReal) + f.asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        f hf.2.nonempty x u).1 (by simpa [u] using hf_sub)
    have hfy_g :
        (g (L x) : EReal) + g.asEReal∗ v =
          ((⟪L x, v⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        g hg.2.nonempty (L x) v).1 hg_sub
    let A : EReal := (f x : EReal) + f.asEReal∗ (-(L.adjoint v))
    let B : EReal := (g (L x) : EReal) + g.asEReal∗ v
    have hA :
        A = ((⟪x, -(L.adjoint v)⟫_ℝ : ℝ) : EReal) := by
      simpa [A, u] using hfy_f
    have hB :
        B = ((⟪L x, v⟫_ℝ : ℝ) : EReal) := by
      simpa [B] using hfy_g
    have hsum : A + B = 0 := by
      rw [hA, hB]
      exact adjoint_pairings_cancel L x v
    let a : EReal := (f x : EReal)
    let b : EReal := (g (L x) : EReal)
    let c : EReal := f.asEReal∗ (-(L.adjoint v))
    let d : EReal := g.asEReal∗ v
    have habcd : (a + b) + (c + d) = (a + c) + (b + d) := by
      calc
        (a + b) + (c + d) = a + (b + (c + d)) := by
          rw [add_assoc]
        _ = a + ((b + c) + d) := by
          exact congrArg (fun t : EReal ↦ a + t) (show b + (c + d) = (b + c) + d by
            rw [← add_assoc])
        _ = a + ((c + b) + d) := by
          rw [add_comm b c]
        _ = a + (c + (b + d)) := by
          rw [add_assoc]
        _ = (a + c) + (b + d) := by
          rw [← add_assoc]
    calc
      ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) =
          (a + c) + (b + d) := by
            change (a + b) + (c + d) = (a + c) + (b + d)
            exact habcd
      _ = A + B := by
            rfl
      _ = 0 := hsum

/-- Helper for Theorem 19 1: the composite primal-dual contact equality is equivalent to the
zero-gap identity obtained by expanding the primal and dual objective values. -/
theorem composite_contact_eq_iff_zero_gap
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    compositePrimalObjective f g L x = -compositeDualObjective f g L v ↔
      ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 := by
  have hf_proper : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hg_proper : IsProper g.asEReal := isProper_of_mem_gammaZero hg
  let lhs : EReal := (f x : EReal) + (g (L x) : EReal)
  let rhs : EReal := f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v
  have hlhs_ne_bot : lhs ≠ ⊥ := by
    rw [show lhs = (f x : EReal) + (g (L x) : EReal) by rfl, EReal.add_ne_bot_iff]
    exact ⟨ne_of_gt (f x).2, ne_of_gt (g (L x)).2⟩
  have hrhs_ne_bot : rhs ≠ ⊥ := by
    rw [show rhs = f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v by rfl, EReal.add_ne_bot_iff]
    exact ⟨conjugate_ne_bot_of_isProper hf_proper (-(L.adjoint v)),
      conjugate_ne_bot_of_isProper hg_proper v⟩
  constructor
  · intro hcontact
    -- Rewrite the contact equality into the expanded objective values, then apply the finite
    -- `EReal` bridge to turn equality with a negation into a zero-sum identity.
    have hcontact' : lhs = -rhs := by
      simpa [lhs, rhs, compositePrimalObjective_apply, compositeDualObjective_apply, add_assoc,
        add_left_comm, add_comm] using hcontact
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
  · intro hzero
    -- Run the same bridge in the reverse direction and package the result back into the
    -- composite primal-dual contact equality.
    have hzero' : lhs + rhs = 0 := by
      simpa [lhs, rhs] using hzero
    have hlhs_ne_top : lhs ≠ ⊤ := by
      intro hlhs_top
      have htop : lhs + rhs = ⊤ := by
        rw [hlhs_top]
        exact EReal.top_add_of_ne_bot hrhs_ne_bot
      exact EReal.zero_ne_top (hzero'.symm.trans htop)
    have hrhs_ne_top : rhs ≠ ⊤ := by
      intro hrhs_top
      have htop : lhs + rhs = ⊤ := by
        rw [hrhs_top]
        exact EReal.add_top_of_ne_bot hlhs_ne_bot
      exact EReal.zero_ne_top (hzero'.symm.trans htop)
    have hcontact' : lhs = -rhs :=
      (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
        hlhs_ne_top hlhs_ne_bot hrhs_ne_top hrhs_ne_bot).2 hzero'
    simpa [lhs, rhs, compositePrimalObjective_apply, compositeDualObjective_apply, add_assoc,
      add_left_comm, add_comm] using hcontact'

/-- Theorem 19 1: for `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, the following are equivalent
for `x ∈ ℋ` and `v ∈ 𝒦`: (i) `x` minimizes `z ↦ f z + g (L z)`, `v`
minimizes
`w ↦ f^*(-L^* w) + g^*(w)`, and the primal infimum equals the negative of the dual infimum;
(ii) `-L^* v ∈ ∂ f(x)` and `v ∈ ∂ g(Lx)`; (iii)
`x ∈ ∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, with `f^*` and `g^*` represented by `f∗[hf]`
and `g∗[hg]`. -/
theorem primal_dual_solution_tfae_for_composite_objective
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (compositePrimalObjective f g L) ∧
          v ∈ Argmin (compositeDualObjective f g L) ∧
          compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L,
        -L.adjoint v ∈ (∂ f) x ∧
          v ∈ (∂ g) (L x),
        x ∈ (∂ (f∗[hf])) (-L.adjoint v) ∩
          L ⁻¹' ((∂ (g∗[hg])) v)] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨hx_argmin, hv_argmin, hstrong⟩
      -- Rewrite the minimizer hypotheses into the attained primal and dual values at `x` and `v`.
      have hx_value :
          compositePrimalObjective f g L x = compositePrimalOptimalValue f g L := by
        simpa [compositePrimalOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hx_argmin)
      have hv_value :
          compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
        simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hv_argmin)
      have hvalue :
          compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
        calc
          compositePrimalObjective f g L x = compositePrimalOptimalValue f g L := hx_value
          _ = -compositeDualOptimalValue f g L := hstrong
          _ = -compositeDualObjective f g L v := by rw [hv_value]
      -- Route correction: move through the zero-gap Fenchel--Young identity before invoking the
      -- paired subgradient criterion, rather than chasing subgradients from argmins directly.
      have hzero :
          ((f x : EReal) + (g (L x) : EReal)) +
              (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 := by
        exact (composite_contact_eq_iff_zero_gap hf hg L x v).mp hvalue
      exact (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).mp hzero
    · intro hsubgrad
      -- First recover equality in the Fenchel--Young gap, then rebuild both argmin clauses from
      -- weak duality against arbitrary comparison points.
      have hzero :
          ((f x : EReal) + (g (L x) : EReal)) +
              (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 :=
        (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).mpr hsubgrad
      have hvalue :
          compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
        exact (composite_contact_eq_iff_zero_gap hf hg L x v).mpr hzero
      have hx_argmin : x ∈ Argmin (compositePrimalObjective f g L) := by
        rw [mem_argmin_iff_eq_sInf]
        apply le_antisymm
        · refine le_sInf ?_
          rintro y ⟨z, rfl⟩
          have hz :
              compositePrimalObjective f g L z ≥ -compositeDualObjective f g L v :=
            compositePrimalObjective_ge_neg_compositeDualObjective f g L z v
          rw [← hvalue] at hz
          simpa [ge_iff_le] using hz
        · exact sInf_le ⟨x, rfl⟩
      have hv_argmin : v ∈ Argmin (compositeDualObjective f g L) := by
        rw [mem_argmin_iff_eq_sInf]
        apply le_antisymm
        · refine le_sInf ?_
          rintro y ⟨w, rfl⟩
          have hw :
              compositePrimalObjective f g L x ≥ -compositeDualObjective f g L w :=
            compositePrimalObjective_ge_neg_compositeDualObjective f g L x w
          have hneg :
              -compositeDualObjective f g L w ≤ -compositeDualObjective f g L v := by
            rw [hvalue] at hw
            simpa [ge_iff_le] using hw
          exact EReal.neg_le_neg_iff.mp hneg
        · exact sInf_le ⟨v, rfl⟩
      have hx_value :
          compositePrimalObjective f g L x = compositePrimalOptimalValue f g L := by
        simpa [compositePrimalOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hx_argmin)
      have hv_value :
          compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
        simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hv_argmin)
      have hstrong :
          compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
        calc
          compositePrimalOptimalValue f g L = compositePrimalObjective f g L x := hx_value.symm
          _ = -compositeDualObjective f g L v := hvalue
          _ = -compositeDualOptimalValue f g L := by rw [hv_value]
      exact ⟨hx_argmin, hv_argmin, hstrong⟩
  tfae_have 2 ↔ 3 := by
    -- The final edge is exactly the packaged conjugate-subdifferential rewrite.
    exact subgradient_pair_iff_mem_conjugateSubdifferential_inter_preimage hf hg L x v
  tfae_finish

end PrimalSolutionsViaDualSolutions

end ERealFunction
