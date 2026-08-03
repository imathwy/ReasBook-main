import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Example_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section Conjugation

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 10: view `H × ℝ` with the canonical `ℓ²` product metric used by
epigraph and graph slice computations. -/
local instance prop13_10_prod_pseudoMetricSpace_l2 : PseudoMetricSpace (H × ℝ) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) H ℝ

/-- Helper for Proposition 13 10: equip `H × ℝ` with the canonical `ℓ²` product norm. -/
local instance prop13_10_prod_normedAddCommGroup_l2 : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Proposition 13 10: the `ℓ²` product norm on `H × ℝ` is compatible with scalar
multiplication. -/
local instance prop13_10_prod_normedSpace_l2 : NormedSpace ℝ (H × ℝ) := by
  letI : NormedAddCommGroup (H × ℝ) := prop13_10_prod_normedAddCommGroup_l2 (H := H)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) H ℝ

/-- Helper for Proposition 13 10: use the canonical Hilbert product structure on `H × ℝ`. -/
local instance prop13_10_prod_innerProductSpace_l2 : InnerProductSpace ℝ (H × ℝ) where
  inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
  norm_sq_eq_re_inner x := by
    rw [show ‖x‖ = ‖WithLp.toLp 2 x‖ by rfl, WithLp.prod_norm_sq_eq_of_L2]
    simp [sq]
  conj_inner_symm x y := by
    simp [real_inner_comm, mul_comm]
  add_left x y z := by
    simp [inner_add_left, add_mul, add_assoc, add_left_comm, add_comm]
  smul_left x y r := by
    simp [inner_smul_left, mul_add, mul_left_comm, mul_comm]

/-- Helper for Proposition 13 10: outside the domain, the affine defect in the conjugate formula
is `-∞`. -/
private theorem affine_defect_eq_bot_of_not_mem_dom
    (f : H → EReal) (u x : H) (hx : x ∉ dom f) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x = ⊥ := by
  -- Outside `dom f`, the value is `+∞`, so subtracting it forces the defect to `-∞`.
  rw [not_mem_dom_iff] at hx
  simp [hx]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 13 10: any real-height epigraph point projects to the effective domain
of the base function. -/
private theorem mem_dom_of_mem_epigraph
    {f : H → EReal} {x : H} {ξ : ℝ} (hxξ : (x, ξ) ∈ epigraph f) :
    x ∈ dom f := by
  -- The real ordinate bounds `f x` by a finite-above value.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt ((mem_epigraph_iff f x ξ).mp hxξ) (EReal.coe_lt_top ξ)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 13 10: every domain point has its canonical real-height representative
in the epigraph. -/
private theorem mem_epigraph_toReal_of_mem_dom
    {f : H → EReal} {x : H} (hx : x ∈ dom f) :
    (x, (f x).toReal) ∈ epigraph f := by
  -- The `toReal` height is finite and lies above `f x`.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt ((mem_dom_iff f x).mp hx))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 13 10: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Proposition 13 10: on the product slice `(u,-1)`, the product inner product is the
horizontal pairing minus the second coordinate. -/
private theorem prod_inner_slice_eq_sub (u : H) (p : H × ℝ) :
    ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 := by
  change ⟪p.1, u⟫_ℝ + p.2 * (-1 : ℝ) = ⟪p.1, u⟫_ℝ - p.2
  ring

/-- Helper for Proposition 13 10: the support function of the graph slice `(u,-1)` is exactly the
supremum of the affine defects over the domain. -/
private theorem graph_slice_image_eq_affine_defect_image_dom
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) (u : H) :
    (fun p : H × ℝ ↦ ((⟪p, (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal)) '' graph f =
      (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) '' dom f := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp_graph : f p.1 = (p.2 : EReal) := (mem_graph_iff f p.1 p.2).mp hp
    have hp_dom : p.1 ∈ dom f := by
      rw [mem_dom_iff]
      simp [hp_graph]
    refine ⟨p.1, hp_dom, ?_⟩
    have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 :=
      prod_inner_slice_eq_sub u p
    calc
      ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1
          = ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - (p.2 : EReal) := by rw [hp_graph]
      _ = ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
      _ = ((⟪p, (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by rw [hpair]
  · rintro ⟨x, hx, rfl⟩
    have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
    have hx_graph : (x, (f x).toReal) ∈ graph f := by
      rw [mem_graph_iff]
      simpa using (EReal.coe_toReal hx_top (hbot x)).symm
    refine ⟨(x, (f x).toReal), hx_graph, ?_⟩
    have hpair :
        ⟪(x, (f x).toReal), (u, (-1 : ℝ))⟫_ℝ =
          ⟪x, u⟫_ℝ - (f x).toReal :=
      prod_inner_slice_eq_sub u (x, (f x).toReal)
    symm
    calc
      ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x
          = ((⟪x, u⟫_ℝ : ℝ) : EReal) - (((f x).toReal : ℝ) : EReal) := by
            rw [EReal.coe_toReal hx_top (hbot x)]
      _ = ((⟪x, u⟫_ℝ - (f x).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
      _ = ((⟪(x, (f x).toReal), (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by rw [hpair]

/-- Helper for Proposition 13 10: the conjugate is the support function of the epigraph along the
slice `u ↦ (u,-1)`. -/
private theorem conjugate_eq_support_function_epigraph_slice
    {f : H → EReal} :
    f∗ = fun u ↦ σ[epigraph f] (u, -1) := by
  funext u
  -- Rewrite the epigraph support function as the conjugate of its indicator and compare the two
  -- indexed suprema term by term.
  rw [← conjugate_indicator_eq_supportFunction (C := epigraph f)]
  let B : H × ℝ → EReal := fun p ↦
    ((⟪p, (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) -
      (((ι[epigraph f] p : Set.Ioi (⊥ : EReal)) : EReal))
  change (⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) = ⨆ p : H × ℝ, B p
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases htop : f x = ⊤
    · simp [htop]
    · by_cases hbot : f x = ⊥
      · have hsup_top :
            (⨆ p : H × ℝ, B p) = ⊤ := by
          refine (EReal.eq_top_iff_forall_lt _).2 ?_
          intro M
          let ξ : ℝ := ⟪x, u⟫_ℝ - M - 1
          have hmem : (x, ξ) ∈ epigraph f := by
            rw [mem_epigraph_iff, hbot]
            exact bot_le
          have hvalue : B (x, ξ) = ((M + 1 : ℝ) : EReal) := by
            calc
              B (x, ξ) = ((⟪(x, ξ), (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by
                simp [B, indicator_apply, hmem]
              _ = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) := by
                change (((⟪x, u⟫_ℝ + ξ * (-1) : ℝ)) : EReal) = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal)
                congr 1
                ring
              _ = ((M + 1 : ℝ) : EReal) := by
                have hreal : ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - M - 1) = M + 1 := by
                  ring
                simpa [ξ] using congrArg (fun r : ℝ ↦ (r : EReal)) hreal
          have hlt : (M : EReal) < ((M + 1 : ℝ) : EReal) := by
            exact_mod_cast (show M < M + 1 by linarith)
          exact lt_of_lt_of_le hlt <| by
            rw [← hvalue]
            exact le_iSup B (x, ξ)
        rw [show ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x = ⊤ by simp [hbot]]
        rw [hsup_top]
      · let ξ : ℝ := (f x).toReal
        have hmem : (x, ξ) ∈ epigraph f := by
          rw [mem_epigraph_iff]
          exact EReal.le_coe_toReal htop
        have hξ : ((ξ : ℝ) : EReal) = f x := by
          dsimp [ξ]
          simpa using EReal.coe_toReal htop hbot
        have hpoint :
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x =
              B (x, ξ) := by
          calc
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x
                = ((⟪x, u⟫_ℝ : ℝ) : EReal) - ((ξ : ℝ) : EReal) := by
                    rw [hξ]
            _ = ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) := by
                    rw [← EReal.coe_sub]
            _ = B (x, ξ) := by
                calc
                  ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal)
                      = ((⟪(x, ξ), (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal) := by
                          change ((⟪x, u⟫_ℝ - ξ : ℝ) : EReal) =
                            (((⟪x, u⟫_ℝ + ξ * (-1) : ℝ)) : EReal)
                          congr 1
                          ring
                  _ = B (x, ξ) := by
                          simp [B, indicator_apply, hmem]
        rw [hpoint]
        exact le_iSup B (x, ξ)
  · refine iSup_le ?_
    intro p
    by_cases hp : p ∈ epigraph f
    · have hp_le : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_iff f p.1 p.2).1 hp
      have hp_term :
          B p ≤ ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 := by
        by_cases hbot : f p.1 = ⊥
        · rw [show ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 = ⊤ by simp [hbot]]
          exact le_top
        · have htop : f p.1 ≠ ⊤ := by
            exact ne_of_lt <| lt_of_le_of_lt hp_le (EReal.coe_lt_top p.2)
          have htoReal_le : (f p.1).toReal ≤ p.2 := by
            simpa using EReal.toReal_le_toReal hp_le hbot (EReal.coe_ne_top p.2)
          have hreal :
              (⟪p.1, u⟫_ℝ - p.2 : ℝ) ≤ ⟪p.1, u⟫_ℝ - (f p.1).toReal :=
            sub_le_sub_left htoReal_le _
          have hcast :
              ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal) ≤
                ((⟪p.1, u⟫_ℝ - (f p.1).toReal : ℝ) : EReal) := by
            exact_mod_cast hreal
          have htoReal : ((((f p.1).toReal : ℝ) : EReal)) = f p.1 := by
            simpa using EReal.coe_toReal htop hbot
          calc
            B p = ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal) := by
              have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 := by
                change ⟪p.1, u⟫_ℝ + p.2 * (-1 : ℝ) = ⟪p.1, u⟫_ℝ - p.2
                ring
              simp [B, indicator_apply, hp, hpair]
            _ ≤ ((⟪p.1, u⟫_ℝ - (f p.1).toReal : ℝ) : EReal) := hcast
            _ = ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - (((f p.1).toReal : ℝ) : EReal) := by
              rw [← EReal.coe_sub]
            _ = ((⟪p.1, u⟫_ℝ : ℝ) : EReal) - f p.1 := by
              rw [htoReal]
      exact le_trans hp_term <| le_iSup (fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) p.1
    · have hp_term : B p = ⊥ := by
        simp [B, indicator_apply, hp]
      rw [hp_term]
      exact bot_le

-- Proof sketch: evaluate the conjugate at `0`, so the inner-product term vanishes and the supremum
-- of `x ↦ -f x` becomes the negative of the infimum of `f`.
/-- Proposition 13 10 (1): clause (i). The conjugate at the origin is the negative infimum of the
values of `f`. -/
theorem conjugate_zero_eq_neg_iInf
    (f : H → EReal) :
    f∗ 0 = - (⨅ x : H, f x) := by
  -- At the origin the pairing vanishes, so conjugation becomes pointwise negation followed by a
  -- supremum.
  calc
    f∗ 0 = ⨆ x : H, -f x := by
      simp [conjugate_apply]
    _ = - (⨅ x : H, f x) := by
      have hneg : (-(⨅ x : H, f x) : EReal) = ⨆ x : H, -f x := by
        exact OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ f x)
      rw [hneg]

-- Proof sketch: if `conjugate f` attains `-∞`, then every affine defect `⟪x,u⟫ - f x` is `-∞`,
-- forcing `f x = +∞` for all `x`; conversely, if `f ≡ +∞`, then every conjugate value is `-∞`.
/-- Proposition 13.10 (2): clause (ii). The conjugate attains `-∞` exactly when `f` is
identically `+∞`. -/
theorem bot_mem_range_conjugate_iff_eq_top
    (f : H → EReal) :
    (⊥ : EReal) ∈ Set.range f∗ ↔ f = ⊤ := by
  constructor
  · rintro ⟨u, hu⟩
    funext x
    have hdef_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x ≤ f∗ u := by
      simpa [conjugate_apply] using
        (le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x)
    rw [hu] at hdef_le
    have hdef_eq : ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x = ⊥ := by
      exact le_bot_iff.mp hdef_le
    by_cases htop : f x = ⊤
    · simp [htop]
    · have hfalse : False := by
        by_cases hbot : f x = ⊥
        · simp [hbot] at hdef_eq
        · cases hx : f x with
          | top =>
              exact htop hx
          | bot =>
              exact hbot hx
          | coe r =>
              have hcoe : (((⟪x, u⟫_ℝ - r : ℝ) : EReal) = ⊥) := by
                simpa [hx] using hdef_eq
              exact EReal.coe_ne_bot _ hcoe
      exact False.elim hfalse
  · intro hf
    refine ⟨0, ?_⟩
    simp [hf, conjugate_apply]

-- Proof sketch: unfold the definition of the conjugate when `f ≡ +∞`; conversely, if
-- `conjugate f ≡ -∞`, then evaluating at `0` and using part (i) forces `inf f(H) = +∞`.
/-- Proposition 13.10 (3): clause (ii). The function `f` is identically `+∞` exactly when its
conjugate is identically `-∞`. -/
theorem conjugate_eq_bot_iff_eq_top
    (f : H → EReal) :
    f∗ = ⊥ ↔ f = ⊤ := by
  constructor
  · intro hbot
    have hrange : (⊥ : EReal) ∈ Set.range f∗ := by
      refine ⟨0, ?_⟩
      simpa using congrFun hbot (0 : H)
    exact (bot_mem_range_conjugate_iff_eq_top f).mp hrange
  · intro hf
    ext u
    simp [hf, conjugate_apply]

-- Proof sketch: properness of `conjugate f` excludes `conjugate f ≡ -∞`, so part (ii) gives that
-- `f` is not identically `+∞`; combine this with part (i) to rule out `f = -∞` anywhere and obtain
-- nonempty domain.
/-- Proposition 13.10 (4): clause (iii). Properness of the conjugate forces properness of the
original function. -/
theorem is_proper_of_conjugate_is_proper
    {f : H → EReal} (hproper : IsProper f∗) :
    IsProper f := by
  rcases hproper.2 with ⟨u₀, hu₀⟩
  have hu₀_top : f∗ u₀ ≠ ⊤ := ne_of_lt ((mem_dom_iff _ _).mp hu₀)
  have hbot_not_mem : (⊥ : EReal) ∉ Set.range f∗ :=
    (isProper_iff_bot_notMem_range (f := f∗)).mp hproper |>.1
  have hf_ne_top : f ≠ ⊤ := by
    intro hf_top
    exact hbot_not_mem ((bot_mem_range_conjugate_iff_eq_top f).2 hf_top)
  refine ⟨?_, ?_⟩
  · intro x hfx
    have htop_le : (⊤ : EReal) ≤ f∗ u₀ := by
      calc
        ⊤ = ((⟪x, u₀⟫_ℝ : ℝ) : EReal) - f x := by simp [hfx]
        _ ≤ f∗ u₀ := by
          simpa [conjugate_apply] using
            (le_iSup (fun y : H ↦ ((⟪y, u₀⟫_ℝ : ℝ) : EReal) - f y) x)
    exact hu₀_top (le_antisymm le_top htop_le)
  · by_contra hdom
    apply hf_ne_top
    funext x
    apply (not_mem_dom_iff f x).mp
    intro hx
    exact hdom ⟨x, hx⟩

-- Proof sketch: outside `dom f`, the value `f x` is `+∞`, so the affine defect
-- `⟪x,u⟫ - f x` equals `-∞` and does not change the supremum defining `conjugate f`.
/-- Proposition 13.10 (5): clause (iv). The conjugate may be computed by taking the supremum only
over the effective domain of `f`. -/
theorem conjugate_eq_sSup_image_dom
    (f : H → EReal) (u : H) :
    f∗ u =
      sSup ((fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) '' dom f) := by
  -- The only discarded indices are those where `f x = ⊤`, and there the affine defect is `-∞`.
  rw [conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases hx : x ∈ dom f
    · exact le_sSup (Set.mem_image_of_mem (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) hx)
    · rw [affine_defect_eq_bot_of_not_mem_dom f u x hx]
      exact bot_le
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x

/-- Helper for Proposition 13 10: if `f` never attains `-∞`, then the conjugate is the support
function of the graph along the slice `u ↦ (u,-1)`. -/
private theorem conjugate_eq_support_function_graph_slice
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    f∗ = fun u ↦ σ[graph f] (u, -1) := by
  funext u
  -- The graph slice records exactly the affine defects over `dom f` once `f` has no `-∞` values.
  rw [supportFunction_eq_sSup_image, graph_slice_image_eq_affine_defect_image_dom hbot,
    conjugate_eq_sSup_image_dom]

-- Proof sketch: rewrite epigraph membership as `f x ≤ ξ`; for fixed `x`, the quantity
-- `⟪x,u⟫ - ξ` is maximized by choosing `ξ = f x`, so the supremum over `epigraph f` agrees with
-- the supremum over `dom f`.
/-- Proposition 13.10 (6): clause (iv). The conjugate is also the supremum of the affine
functional `(x, ξ) ↦ ⟪x, u⟫ - ξ` over the epigraph of `f`. -/
theorem conjugate_eq_sSup_image_epigraph
    (f : H → EReal) (u : H) :
    f∗ u =
      sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f) := by
  -- The epigraph slice support function expands to the same supremum as the conjugate.
  have hsupp :
      σ[epigraph f] (u, -1) =
        sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f) := by
    calc
      σ[epigraph f] (u, -1)
          = sSup ((fun p : H × ℝ ↦ ((⟪p, (u, (-1 : ℝ))⟫_ℝ : ℝ) : EReal)) '' epigraph f) := by
              rw [supportFunction_eq_sSup_image]
      _ = sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f) := by
            congr 1
            ext z
            constructor
            · rintro ⟨p, hp, rfl⟩
              refine ⟨p, hp, ?_⟩
              have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 :=
                prod_inner_slice_eq_sub u p
              simp [hpair]
            · rintro ⟨p, hp, rfl⟩
              refine ⟨p, hp, ?_⟩
              have hpair : ⟪p, (u, (-1 : ℝ))⟫_ℝ = ⟪p.1, u⟫_ℝ - p.2 :=
                prod_inner_slice_eq_sub u p
              simp [hpair]
  calc
    f∗ u = σ[epigraph f] (u, -1) := by
      exact congrFun (conjugate_eq_support_function_epigraph_slice (f := f)) u
    _ = sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f) := hsupp

-- Proof sketch: expand the conjugate of the epigraph indicator on `H × ℝ`; evaluating it at
-- `(u, -1)` gives the same supremum over `epigraph f` as in part (iv).
/-- Proposition 13.10 (7): clause (v). The conjugate of `f` is the conjugate of the epigraph
indicator `ι[epigraph f]`, evaluated along the slice `u ↦ (u, -1)` in the Hilbert product
space `H × ℝ`. -/
theorem conjugate_eq_conjugate_indicator_epigraph
    (f : H → EReal) :
    f∗ =
      fun u ↦ ((ι[epigraph f]).asEReal)∗ (u, -1) := by
  funext u
  -- First identify `f∗` with the epigraph support function, then rewrite that support function as
  -- the conjugate of the indicator.
  calc
    f∗ u = σ[epigraph f] (u, -1) := by
      exact congrFun (conjugate_eq_support_function_epigraph_slice (f := f)) u
    _ = ((ι[epigraph f]).asEReal)∗ (u, -1) := by
      rw [← conjugate_indicator_eq_supportFunction (C := epigraph f)]

-- Proof sketch: identify the conjugate of the epigraph indicator with the support function of the
-- epigraph, then specialize to the slice `(u, -1)`.
/-- Proposition 13.10 (8): clause (v). The conjugate of `f` is the support function of the
epigraph, evaluated at `(u, -1)` in the Hilbert product space `H × ℝ`. -/
theorem conjugate_eq_support_function_epigraph
    (f : H → EReal) :
    f∗ =
      fun u ↦ σ[epigraph f] (u, -1) := by
  -- This is the file-local epigraph-slice identity proved above.
  exact conjugate_eq_support_function_epigraph_slice (f := f)

-- Proof sketch: if `f` never attains `-∞`, then points of `graph f` encode exactly the values of
-- `f` that can occur with real ordinate; expanding the graph-indicator conjugate at `(u, -1)`
-- reproduces the same supremum as the definition of `conjugate f`.
/-- Proposition 13.10 (9): clause (vi). If `f` never attains `-∞`, then the conjugate is the
conjugate of the graph indicator `ι[graph f]`, evaluated along `u ↦ (u, -1)` in the Hilbert
product space `H × ℝ`. -/
theorem conjugate_eq_conjugate_indicator_graph
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    f∗ =
      fun u ↦ ((ι[graph f]).asEReal)∗ (u, -1) := by
  funext u
  -- Under the no-`-∞` hypothesis, the graph slice records exactly the same affine defects as the
  -- conjugate, so the indicator-conjugate rewrite applies on that slice.
  calc
    f∗ u = σ[graph f] (u, -1) := by
      exact congrFun (conjugate_eq_support_function_graph_slice hbot) u
    _ = ((ι[graph f]).asEReal)∗ (u, -1) := by
      rw [← conjugate_indicator_eq_supportFunction (C := graph f)]

-- Proof sketch: if `f` never attains `-∞`, then the graph-indicator conjugate agrees with the
-- support function of `graph f`; then restrict this support function to the slice `(u, -1)`.
/-- Proposition 13.10 (10): clause (vi). If `f` never attains `-∞`, then the conjugate is the
support function of the graph, evaluated at `(u, -1)` in the Hilbert product space `H × ℝ`. -/
theorem conjugate_eq_support_function_graph
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    f∗ =
      fun u ↦ σ[graph f] (u, -1) := by
  -- This is the graph analogue of the epigraph slice identity.
  exact conjugate_eq_support_function_graph_slice hbot

end Conjugation

end

end ERealFunction
