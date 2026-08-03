module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Separation.Lemmas

public section

open Set Filter Topology
open scoped ContinuousMap

universe u

namespace Set.IsDeformationRetract

/-- A singleton deformation retract forces the path component of its point in every
neighborhood to contain a neighborhood of that point. -/
theorem pathComponentIn_mem_nhds {X : Type u} [TopologicalSpace X]
    {x₀ : X} (h : IsDeformationRetract ({x₀} : Set X)) {U : Set X}
    (hU : U ∈ 𝓝 x₀) :
    pathComponentIn U x₀ ∈ 𝓝 x₀ := by
  -- Replace the given neighborhood by an open set on which the homotopy will be controlled.
  obtain ⟨O, hOU, hOopen, hxO⟩ := mem_nhds_iff.mp hU
  obtain ⟨r, ⟨H⟩⟩ := (isDeformationRetract_iff ({x₀} : Set X)).mp h
  have htrack : Set.univ ×ˢ ({x₀} : Set X) ⊆ H ⁻¹' O := by
    rintro ⟨t, x⟩ ⟨-, hx⟩
    change H (t, x) ∈ O
    have hxmem : x ∈ ({x₀} : Set X) := hx
    rw [H.eq_fst t hxmem, Set.mem_singleton_iff.mp hxmem]
    exact hxO
  obtain ⟨T, V, hTopen, hVopen, hT, hxV, hTV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton
      (hOopen.preimage H.continuous) htrack
  apply mem_of_superset (hVopen.mem_nhds (hxV (Set.mem_singleton x₀)))
  intro y hy
  -- Reversing the point-track joins the fixed point to `y` entirely inside `U`.
  have hend : r.toAmbient y = x₀ := Set.mem_singleton_iff.mp (r.apply y).2
  refine ⟨(H.toHomotopy.evalAt y).cast rfl hend.symm |>.symm, ?_⟩
  intro t
  apply hOU
  exact hTV ⟨hT (Set.mem_univ t), hy⟩

end Set.IsDeformationRetract

namespace TopologistsComb

/-- The set of positive reciprocal abscissae of the topologist's comb. -/
def abscissae : Set ℝ :=
  Set.range (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ))

/-- The union of the vertical teeth, limiting vertical segment, and horizontal base of the
topologist's comb. -/
def carrier : Set (ℝ × ℝ) :=
  (({0} ∪ abscissae) ×ˢ Icc 0 1) ∪ (Icc 0 1 ×ˢ {0})

/-- The topologist's comb as a topological subspace of `ℝ × ℝ`. -/
abbrev Space := carrier

/-- The distinguished upper endpoint `(0, 1)` of the limiting vertical segment. -/
def basepoint : Space :=
  ⟨(0, 1), by
    left
    exact ⟨Or.inl rfl, ⟨zero_le_one, le_rfl⟩⟩⟩

private def origin : Space :=
  ⟨(0, 0), by
    right
    exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩⟩

private def lower (p : Space) : Space :=
  ⟨(p.1.1, 0), by
    right
    rcases p.2 with hp | hp
    · rcases hp.1 with hx | hx
      · rw [hx]
        exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
      · obtain ⟨n, hn⟩ := hx
        rw [← hn]
        exact ⟨⟨by positivity, by
          rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)⟩, rfl⟩
    · exact ⟨hp.1, rfl⟩⟩

private theorem continuous_lower : Continuous lower := by
  apply Continuous.subtype_mk
  fun_prop

private def collapseVertical : ContinuousMap.Homotopy (ContinuousMap.id Space)
    ⟨lower, continuous_lower⟩ where
  toFun p := ⟨(p.2.1.1, (1 - p.1) * p.2.1.2), by
    rcases p.2.2 with hp | hp
    · left
      exact ⟨hp.1, by
        constructor <;> nlinarith [p.1.2.1, p.1.2.2, hp.2.1, hp.2.2]⟩
    · right
      rw [hp.2]
      exact ⟨hp.1, by simp⟩⟩
  map_zero_left p := by ext <;> simp
  map_one_left p := by ext <;> simp [lower]

private def contractBase : ContinuousMap.Homotopy ⟨lower, continuous_lower⟩
    (ContinuousMap.const Space origin) where
  toFun p := ⟨((1 - p.1) * p.2.1.1, 0), by
    right
    constructor
    · constructor
      · nlinarith [p.1.2.1, p.1.2.2, show 0 ≤ p.2.1.1 from by
          rcases p.2.2 with hp | hp
          · rcases hp.1 with hx | hx
            · rw [Set.mem_singleton_iff.mp hx]
            · obtain ⟨n, hn⟩ := hx
              rw [← hn]
              positivity
          · exact hp.1.1]
      · have hx : p.2.1.1 ≤ 1 := by
          rcases p.2.2 with hp | hp
          · rcases hp.1 with hx | hx
            · rw [Set.mem_singleton_iff.mp hx]
              exact zero_le_one
            · obtain ⟨n, hn⟩ := hx
              rw [← hn]
              apply (div_le_one (by positivity)).2
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          · exact hp.1.2
        nlinarith [p.1.2.1, p.1.2.2]
    · rfl⟩
  map_zero_left p := by ext <;> simp [lower]
  map_one_left p := by ext <;> simp [origin]

private def ascendLimit : ContinuousMap.Homotopy (ContinuousMap.const Space origin)
    (ContinuousMap.const Space basepoint) where
  toFun p := ⟨(0, p.1), by
    left
    exact ⟨Or.inl rfl, p.1.2⟩⟩
  map_zero_left p := by ext <;> simp [origin]
  map_one_left p := by ext <;> simp [basepoint]

/-- A contraction of the topologist's comb to its distinguished point. -/
noncomputable def contraction : ContinuousMap.Homotopy (ContinuousMap.id Space)
    (ContinuousMap.const Space basepoint) :=
  (collapseVertical.trans contractBase).trans ascendLimit

/-- The inclusion of the distinguished singleton into the topologist's comb is a homotopy
equivalence, providing the positive half of Exercise 58.8. -/
@[expose]
noncomputable def inclusionHomotopyEquiv : ({basepoint} : Set Space) ≃ₕ Space where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := ContinuousMap.const Space ⟨basepoint, Set.mem_singleton basepoint⟩
  left_inv := by
    rw [Subsingleton.elim
      ((ContinuousMap.const Space ⟨basepoint, Set.mem_singleton basepoint⟩).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(({basepoint} : Set Space), Space)))
      (ContinuousMap.id ({basepoint} : Set Space))]
  right_inv := by
    rw [show (⟨Subtype.val, continuous_subtype_val⟩ : C(({basepoint} : Set Space), Space)).comp
        (ContinuousMap.const Space ⟨basepoint, Set.mem_singleton basepoint⟩) =
        ContinuousMap.const Space basepoint by rfl]
    exact ⟨contraction.symm⟩

/-- The forward map of `inclusionHomotopyEquiv` is the singleton subtype inclusion. -/
theorem inclusionHomotopyEquiv_apply (p : ({basepoint} : Set Space)) :
    inclusionHomotopyEquiv p = p := by rfl

/-- Helper for Exercise 58.8: a path in the positive-height part of the comb has constant
horizontal coordinate. -/
private theorem horizontalCoordinate_eq_of_joinedIn_of_positive
    {F : Set Space} {p q : Space} (hpositive : ∀ z ∈ F, 0 < z.1.2)
    (hjoined : JoinedIn F p q) : p.1.1 = q.1.1 := by
  let γ := hjoined.somePath
  let f : unitInterval → ℝ := fun t ↦ (γ t).1.1
  have hfcontinuous : Continuous f := by
    dsimp [f, γ]
    fun_prop
  have hfrange : Set.range f ⊆ ({0} ∪ abscissae : Set ℝ) := by
    rintro x ⟨t, rfl⟩
    have hcarrier := (γ t).2
    rcases hcarrier with hvertical | hbase
    · exact hvertical.1
    · have hzero : (γ t).1.2 = 0 := Set.mem_singleton_iff.mp hbase.2
      have hpos := hpositive (γ t) (hjoined.somePath_mem t)
      linarith
  have hcountable : ({0} ∪ abscissae : Set ℝ).Countable :=
    (Set.countable_singleton 0).union (by
      rw [abscissae]
      exact Set.countable_range _)
  have hsubsingleton : (Set.range f).Subsingleton :=
    hcountable.isTotallyDisconnected (Set.range f) hfrange
      (isPreconnected_range hfcontinuous)
  have hends : f 0 = f 1 := hsubsingleton (Set.mem_range_self 0) (Set.mem_range_self 1)
  simpa [f, γ] using hends

/-- Helper for Exercise 58.8: every upper endpoint of a nonlimiting tooth lies in the comb. -/
private theorem toothTop_mem_carrier (n : ℕ) :
    (1 / ((n + 1 : ℕ) : ℝ), 1) ∈ carrier := by
  -- Use the vertical-tooth branch of the carrier description.
  left
  exact ⟨Or.inr ⟨n, rfl⟩, ⟨zero_le_one, le_rfl⟩⟩

/-- Helper for Exercise 58.8: the upper endpoints of the teeth converge to `basepoint`. -/
private theorem tendsto_toothTop_basepoint :
    Tendsto (fun n : ℕ ↦
      (⟨(1 / ((n + 1 : ℕ) : ℝ), 1), toothTop_mem_carrier n⟩ : Space))
      atTop (𝓝 basepoint) := by
  -- Convergence in the subtype is detected by the underlying coordinate pair.
  rw [tendsto_subtype_rng]
  have hfirst : Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hsecond : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact hfirst.prodMk_nhds hsecond

/-- Some neighborhood of the distinguished point has a path component there that does not
contain any neighborhood of the distinguished point. -/
theorem exists_neighborhood_pathComponentIn_not_mem_nhds :
    ∃ U : Set Space, U ∈ 𝓝 basepoint ∧ pathComponentIn U basepoint ∉ 𝓝 basepoint := by
  let U : Set Space := {p | (1 / 2 : ℝ) < p.1.2}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)
  have hbaseU : basepoint ∈ U := by
    norm_num [U, basepoint]
  refine ⟨U, hUopen.mem_nhds hbaseU, ?_⟩
  intro hpath
  -- Convergence forces a nonlimiting tooth endpoint into any alleged component neighborhood.
  have heventually : ∀ᶠ n in atTop,
      (⟨(1 / ((n + 1 : ℕ) : ℝ), 1), toothTop_mem_carrier n⟩ : Space) ∈
        pathComponentIn U basepoint :=
    tendsto_toothTop_basepoint.eventually hpath
  obtain ⟨n, hn⟩ := (eventually_atTop.1 heventually)
  have hjoined : JoinedIn U basepoint
      (⟨(1 / ((n + 1 : ℕ) : ℝ), 1), toothTop_mem_carrier n⟩ : Space) := hn n le_rfl
  have hhorizontal := horizontalCoordinate_eq_of_joinedIn_of_positive
    (F := U) (p := basepoint)
    (q := (⟨(1 / ((n + 1 : ℕ) : ℝ), 1), toothTop_mem_carrier n⟩ : Space))
    (fun z hz ↦ by
      dsimp [U] at hz
      linarith)
    hjoined
  -- The limiting tooth has coordinate zero, while every selected tooth has positive coordinate.
  have hnonzero : (1 / ((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply hnonzero
  simpa [basepoint] using hhorizontal.symm

/-- Exercise 58.8 (2): The distinguished singleton is not a deformation retract of the
topologist's comb. -/
theorem singleton_not_isDeformationRetract :
    ¬ Set.IsDeformationRetract ({basepoint} : Set Space) := by
  intro h
  obtain ⟨U, hU, hpath⟩ := exists_neighborhood_pathComponentIn_not_mem_nhds
  exact hpath (h.pathComponentIn_mem_nhds hU)

end TopologistsComb
