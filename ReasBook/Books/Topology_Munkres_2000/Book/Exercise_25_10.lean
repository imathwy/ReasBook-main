module

public import Topology_Munkres_2000.Book.Exercise_25_10.Quasicomponent
public import Topology_Munkres_2000.Book.Definition_13_3.RealLine
public import Topology_Munkres_2000.Book.Definition_25_2
public import Topology_Munkres_2000.Book.Definition_25_3
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Separation.Lemmas

public section

open Set
open Filter
open scoped Topology unitInterval

universe u

/-- The set of negatives of reciprocals of positive integers. -/
def negativeReciprocals : Set ℝ :=
  (fun x : ℝ ↦ -x) '' RealTopology.positiveReciprocals

/-- The reciprocal vertical-segment space with its two limiting endpoints. -/
def quasicomponentExampleA : Set (ℝ × ℝ) :=
  (RealTopology.positiveReciprocals ×ˢ Icc 0 1) ∪ {(0, 0)} ∪ {(0, 1)}

/-- The reciprocal vertical-segment space joined along its lower edge. -/
def quasicomponentExampleB : Set (ℝ × ℝ) :=
  quasicomponentExampleA ∪ (Icc 0 1 ×ˢ {(0 : ℝ)})

/-- The four reciprocal families of vertical and horizontal segments. -/
def quasicomponentExampleC : Set (ℝ × ℝ) :=
  (RealTopology.positiveReciprocals ×ˢ Icc 0 1) ∪
    (negativeReciprocals ×ˢ Icc (-1) 0) ∪
    (Icc 0 1 ×ˢ negativeReciprocals) ∪
    (Icc (-1) 0 ×ˢ RealTopology.positiveReciprocals)

/-- Two points of `quasicomponentExampleC` lie on the same one of its four families of arms. -/
def sameCArm (p q : ℝ × ℝ) : Prop :=
  (p ∈ RealTopology.positiveReciprocals ×ˢ Icc 0 1 ∧
      q ∈ RealTopology.positiveReciprocals ×ˢ Icc 0 1 ∧ p.1 = q.1) ∨
    (p ∈ negativeReciprocals ×ˢ Icc (-1) 0 ∧
      q ∈ negativeReciprocals ×ˢ Icc (-1) 0 ∧ p.1 = q.1) ∨
    (p ∈ Icc 0 1 ×ˢ negativeReciprocals ∧
      q ∈ Icc 0 1 ×ˢ negativeReciprocals ∧ p.2 = q.2) ∨
    (p ∈ Icc (-1) 0 ×ˢ RealTopology.positiveReciprocals ∧
      q ∈ Icc (-1) 0 ×ˢ RealTopology.positiveReciprocals ∧ p.2 = q.2)

/-- Helper for Exercise 25.10: the positive reciprocal set is countable. -/
lemma countable_positiveReciprocals : RealTopology.positiveReciprocals.Countable := by
  -- Embed every positive reciprocal in the range of the reciprocal map on `ℕ`.
  refine (Set.countable_range fun n : ℕ ↦ ((n : ℝ)⁻¹)).mono ?_
  intro x hx
  rw [RealTopology.mem_positiveReciprocals] at hx
  obtain ⟨n, _, rfl⟩ := hx
  exact ⟨n, rfl⟩

/-- Helper for Exercise 25.10: the negative reciprocal set is countable. -/
lemma countable_negativeReciprocals : negativeReciprocals.Countable := by
  -- Negation carries the already-countable positive reciprocal set onto this set.
  exact countable_positiveReciprocals.image (fun x : ℝ ↦ -x)

/-- Helper for Exercise 25.10: a continuous real-valued function is constant on a
preconnected set when its values lie in a countable set. -/
lemma eq_of_isPreconnected_mapsTo_countable {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {f : X → ℝ} (hf : Continuous f)
    {t : Set ℝ} (ht : t.Countable) (hfst : MapsTo f s t) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y := by
  -- The image is both preconnected and contained in a totally disconnected set.
  have himage : IsPreconnected (f '' s) := hs.image f hf.continuousOn
  have hsub : f '' s ⊆ t := image_subset_iff.mpr hfst
  have hsingle : (f '' s).Subsingleton := ht.isTotallyDisconnected (f '' s) hsub himage
  exact hsingle ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- Helper for Exercise 25.10: the first coordinate of a point of Example A is either zero
or a positive reciprocal. -/
lemma exampleA_first_mem (p : quasicomponentExampleA) :
    p.1.1 ∈ insert 0 RealTopology.positiveReciprocals := by
  -- Read the coordinate information from the three pieces defining Example A.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · exact mem_insert_iff.mpr (Or.inr hp.1)
    · exact mem_insert_iff.mpr (Or.inl (Prod.ext_iff.mp hp).1)
  · exact mem_insert_iff.mpr (Or.inl (Prod.ext_iff.mp hp).1)

/-- Helper for Exercise 25.10: a zero-first-coordinate point of Example A has second
coordinate zero or one. -/
lemma exampleA_second_mem_of_first_eq_zero (p : quasicomponentExampleA)
    (hp : p.1.1 = 0) : p.1.2 ∈ ({0, 1} : Set ℝ) := by
  -- The reciprocal vertical pieces have nonzero first coordinate, so only the endpoints remain.
  rcases p.property with hmem | hmem
  · rcases hmem with hmem | hmem
    · have hfirst := hmem.1
      rw [RealTopology.mem_positiveReciprocals] at hfirst
      obtain ⟨n, hn, hcoord⟩ := hfirst
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
      have hinv : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero hn0
      exact (hinv (hcoord ▸ hp)).elim
    · left
      exact (Prod.ext_iff.mp hmem).2
  · right
    exact (Prod.ext_iff.mp hmem).2

/-- Helper for Exercise 25.10: every positive-reciprocal vertical fiber of Example A is
path connected. -/
lemma isPathConnected_exampleA_fiber {a : ℝ}
    (ha : a ∈ RealTopology.positiveReciprocals) :
    IsPathConnected {q : quasicomponentExampleA | q.1.1 = a} := by
  -- The ambient arm `{a} × [0,1]` is path connected and lies in Example A.
  have hinterval : IsPathConnected (Icc (0 : ℝ) 1) := by
    exact (convex_Icc 0 1).isPathConnected (nonempty_Icc.mpr zero_le_one)
  have harm : IsPathConnected ({a} ×ˢ Icc (0 : ℝ) 1) :=
    (isPathConnected_singleton a).prod hinterval
  have hsubset : ({a} ×ˢ Icc (0 : ℝ) 1) ⊆ quasicomponentExampleA := by
    intro z hz
    exact Or.inl (Or.inl ⟨hz.1 ▸ ha, hz.2⟩)
  have hpullback := harm.preimage_coe hsubset
  -- Membership in the pullback is exactly equality of first coordinates.
  have hset : ((↑) : quasicomponentExampleA → ℝ × ℝ) ⁻¹' ({a} ×ˢ Icc (0 : ℝ) 1) =
      {q : quasicomponentExampleA | q.1.1 = a} := by
    ext q
    constructor
    · intro hq
      exact hq.1
    · intro hq
      have hmem := q.property
      rcases hmem with hmem | hmem
      · rcases hmem with hmem | hmem
        · exact ⟨hq, hmem.2⟩
        · have hzero : q.1.1 = 0 := (Prod.ext_iff.mp hmem).1
          have ha0 : a ≠ 0 := by
            rw [RealTopology.mem_positiveReciprocals] at ha
            obtain ⟨n, hn, rfl⟩ := ha
            exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
          exact (ha0 (hq ▸ hzero)).elim
      · have hzero : q.1.1 = 0 := (Prod.ext_iff.mp hmem).1
        have ha0 : a ≠ 0 := by
          rw [RealTopology.mem_positiveReciprocals] at ha
          obtain ⟨n, hn, rfl⟩ := ha
          exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
        exact (ha0 (hq ▸ hzero)).elim
  rwa [hset] at hpullback

/-- Helper for Exercise 25.10: the shifted positive reciprocal sequence lies in the
positive reciprocal set. -/
lemma shiftedReciprocal_mem (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)⁻¹) ∈ RealTopology.positiveReciprocals := by
  -- The shift makes every denominator strictly positive.
  rw [RealTopology.mem_positiveReciprocals]
  exact ⟨n + 1, Nat.succ_pos n, rfl⟩

/-- Helper for Exercise 25.10: the shifted positive reciprocal sequence converges to zero. -/
lemma tendsto_shiftedReciprocal_zero :
    Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  -- Use the canonical reciprocal limit for shifted natural denominators.
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Helper for Exercise 25.10: both limiting endpoints belong to Example A. -/
lemma exampleA_limitEndpoint_mem (c : ℝ) (hc : c = 0 ∨ c = 1) :
    (0, c) ∈ quasicomponentExampleA := by
  -- Select the corresponding singleton endpoint in the defining union.
  rcases hc with rfl | rfl
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr rfl

/-- Helper for Exercise 25.10: every shifted reciprocal endpoint belongs to Example A. -/
lemma exampleA_reciprocalEndpoint_mem (n : ℕ) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    ((((n + 1 : ℕ) : ℝ)⁻¹), c) ∈ quasicomponentExampleA := by
  -- The point lies on the vertical arm indexed by `n + 1`.
  exact Or.inl (Or.inl ⟨shiftedReciprocal_mem n, hc⟩)

/-- Helper for Exercise 25.10: the lower limiting endpoint of Example A as a subtype point. -/
def exampleALowerEndpoint : quasicomponentExampleA :=
  ⟨(0, 0), exampleA_limitEndpoint_mem 0 (Or.inl rfl)⟩

/-- Helper for Exercise 25.10: the upper limiting endpoint of Example A as a subtype point. -/
def exampleAUpperEndpoint : quasicomponentExampleA :=
  ⟨(0, 1), exampleA_limitEndpoint_mem 1 (Or.inr rfl)⟩

/-- Helper for Exercise 25.10: a canonical endpoint on the `n`th reciprocal arm. -/
noncomputable def exampleAReciprocalEndpoint (n : ℕ) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    quasicomponentExampleA :=
  ⟨((((n + 1 : ℕ) : ℝ)⁻¹), c), exampleA_reciprocalEndpoint_mem n c hc⟩

/-- Helper for Exercise 25.10: reciprocal arm endpoints converge to the corresponding
limiting endpoint in Example A. -/
lemma tendsto_exampleAReciprocalEndpoint (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1)
    (hlimit : c = 0 ∨ c = 1) :
    Tendsto (fun n ↦ exampleAReciprocalEndpoint n c hc) atTop
      (𝓝 ⟨(0, c), exampleA_limitEndpoint_mem c hlimit⟩) := by
  -- Check convergence after coercing to the ambient product.
  rw [tendsto_subtype_rng]
  exact tendsto_shiftedReciprocal_zero.prodMk_nhds tendsto_const_nhds

/-- Helper for Exercise 25.10: a clopen subset of Example A contains one limiting endpoint
if and only if it contains the other. -/
lemma isClopen_exampleA_mem_zeroEndpoints_iff {U : Set quasicomponentExampleA}
    (hU : IsClopen U) : exampleALowerEndpoint ∈ U ↔ exampleAUpperEndpoint ∈ U := by
  -- Route correction: propagate an eventual reciprocal tail before taking the opposite limit.
  -- Openness gives a tail of lower arm endpoints; connected arms fill the top endpoints.
  constructor
  · intro hlower
    have hlowerTail : ∀ᶠ n in atTop,
        exampleAReciprocalEndpoint n 0 ⟨le_rfl, zero_le_one⟩ ∈ U :=
      (tendsto_exampleAReciprocalEndpoint 0 ⟨le_rfl, zero_le_one⟩ (Or.inl rfl))
        (hU.2.mem_nhds hlower)
    have hupperTail : ∀ᶠ n in atTop,
        exampleAReciprocalEndpoint n 1 ⟨zero_le_one, le_rfl⟩ ∈ U := by
      filter_upwards [hlowerTail] with n hn
      have harm := isPathConnected_exampleA_fiber (shiftedReciprocal_mem n)
      exact harm.isConnected.isPreconnected.subset_isClopen hU ⟨_, rfl, hn⟩ rfl
    exact hU.1.mem_of_tendsto (tendsto_exampleAReciprocalEndpoint 1
      ⟨zero_le_one, le_rfl⟩ (Or.inr rfl)) hupperTail
  · intro hupper
    have hupperTail : ∀ᶠ n in atTop,
        exampleAReciprocalEndpoint n 1 ⟨zero_le_one, le_rfl⟩ ∈ U :=
      (tendsto_exampleAReciprocalEndpoint 1 ⟨zero_le_one, le_rfl⟩ (Or.inr rfl))
        (hU.2.mem_nhds hupper)
    have hlowerTail : ∀ᶠ n in atTop,
        exampleAReciprocalEndpoint n 0 ⟨le_rfl, zero_le_one⟩ ∈ U := by
      filter_upwards [hupperTail] with n hn
      have harm := isPathConnected_exampleA_fiber (shiftedReciprocal_mem n)
      exact harm.isConnected.isPreconnected.subset_isClopen hU ⟨_, rfl, hn⟩ rfl
    exact hU.1.mem_of_tendsto (tendsto_exampleAReciprocalEndpoint 0
      ⟨le_rfl, zero_le_one⟩ (Or.inl rfl)) hlowerTail

/-- Helper for Exercise 25.10: adjacent reciprocal values isolate one positive reciprocal
inside the possible first coordinates of Example A. -/
lemma positiveReciprocal_interval_eq (n : ℕ) (hn : 0 < n) :
    Ioo (((n + 1 : ℕ) : ℝ)⁻¹)
        (if n = 1 then 2 else (((n - 1 : ℕ) : ℝ)⁻¹)) ∩
      insert 0 RealTopology.positiveReciprocals =
        {((n : ℝ)⁻¹)} := by
  -- Compare any reciprocal in the interval with the adjacent denominators.
  ext x
  constructor
  · rintro ⟨hxInterval, hxCoordinate⟩
    rcases hxCoordinate with rfl | hxReciprocal
    · have hlowerPositive : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      exact (not_lt_of_ge hlowerPositive.le hxInterval.1).elim
    · rw [RealTopology.mem_positiveReciprocals] at hxReciprocal
      obtain ⟨m, hm, rfl⟩ := hxReciprocal
      have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
      have hnSuccReal : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hmLtSucc : m < n + 1 := by
        exact_mod_cast (inv_lt_inv₀ hnSuccReal hmReal).mp hxInterval.1
      by_cases hnOne : n = 1
      · subst n
        have hmEq : m = 1 := by omega
        simp [hmEq]
      · have hnPred : 0 < n - 1 := by omega
        have hnPredReal : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnPred
        have hpredLtM : n - 1 < m := by
          exact_mod_cast (inv_lt_inv₀ hmReal hnPredReal).mp
            (by simpa [hnOne] using hxInterval.2)
        have hmEq : m = n := by omega
        simp [hmEq]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · constructor
      · have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
        have hnSuccReal : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        exact (inv_lt_inv₀ hnSuccReal hnReal).mpr
          (by exact_mod_cast Nat.lt_succ_self n)
      · by_cases hnOne : n = 1
        · subst n
          norm_num
        · have hnPred : 0 < n - 1 := by omega
          have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
          have hnPredReal : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnPred
          simpa [hnOne] using
            (inv_lt_inv₀ hnReal hnPredReal).mpr
              (by exact_mod_cast (show n - 1 < n by omega))
    · right
      rw [RealTopology.mem_positiveReciprocals]
      exact ⟨n, hn, rfl⟩

/-- Helper for Exercise 25.10: every positive reciprocal has an open neighborhood meeting
the possible first coordinates of Example A only at that reciprocal. -/
lemma positiveReciprocal_isolated {a : ℝ}
    (ha : a ∈ RealTopology.positiveReciprocals) :
    ∃ V : Set ℝ, IsOpen V ∧ a ∈ V ∧
      V ∩ insert 0 RealTopology.positiveReciprocals = {a} := by
  -- Choose the adjacent-reciprocal interval around a representing denominator.
  rw [RealTopology.mem_positiveReciprocals] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  refine ⟨Ioo (((n + 1 : ℕ) : ℝ)⁻¹)
    (if n = 1 then 2 else (((n - 1 : ℕ) : ℝ)⁻¹)), isOpen_Ioo, ?_,
    positiveReciprocal_interval_eq n hn⟩
  -- The center reciprocal lies strictly between its chosen neighbors.
  constructor
  · have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnSuccReal : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    exact (inv_lt_inv₀ hnSuccReal hnReal).mpr
      (by exact_mod_cast Nat.lt_succ_self n)
  · by_cases hnOne : n = 1
    · subst n
      norm_num
    · have hnPred : 0 < n - 1 := by omega
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hnPredReal : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnPred
      simpa [hnOne] using
        (inv_lt_inv₀ hnReal hnPredReal).mpr
          (by exact_mod_cast (show n - 1 < n by omega))

/-- Helper for Exercise 25.10: every nonzero reciprocal fiber of Example A is clopen. -/
lemma isClopen_exampleA_fiber {a : ℝ} (ha : a ∈ RealTopology.positiveReciprocals) :
    IsClopen {q : quasicomponentExampleA | q.1.1 = a} := by
  -- Closedness is the equality locus of two continuous real-valued maps.
  have hcontinuous : Continuous (fun q : quasicomponentExampleA ↦ q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hclosed : IsClosed {q : quasicomponentExampleA | q.1.1 = a} := by
    exact isClosed_eq hcontinuous continuous_const
  obtain ⟨V, hVOpen, haV, hVisolate⟩ := positiveReciprocal_isolated ha
  -- On Example A, the fiber is exactly the preimage of the isolating interval.
  have hfiber : {q : quasicomponentExampleA | q.1.1 = a} =
      (fun q : quasicomponentExampleA ↦ q.1.1) ⁻¹' V := by
    ext q
    constructor
    · intro hq
      have hqa : q.1.1 = a := hq
      simpa only [Set.mem_preimage, hqa] using haV
    · intro hq
      have hcontrolled : q.1.1 ∈ V ∩ insert 0 RealTopology.positiveReciprocals :=
        ⟨hq, exampleA_first_mem q⟩
      rw [hVisolate] at hcontrolled
      exact Set.mem_singleton_iff.mp hcontrolled
  -- Pull openness back through the continuous coordinate map.
  refine ⟨hclosed, ?_⟩
  rw [hfiber]
  exact hVOpen.preimage hcontinuous

/-- Helper for Exercise 25.10: any two zero-coordinate points of Example A belong to the
same quasicomponent. -/
lemma mem_quasicomponent_exampleA_of_first_eq_zero
    (p q : quasicomponentExampleA) (hp : p.1.1 = 0) (hq : q.1.1 = 0) :
    q ∈ quasicomponent p := by
  -- Reduce both points to the two named limiting endpoints.
  have hpSecond := exampleA_second_mem_of_first_eq_zero p hp
  have hqSecond := exampleA_second_mem_of_first_eq_zero q hq
  rcases hpSecond with hpSecond | hpSecond
  · have hpEq : p = exampleALowerEndpoint := by
      exact Subtype.ext (Prod.ext hp hpSecond)
    rcases hqSecond with hqSecond | hqSecond
    · have hqEq : q = exampleALowerEndpoint := by
        exact Subtype.ext (Prod.ext hq hqSecond)
      rw [hpEq, hqEq]
      rw [mem_quasicomponent_iff]
      intro U _ hU
      exact hU
    · have hqEq : q = exampleAUpperEndpoint := by
        exact Subtype.ext (Prod.ext hq hqSecond)
      rw [hpEq, hqEq, mem_quasicomponent_iff]
      intro U hU hlower
      exact (isClopen_exampleA_mem_zeroEndpoints_iff hU).mp hlower
  · have hpEq : p = exampleAUpperEndpoint := by
      exact Subtype.ext (Prod.ext hp hpSecond)
    rcases hqSecond with hqSecond | hqSecond
    · have hqEq : q = exampleALowerEndpoint := by
        exact Subtype.ext (Prod.ext hq hqSecond)
      rw [hpEq, hqEq, mem_quasicomponent_iff]
      intro U hU hupper
      exact (isClopen_exampleA_mem_zeroEndpoints_iff hU).mpr hupper
    · have hqEq : q = exampleAUpperEndpoint := by
        exact Subtype.ext (Prod.ext hq hqSecond)
      rw [hpEq, hqEq]
      rw [mem_quasicomponent_iff]
      intro U _ hU
      exact hU

/- Exercise 25.10 (1): Two points are in the same quasicomponent exactly when no clopen
set contains the first and excludes the second. -/
#check mem_quasicomponent_iff_no_clopen_separation

/-- Part (2) of Exercise 25.10: belonging to the same quasicomponent is an equivalence relation. -/
theorem sameQuasicomponent_equivalence {X : Type u} [TopologicalSpace X] :
    Equivalence (fun x y : X ↦ y ∈ quasicomponent x) := by
  -- Every point belongs to each of its clopen neighborhoods.
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [mem_quasicomponent_iff]
    intro U _ hx
    exact hx
  -- Symmetry is the complement argument built into quasicomponent membership.
  · intro x y hxy
    rwa [mem_quasicomponent_comm]
  -- Universal membership in clopen neighborhoods composes transitively.
  · intro x y z hxy hyz
    rw [mem_quasicomponent_iff] at hxy hyz ⊢
    intro U hU hx
    exact hyz U hU (hxy U hU hx)

/-- Part (3) of Exercise 25.10: every connected component is contained in its quasicomponent. -/
theorem connectedComponent_subset_quasicomponent {X : Type u} [TopologicalSpace X]
    (x : X) :
    connectedComponent x ⊆ quasicomponent x := by
  -- A connected component cannot leave any clopen neighborhood of its base point.
  intro y hy
  rw [mem_quasicomponent_iff]
  intro U hU hx
  exact hU.connectedComponent_subset hx hy

/-- Part (4) of Exercise 25.10: in a locally connected space, connected components and
quasicomponents coincide. -/
theorem connectedComponent_eq_quasicomponent {X : Type u} [TopologicalSpace X]
    [LocallyConnectedSpace X] (x : X) :
    connectedComponent x = quasicomponent x := by
  -- One inclusion is general; local connectedness makes the component itself clopen.
  refine Set.Subset.antisymm (connectedComponent_subset_quasicomponent x) ?_
  intro y hy
  rw [mem_quasicomponent_iff] at hy
  exact hy (connectedComponent x) isClopen_connectedComponent mem_connectedComponent

/-- Part (5) of Exercise 25.10: the components of `quasicomponentExampleA` are its two limiting
endpoints and its individual vertical segments. -/
theorem connectedComponent_exampleA (p : quasicomponentExampleA) :
    connectedComponent p =
      if p.1.1 = 0 then {p} else {q : quasicomponentExampleA | q.1.1 = p.1.1} := by
  -- Connected coordinate images inside countable subsets of `ℝ` are singletons.
  by_cases hp0 : p.1.1 = 0
  · rw [if_pos hp0]
    have hfirst_zero (r : quasicomponentExampleA) (hr : r ∈ connectedComponent p) :
        r.1.1 = 0 := by
      exact (eq_of_isPreconnected_mapsTo_countable isPreconnected_connectedComponent
        (continuous_fst.comp continuous_subtype_val)
        (countable_positiveReciprocals.insert 0)
        (fun z _ ↦ exampleA_first_mem z) hr mem_connectedComponent).trans hp0
    apply Set.Subset.antisymm
    · intro q hq
      have hfirst : q.1.1 = p.1.1 := (hfirst_zero q hq).trans hp0.symm
      have hsecond : q.1.2 = p.1.2 :=
        eq_of_isPreconnected_mapsTo_countable isPreconnected_connectedComponent
          (continuous_snd.comp continuous_subtype_val)
          (Set.toFinite ({0, 1} : Set ℝ)).to_countable
          (fun r hr ↦ exampleA_second_mem_of_first_eq_zero r (hfirst_zero r hr))
          hq mem_connectedComponent
      exact Set.mem_singleton_iff.mpr (Subtype.ext (Prod.ext hfirst hsecond))
    · intro q hq
      rw [Set.mem_singleton_iff.mp hq]
      exact mem_connectedComponent
  · rw [if_neg hp0]
    have hpK : p.1.1 ∈ RealTopology.positiveReciprocals := by
      rcases exampleA_first_mem p with hzero | hK
      · exact (hp0 hzero).elim
      · exact hK
    apply Set.Subset.antisymm
    · intro q hq
      exact eq_of_isPreconnected_mapsTo_countable isPreconnected_connectedComponent
        (continuous_fst.comp continuous_subtype_val)
        (countable_positiveReciprocals.insert 0)
        (fun r _ ↦ exampleA_first_mem r) hq mem_connectedComponent
    · exact (isPathConnected_exampleA_fiber hpK).isConnected.subset_connectedComponent rfl

/-- Part (6) of Exercise 25.10: the path components of `quasicomponentExampleA` are its two
limiting endpoints and its individual vertical segments. -/
theorem pathComponent_exampleA (p : quasicomponentExampleA) :
    pathComponent p =
      if p.1.1 = 0 then {p} else {q : quasicomponentExampleA | q.1.1 = p.1.1} := by
  -- The connected-component classification gives the upper bound; each nonzero fiber is a path.
  by_cases hp0 : p.1.1 = 0
  · rw [if_pos hp0]
    apply Set.Subset.antisymm
    · intro q hq
      have hconnected := pathComponent_subset_component p hq
      rw [connectedComponent_exampleA p, if_pos hp0] at hconnected
      exact hconnected
    · intro q hq
      rw [Set.mem_singleton_iff.mp hq]
      exact mem_pathComponent_self p
  · rw [if_neg hp0]
    have hpK : p.1.1 ∈ RealTopology.positiveReciprocals := by
      rcases exampleA_first_mem p with hzero | hK
      · exact (hp0 hzero).elim
      · exact hK
    apply Set.Subset.antisymm
    · intro q hq
      have hconnected := pathComponent_subset_component p hq
      rw [connectedComponent_exampleA p, if_neg hp0] at hconnected
      exact hconnected
    · exact (isPathConnected_exampleA_fiber hpK).subset_pathComponent rfl

/-- Part (7) of Exercise 25.10: the two limiting endpoints of `quasicomponentExampleA` form one
quasicomponent, while each vertical segment forms another. -/
theorem quasicomponent_exampleA (p : quasicomponentExampleA) :
    quasicomponent p =
      if p.1.1 = 0 then {q : quasicomponentExampleA | q.1.1 = 0}
      else {q : quasicomponentExampleA | q.1.1 = p.1.1} := by
  -- Clopen reciprocal fibers separate distinct arms; endpoint propagation identifies
  -- the two limits.
  by_cases hp0 : p.1.1 = 0
  · rw [if_pos hp0]
    apply Set.Subset.antisymm
    · intro q hq
      by_contra hq0
      have hqK : q.1.1 ∈ RealTopology.positiveReciprocals := by
        rcases exampleA_first_mem q with hzero | hK
        · exact (hq0 hzero).elim
        · exact hK
      rw [mem_quasicomponent_iff] at hq
      have hfiber := isClopen_exampleA_fiber hqK
      have hqMem : q ∈ {r : quasicomponentExampleA | r.1.1 = q.1.1} := rfl
      have hpNotMem : p ∉ {r : quasicomponentExampleA | r.1.1 = q.1.1} := by
        intro hmem
        exact hq0 (hmem.symm.trans hp0)
      have hpMemCompl :
          p ∈ ({r : quasicomponentExampleA | r.1.1 = q.1.1})ᶜ := hpNotMem
      have hqMemCompl := hq _ hfiber.compl hpMemCompl
      exact hqMemCompl hqMem
    · intro q hq
      exact mem_quasicomponent_exampleA_of_first_eq_zero p q hp0 hq
  · rw [if_neg hp0]
    have hpK : p.1.1 ∈ RealTopology.positiveReciprocals := by
      rcases exampleA_first_mem p with hzero | hK
      · exact (hp0 hzero).elim
      · exact hK
    apply Set.Subset.antisymm
    · intro q hq
      rw [mem_quasicomponent_iff] at hq
      exact hq _ (isClopen_exampleA_fiber hpK) rfl
    · intro q hq
      apply connectedComponent_subset_quasicomponent p
      exact (isPathConnected_exampleA_fiber hpK).isConnected.subset_connectedComponent rfl hq

/-- Helper for Exercise 25.10: all points of Example B except the upper limiting endpoint
form a path-connected set. -/
lemma isPathConnected_exampleB_withoutUpper :
    IsPathConnected {q : quasicomponentExampleB | q.1 ≠ (0, 1)} := by
  -- Route correction: use the lower horizontal edge as a spine instead of propagating clopen sets.
  have hinterval : IsPathConnected (Icc (0 : ℝ) 1) := by
    exact (convex_Icc 0 1).isPathConnected (nonempty_Icc.mpr zero_le_one)
  have hlowerAmbient : IsPathConnected (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) :=
    hinterval.prod (isPathConnected_singleton 0)
  have hlowerSubset : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ quasicomponentExampleB := by
    intro z hz
    exact Or.inr hz
  have hlower := hlowerAmbient.preimage_coe hlowerSubset
  have hlowerCore :
      ((↑) : quasicomponentExampleB → ℝ × ℝ) ⁻¹' (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) ⊆
        {q : quasicomponentExampleB | q.1 ≠ (0, 1)} := by
    intro q hq hqUpper
    have hsecond : q.1.2 = 0 := Set.mem_singleton_iff.mp hq.2
    exact zero_ne_one (hsecond.symm.trans (congrArg Prod.snd hqUpper))
  have hbaseMemB : (0, 0) ∈ quasicomponentExampleB :=
    Or.inl (exampleA_limitEndpoint_mem 0 (Or.inl rfl))
  let base : quasicomponentExampleB := ⟨(0, 0), hbaseMemB⟩
  have hbaseLower : base ∈
      ((↑) : quasicomponentExampleB → ℝ × ℝ) ⁻¹' (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) := by
    exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have hbaseCore : base ∈ {q : quasicomponentExampleB | q.1 ≠ (0, 1)} :=
    hlowerCore hbaseLower
  -- Every point reaches the spine directly or through the foot of its reciprocal arm.
  refine ⟨base, hbaseCore, ?_⟩
  intro q hqCore
  rcases q.property with hqA | hqLower
  · rcases hqA with hqArmOrLower | hqUpper
    · rcases hqArmOrLower with hqArm | hqLowerEndpoint
      · have haIcc : q.1.1 ∈ Icc (0 : ℝ) 1 := by
          have hqReciprocal := hqArm.1
          rw [RealTopology.mem_positiveReciprocals] at hqReciprocal
          obtain ⟨n, hn, hqFirst⟩ := hqReciprocal
          rw [hqFirst]
          constructor
          · positivity
          · have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
            have hnPositive : (0 : ℝ) < n := by exact_mod_cast hn
            simpa using (inv_le_one₀ hnPositive).mpr hnReal
        have hfootMemB : (q.1.1, 0) ∈ quasicomponentExampleB :=
          Or.inr ⟨haIcc, rfl⟩
        let foot : quasicomponentExampleB := ⟨(q.1.1, 0), hfootMemB⟩
        have hfootLower : foot ∈
            ((↑) : quasicomponentExampleB → ℝ × ℝ) ⁻¹'
              (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) := by
          exact ⟨haIcc, rfl⟩
        have harmAmbient : IsPathConnected ({q.1.1} ×ˢ Icc (0 : ℝ) 1) :=
          (isPathConnected_singleton q.1.1).prod hinterval
        have harmSubset : {q.1.1} ×ˢ Icc (0 : ℝ) 1 ⊆ quasicomponentExampleB := by
          intro z hz
          exact Or.inl (Or.inl (Or.inl ⟨hz.1 ▸ hqArm.1, hz.2⟩))
        have harm := harmAmbient.preimage_coe harmSubset
        have harmCore :
            ((↑) : quasicomponentExampleB → ℝ × ℝ) ⁻¹'
                ({q.1.1} ×ˢ Icc (0 : ℝ) 1) ⊆
              {r : quasicomponentExampleB | r.1 ≠ (0, 1)} := by
          intro r hr hrUpper
          have hfirst : r.1.1 = q.1.1 := Set.mem_singleton_iff.mp hr.1
          have hqPositive : 0 < q.1.1 := by
            have hqReciprocal := hqArm.1
            rw [RealTopology.mem_positiveReciprocals] at hqReciprocal
            obtain ⟨n, hn, hqFirst⟩ := hqReciprocal
            rw [hqFirst]
            positivity
          exact ne_of_gt hqPositive (hfirst.symm.trans (congrArg Prod.fst hrUpper))
        have hbaseFoot := hlower.joinedIn base hbaseLower foot hfootLower
        have hfootQ := harm.joinedIn foot ⟨rfl, ⟨le_rfl, zero_le_one⟩⟩ q
          ⟨rfl, hqArm.2⟩
        exact (hbaseFoot.mono hlowerCore).trans (hfootQ.mono harmCore)
      · have hqLower' : q ∈
            ((↑) : quasicomponentExampleB → ℝ × ℝ) ⁻¹'
              (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) := by
          have hqEq : q.1 = (0, 0) := hqLowerEndpoint
          have qEq : q = (⟨(0, 0), hbaseMemB⟩ : quasicomponentExampleB) :=
            Subtype.ext hqEq
          rw [qEq]
          exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
        exact (hlower.joinedIn base hbaseLower q hqLower').mono hlowerCore
    · exact (hqCore hqUpper).elim
  · exact (hlower.joinedIn base hbaseLower q hqLower).mono hlowerCore

/-- Helper for Exercise 25.10: every canonical reciprocal upper endpoint belongs to Example B. -/
lemma exampleB_reciprocalUpperEndpoint_mem (n : ℕ) :
    ((((n + 1 : ℕ) : ℝ)⁻¹), 1) ∈ quasicomponentExampleB := by
  -- Enter Example B through its Example A summand.
  exact Or.inl (exampleA_reciprocalEndpoint_mem n 1 ⟨zero_le_one, le_rfl⟩)

/-- Helper for Exercise 25.10: the canonical reciprocal upper endpoint as a point of Example B. -/
noncomputable def exampleBReciprocalUpperEndpoint (n : ℕ) : quasicomponentExampleB :=
  ⟨((((n + 1 : ℕ) : ℝ)⁻¹), 1), exampleB_reciprocalUpperEndpoint_mem n⟩

/-- Helper for Exercise 25.10: the upper limiting endpoint belongs to Example B. -/
lemma exampleB_upperEndpoint_mem : (0, 1) ∈ quasicomponentExampleB := by
  -- Enter Example B through its Example A summand.
  exact Or.inl (exampleA_limitEndpoint_mem 1 (Or.inr rfl))

/-- Helper for Exercise 25.10: above the lower edge, the first coordinate of an Example B
point is zero or a positive reciprocal. -/
lemma exampleB_first_mem_of_second_ne_zero (p : quasicomponentExampleB)
    (hp : p.1.2 ≠ 0) :
    p.1.1 ∈ insert 0 RealTopology.positiveReciprocals := by
  -- The lower-edge summand is excluded by the nonzero second coordinate.
  rcases p.property with hpA | hpLower
  · exact exampleA_first_mem ⟨p.1, hpA⟩
  · exact (hp (Set.mem_singleton_iff.mp hpLower.2)).elim

/-- Helper for Exercise 25.10: a zero-first-coordinate point of Example B has second
coordinate zero or one. -/
lemma exampleB_second_mem_of_first_eq_zero (p : quasicomponentExampleB)
    (hp : p.1.1 = 0) : p.1.2 ∈ ({0, 1} : Set ℝ) := by
  -- Example A contributes its two limiting endpoints, while the lower edge contributes zero.
  rcases p.property with hpA | hpLower
  · exact exampleA_second_mem_of_first_eq_zero ⟨p.1, hpA⟩ hp
  · exact Or.inl (Set.mem_singleton_iff.mp hpLower.2)

/-- Helper for Exercise 25.10: reciprocal upper endpoints converge to the upper limiting
endpoint. -/
lemma tendsto_exampleBReciprocalUpperEndpoint :
    Tendsto exampleBReciprocalUpperEndpoint atTop
      (𝓝 (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB)) := by
  -- Check convergence after coercing to the ambient product.
  rw [tendsto_subtype_rng]
  exact tendsto_shiftedReciprocal_zero.prodMk_nhds tendsto_const_nhds

/-- Helper for Exercise 25.10: the non-upper part of Example B is dense. -/
lemma closure_exampleB_withoutUpper :
    closure {q : quasicomponentExampleB | q.1 ≠ (0, 1)} = Set.univ := by
  -- All non-upper points are in the closure; the endpoint is supplied by the reciprocal sequence.
  apply Set.eq_univ_of_univ_subset
  intro q _
  by_cases hqUpper : q.1 = (0, 1)
  · have qEq : q = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) :=
      Subtype.ext hqUpper
    rw [qEq]
    apply isClosed_closure.mem_of_tendsto tendsto_exampleBReciprocalUpperEndpoint
    filter_upwards [] with n
    apply subset_closure
    intro hnUpper
    have hfirst := congrArg Prod.fst hnUpper
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))) hfirst
  · exact subset_closure hqUpper

/-- Part (8) of Exercise 25.10: `quasicomponentExampleB` has one connected component. -/
theorem connectedComponent_exampleB (p : quasicomponentExampleB) :
    connectedComponent p = Set.univ := by
  -- The dense path-connected core has preconnected closure equal to the whole space.
  have hunivPreconnected : IsPreconnected (Set.univ : Set quasicomponentExampleB) := by
    rw [← closure_exampleB_withoutUpper]
    exact isPathConnected_exampleB_withoutUpper.isConnected.isPreconnected.closure
  apply Set.eq_univ_of_univ_subset
  exact hunivPreconnected.subset_connectedComponent (Set.mem_univ p)

/-- Helper for Exercise 25.10: before a least lower-edge hitting time, the second
coordinate of the path is nonzero. -/
lemma exampleB_second_ne_zero_before_least_zero {x y : quasicomponentExampleB}
    (γ : Path x y) (t₀ : I)
    (hmin : IsMinOn id {t : I | (γ t).1.2 = 0} t₀) :
    ∀ t ∈ Ico 0 t₀, (γ t).1.2 ≠ 0 := by
  -- Minimality rules out any earlier time at which the path reaches the lower edge.
  intro t ht hzero
  exact (not_le_of_gt ht.2) (hmin hzero)

/-- Helper for Exercise 25.10: a path from the upper endpoint is constant on the
half-open prefix before its least lower-edge hitting time. -/
lemma exampleB_path_prefix_eq_upper {y : quasicomponentExampleB}
    (γ : Path (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) y)
    (t₀ : I) (ht₀pos : 0 < t₀)
    (hmin : IsMinOn id {t : I | (γ t).1.2 = 0} t₀) :
    ∀ t ∈ Ico 0 t₀,
      γ t = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) := by
  -- The first coordinate has countable image on the prefix, hence is constant there.
  have hcontinuous : Continuous (fun t : I ↦ (γ t).1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp γ.continuous)
  have hmaps : MapsTo (fun t : I ↦ (γ t).1.1) (Ico 0 t₀)
      (insert 0 RealTopology.positiveReciprocals) := by
    intro t ht
    exact exampleB_first_mem_of_second_ne_zero (γ t)
      (exampleB_second_ne_zero_before_least_zero γ t₀ hmin t ht)
  intro t ht
  have hfirstEq : (γ t).1.1 = (γ 0).1.1 :=
    eq_of_isPreconnected_mapsTo_countable isPreconnected_Ico hcontinuous
      (countable_positiveReciprocals.insert 0) hmaps ht ⟨le_rfl, ht₀pos⟩
  have hsourceFirst : (γ 0).1.1 = 0 :=
    congrArg (fun q : quasicomponentExampleB ↦ q.1.1) γ.source
  have hfirst : (γ t).1.1 = 0 := hfirstEq.trans hsourceFirst
  -- The zero fiber contains only the lower and upper endpoints; nonzeroness selects upper.
  rcases exampleB_second_mem_of_first_eq_zero (γ t) hfirst with hsecond | hsecond
  · exact ((exampleB_second_ne_zero_before_least_zero γ t₀ hmin t ht) hsecond).elim
  · exact Subtype.ext (Prod.ext hfirst hsecond)

/-- Helper for Exercise 25.10: a path starting at the upper endpoint never reaches
the lower edge of Example B. -/
lemma exampleB_path_second_ne_zero {y : quasicomponentExampleB}
    (γ : Path (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) y) :
    ∀ t : I, (γ t).1.2 ≠ 0 := by
  -- A least zero time would be a limit of a prefix already forced to remain upper.
  intro t hzero
  let Z : Set I := {s : I | (γ s).1.2 = 0}
  have hcoord : Continuous (fun s : I ↦ (γ s).1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp γ.continuous)
  have hZclosed : IsClosed Z := isClosed_singleton.preimage hcoord
  have hZcompact : IsCompact Z := hZclosed.isCompact
  have hZnonempty : Z.Nonempty := ⟨t, hzero⟩
  obtain ⟨t₀, ht₀Z, ht₀min⟩ :=
    hZcompact.exists_isMinOn hZnonempty continuous_id.continuousOn
  have ht₀ne : t₀ ≠ 0 := by
    intro ht₀
    subst t₀
    have hsourceSecond : (γ 0).1.2 = 1 :=
      congrArg (fun q : quasicomponentExampleB ↦ q.1.2) γ.source
    exact zero_ne_one (ht₀Z.symm.trans hsourceSecond)
  have ht₀pos : 0 < t₀ :=
    lt_of_le_of_ne (show 0 ≤ t₀ from t₀.property.1) (Ne.symm ht₀ne)
  have hprefix : Ico (0 : I) t₀ ⊆ {s : I | (γ s).1 = (0, 1)} := by
    intro s hs
    exact congrArg Subtype.val (exampleB_path_prefix_eq_upper γ t₀ ht₀pos ht₀min s hs)
  have hupperClosed : IsClosed {s : I | (γ s).1 = (0, 1)} :=
    isClosed_singleton.preimage (continuous_subtype_val.comp γ.continuous)
  have hclosure : closure (Ico (0 : I) t₀) ⊆ {s : I | (γ s).1 = (0, 1)} :=
    closure_minimal hprefix hupperClosed
  have ht₀closure : t₀ ∈ closure (Ico (0 : I) t₀) := by
    rw [closure_Ico (Ne.symm ht₀ne)]
    exact ⟨show (0 : I) ≤ t₀ from t₀.property.1, le_rfl⟩
  have ht₀upper := hclosure ht₀closure
  exact zero_ne_one (ht₀Z.symm.trans (congrArg Prod.snd ht₀upper))

/-- Helper for Exercise 25.10: every path starting at the upper endpoint of Example B
is constant. -/
lemma exampleB_path_eq_upper {y : quasicomponentExampleB}
    (γ : Path (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) y) :
    ∀ t : I, γ t = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) := by
  -- With the lower edge excluded, the first coordinate again has countable image globally.
  have hnonzero := exampleB_path_second_ne_zero γ
  have hcontinuous : Continuous (fun t : I ↦ (γ t).1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp γ.continuous)
  have hmaps : MapsTo (fun t : I ↦ (γ t).1.1) Set.univ
      (insert 0 RealTopology.positiveReciprocals) := by
    intro t _
    exact exampleB_first_mem_of_second_ne_zero (γ t) (hnonzero t)
  intro t
  have hfirstEq : (γ t).1.1 = (γ 0).1.1 :=
    eq_of_isPreconnected_mapsTo_countable isPreconnected_univ hcontinuous
      (countable_positiveReciprocals.insert 0) hmaps (mem_univ t) (mem_univ 0)
  have hsourceFirst : (γ 0).1.1 = 0 :=
    congrArg (fun q : quasicomponentExampleB ↦ q.1.1) γ.source
  have hfirst : (γ t).1.1 = 0 := hfirstEq.trans hsourceFirst
  -- The zero-fiber classification and nonzeroness force the upper endpoint value.
  rcases exampleB_second_mem_of_first_eq_zero (γ t) hfirst with hsecond | hsecond
  · exact ((hnonzero t) hsecond).elim
  · exact Subtype.ext (Prod.ext hfirst hsecond)

/-- Helper for Exercise 25.10: the upper limiting endpoint is a singleton path component. -/
lemma pathComponent_exampleB_upperEndpoint :
    pathComponent (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) =
      {(⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB)} := by
  -- Path rigidity gives the forward inclusion; reflexivity gives the reverse inclusion.
  apply Set.Subset.antisymm
  · intro q hq
    rw [mem_pathComponent_iff] at hq
    let γ := hq.somePath
    have hqEq : q = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) :=
      γ.target.symm.trans (exampleB_path_eq_upper γ 1)
    exact Set.mem_singleton_iff.mpr hqEq
  · intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact mem_pathComponent_self _

/-- Part (9) of Exercise 25.10: the upper limiting endpoint of `quasicomponentExampleB` is one path
component, and all remaining points form the other. -/
theorem pathComponent_exampleB (p : quasicomponentExampleB) :
    pathComponent p =
      if p.1 = (0, 1) then {p} else {q : quasicomponentExampleB | q.1 ≠ (0, 1)} := by
  -- Split off the singleton upper component; the remaining points are already path connected.
  by_cases hpUpper : p.1 = (0, 1)
  · rw [if_pos hpUpper]
    have hpEq : p = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) :=
      Subtype.ext hpUpper
    rw [hpEq, pathComponent_exampleB_upperEndpoint]
  · rw [if_neg hpUpper]
    apply Set.Subset.antisymm
    · intro q hq hqUpper
      have hqEq : q = (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) :=
        Subtype.ext hqUpper
      have hupperMem :
          (⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB) ∈
            pathComponent p := by
        rwa [← hqEq]
      have hcomponents := pathComponent_congr hupperMem
      have hpSingleton :
          p ∈ ({(⟨(0, 1), exampleB_upperEndpoint_mem⟩ : quasicomponentExampleB)} :
            Set quasicomponentExampleB) := by
        rw [← pathComponent_exampleB_upperEndpoint, hcomponents]
        exact mem_pathComponent_self p
      have hpEq := Set.mem_singleton_iff.mp hpSingleton
      exact hpUpper (congrArg Subtype.val hpEq)
    · exact isPathConnected_exampleB_withoutUpper.subset_pathComponent hpUpper

/-- Part (10) of Exercise 25.10: `quasicomponentExampleB` has one quasicomponent. -/
theorem quasicomponent_exampleB (p : quasicomponentExampleB) :
    quasicomponent p = Set.univ := by
  -- The unique connected component is contained in the quasicomponent.
  apply Set.eq_univ_of_univ_subset
  rw [← connectedComponent_exampleB p]
  exact connectedComponent_subset_quasicomponent p

/-- Helper for Exercise 25.10: a positive reciprocal lies in the unit interval. -/
lemma positiveReciprocal_mem_unitInterval {a : ℝ}
    (ha : a ∈ RealTopology.positiveReciprocals) : a ∈ Icc (0 : ℝ) 1 := by
  -- Write the reciprocal using a positive natural denominator and compare it with one.
  rw [RealTopology.mem_positiveReciprocals] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPositive : (0 : ℝ) < n := by exact_mod_cast hn
  have hInvPositive : 0 < (n : ℝ)⁻¹ := by positivity
  exact ⟨hInvPositive.le, (inv_le_one₀ hnPositive).mpr hnReal⟩

/-- Helper for Exercise 25.10: a negative reciprocal lies in `[-1, 0]`. -/
lemma negativeReciprocal_mem_negUnitInterval {a : ℝ}
    (ha : a ∈ negativeReciprocals) : a ∈ Icc (-1 : ℝ) 0 := by
  -- Negate the unit-interval bounds for the corresponding positive reciprocal.
  obtain ⟨b, hb, rfl⟩ := ha
  have hbIcc := positiveReciprocal_mem_unitInterval hb
  exact ⟨neg_le_neg hbIcc.2, neg_nonpos.mpr hbIcc.1⟩

/-- Helper for Exercise 25.10: every point of Example C lies on the same arm as itself. -/
lemma sameCArm_self (p : quasicomponentExampleC) : sameCArm p.1 p.1 := by
  -- Select the disjunct corresponding to the summand containing the point.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact Or.inl ⟨hp, hp, rfl⟩
      · exact Or.inr (Or.inl ⟨hp, hp, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hp, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hp, hp, rfl⟩))

/-- Helper for Exercise 25.10: the arm selected by `sameCArm` is path connected. -/
lemma isPathConnected_exampleC_sameCArm (p : quasicomponentExampleC) :
    IsPathConnected {q : quasicomponentExampleC | sameCArm p.1 q.1} := by
  -- Use `p` as the common base point and connect each target inside its asserted arm.
  refine ⟨p, sameCArm_self p, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · have hinterval : IsPathConnected (Icc (0 : ℝ) 1) :=
      (convex_Icc 0 1).isPathConnected (nonempty_Icc.mpr zero_le_one)
    have harm : IsPathConnected ({p.1.1} ×ˢ Icc (0 : ℝ) 1) :=
      (isPathConnected_singleton p.1.1).prod hinterval
    have hsubset : {p.1.1} ×ˢ Icc (0 : ℝ) 1 ⊆ quasicomponentExampleC := by
      intro z hz
      exact Or.inl (Or.inl (Or.inl ⟨hz.1 ▸ hq.1.1, hz.2⟩))
    have hpullback := harm.preimage_coe hsubset
    have hjoined := hpullback.joinedIn p ⟨rfl, hq.1.2⟩ q ⟨hq.2.2.symm, hq.2.1.2⟩
    refine hjoined.mono ?_
    intro z hz
    exact Or.inl ⟨hq.1, ⟨hz.1 ▸ hq.1.1, hz.2⟩, hz.1.symm⟩
  · rcases hq with hq | hq
    · have hnegOneZero : (-1 : ℝ) ≤ 0 := by norm_num
      have hinterval : IsPathConnected (Icc (-1 : ℝ) 0) :=
        (convex_Icc (-1) 0).isPathConnected (nonempty_Icc.mpr hnegOneZero)
      have harm : IsPathConnected ({p.1.1} ×ˢ Icc (-1 : ℝ) 0) :=
        (isPathConnected_singleton p.1.1).prod hinterval
      have hsubset : {p.1.1} ×ˢ Icc (-1 : ℝ) 0 ⊆ quasicomponentExampleC := by
        intro z hz
        exact Or.inl (Or.inl (Or.inr ⟨hz.1 ▸ hq.1.1, hz.2⟩))
      have hpullback := harm.preimage_coe hsubset
      have hjoined := hpullback.joinedIn p ⟨rfl, hq.1.2⟩ q
        ⟨hq.2.2.symm, hq.2.1.2⟩
      refine hjoined.mono ?_
      intro z hz
      exact Or.inr (Or.inl ⟨hq.1, ⟨hz.1 ▸ hq.1.1, hz.2⟩, hz.1.symm⟩)
    · rcases hq with hq | hq
      · have hinterval : IsPathConnected (Icc (0 : ℝ) 1) :=
          (convex_Icc 0 1).isPathConnected (nonempty_Icc.mpr zero_le_one)
        have harm : IsPathConnected (Icc (0 : ℝ) 1 ×ˢ {p.1.2}) :=
          hinterval.prod (isPathConnected_singleton p.1.2)
        have hsubset : Icc (0 : ℝ) 1 ×ˢ {p.1.2} ⊆ quasicomponentExampleC := by
          intro z hz
          exact Or.inl (Or.inr ⟨hz.1, hz.2 ▸ hq.1.2⟩)
        have hpullback := harm.preimage_coe hsubset
        have hjoined := hpullback.joinedIn p ⟨hq.1.1, rfl⟩ q
          ⟨hq.2.1.1, hq.2.2.symm⟩
        refine hjoined.mono ?_
        intro z hz
        exact Or.inr (Or.inr (Or.inl ⟨hq.1, ⟨hz.1, hz.2 ▸ hq.1.2⟩, hz.2.symm⟩))
      · have hnegOneZero : (-1 : ℝ) ≤ 0 := by norm_num
        have hinterval : IsPathConnected (Icc (-1 : ℝ) 0) :=
          (convex_Icc (-1) 0).isPathConnected (nonempty_Icc.mpr hnegOneZero)
        have harm : IsPathConnected (Icc (-1 : ℝ) 0 ×ˢ {p.1.2}) :=
          hinterval.prod (isPathConnected_singleton p.1.2)
        have hsubset : Icc (-1 : ℝ) 0 ×ˢ {p.1.2} ⊆ quasicomponentExampleC := by
          intro z hz
          exact Or.inr ⟨hz.1, hz.2 ▸ hq.1.2⟩
        have hpullback := harm.preimage_coe hsubset
        have hjoined := hpullback.joinedIn p ⟨hq.1.1, rfl⟩ q
          ⟨hq.2.1.1, hq.2.2.symm⟩
        refine hjoined.mono ?_
        intro z hz
        exact Or.inr (Or.inr (Or.inr ⟨hq.1, ⟨hz.1, hz.2 ▸ hq.1.2⟩, hz.2.symm⟩))

/-- Helper for Exercise 25.10: a clopen set containing a point contains its entire C-arm. -/
lemma sameCArm_subset_of_mem_isClopen {U : Set quasicomponentExampleC}
    (hU : IsClopen U) {p : quasicomponentExampleC} (hp : p ∈ U) :
    {q : quasicomponentExampleC | sameCArm p.1 q.1} ⊆ U := by
  -- A preconnected arm meeting a clopen set cannot meet its complement.
  exact (isPathConnected_exampleC_sameCArm p).isConnected.isPreconnected.subset_isClopen
    hU ⟨p, sameCArm_self p, hp⟩

/-- Helper for Exercise 25.10: a shifted reciprocal point lies on a positive vertical arm. -/
lemma exampleC_positiveVerticalPoint_mem (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ((((n + 1 : ℕ) : ℝ)⁻¹), b) ∈ quasicomponentExampleC := by
  -- Enter the first summand of Example C.
  exact Or.inl (Or.inl (Or.inl ⟨shiftedReciprocal_mem n, hb⟩))

/-- Helper for Exercise 25.10: the canonical point on a positive vertical arm. -/
noncomputable def exampleCPositiveVerticalPoint (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1)
    (n : ℕ) : quasicomponentExampleC :=
  ⟨((((n + 1 : ℕ) : ℝ)⁻¹), b), exampleC_positiveVerticalPoint_mem b hb n⟩

/-- Helper for Exercise 25.10: the ambient value of a canonical positive vertical point. -/
lemma exampleCPositiveVerticalPoint_coe (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (exampleCPositiveVerticalPoint b hb n : ℝ × ℝ) =
      ((((n + 1 : ℕ) : ℝ)⁻¹), b) := by
  -- Expose only the ambient coordinate pair of the subtype constructor.
  rfl

/-- Helper for Exercise 25.10: a shifted negative-reciprocal point lies on a negative
horizontal arm. -/
lemma exampleC_negativeHorizontalPoint_mem (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (a, -(((n + 1 : ℕ) : ℝ)⁻¹)) ∈ quasicomponentExampleC := by
  -- Enter the third summand, recording the negative reciprocal by its witness.
  exact Or.inl (Or.inr ⟨ha, ⟨_, shiftedReciprocal_mem n, rfl⟩⟩)

/-- Helper for Exercise 25.10: the canonical point on a negative horizontal arm. -/
noncomputable def exampleCNegativeHorizontalPoint (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (n : ℕ) : quasicomponentExampleC :=
  ⟨(a, -(((n + 1 : ℕ) : ℝ)⁻¹)), exampleC_negativeHorizontalPoint_mem a ha n⟩

/-- Helper for Exercise 25.10: the ambient value of a canonical negative horizontal point. -/
lemma exampleCNegativeHorizontalPoint_coe (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (exampleCNegativeHorizontalPoint a ha n : ℝ × ℝ) =
      (a, -(((n + 1 : ℕ) : ℝ)⁻¹)) := by
  -- Expose only the ambient coordinate pair of the subtype constructor.
  rfl

/-- Helper for Exercise 25.10: a shifted negative reciprocal point lies on a negative
vertical arm. -/
lemma exampleC_negativeVerticalPoint_mem (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 0) (n : ℕ) :
    (-(((n + 1 : ℕ) : ℝ)⁻¹), b) ∈ quasicomponentExampleC := by
  -- Enter the second summand, recording the negative reciprocal by its witness.
  exact Or.inl (Or.inl (Or.inr ⟨⟨_, shiftedReciprocal_mem n, rfl⟩, hb⟩))

/-- Helper for Exercise 25.10: the canonical point on a negative vertical arm. -/
noncomputable def exampleCNegativeVerticalPoint (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 0)
    (n : ℕ) : quasicomponentExampleC :=
  ⟨(-(((n + 1 : ℕ) : ℝ)⁻¹), b), exampleC_negativeVerticalPoint_mem b hb n⟩

/-- Helper for Exercise 25.10: the ambient value of a canonical negative vertical point. -/
lemma exampleCNegativeVerticalPoint_coe (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 0) (n : ℕ) :
    (exampleCNegativeVerticalPoint b hb n : ℝ × ℝ) =
      (-(((n + 1 : ℕ) : ℝ)⁻¹), b) := by
  -- Expose only the ambient coordinate pair of the subtype constructor.
  rfl

/-- Helper for Exercise 25.10: a shifted reciprocal point lies on a positive horizontal arm. -/
lemma exampleC_positiveHorizontalPoint_mem (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 0)
    (n : ℕ) : (a, (((n + 1 : ℕ) : ℝ)⁻¹)) ∈ quasicomponentExampleC := by
  -- Enter the fourth summand of Example C.
  exact Or.inr ⟨ha, shiftedReciprocal_mem n⟩

/-- Helper for Exercise 25.10: the canonical point on a positive horizontal arm. -/
noncomputable def exampleCPositiveHorizontalPoint (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 0)
    (n : ℕ) : quasicomponentExampleC :=
  ⟨(a, (((n + 1 : ℕ) : ℝ)⁻¹)), exampleC_positiveHorizontalPoint_mem a ha n⟩

/-- Helper for Exercise 25.10: the ambient value of a canonical positive horizontal point. -/
lemma exampleCPositiveHorizontalPoint_coe (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 0)
    (n : ℕ) :
    (exampleCPositiveHorizontalPoint a ha n : ℝ × ℝ) =
      (a, (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  -- Expose only the ambient coordinate pair of the subtype constructor.
  rfl

/-- Helper for Exercise 25.10: a clopen set containing a positive vertical arm contains
an eventual tail of the adjacent negative horizontal arms. -/
lemma eventually_negativeHorizontal_mem_of_positiveVertical_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1)
    (hpU : p ∈ U) :
    ∀ᶠ n in atTop,
      exampleCNegativeHorizontalPoint p.1.1
        (positiveReciprocal_mem_unitInterval hpArm.1) n ∈ U := by
  -- Fill the source arm down to the axis endpoint.
  have hbottomMem : (p.1.1, 0) ∈ quasicomponentExampleC :=
    Or.inl (Or.inl (Or.inl ⟨hpArm.1, ⟨le_rfl, zero_le_one⟩⟩))
  let bottom : quasicomponentExampleC := ⟨(p.1.1, 0), hbottomMem⟩
  have hbottomSame : sameCArm p.1 bottom.1 := by
    exact Or.inl ⟨hpArm, ⟨hpArm.1, ⟨le_rfl, zero_le_one⟩⟩, rfl⟩
  have hbottomU : bottom ∈ U := sameCArm_subset_of_mem_isClopen hU hpU hbottomSame
  -- Negative reciprocal levels converge to that endpoint inside the subtype.
  have hnegative :
      Tendsto (fun n : ℕ ↦ -(((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using tendsto_shiftedReciprocal_zero.neg
  have htendsto :
      Tendsto
        (exampleCNegativeHorizontalPoint p.1.1
          (positiveReciprocal_mem_unitInterval hpArm.1)) atTop (𝓝 bottom) := by
    rw [tendsto_subtype_rng]
    simpa only [exampleCNegativeHorizontalPoint_coe, bottom] using
      tendsto_const_nhds.prodMk_nhds hnegative
  exact htendsto (hU.2.mem_nhds hbottomU)

/-- Helper for Exercise 25.10: a clopen set containing a negative horizontal arm contains
an eventual tail of the adjacent negative vertical arms. -/
lemma eventually_negativeVertical_mem_of_negativeHorizontal_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ Icc (0 : ℝ) 1 ×ˢ negativeReciprocals) (hpU : p ∈ U) :
    ∀ᶠ n in atTop,
      exampleCNegativeVerticalPoint p.1.2
        (negativeReciprocal_mem_negUnitInterval hpArm.2) n ∈ U := by
  -- Fill the source arm leftward to its axis endpoint.
  have hleftMem : (0, p.1.2) ∈ quasicomponentExampleC :=
    Or.inl (Or.inr ⟨⟨le_rfl, zero_le_one⟩, hpArm.2⟩)
  let left : quasicomponentExampleC := ⟨(0, p.1.2), hleftMem⟩
  have hleftSame : sameCArm p.1 left.1 := by
    exact Or.inr (Or.inr (Or.inl
      ⟨hpArm, ⟨⟨le_rfl, zero_le_one⟩, hpArm.2⟩, rfl⟩))
  have hleftU : left ∈ U := sameCArm_subset_of_mem_isClopen hU hpU hleftSame
  -- Negative reciprocal first coordinates converge to that endpoint.
  have hnegative :
      Tendsto (fun n : ℕ ↦ -(((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using tendsto_shiftedReciprocal_zero.neg
  have htendsto :
      Tendsto
        (exampleCNegativeVerticalPoint p.1.2
          (negativeReciprocal_mem_negUnitInterval hpArm.2)) atTop (𝓝 left) := by
    rw [tendsto_subtype_rng]
    simpa only [exampleCNegativeVerticalPoint_coe, left] using
      hnegative.prodMk_nhds tendsto_const_nhds
  exact htendsto (hU.2.mem_nhds hleftU)

/-- Helper for Exercise 25.10: a clopen set containing a negative vertical arm contains
an eventual tail of the adjacent positive horizontal arms. -/
lemma eventually_positiveHorizontal_mem_of_negativeVertical_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ negativeReciprocals ×ˢ Icc (-1 : ℝ) 0) (hpU : p ∈ U) :
    ∀ᶠ n in atTop,
      exampleCPositiveHorizontalPoint p.1.1
        (negativeReciprocal_mem_negUnitInterval hpArm.1) n ∈ U := by
  -- Fill the source arm upward to its axis endpoint.
  have hnegOneZero : (-1 : ℝ) ≤ 0 := by norm_num
  have hzeroNegIcc : (0 : ℝ) ∈ Icc (-1 : ℝ) 0 := ⟨hnegOneZero, le_rfl⟩
  have htopMem : (p.1.1, 0) ∈ quasicomponentExampleC :=
    Or.inl (Or.inl (Or.inr ⟨hpArm.1, hzeroNegIcc⟩))
  let top : quasicomponentExampleC := ⟨(p.1.1, 0), htopMem⟩
  have htopSame : sameCArm p.1 top.1 := by
    exact Or.inr (Or.inl ⟨hpArm, ⟨hpArm.1, hzeroNegIcc⟩, rfl⟩)
  have htopU : top ∈ U := sameCArm_subset_of_mem_isClopen hU hpU htopSame
  -- Positive reciprocal heights converge to that endpoint.
  have htendsto :
      Tendsto
        (exampleCPositiveHorizontalPoint p.1.1
          (negativeReciprocal_mem_negUnitInterval hpArm.1)) atTop (𝓝 top) := by
    rw [tendsto_subtype_rng]
    simpa only [exampleCPositiveHorizontalPoint_coe, top] using
      tendsto_const_nhds.prodMk_nhds tendsto_shiftedReciprocal_zero
  exact htendsto (hU.2.mem_nhds htopU)

/-- Helper for Exercise 25.10: a clopen set containing a positive horizontal arm contains
an eventual tail of the adjacent positive vertical arms. -/
lemma eventually_positiveVertical_mem_of_positiveHorizontal_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ Icc (-1 : ℝ) 0 ×ˢ RealTopology.positiveReciprocals)
    (hpU : p ∈ U) :
    ∀ᶠ n in atTop,
      exampleCPositiveVerticalPoint p.1.2
        (positiveReciprocal_mem_unitInterval hpArm.2) n ∈ U := by
  -- Fill the source arm rightward to its axis endpoint.
  have hnegOneZero : (-1 : ℝ) ≤ 0 := by norm_num
  have hzeroNegIcc : (0 : ℝ) ∈ Icc (-1 : ℝ) 0 := ⟨hnegOneZero, le_rfl⟩
  have hrightMem : (0, p.1.2) ∈ quasicomponentExampleC :=
    Or.inr ⟨hzeroNegIcc, hpArm.2⟩
  let right : quasicomponentExampleC := ⟨(0, p.1.2), hrightMem⟩
  have hrightSame : sameCArm p.1 right.1 := by
    exact Or.inr (Or.inr (Or.inr
      ⟨hpArm, ⟨hzeroNegIcc, hpArm.2⟩, rfl⟩))
  have hrightU : right ∈ U := sameCArm_subset_of_mem_isClopen hU hpU hrightSame
  -- Positive reciprocal first coordinates converge to that endpoint.
  have htendsto :
      Tendsto
        (exampleCPositiveVerticalPoint p.1.2
          (positiveReciprocal_mem_unitInterval hpArm.2)) atTop (𝓝 right) := by
    rw [tendsto_subtype_rng]
    simpa only [exampleCPositiveVerticalPoint_coe, right] using
      tendsto_shiftedReciprocal_zero.prodMk_nhds tendsto_const_nhds
  exact htendsto (hU.2.mem_nhds hrightU)

/-- Helper for Exercise 25.10: a canonical positive vertical bottom endpoint belongs to C. -/
lemma exampleC_positiveVerticalBottom_mem (n : ℕ) :
    ((((n + 1 : ℕ) : ℝ)⁻¹), 0) ∈ quasicomponentExampleC := by
  -- Enter the positive vertical summand at height zero.
  exact Or.inl (Or.inl (Or.inl
    ⟨shiftedReciprocal_mem n, ⟨le_rfl, zero_le_one⟩⟩))

/-- Helper for Exercise 25.10: the canonical bottom endpoint of a positive vertical arm. -/
noncomputable def exampleCPositiveVerticalBottom (n : ℕ) : quasicomponentExampleC :=
  ⟨((((n + 1 : ℕ) : ℝ)⁻¹), 0), exampleC_positiveVerticalBottom_mem n⟩

/-- Helper for Exercise 25.10: the ambient value of a positive vertical bottom endpoint. -/
lemma exampleCPositiveVerticalBottom_coe (n : ℕ) :
    (exampleCPositiveVerticalBottom n : ℝ × ℝ) =
      ((((n + 1 : ℕ) : ℝ)⁻¹), 0) := by
  -- Expose only the ambient coordinate pair of the subtype constructor.
  rfl

/-- Helper for Exercise 25.10: an eventual tail on positive vertical arms can be moved
armwise to the canonical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_eventually_positiveVertical_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1)
    (h : ∀ᶠ n in atTop, exampleCPositiveVerticalPoint b hb n ∈ U) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- Fill each eventual positive vertical arm down to its canonical endpoint.
  filter_upwards [h] with n hn
  have hsourceArm :
      (exampleCPositiveVerticalPoint b hb n).1 ∈
        RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1 := by
    rw [exampleCPositiveVerticalPoint_coe]
    exact ⟨shiftedReciprocal_mem n, hb⟩
  have htargetArm :
      (exampleCPositiveVerticalBottom n).1 ∈
        RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1 := by
    rw [exampleCPositiveVerticalBottom_coe]
    exact ⟨shiftedReciprocal_mem n, ⟨le_rfl, zero_le_one⟩⟩
  have hsame : sameCArm (exampleCPositiveVerticalPoint b hb n).1
      (exampleCPositiveVerticalBottom n).1 := by
    exact Or.inl ⟨hsourceArm, htargetArm, rfl⟩
  exact sameCArm_subset_of_mem_isClopen hU hn hsame

/-- Helper for Exercise 25.10: membership of a positive horizontal arm propagates to
an eventual tail of canonical positive vertical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_positiveHorizontal_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ Icc (-1 : ℝ) 0 ×ˢ RealTopology.positiveReciprocals)
    (hpU : p ∈ U) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- Cross the positive-horizontal/positive-vertical corner, then normalize each arm.
  exact eventually_positiveVerticalBottom_mem_of_eventually_positiveVertical_mem hU
    (positiveReciprocal_mem_unitInterval hpArm.2)
    (eventually_positiveVertical_mem_of_positiveHorizontal_mem hU hpArm hpU)

/-- Helper for Exercise 25.10: membership of a negative vertical arm propagates to
an eventual tail of canonical positive vertical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_negativeVertical_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ negativeReciprocals ×ˢ Icc (-1 : ℝ) 0) (hpU : p ∈ U) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- First cross to a positive horizontal arm, then use the remaining corner.
  have htail := eventually_positiveHorizontal_mem_of_negativeVertical_mem hU hpArm hpU
  obtain ⟨n, hn⟩ := Filter.Eventually.exists htail
  have hnextArm :
      (exampleCPositiveHorizontalPoint p.1.1
        (negativeReciprocal_mem_negUnitInterval hpArm.1) n).1 ∈
          Icc (-1 : ℝ) 0 ×ˢ RealTopology.positiveReciprocals := by
    rw [exampleCPositiveHorizontalPoint_coe]
    exact ⟨negativeReciprocal_mem_negUnitInterval hpArm.1, shiftedReciprocal_mem n⟩
  exact eventually_positiveVerticalBottom_mem_of_positiveHorizontal_mem hU hnextArm hn

/-- Helper for Exercise 25.10: membership of a negative horizontal arm propagates to
an eventual tail of canonical positive vertical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_negativeHorizontal_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ Icc (0 : ℝ) 1 ×ˢ negativeReciprocals) (hpU : p ∈ U) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- First cross to a negative vertical arm, then continue around the two remaining corners.
  have htail := eventually_negativeVertical_mem_of_negativeHorizontal_mem hU hpArm hpU
  obtain ⟨n, hn⟩ := Filter.Eventually.exists htail
  have hnextArm :
      (exampleCNegativeVerticalPoint p.1.2
        (negativeReciprocal_mem_negUnitInterval hpArm.2) n).1 ∈
          negativeReciprocals ×ˢ Icc (-1 : ℝ) 0 := by
    rw [exampleCNegativeVerticalPoint_coe]
    exact ⟨⟨_, shiftedReciprocal_mem n, rfl⟩,
      negativeReciprocal_mem_negUnitInterval hpArm.2⟩
  exact eventually_positiveVerticalBottom_mem_of_negativeVertical_mem hU hnextArm hn

/-- Helper for Exercise 25.10: membership of a positive vertical arm propagates once
around the cycle to an eventual tail of canonical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_positiveVertical_mem
    {U : Set quasicomponentExampleC} (hU : IsClopen U) {p : quasicomponentExampleC}
    (hpArm : p.1 ∈ RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1)
    (hpU : p ∈ U) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- Cross first to a negative horizontal arm, then use the other three corners.
  have htail := eventually_negativeHorizontal_mem_of_positiveVertical_mem hU hpArm hpU
  obtain ⟨n, hn⟩ := Filter.Eventually.exists htail
  have hnextArm :
      (exampleCNegativeHorizontalPoint p.1.1
        (positiveReciprocal_mem_unitInterval hpArm.1) n).1 ∈
          Icc (0 : ℝ) 1 ×ˢ negativeReciprocals := by
    rw [exampleCNegativeHorizontalPoint_coe]
    exact ⟨positiveReciprocal_mem_unitInterval hpArm.1,
      ⟨_, shiftedReciprocal_mem n, rfl⟩⟩
  exact eventually_positiveVerticalBottom_mem_of_negativeHorizontal_mem hU hnextArm hn

/-- Helper for Exercise 25.10: every nonempty clopen subset of C contains a common
eventual tail of positive vertical bottom endpoints. -/
lemma eventually_positiveVerticalBottom_mem_of_isClopen
    {U : Set quasicomponentExampleC} (hU : IsClopen U) (hUnonempty : U.Nonempty) :
    ∀ᶠ n in atTop, exampleCPositiveVerticalBottom n ∈ U := by
  -- Start the cyclic propagation in whichever of the four summands contains the chosen point.
  obtain ⟨p, hpU⟩ := hUnonempty
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact eventually_positiveVerticalBottom_mem_of_positiveVertical_mem hU hp hpU
      · exact eventually_positiveVerticalBottom_mem_of_negativeVertical_mem hU hp hpU
    · exact eventually_positiveVerticalBottom_mem_of_negativeHorizontal_mem hU hp hpU
  · exact eventually_positiveVerticalBottom_mem_of_positiveHorizontal_mem hU hp hpU

/-- Helper for Exercise 25.10: every positive reciprocal is strictly positive. -/
lemma positiveReciprocal_pos {a : ℝ} (ha : a ∈ RealTopology.positiveReciprocals) : 0 < a := by
  -- Positivity follows immediately from the positive natural denominator.
  rw [RealTopology.mem_positiveReciprocals] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  positivity

/-- Helper for Exercise 25.10: every negative reciprocal is strictly negative. -/
lemma negativeReciprocal_neg {a : ℝ} (ha : a ∈ negativeReciprocals) : a < 0 := by
  -- Unpack the image under negation and use positivity of the original reciprocal.
  obtain ⟨b, hb, rfl⟩ := ha
  exact neg_neg_of_pos (positiveReciprocal_pos hb)

/-- Helper for Exercise 25.10: negating a negative reciprocal recovers a positive reciprocal. -/
lemma neg_mem_positiveReciprocals_of_mem_negativeReciprocals {a : ℝ}
    (ha : a ∈ negativeReciprocals) : -a ∈ RealTopology.positiveReciprocals := by
  -- The defining image witness becomes the desired value after double negation.
  obtain ⟨b, hb, rfl⟩ := ha
  simpa only [neg_neg] using hb

/-- Helper for Exercise 25.10: negating a positive reciprocal gives a negative reciprocal. -/
lemma neg_mem_negativeReciprocals_of_mem_positiveReciprocals {a : ℝ}
    (ha : a ∈ RealTopology.positiveReciprocals) : -a ∈ negativeReciprocals := by
  -- Use `a` itself as the image witness in the definition of negative reciprocals.
  exact ⟨a, ha, rfl⟩

/-- Helper for Exercise 25.10: a number is positive when its negation is negative. -/
lemma pos_of_neg_lt_zero {a : ℝ} (ha : -a < 0) : 0 < a := by
  -- Negate the strict inequality.
  linarith

/-- Helper for Exercise 25.10: the nonnegative upper-right part of C is precisely its
positive vertical family. -/
lemma exampleC_mem_positiveVertical_of_first_pos_second_nonneg
    (p : quasicomponentExampleC) (hx : 0 < p.1.1) (hy : 0 ≤ p.1.2) :
    p.1 ∈ RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1 := by
  -- The sign assumptions exclude the other three defining summands.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact hp
      · exact (not_lt_of_ge hx.le (negativeReciprocal_neg hp.1)).elim
    · exact (not_lt_of_ge hy (negativeReciprocal_neg hp.2)).elim
  · exact (not_lt_of_ge hp.1.2 hx).elim

/-- Helper for Exercise 25.10: the lower-right part of C is precisely its negative
horizontal family. -/
lemma exampleC_mem_negativeHorizontal_of_first_nonneg_second_neg
    (p : quasicomponentExampleC) (hx : 0 ≤ p.1.1) (hy : p.1.2 < 0) :
    p.1 ∈ Icc (0 : ℝ) 1 ×ˢ negativeReciprocals := by
  -- The sign assumptions exclude the two vertical and the positive horizontal summands.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact (not_lt_of_ge hp.2.1 hy).elim
      · exact (not_lt_of_ge hx (negativeReciprocal_neg hp.1)).elim
    · exact hp
  · exact (not_lt_of_ge hy.le (positiveReciprocal_pos hp.2)).elim

/-- Helper for Exercise 25.10: the nonpositive lower-left part of C is precisely its
negative vertical family. -/
lemma exampleC_mem_negativeVertical_of_first_neg_second_nonpos
    (p : quasicomponentExampleC) (hx : p.1.1 < 0) (hy : p.1.2 ≤ 0) :
    p.1 ∈ negativeReciprocals ×ˢ Icc (-1 : ℝ) 0 := by
  -- The sign assumptions exclude the positive vertical and both horizontal summands.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact (not_lt_of_ge (positiveReciprocal_pos hp.1).le hx).elim
      · exact hp
    · exact (not_lt_of_ge hp.1.1 hx).elim
  · exact (not_lt_of_ge hy (positiveReciprocal_pos hp.2)).elim

/-- Helper for Exercise 25.10: the upper-left part of C is precisely its positive
horizontal family. -/
lemma exampleC_mem_positiveHorizontal_of_first_nonpos_second_pos
    (p : quasicomponentExampleC) (hx : p.1.1 ≤ 0) (hy : 0 < p.1.2) :
    p.1 ∈ Icc (-1 : ℝ) 0 ×ˢ RealTopology.positiveReciprocals := by
  -- The sign assumptions exclude both vertical summands and the negative horizontal summand.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · exact (not_lt_of_ge hx (positiveReciprocal_pos hp.1)).elim
      · exact (not_lt_of_ge hp.2.2 hy).elim
    · exact (not_lt_of_ge (negativeReciprocal_neg hp.2).le hy).elim
  · exact hp

/-- Helper for Exercise 25.10: a continuous function starting nonnegative cannot acquire
a negative value when every negative value available on the interval is countable. -/
lemma continuous_nonnegative_of_negative_mem_countable {f : I → ℝ} (hf : Continuous f)
    {T : I} (hf0 : 0 ≤ f 0) {s : Set ℝ} (hs : s.Countable)
    (hnegative : ∀ t ∈ Icc (0 : I) T, f t < 0 → f t ∈ s) :
    ∀ t ∈ Icc (0 : I) T, 0 ≤ f t := by
  -- A negative endpoint would force a whole nondegenerate real interval into a countable set.
  intro t ht
  by_contra hft
  have hftNeg : f t < 0 := lt_of_not_ge hft
  have himage := intermediate_value_Icc' ht.1 hf.continuousOn
  have hintervalSubset : Icc (f t) 0 ⊆ insert 0 s := by
    intro z hz
    have hzFull : z ∈ Icc (f t) (f 0) := ⟨hz.1, hz.2.trans hf0⟩
    obtain ⟨r, hrInterval, hrValue⟩ := himage hzFull
    by_cases hzZero : z = 0
    · exact mem_insert_iff.mpr (Or.inl hzZero)
    · apply mem_insert_iff.mpr
      right
      have hrMem := hnegative r ⟨hrInterval.1, hrInterval.2.trans ht.2⟩
        (hrValue.trans_lt (lt_of_le_of_ne hz.2 hzZero))
      rwa [hrValue] at hrMem
  have hcountable : (Icc (f t) 0).Countable := (hs.insert 0).mono hintervalSubset
  exact hft ((Cardinal.Real.Icc_countable_iff).mp hcountable)

/-- Helper for Exercise 25.10: two countable coordinate barriers keep a continuous path
inside an oriented closed quadrant. -/
lemma continuous_staysIn_countableQuadrant {f g : I → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hf0 : 0 < f 0) (hg0 : 0 ≤ g 0)
    {positiveValues negativeValues : Set ℝ} (hpositiveCountable : positiveValues.Countable)
    (hnegativeCountable : negativeValues.Countable)
    (hnegative : ∀ t, 0 ≤ f t → g t < 0 → g t ∈ negativeValues)
    (hpositive : ∀ t, 0 < f t → 0 ≤ g t → f t ∈ positiveValues) :
    ∀ t, 0 < f t ∧ 0 ≤ g t := by
  -- First show that `f` cannot reach zero: before its least zero, the second barrier
  -- keeps `g` nonnegative and hence confines `f` to its countable positive values.
  have hfPositive : ∀ t, 0 < f t := by
    intro t
    by_contra hft
    let Z : Set I := {r : I | f r = 0}
    have hZclosed : IsClosed Z := isClosed_singleton.preimage hf
    have hZcompact : IsCompact Z := hZclosed.isCompact
    have hZnonempty : Z.Nonempty := by
      have htNonpos : f t ≤ 0 := le_of_not_gt hft
      have hzeroBetween : (0 : ℝ) ∈ Icc (f t) (f 0) := ⟨htNonpos, hf0.le⟩
      have htDomain : (0 : I) ≤ t := t.property.1
      have hzeroRange : 0 ∈ f '' Icc (0 : I) t := by
        exact (intermediate_value_Icc' (f := f) htDomain hf.continuousOn)
          hzeroBetween
      obtain ⟨r, _, hrZero⟩ := hzeroRange
      exact ⟨r, hrZero⟩
    obtain ⟨t₀, ht₀Zero, ht₀Min⟩ :=
      hZcompact.exists_isMinOn hZnonempty continuous_id.continuousOn
    have ht₀Ne : t₀ ≠ 0 := by
      intro ht₀
      subst t₀
      exact (ne_of_gt hf0) ht₀Zero
    have ht₀Pos : 0 < t₀ :=
      lt_of_le_of_ne (show (0 : I) ≤ t₀ from t₀.property.1) (Ne.symm ht₀Ne)
    have hbefore : ∀ r ∈ Ico (0 : I) t₀, 0 < f r := by
      intro r hr
      by_contra hfr
      have hfrNonpos : f r ≤ 0 := le_of_not_gt hfr
      have hzeroRange : 0 ∈ f '' Icc (0 : I) r := by
        apply intermediate_value_Icc' hr.1 hf.continuousOn
        exact ⟨hfrNonpos, hf0.le⟩
      obtain ⟨w, hwInterval, hwZero⟩ := hzeroRange
      have ht₀Le : t₀ ≤ w := ht₀Min hwZero
      exact (not_le_of_gt hr.2) (ht₀Le.trans hwInterval.2)
    have hfNonnegative : ∀ r ∈ Icc (0 : I) t₀, 0 ≤ f r := by
      intro r hr
      rcases lt_or_eq_of_le hr.2 with hrLt | hrEq
      · exact (hbefore r ⟨hr.1, hrLt⟩).le
      · subst r
        rw [ht₀Zero]
    have hgNonnegative : ∀ r ∈ Icc (0 : I) t₀, 0 ≤ g r :=
      continuous_nonnegative_of_negative_mem_countable hg hg0 hnegativeCountable
        (fun r hr hgr ↦ hnegative r (hfNonnegative r hr) hgr)
    have hmaps : MapsTo f (Icc (0 : I) t₀) (insert 0 positiveValues) := by
      intro r hr
      by_cases hrEq : r = t₀
      · subst r
        exact mem_insert_iff.mpr (Or.inl ht₀Zero)
      · apply mem_insert_iff.mpr
        right
        have hrLt : r < t₀ := lt_of_le_of_ne hr.2 hrEq
        exact hpositive r (hbefore r ⟨hr.1, hrLt⟩) (hgNonnegative r hr)
    have ht₀Mem : t₀ ∈ Icc (0 : I) t₀ := ⟨t₀.property.1, le_rfl⟩
    have hzeroMem : (0 : I) ∈ Icc (0 : I) t₀ := ⟨le_rfl, ht₀Pos.le⟩
    have heq : f t₀ = f 0 :=
      eq_of_isPreconnected_mapsTo_countable isPreconnected_Icc hf
        (hpositiveCountable.insert 0) hmaps ht₀Mem hzeroMem
    exact (ne_of_gt hf0) (heq.symm.trans ht₀Zero)
  -- With `f` everywhere positive, the first barrier globally keeps `g` nonnegative.
  intro t
  refine ⟨hfPositive t, ?_⟩
  exact continuous_nonnegative_of_negative_mem_countable hg hg0 hnegativeCountable
    (fun r _ hgr ↦ hnegative r (hfPositive r).le hgr) t ⟨t.property.1, le_rfl⟩

/-- Exercise 25.10 (11): The space `quasicomponentExampleC` has one connected component. -/
theorem connectedComponent_exampleC (p : quasicomponentExampleC) :
    connectedComponent p = Set.univ := by
  -- Cyclic arm propagation forces every nonempty clopen set and its complement to
  -- contain the same eventual tail, so a nontrivial clopen partition is impossible.
  have hpreconnected : PreconnectedSpace quasicomponentExampleC := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    rcases U.eq_empty_or_nonempty with hUempty | hUnonempty
    · exact Or.inl hUempty
    · right
      apply Set.eq_univ_of_univ_subset
      intro q _
      by_contra hqU
      have hcomplNonempty : Uᶜ.Nonempty := ⟨q, hqU⟩
      have htailU := eventually_positiveVerticalBottom_mem_of_isClopen hU hUnonempty
      have htailCompl :=
        eventually_positiveVerticalBottom_mem_of_isClopen hU.compl hcomplNonempty
      have hboth : ∀ᶠ n in atTop,
          exampleCPositiveVerticalBottom n ∈ U ∧
            exampleCPositiveVerticalBottom n ∈ Uᶜ := htailU.and htailCompl
      obtain ⟨n, hnU, hnCompl⟩ := Filter.Eventually.exists hboth
      exact hnCompl hnU
  -- The standard component characterization now turns preconnectedness into the result.
  exact preconnectedSpace_iff_connectedComponent.mp hpreconnected p

/-- Helper for Exercise 25.10: every path in C remains on the arm containing its source. -/
lemma exampleCPath_staysOnSourceArm {p q : quasicomponentExampleC} (γ : Path p q)
    (t : I) : sameCArm p.1 (γ t).1 := by
  -- Both ambient coordinates of the path are continuous.
  have hfirst : Continuous (fun s : I ↦ (γ s).1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp γ.continuous)
  have hsecond : Continuous (fun s : I ↦ (γ s).1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp γ.continuous)
  have hsourceFirst : (γ 0).1.1 = p.1.1 :=
    congrArg (fun z : quasicomponentExampleC ↦ z.1.1) γ.source
  have hsourceSecond : (γ 0).1.2 = p.1.2 :=
    congrArg (fun z : quasicomponentExampleC ↦ z.1.2) γ.source
  -- Orient the two coordinates according to the source family and apply the common
  -- countable-quadrant barrier.  The remaining arm coordinate is then constant.
  rcases p.property with hp | hp
  · rcases hp with hp | hp
    · rcases hp with hp | hp
      · have hfirstZero : 0 < (γ 0).1.1 := by
          rw [hsourceFirst]
          exact positiveReciprocal_pos hp.1
        have hsecondZero : 0 ≤ (γ 0).1.2 := by
          rw [hsourceSecond]
          exact hp.2.1
        have hquadrant : ∀ s : I, 0 < (γ s).1.1 ∧ 0 ≤ (γ s).1.2 :=
          continuous_staysIn_countableQuadrant hfirst hsecond hfirstZero hsecondZero
            countable_positiveReciprocals countable_negativeReciprocals
            (fun s hsFirst hsSecond ↦
              (exampleC_mem_negativeHorizontal_of_first_nonneg_second_neg
                (γ s) hsFirst hsSecond).2)
            (fun s hsFirst hsSecond ↦
              (exampleC_mem_positiveVertical_of_first_pos_second_nonneg
                (γ s) hsFirst hsSecond).1)
        have htargetArm (s : I) :
            (γ s).1 ∈ RealTopology.positiveReciprocals ×ˢ Icc (0 : ℝ) 1 :=
          exampleC_mem_positiveVertical_of_first_pos_second_nonneg
            (γ s) (hquadrant s).1 (hquadrant s).2
        have hmaps : MapsTo (fun s : I ↦ (γ s).1.1) Set.univ
            RealTopology.positiveReciprocals := by
          intro s _
          exact (htargetArm s).1
        have hcoordinate : (γ t).1.1 = p.1.1 :=
          (eq_of_isPreconnected_mapsTo_countable isPreconnected_univ hfirst
            countable_positiveReciprocals hmaps (mem_univ t) (mem_univ 0)).trans
              hsourceFirst
        exact Or.inl ⟨hp, htargetArm t, hcoordinate.symm⟩
      · have hfirstZero : 0 < -(γ 0).1.1 := by
          rw [hsourceFirst]
          exact neg_pos.mpr (negativeReciprocal_neg hp.1)
        have hsecondZero : 0 ≤ -(γ 0).1.2 := by
          rw [hsourceSecond]
          exact neg_nonneg.mpr hp.2.2
        have hquadrant : ∀ s : I, 0 < -(γ s).1.1 ∧ 0 ≤ -(γ s).1.2 :=
          continuous_staysIn_countableQuadrant hfirst.neg hsecond.neg
            hfirstZero hsecondZero countable_positiveReciprocals
            countable_negativeReciprocals
            (fun s hsFirst hsSecond ↦
              neg_mem_negativeReciprocals_of_mem_positiveReciprocals
                (exampleC_mem_positiveHorizontal_of_first_nonpos_second_pos
                  (γ s) (neg_nonneg.mp hsFirst) (pos_of_neg_lt_zero hsSecond)).2)
            (fun s hsFirst hsSecond ↦
              neg_mem_positiveReciprocals_of_mem_negativeReciprocals
                (exampleC_mem_negativeVertical_of_first_neg_second_nonpos
                  (γ s) (neg_pos.mp hsFirst) (neg_nonneg.mp hsSecond)).1)
        have htargetArm (s : I) :
            (γ s).1 ∈ negativeReciprocals ×ˢ Icc (-1 : ℝ) 0 :=
          exampleC_mem_negativeVertical_of_first_neg_second_nonpos
            (γ s) (neg_pos.mp (hquadrant s).1) (neg_nonneg.mp (hquadrant s).2)
        have hmaps : MapsTo (fun s : I ↦ (γ s).1.1) Set.univ negativeReciprocals := by
          intro s _
          exact (htargetArm s).1
        have hcoordinate : (γ t).1.1 = p.1.1 :=
          (eq_of_isPreconnected_mapsTo_countable isPreconnected_univ hfirst
            countable_negativeReciprocals hmaps (mem_univ t) (mem_univ 0)).trans
              hsourceFirst
        exact Or.inr (Or.inl ⟨hp, htargetArm t, hcoordinate.symm⟩)
    · have hfirstZero : 0 < -(γ 0).1.2 := by
        rw [hsourceSecond]
        exact neg_pos.mpr (negativeReciprocal_neg hp.2)
      have hsecondZero : 0 ≤ (γ 0).1.1 := by
        rw [hsourceFirst]
        exact hp.1.1
      have hquadrant : ∀ s : I, 0 < -(γ s).1.2 ∧ 0 ≤ (γ s).1.1 :=
        continuous_staysIn_countableQuadrant hsecond.neg hfirst
          hfirstZero hsecondZero countable_positiveReciprocals
          countable_negativeReciprocals
          (fun s hsFirst hsSecond ↦
            (exampleC_mem_negativeVertical_of_first_neg_second_nonpos
              (γ s) hsSecond (neg_nonneg.mp hsFirst)).1)
          (fun s hsFirst hsSecond ↦
            neg_mem_positiveReciprocals_of_mem_negativeReciprocals
              (exampleC_mem_negativeHorizontal_of_first_nonneg_second_neg
                (γ s) hsSecond (neg_pos.mp hsFirst)).2)
      have htargetArm (s : I) :
          (γ s).1 ∈ Icc (0 : ℝ) 1 ×ˢ negativeReciprocals :=
        exampleC_mem_negativeHorizontal_of_first_nonneg_second_neg
          (γ s) (hquadrant s).2 (neg_pos.mp (hquadrant s).1)
      have hmaps : MapsTo (fun s : I ↦ (γ s).1.2) Set.univ negativeReciprocals := by
        intro s _
        exact (htargetArm s).2
      have hcoordinate : (γ t).1.2 = p.1.2 :=
        (eq_of_isPreconnected_mapsTo_countable isPreconnected_univ hsecond
          countable_negativeReciprocals hmaps (mem_univ t) (mem_univ 0)).trans
            hsourceSecond
      exact Or.inr (Or.inr (Or.inl ⟨hp, htargetArm t, hcoordinate.symm⟩))
  · have hfirstZero : 0 < (γ 0).1.2 := by
      rw [hsourceSecond]
      exact positiveReciprocal_pos hp.2
    have hsecondZero : 0 ≤ -(γ 0).1.1 := by
      rw [hsourceFirst]
      exact neg_nonneg.mpr hp.1.2
    have hquadrant : ∀ s : I, 0 < (γ s).1.2 ∧ 0 ≤ -(γ s).1.1 :=
      continuous_staysIn_countableQuadrant hsecond hfirst.neg
        hfirstZero hsecondZero countable_positiveReciprocals countable_negativeReciprocals
        (fun s hsFirst hsSecond ↦
          neg_mem_negativeReciprocals_of_mem_positiveReciprocals
            (exampleC_mem_positiveVertical_of_first_pos_second_nonneg
              (γ s) (pos_of_neg_lt_zero hsSecond) hsFirst).1)
        (fun s hsFirst hsSecond ↦
          (exampleC_mem_positiveHorizontal_of_first_nonpos_second_pos
            (γ s) (neg_nonneg.mp hsSecond) hsFirst).2)
    have htargetArm (s : I) :
        (γ s).1 ∈ Icc (-1 : ℝ) 0 ×ˢ RealTopology.positiveReciprocals :=
      exampleC_mem_positiveHorizontal_of_first_nonpos_second_pos
        (γ s) (neg_nonneg.mp (hquadrant s).2) (hquadrant s).1
    have hmaps : MapsTo (fun s : I ↦ (γ s).1.2) Set.univ
        RealTopology.positiveReciprocals := by
      intro s _
      exact (htargetArm s).2
    have hcoordinate : (γ t).1.2 = p.1.2 :=
      (eq_of_isPreconnected_mapsTo_countable isPreconnected_univ hsecond
        countable_positiveReciprocals hmaps (mem_univ t) (mem_univ 0)).trans
          hsourceSecond
    exact Or.inr (Or.inr (Or.inr ⟨hp, htargetArm t, hcoordinate.symm⟩))

/-- Part (12) of Exercise 25.10: the path components of `quasicomponentExampleC` are its individual
vertical and horizontal arms. -/
theorem pathComponent_exampleC (p : quasicomponentExampleC) :
    pathComponent p = {q : quasicomponentExampleC | sameCArm p.1 q.1} := by
  -- Path rigidity gives the upper bound, while the selected arm is itself path connected.
  apply Set.Subset.antisymm
  · intro q hq
    rw [mem_pathComponent_iff] at hq
    let γ := hq.somePath
    have hsame := exampleCPath_staysOnSourceArm γ 1
    rw [γ.target] at hsame
    exact hsame
  · exact (isPathConnected_exampleC_sameCArm p).subset_pathComponent (sameCArm_self p)

/-- Part (13) of Exercise 25.10: `quasicomponentExampleC` has one quasicomponent. -/
theorem quasicomponent_exampleC (p : quasicomponentExampleC) :
    quasicomponent p = Set.univ := by
  -- The unique connected component is contained in the quasicomponent.
  apply Set.eq_univ_of_univ_subset
  rw [← connectedComponent_exampleC p]
  exact connectedComponent_subset_quasicomponent p
