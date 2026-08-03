module

public import Topology_Munkres_2000.Book.Definition_6_0_3.CountablyLocallyFinite
public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.WithTopology

public section

open Set

/-- The cylinder determined by a cutoff and a binary choice at every later coordinate. -/
def binaryTailCylinder (n : ℕ) (bits : Set.Ioi n → Bool) : Set UniformRealSequence :=
  {x | ∀ i : Set.Ioi n, x.ofTopology i = if bits i then 1 else 0}

/-- Membership in a binary tail cylinder is the corresponding coordinatewise condition. -/
theorem mem_binaryTailCylinder_iff {n : ℕ} {bits : Set.Ioi n → Bool}
    {x : UniformRealSequence} :
    x ∈ binaryTailCylinder n bits ↔
      ∀ i : Set.Ioi n, x.ofTopology i = if bits i then 1 else 0 :=
  Iff.rfl

/-- Construction for Exercise 39.6: the collection `𝓑ₙ` of all cylinders whose coordinates after `n`
are independently fixed to `0` or `1`. -/
def binaryTailCylinders (n : ℕ) : Set (Set UniformRealSequence) :=
  Set.range (binaryTailCylinder n)

/-- Membership in `binaryTailCylinders n` means being determined by some binary tail. -/
theorem mem_binaryTailCylinders_iff {n : ℕ} {s : Set UniformRealSequence} :
    s ∈ binaryTailCylinders n ↔
      ∃ bits : Set.Ioi n → Bool, binaryTailCylinder n bits = s :=
  Iff.rfl

/-- Construction for Exercise 39.6: the collection `𝓑` is the union of the collections `𝓑ₙ`. -/
def binaryTailCylinderFamily : Set (Set UniformRealSequence) :=
  ⋃ n, binaryTailCylinders n

/-- Membership in the full binary-tail family means membership at some finite cutoff. -/
theorem mem_binaryTailCylinderFamily_iff {s : Set UniformRealSequence} :
    s ∈ binaryTailCylinderFamily ↔
      ∃ n : ℕ, ∃ bits : Set.Ioi n → Bool, binaryTailCylinder n bits = s := by
  simp [binaryTailCylinderFamily, binaryTailCylinders]

/-- Helper for Exercise 39.6: the sequence canonically realizing prescribed binary tail data. -/
def binaryTailPoint (n : ℕ) (bits : Set.Ioi n → Bool) : UniformRealSequence :=
  WithTopology.toTopology (UniformMetric.topology ℕ) fun k ↦
    if hk : k ∈ Set.Ioi n then if bits ⟨k, hk⟩ then 1 else 0 else 0

/-- Helper for Exercise 39.6: the canonical binary-tail point belongs to its cylinder. -/
theorem binaryTailPoint_mem (n : ℕ) (bits : Set.Ioi n → Bool) :
    binaryTailPoint n bits ∈ binaryTailCylinder n bits := by
  -- At every constrained coordinate, the cutoff test selects the prescribed bit.
  intro i
  unfold binaryTailPoint
  rw [WithTopology.ofTopology_toTopology, dif_pos i.property]

/-- Helper for Exercise 39.6: distinct fixed-cutoff cylinders are uniformly distance `1` apart. -/
theorem dist_eq_one_of_mem_binaryTailCylinders {n : ℕ}
    {bits bits' : Set.Ioi n → Bool} (hbits : bits ≠ bits')
    {x y : UniformRealSequence} (hx : x ∈ binaryTailCylinder n bits)
    (hy : y ∈ binaryTailCylinder n bits') :
    (UniformMetric.metricSpace ℕ).dist x.ofTopology y.ofTopology = 1 := by
  -- A differing tail coordinate contributes the maximal truncated distance.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hbits
  apply le_antisymm
  · exact UniformMetric.dist_le_one _ _
  · rw [UniformMetric.dist_eq]
    have hbounded :
        BddAbove (Set.range fun j ↦ min (dist (x.ofTopology j) (y.ofTopology j)) 1) := by
      refine ⟨1, Set.forall_mem_range.mpr fun j ↦ min_le_right _ _⟩
    calc
      1 = min (dist (x.ofTopology i) (y.ofTopology i)) 1 := by
        rw [hx i, hy i]
        cases hbi : bits i <;> cases hb'i : bits' i <;> simp_all
      _ ≤ ⨆ j, min (dist (x.ofTopology j) (y.ofTopology j)) 1 :=
        le_ciSup hbounded i

/-- Helper for Exercise 39.6: the binary-tail cylinder constructor is injective at each cutoff. -/
theorem binaryTailCylinder_injective (n : ℕ) :
    Function.Injective (binaryTailCylinder n) := by
  -- Equality of cylinders lets the canonical point for one tail test every coordinate of the other.
  intro bits bits' hsets
  funext i
  have hmem : binaryTailPoint n bits ∈ binaryTailCylinder n bits' := by
    rw [← hsets]
    exact binaryTailPoint_mem n bits
  have hcoordinate := hmem i
  unfold binaryTailPoint at hcoordinate
  rw [WithTopology.ofTopology_toTopology, dif_pos i.property] at hcoordinate
  cases hbi : bits i <;> cases hb'i : bits' i <;> simp_all

/-- Helper for Exercise 39.6: subsets of `ℕ` encoded on the positive tail coordinates. -/
noncomputable def positiveTailBits (s : Set ℕ) : Set.Ioi 0 → Bool :=
  fun i ↦ s.boolIndicator (i.1 - 1)

/-- Helper for Exercise 39.6: the positive-coordinate subset encoding is injective. -/
theorem positiveTailBits_injective : Function.Injective positiveTailBits := by
  -- Evaluating at `k + 1` recovers membership of `k` in the encoded subset.
  intro s t hbits
  ext k
  have hcoordinate := congrFun hbits ⟨k + 1, Nat.zero_lt_succ k⟩
  unfold positiveTailBits at hcoordinate
  rw [Nat.add_sub_cancel] at hcoordinate
  rw [s.mem_iff_boolIndicator, t.mem_iff_boolIndicator, hcoordinate]

/-- Helper for Exercise 39.6: the zero-tail cylinder at cutoff `n` belongs to the full family. -/
theorem zeroTailCylinder_mem_family (n : ℕ) :
    binaryTailCylinder n (fun _ ↦ false) ∈ binaryTailCylinderFamily := by
  -- The cylinder occurs in the `n`th fixed-cutoff subcollection.
  rw [mem_binaryTailCylinderFamily_iff]
  exact ⟨n, fun _ ↦ false, rfl⟩

/-- Helper for Exercise 39.6: zero-tail cylinders at distinct cutoffs are distinct. -/
theorem zeroTailCylinders_injective :
    Function.Injective (fun n : ℕ ↦ binaryTailCylinder n (fun _ ↦ false)) := by
  -- A sequence supported at the larger cutoff separates two unequal cutoffs.
  intro m n hsets
  apply Nat.le_antisymm
  · by_contra hnm
    have hmn : n < m := Nat.lt_of_not_ge hnm
    let x : UniformRealSequence :=
      WithTopology.toTopology (UniformMetric.topology ℕ) fun k ↦ if k = m then 1 else 0
    have hx : x ∈ binaryTailCylinder m (fun _ ↦ false) := by
      intro i
      simp [x, Nat.ne_of_gt i.property]
    have hx' : x ∈ binaryTailCylinder n (fun _ ↦ false) := by
      change binaryTailCylinder m (fun _ ↦ false) =
        binaryTailCylinder n (fun _ ↦ false) at hsets
      rw [← hsets]
      exact hx
    have hcoordinate := hx' ⟨m, hmn⟩
    simp [x] at hcoordinate
  · by_contra hmn
    have hnm : m < n := Nat.lt_of_not_ge hmn
    let x : UniformRealSequence :=
      WithTopology.toTopology (UniformMetric.topology ℕ) fun k ↦ if k = n then 1 else 0
    have hx : x ∈ binaryTailCylinder n (fun _ ↦ false) := by
      intro i
      simp [x, Nat.ne_of_gt i.property]
    have hx' : x ∈ binaryTailCylinder m (fun _ ↦ false) := by
      change binaryTailCylinder m (fun _ ↦ false) =
        binaryTailCylinder n (fun _ ↦ false) at hsets
      rw [hsets]
      exact hx
    have hcoordinate := hx' ⟨n, hnm⟩
    simp [x] at hcoordinate

/-- Companion to Exercise 39.6: Each fixed-cutoff collection of binary tail cylinders is locally
finite in the uniform topology. -/
theorem locallyFinite_binaryTailCylinders (n : ℕ) :
    (binaryTailCylinders n).LocallyFinite := by
  -- A pulled-back uniform ball of radius `1/3` can meet at most one cylinder.
  rw [Set.locallyFinite_iff]
  intro x
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  let U : Set UniformRealSequence :=
    WithTopology.ofTopology ⁻¹' Metric.ball x.ofTopology (1 / 3 : ℝ)
  have hU : U ∈ nhds x := by
    apply
      (@WithTopology.continuous_ofTopology (ℕ → ℝ) (UniformMetric.topology ℕ)).continuousAt
        |>.preimage_mem_nhds
    exact Metric.ball_mem_nhds _ (by norm_num)
  refine ⟨U, hU, Set.Subsingleton.finite ?_⟩
  intro A hA B hB
  obtain ⟨bits, rfl⟩ := hA.1
  obtain ⟨bits', rfl⟩ := hB.1
  by_contra hsets
  have hbits : bits ≠ bits' := by
    intro h
    exact hsets (congrArg (binaryTailCylinder n) h)
  obtain ⟨a, ha, haU⟩ := hA.2
  obtain ⟨b, hb, hbU⟩ := hB.2
  have hab : dist a.ofTopology b.ofTopology = 1 :=
    dist_eq_one_of_mem_binaryTailCylinders hbits ha hb
  have ha_close : dist a.ofTopology x.ofTopology < 1 / 3 := haU
  have hb_close : dist x.ofTopology b.ofTopology < 1 / 3 := by
    rw [dist_comm]
    exact hbU
  have htriangle := dist_triangle a.ofTopology x.ofTopology b.ofTopology
  rw [hab] at htriangle
  linarith

/-- Companion to Exercise 39.6: The binary-tail cylinder family is countably locally finite in the
uniform topology. -/
theorem countablyLocallyFinite_binaryTailCylinderFamily :
    binaryTailCylinderFamily.CountablyLocallyFinite := by
  -- The defining cutoff decomposition is countable, and every piece is locally finite.
  rw [Set.countablyLocallyFinite_iff]
  exact ⟨binaryTailCylinders, rfl, locallyFinite_binaryTailCylinders⟩

/-- Companion to Exercise 39.6: The binary-tail cylinder family is not countable. -/
theorem not_countable_binaryTailCylinderFamily :
    ¬binaryTailCylinderFamily.Countable := by
  -- Pull countability back through two injections to contradict Cantor's theorem.
  intro hcountable
  classical
  have hfixed : (binaryTailCylinders 0).Countable := by
    apply hcountable.mono
    exact subset_iUnion binaryTailCylinders 0
  have htails : (Set.univ : Set (Set.Ioi 0 → Bool)).Countable := by
    simpa [binaryTailCylinders] using
      hfixed.preimage (binaryTailCylinder_injective 0)
  have hsubsets : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using htails.preimage positiveTailBits_injective
  obtain ⟨f, hf⟩ := hsubsets.exists_surjective Set.univ_nonempty
  let g : ℕ → Set ℕ := fun k ↦ (f k).1
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨k, hk⟩ := hf ⟨s, Set.mem_univ s⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact Function.cantor_surjective g hg

/-- Companion to Exercise 39.6: The binary-tail cylinder family is not locally finite in the
uniform topology. -/
theorem not_locallyFinite_binaryTailCylinderFamily :
    ¬binaryTailCylinderFamily.LocallyFinite := by
  -- Local finiteness would make the cylinders through zero point-finite.
  intro hlocal
  let z : UniformRealSequence := WithTopology.toTopology (UniformMetric.topology ℕ) 0
  have hpoint := (_root_.LocallyFinite.point_finite hlocal z)
  let f : ℕ → binaryTailCylinderFamily := fun n ↦
    ⟨binaryTailCylinder n (fun _ ↦ false), zeroTailCylinder_mem_family n⟩
  have hf : Function.Injective f := by
    intro m n hmn
    apply zeroTailCylinders_injective
    exact congrArg Subtype.val hmn
  have hrange : Set.range f ⊆ {A : binaryTailCylinderFamily | z ∈ A.1} := by
    intro A hA
    obtain ⟨n, rfl⟩ := hA
    simp [f, z, mem_binaryTailCylinder_iff]
  exact Set.infinite_range_of_injective hf (hpoint.subset hrange)


/-- Exercise 39.6: The collections `𝓑ₙ` are locally finite, while their union `𝓑` is
countably locally finite but neither countable nor locally finite. -/
theorem «locallyFinite_binaryTailCylinders, countablyLocallyFinite_binaryTailCylinderFamily,
    not_countable_binaryTailCylinderFamily, not_locallyFinite_binaryTailCylinderFamily» :
    (∀ n, (binaryTailCylinders n).LocallyFinite) ∧
      binaryTailCylinderFamily.CountablyLocallyFinite ∧
      ¬binaryTailCylinderFamily.Countable ∧
      ¬binaryTailCylinderFamily.LocallyFinite := by
  -- Bundle the four named conclusions into the exercise-level entry point.
  exact ⟨locallyFinite_binaryTailCylinders,
    countablyLocallyFinite_binaryTailCylinderFamily,
    not_countable_binaryTailCylinderFamily,
    not_locallyFinite_binaryTailCylinderFamily⟩
