module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Topology_Munkres_2000.Book.Theorem_19_1.Basis
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public section

/-- The rational sequences that are eventually zero, regarded as a named topological space. -/
@[expose]
def RationalEventuallyZeroBox := ℕ →₀ ℚ

namespace RationalEventuallyZeroBox

/-- The carrier equivalence with finitely supported rational sequences. -/
@[expose]
def toFinsupp : RationalEventuallyZeroBox ≃ (ℕ →₀ ℚ) := Equiv.refl _

/-- Coordinatewise inclusion of an eventually zero rational sequence into `ℕ → ℝ`. -/
@[expose]
def toRealSequence (x : RationalEventuallyZeroBox) : ℕ → ℝ :=
  fun n ↦ (toFinsupp x n : ℝ)

/-- Evaluation of the coordinatewise inclusion. -/
@[simp]
theorem toRealSequence_apply (x : RationalEventuallyZeroBox) (n : ℕ) :
    toRealSequence x n = toFinsupp x n := rfl

/-- The named space of eventually zero rational sequences is countable. -/
instance instCountable : Countable RationalEventuallyZeroBox :=
  toFinsupp.countable_iff.mpr inferInstance

/-- The subspace topology inherited from the box topology on `ℕ → ℝ`. -/
instance instTopologicalSpace : TopologicalSpace RationalEventuallyZeroBox :=
  TopologicalSpace.induced toRealSequence
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))

/-- The topology is induced by coordinatewise inclusion into the box product `ℕ → ℝ`. -/
theorem topology_eq_induced :
    (inferInstance : TopologicalSpace RationalEventuallyZeroBox) =
      TopologicalSpace.induced toRealSequence
        (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) := rfl

/-- Coordinatewise inclusion into the real sequence space is injective. -/
theorem toRealSequence_injective : Function.Injective toRealSequence := by
  intro x y h
  apply toFinsupp.injective
  ext n
  exact Rat.cast_injective (congrFun h n)

end RationalEventuallyZeroBox

namespace RationalEventuallyZeroBox

/-- Helper for Exercise 30.17: the carrier equivalence acts as the identity on finitely
supported rational sequences. -/
@[simp]
theorem toFinsupp_eq (x : RationalEventuallyZeroBox) : toFinsupp x = x := rfl

/-- Helper for Exercise 30.17: the zero eventually-zero rational sequence. -/
def zeroSequence : RationalEventuallyZeroBox := (0 : ℕ →₀ ℚ)

/-- Helper for Exercise 30.17: the zero sequence has real value zero at every coordinate. -/
@[simp]
theorem toRealSequence_zeroSequence (n : ℕ) : toRealSequence zeroSequence n = 0 := by
  -- Compute through the carrier equivalence once, avoiding later definitional unfolding.
  rw [toRealSequence_apply, toFinsupp_eq]
  exact Rat.cast_zero

/-- Helper for Exercise 30.17: a singleton finitely supported sequence has its chosen
real value at the selected coordinate. -/
@[simp]
theorem toRealSequence_single_same (n : ℕ) (q : ℚ) :
    toRealSequence (Finsupp.single n q) n = q := by
  -- Reduce coordinatewise inclusion to the standard singleton computation.
  rw [toRealSequence_apply, toFinsupp_eq, Finsupp.single_eq_same]

/-- Helper for Exercise 30.17: a singleton finitely supported sequence is zero away from
its selected coordinate. -/
@[simp]
theorem toRealSequence_single_of_ne {i n : ℕ} (hin : i ≠ n) (q : ℚ) :
    toRealSequence (Finsupp.single n q) i = 0 := by
  -- Reduce coordinatewise inclusion to the standard off-diagonal singleton computation.
  rw [toRealSequence_apply, toFinsupp_eq, Finsupp.single_eq_of_ne hin]
  exact Rat.cast_zero

/-- Helper for Exercise 30.17: every neighborhood of zero contains the preimage of an
ambient coordinatewise open box. -/
theorem exists_box_preimage_subset_nhds_zero {U : Set RationalEventuallyZeroBox}
    (hU : U ∈ nhds zeroSequence) :
    ∃ V : ℕ → Set ℝ,
      (∀ i, IsOpen (V i)) ∧ (∀ i, 0 ∈ V i) ∧
        toRealSequence ⁻¹' Set.pi Set.univ V ⊆ U := by
  -- Pass to the ambient neighborhood supplied by the induced topology.
  have hUinduced :
      U ∈ @nhds RationalEventuallyZeroBox
        (TopologicalSpace.induced toRealSequence
          (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))) zeroSequence := hU
  obtain ⟨O, hOnhds, hOU⟩ :=
    (mem_nhds_induced (T := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      toRealSequence zeroSequence U).mp hUinduced
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  have hb := (Pi.isTopologicalBasis_boxBasis :
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)).IsTopologicalBasis
      (Pi.boxBasis (fun _ : ℕ ↦ ℝ)))
  obtain ⟨s, hs, hzero, hsO⟩ := hb.mem_nhds_iff.mp hOnhds
  obtain ⟨V, hVopen, rfl⟩ := (Pi.mem_boxBasis s).mp hs
  -- Read coordinatewise zero membership from membership in the ambient box.
  refine ⟨V, hVopen, ?_, ?_⟩
  · intro i
    have hzeroCoordinate := hzero i (Set.mem_univ i)
    rwa [toRealSequence_zeroSequence] at hzeroCoordinate
  · intro x hx
    exact hOU (hsO hx)

/-- Helper for Exercise 30.17: a countable family of ambient open boxes at zero misses
one diagonal open neighborhood at every stage. -/
theorem exists_diagonal_box_not_containing (V : ℕ → ℕ → Set ℝ)
    (hVopen : ∀ n i, IsOpen (V n i)) (hVzero : ∀ n i, 0 ∈ V n i) :
    ∃ W : Set RationalEventuallyZeroBox,
      IsOpen W ∧ zeroSequence ∈ W ∧
        ∀ n, ¬ (toRealSequence ⁻¹' Set.pi Set.univ (V n)) ⊆ W := by
  -- Choose a positive rational coordinate inside each diagonal neighborhood.
  classical
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  have hVnhds : ∀ n, V n n ∈ nhds (0 : ℝ) := by
    intro n
    exact (hVopen n n).mem_nhds (hVzero n n)
  choose r hrpos hrsub using fun n ↦ Metric.mem_nhds_iff.mp (hVnhds n)
  choose q hqpos hqlt using fun n ↦ exists_pos_rat_lt (hrpos n)
  let D : ℕ → Set ℝ := fun n ↦ Metric.ball 0 ((q n : ℝ) / 2)
  let W : Set RationalEventuallyZeroBox :=
    toRealSequence ⁻¹' Set.pi Set.univ D
  refine ⟨W, ?_, ?_, ?_⟩
  · -- The induced topology makes the preimage of the diagonal ambient box open.
    exact @isOpen_induced RationalEventuallyZeroBox (ℕ → ℝ)
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) toRealSequence _
      (Pi.isOpen_box D fun _ ↦ Metric.isOpen_ball)
  · -- Positivity of every chosen rational radius puts zero in the diagonal box.
    intro n _
    simp only [D, toRealSequence_zeroSequence, Metric.mem_ball, dist_self]
    have hqreal : (0 : ℝ) < q n := Rat.cast_pos.mpr (hqpos n)
    linarith
  · intro n
    -- The finitely supported sequence with only coordinate `n` nonzero lies in box `n`.
    let z : RationalEventuallyZeroBox := Finsupp.single n (q n)
    have hzV : z ∈ toRealSequence ⁻¹' Set.pi Set.univ (V n) := by
      intro i _
      by_cases hin : i = n
      · subst i
        apply hrsub n
        simpa [z, Metric.mem_ball, Real.dist_eq,
          abs_of_pos (Rat.cast_pos.mpr (hqpos n) : (0 : ℝ) < q n)] using hqlt n
      · have hzCoordinate : toRealSequence z i = 0 :=
          toRealSequence_single_of_ne hin (q n)
        rw [hzCoordinate]
        exact hVzero n i
    have hzW : z ∉ W := by
      intro hz
      have hcoord := hz n (Set.mem_univ n)
      simp only [D, z, toRealSequence_single_same, Metric.mem_ball, Real.dist_eq,
        sub_zero] at hcoord
      have hqreal : (0 : ℝ) < q n := Rat.cast_pos.mpr (hqpos n)
      rw [abs_of_pos hqreal] at hcoord
      linarith
    exact fun hsubset ↦ hzW (hsubset hzV)

end RationalEventuallyZeroBox

/-- Exercise 30.17 (1): The eventually zero rational sequences in the box product
do not satisfy the first countability axiom. -/
theorem rationalEventuallyZeroBox_not_firstCountable :
    ¬FirstCountableTopology RationalEventuallyZeroBox := by
  -- A hypothetical first-countable structure gives a countable neighborhood basis at zero.
  intro hfirst
  letI : FirstCountableTopology RationalEventuallyZeroBox := hfirst
  obtain ⟨U, hUbasis⟩ :=
    Filter.exists_antitone_basis (nhds RationalEventuallyZeroBox.zeroSequence)
  have hUnhds : ∀ n, U n ∈ nhds RationalEventuallyZeroBox.zeroSequence := hUbasis.mem
  choose V hVopen hVzero hVU using fun n ↦
    RationalEventuallyZeroBox.exists_box_preimage_subset_nhds_zero (hUnhds n)
  obtain ⟨W, hWopen, hWzero, hVW⟩ :=
    RationalEventuallyZeroBox.exists_diagonal_box_not_containing V hVopen hVzero
  have hWnhds : W ∈ nhds RationalEventuallyZeroBox.zeroSequence := hWopen.mem_nhds hWzero
  obtain ⟨n, hUnW⟩ := hUbasis.mem_iff.mp hWnhds
  -- The refined box lies in `U n`, contradicting its diagonal obstruction.
  exact hVW n (Set.Subset.trans (hVU n) hUnW)

/-- Exercise 30.17 (2): The eventually zero rational sequences in the box product
do not satisfy the second countability axiom. -/
theorem rationalEventuallyZeroBox_not_secondCountable :
    ¬SecondCountableTopology RationalEventuallyZeroBox := by
  -- Second countability supplies first countability, contradicting the preceding theorem.
  intro hsecond
  letI : SecondCountableTopology RationalEventuallyZeroBox := hsecond
  exact rationalEventuallyZeroBox_not_firstCountable inferInstance

/- Exercise 30.17 (3): The eventually zero rational sequences in the box product
satisfy the separability axiom. -/
#check (inferInstance : TopologicalSpace.SeparableSpace RationalEventuallyZeroBox)

/- Exercise 30.17 (4): The eventually zero rational sequences in the box product
satisfy the Lindelöf axiom. -/
#check (inferInstance : LindelofSpace RationalEventuallyZeroBox)
