import Mathlib.Topology.Order.ProjIcc
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_4_2

open scoped unitInterval
open unitInterval

universe u

/-- Helper for Theorem 6.4.5: the endpoint `{0} ⊆ I` is a DR-pair. -/
lemma zeroSingletonIsDRPair : IsDRPair ({0} : Set I) := by
  let control : C(I, I) :=
    { toFun := fun x ↦ Set.projIcc 0 1 zero_le_one (((1 / 2 : ℝ) * x : ℝ))
      continuous_toFun := continuous_projIcc.comp (continuous_const.mul continuous_subtype_val) }
  have hContHomotopyMap :
      Continuous fun p : I × I ↦ Set.projIcc 0 1 zero_le_one (((1 : ℝ) - p.2) * p.1) := by
    exact continuous_projIcc.comp
      ((continuous_const.sub ((continuous_subtype_val.comp continuous_snd))).mul
        (continuous_subtype_val.comp continuous_fst))
  let retract : C(I, I) := ContinuousMap.const I (0 : I)
  let homotopyMap : C(I × I, I) :=
    { toFun := fun p ↦ Set.projIcc 0 1 zero_le_one (((1 : ℝ) - p.2) * p.1)
      continuous_toFun := hContHomotopyMap }
  have hZero : ∀ x : I, homotopyMap (x, 0) = x := by
    intro x
    apply Subtype.ext
    simp [homotopyMap, Set.projIcc_of_mem]
  have hOne : ∀ x : I, homotopyMap (x, 1) = retract x := by
    intro x
    apply Subtype.ext
    simp [homotopyMap, retract]
  let homotopy : (ContinuousMap.id I).Homotopy retract :=
    ContinuousMap.Homotopy.ofProdSwap homotopyMap hZero hOne
  have hRel :
      (ContinuousMap.id I).HomotopyRel retract ({0} : Set I) := by
    refine ⟨homotopy, ?_⟩
    intro t x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simp [homotopy, homotopyMap, retract, ContinuousMap.Homotopy.ofProdSwap]
  have hZeroSet : control ⁻¹' ({0} : Set I) = ({0} : Set I) := by
    ext x
    constructor
    · intro hx
      have hxle : (((1 / 2 : ℝ) * x : ℝ)) ≤ 0 := by
        simpa [control, projIcc_eq_zero] using hx
      have hxReal : (x : ℝ) = 0 := by
        nlinarith [x.2.1, hxle]
      exact Set.mem_singleton_iff.mpr (Subtype.ext hxReal)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [control]
  have hEndpoint : ∀ x : I, control x < 1 → retract x ∈ ({0} : Set I) := by
    intro x hx
    simp [retract]
  have hControlLtOne : ∀ x : I, control x < 1 := by
    intro x
    have hhalf : ((1 / 2 : ℝ)) ∈ I := by
      constructor <;> norm_num
    have hmem : (((1 / 2 : ℝ) * x : ℝ)) ∈ I := unitInterval.mul_mem hhalf x.2
    have hx : (((1 / 2 : ℝ) * x : ℝ)) < 1 := by
      nlinarith [x.2.2]
    change Set.projIcc 0 1 zero_le_one (((1 / 2 : ℝ) * x : ℝ)) < (1 : I)
    rw [Set.projIcc_of_mem _ hmem]
    simpa using hx
  let witness : DRPair ({0} : Set I) :=
    { control := control
      retract := retract
      homotopy := hRel
      zeroSet_eq := hZeroSet
      endpoint_mem := hEndpoint
      control_lt_one := hControlLtOne }
  exact ⟨witness⟩
