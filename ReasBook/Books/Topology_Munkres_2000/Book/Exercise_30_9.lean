module

public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Exercise_16_8
public import Topology_Munkres_2000.Book.Exercise_30_9.Antidiagonal

public section

open Set

/- Exercise 30.9 (1): A closed subspace of a Lindelöf space is Lindelöf. -/
#check IsClosed.isLindelof

/- Exercise 30.9 (2): The Sorgenfrey plane has a countable dense subset. -/
#check (inferInstance : TopologicalSpace.SeparableSpace (SorgenfreyLine × SorgenfreyLine))

namespace SorgenfreyPlane

/-- Helper for Exercise 30.9: the carrier map from the Sorgenfrey line to `ℝ` is continuous. -/
lemma continuousToReal : Continuous SorgenfreyLine.toReal := by
  -- Refine each usual open neighborhood to a lower-limit interval at the same point.
  rw [continuous_def]
  intro s hs
  refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hx
  obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
  refine ⟨Set.Ico (SorgenfreyLine.toReal x) b, ?_, ?_, ?_⟩
  · exact ⟨SorgenfreyLine.toReal x, b, hxab.2, rfl⟩
  · exact Set.left_mem_Ico.mpr hxab.2
  · intro y hy
    exact hab ⟨hxab.1.trans_le hy.1, hy.2⟩

/-- Helper for Exercise 30.9: the antidiagonal is closed in the Sorgenfrey plane. -/
theorem isClosed_antiDiagonal : IsClosed antiDiagonal := by
  -- Express the antidiagonal as the equality locus of two continuous coordinate maps.
  have heq : antiDiagonal =
      {point | SorgenfreyLine.toReal point.2 = -SorgenfreyLine.toReal point.1} := by
    ext point
    exact mem_antiDiagonal_iff point
  rw [heq]
  exact isClosed_eq (continuousToReal.comp continuous_snd)
    (continuousToReal.comp continuous_fst).neg

/-- Helper for Exercise 30.9: the antidiagonal has the discrete subspace topology. -/
lemma antiDiagonalDiscreteTopology : DiscreteTopology antiDiagonal := by
  -- Identify the antidiagonal with the affine graph of negative slope `-1`.
  rw [antiDiagonal_eq_graphLine]
  have hnegative : (-1 : ℝ) < 0 := by
    norm_num
  exact SorgenfreyAffineLine.graphDiscreteOfNeg (-1) 0 hnegative

/-- Helper for Exercise 30.9: the standard coordinate pair lies on the antidiagonal. -/
lemma realParamPoint_mem (x : ℝ) :
    (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x)) ∈ antiDiagonal := by
  -- Verify the defining coordinate equation of the antidiagonal.
  rw [mem_antiDiagonal_iff]
  simp only [Equiv.apply_symm_apply]

/-- Helper for Exercise 30.9: the canonical real parameterization of the antidiagonal. -/
def antiDiagonalParam (x : ℝ) : antiDiagonal :=
  ⟨(SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x)), realParamPoint_mem x⟩

/-- Helper for Exercise 30.9: the canonical real parameterization is injective. -/
lemma antiDiagonalParam_injective : Function.Injective antiDiagonalParam := by
  -- Equality on the antidiagonal determines equality of the first real coordinates.
  intro x y hxy
  have hfirst := congrArg (fun point : antiDiagonal ↦
    SorgenfreyLine.toReal point.1.1) hxy
  simpa only [antiDiagonalParam, Equiv.apply_symm_apply] using hfirst

/-- Exercise 30.9 (4): The antidiagonal, with its subspace topology, has no countable
dense subset. -/
theorem antiDiagonal_not_separable :
    ¬ TopologicalSpace.SeparableSpace antiDiagonal := by
  -- A separable discrete space has countable underlying type.
  intro hseparable
  letI : DiscreteTopology antiDiagonal := antiDiagonalDiscreteTopology
  letI : Countable antiDiagonal :=
    TopologicalSpace.separableSpace_iff_countable.mp hseparable
  -- Pull countability back along the injective real parameterization.
  have hreal : Countable ℝ := antiDiagonalParam_injective.countable
  exact Cardinal.not_countable_real Set.countable_univ

end SorgenfreyPlane
