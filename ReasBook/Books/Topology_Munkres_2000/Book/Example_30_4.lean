module

public import Topology_Munkres_2000.Book.Example_18_3
public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.DiscreteSubset

public section

/- Example 30.4 (1): The Sorgenfrey line is Lindelöf. -/
#check SorgenfreyLine.instLindelofSpace

namespace SorgenfreyPlane

/-- Helper for Example 30.4: the anti-diagonal in the Sorgenfrey plane. -/
private def sorgenfreyAntiDiagonal : Set (SorgenfreyLine × SorgenfreyLine) :=
  {p | SorgenfreyLine.toReal p.1 = -SorgenfreyLine.toReal p.2}

/-- Helper for Example 30.4: the Sorgenfrey anti-diagonal is closed. -/
private lemma sorgenfreyAntiDiagonal_isClosed : IsClosed sorgenfreyAntiDiagonal := by
  -- Express the anti-diagonal as the equality locus of continuous coordinate maps.
  exact isClosed_eq
    (SorgenfreyLine.continuous_toReal.comp continuous_fst)
    ((SorgenfreyLine.continuous_toReal.comp continuous_snd).neg)

/-- Helper for Example 30.4: the standard real parametrization lands in the anti-diagonal. -/
private lemma sorgenfreyAntiDiagonal_param_mem (r : ℝ) :
    (SorgenfreyLine.toReal.symm r, SorgenfreyLine.toReal.symm (-r)) ∈
      sorgenfreyAntiDiagonal := by
  -- Cancel the carrier equivalence in both coordinates.
  simp only [sorgenfreyAntiDiagonal, Set.mem_setOf_eq, Equiv.apply_symm_apply, neg_neg]

/-- Helper for Example 30.4: the real line parametrizes the Sorgenfrey anti-diagonal. -/
private def sorgenfreyAntiDiagonalParam (r : ℝ) : sorgenfreyAntiDiagonal :=
  ⟨(SorgenfreyLine.toReal.symm r, SorgenfreyLine.toReal.symm (-r)),
    sorgenfreyAntiDiagonal_param_mem r⟩

/-- Helper for Example 30.4: the canonical anti-diagonal parametrization is injective. -/
private lemma sorgenfreyAntiDiagonalParam_injective :
    Function.Injective sorgenfreyAntiDiagonalParam := by
  -- Equality of parametrized points forces equality of their first real coordinates.
  intro r s hrs
  have hfirst := congrArg
    (fun p : sorgenfreyAntiDiagonal ↦ SorgenfreyLine.toReal p.1.1) hrs
  simpa only [sorgenfreyAntiDiagonalParam, Equiv.apply_symm_apply] using hfirst

/-- Helper for Example 30.4: the induced topology on the Sorgenfrey anti-diagonal is discrete. -/
private lemma sorgenfreyAntiDiagonal_discreteTopology :
    DiscreteTopology sorgenfreyAntiDiagonal := by
  -- Isolate each point by a product of lower-limit basis intervals.
  rw [discreteTopology_subtype_iff']
  intro p hp
  have hfirstEndpoint : SorgenfreyLine.toReal p.1 < SorgenfreyLine.toReal p.1 + 1 := by
    linarith
  have hsecondEndpoint : SorgenfreyLine.toReal p.2 < SorgenfreyLine.toReal p.2 + 1 := by
    linarith
  refine ⟨(SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal p.1)
      (SorgenfreyLine.toReal p.1 + 1)) ×ˢ
    (SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal p.2)
      (SorgenfreyLine.toReal p.2 + 1)), ?_, ?_⟩
  · apply IsOpen.prod
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨SorgenfreyLine.toReal p.1, SorgenfreyLine.toReal p.1 + 1,
        hfirstEndpoint, rfl⟩
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨SorgenfreyLine.toReal p.2, SorgenfreyLine.toReal p.2 + 1,
        hsecondEndpoint, rfl⟩
  · ext q
    constructor
    · intro hqmem
      rcases hqmem with ⟨⟨⟨hqx, _⟩, ⟨hqy, _⟩⟩, hq⟩
      change SorgenfreyLine.toReal p.1 = -SorgenfreyLine.toReal p.2 at hp
      change SorgenfreyLine.toReal q.1 = -SorgenfreyLine.toReal q.2 at hq
      have hfirst : SorgenfreyLine.toReal q.1 = SorgenfreyLine.toReal p.1 := by
        linarith
      have hsecond : SorgenfreyLine.toReal q.2 = SorgenfreyLine.toReal p.2 := by
        linarith
      simpa only [Set.mem_singleton_iff] using Prod.ext (SorgenfreyLine.toReal.injective hfirst)
        (SorgenfreyLine.toReal.injective hsecond)
    · intro hqp
      rw [Set.mem_singleton_iff] at hqp
      subst q
      refine ⟨⟨?_, ?_⟩, hp⟩
      · exact ⟨le_rfl, hfirstEndpoint⟩
      · exact ⟨le_rfl, hsecondEndpoint⟩

/-- Helper for Example 30.4: the Sorgenfrey anti-diagonal is uncountable. -/
private lemma sorgenfreyAntiDiagonal_not_countable :
    ¬ sorgenfreyAntiDiagonal.Countable := by
  -- A hypothetical enumeration of the anti-diagonal would enumerate the real line.
  intro hcountable
  letI : Countable sorgenfreyAntiDiagonal := Set.countable_coe_iff.mpr hcountable
  have hreal : Countable ℝ := sorgenfreyAntiDiagonalParam_injective.countable
  exact not_countable hreal

/-- Example 30.4 (2): The Sorgenfrey plane is not Lindelöf. -/
instance instNonLindelofSpace : NonLindelofSpace (SorgenfreyLine × SorgenfreyLine) := by
  -- Restrict hypothetical Lindelöfness to the closed anti-diagonal.
  refine ⟨?_⟩
  intro huniv
  have hantiDiagonal : IsLindelof sorgenfreyAntiDiagonal :=
    huniv.of_isClosed_subset sorgenfreyAntiDiagonal_isClosed (Set.subset_univ _)
  -- A discrete Lindelöf subspace is countable, contradicting the real parametrization.
  exact sorgenfreyAntiDiagonal_not_countable
    (hantiDiagonal.countable sorgenfreyAntiDiagonal_discreteTopology)

/-- The Sorgenfrey plane does not carry a `LindelofSpace` instance. -/
theorem notLindelof : ¬ LindelofSpace (SorgenfreyLine × SorgenfreyLine) :=
  not_LindelofSpace_iff.mpr inferInstance

end SorgenfreyPlane
