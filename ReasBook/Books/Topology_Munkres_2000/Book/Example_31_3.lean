module

public import Topology_Munkres_2000.Book.Example_18_3
public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.NotNormal

public section

open scoped Cardinal

namespace SorgenfreyPlane

/-- Helper for Example 31.3: the anti-diagonal in the Sorgenfrey plane. -/
private def sorgenfreyAntiDiagonal : Set (SorgenfreyLine × SorgenfreyLine) :=
  {p | SorgenfreyLine.toReal p.1 = -SorgenfreyLine.toReal p.2}

/-- Helper for Example 31.3: the Sorgenfrey anti-diagonal is closed. -/
private lemma sorgenfreyAntiDiagonal_isClosed : IsClosed sorgenfreyAntiDiagonal := by
  -- Realize the anti-diagonal as the equality locus of two continuous coordinate maps.
  exact isClosed_eq
    (SorgenfreyLine.continuous_toReal.comp continuous_fst)
    ((SorgenfreyLine.continuous_toReal.comp continuous_snd).neg)

/-- Helper for Example 31.3: the standard real parametrization lands in the anti-diagonal. -/
private lemma sorgenfreyAntiDiagonal_param_mem (r : ℝ) :
    (SorgenfreyLine.toReal.symm r, SorgenfreyLine.toReal.symm (-r)) ∈
      sorgenfreyAntiDiagonal := by
  -- The carrier equivalence cancels on both coordinates.
  simp only [sorgenfreyAntiDiagonal, Set.mem_setOf_eq, Equiv.apply_symm_apply, neg_neg]

/-- Helper for Example 31.3: the real line parametrizes the Sorgenfrey anti-diagonal. -/
private def sorgenfreyAntiDiagonalParam (r : ℝ) : sorgenfreyAntiDiagonal :=
  ⟨(SorgenfreyLine.toReal.symm r, SorgenfreyLine.toReal.symm (-r)),
    sorgenfreyAntiDiagonal_param_mem r⟩

/-- Helper for Example 31.3: the canonical anti-diagonal parametrization is injective. -/
private lemma sorgenfreyAntiDiagonalParam_injective :
    Function.Injective sorgenfreyAntiDiagonalParam := by
  -- Equality of parametrized points forces equality of their first real coordinates.
  intro r s hrs
  have hfirst := congrArg
    (fun p : sorgenfreyAntiDiagonal ↦ SorgenfreyLine.toReal p.1.1) hrs
  simpa only [sorgenfreyAntiDiagonalParam, Equiv.apply_symm_apply] using hfirst

/-- Helper for Example 31.3: the induced topology on the Sorgenfrey anti-diagonal is discrete. -/
private lemma sorgenfreyAntiDiagonal_discreteTopology :
    DiscreteTopology sorgenfreyAntiDiagonal := by
  -- Isolate each point by a product of lower-limit basis intervals.
  rw [discreteTopology_subtype_iff']
  intro p hp
  refine ⟨(SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal p.1)
      (SorgenfreyLine.toReal p.1 + 1)) ×ˢ
    (SorgenfreyLine.toReal ⁻¹' Set.Ico (SorgenfreyLine.toReal p.2)
      (SorgenfreyLine.toReal p.2 + 1)), ?_, ?_⟩
  · apply IsOpen.prod
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨SorgenfreyLine.toReal p.1, SorgenfreyLine.toReal p.1 + 1, by linarith, rfl⟩
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨SorgenfreyLine.toReal p.2, SorgenfreyLine.toReal p.2 + 1, by linarith, rfl⟩
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
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨le_rfl, by linarith⟩

/-- Helper for Example 31.3: the Sorgenfrey anti-diagonal has cardinality at least continuum. -/
private lemma continuum_le_mk_sorgenfreyAntiDiagonal :
    𝔠 ≤ Cardinal.mk sorgenfreyAntiDiagonal := by
  -- Embed the real line by its canonical anti-diagonal parametrization.
  simpa only [Cardinal.mk_real] using
    Cardinal.mk_le_of_injective sorgenfreyAntiDiagonalParam_injective

/-- Example 31.3: The Sorgenfrey plane is not normal. -/
theorem notNormal : ¬ NormalSpace (SorgenfreyLine × SorgenfreyLine) := by
  -- Apply the separable-space obstruction to the closed discrete anti-diagonal.
  letI : DiscreteTopology sorgenfreyAntiDiagonal :=
    sorgenfreyAntiDiagonal_discreteTopology
  exact sorgenfreyAntiDiagonal_isClosed.not_normal_of_continuum_le_mk
    continuum_le_mk_sorgenfreyAntiDiagonal

/-- The Sorgenfrey plane is not normal in Munkres' `T4Space` convention. -/
theorem notT4 : ¬ T4Space (SorgenfreyLine × SorgenfreyLine) := by
  intro h
  exact notNormal h.toNormalSpace

end SorgenfreyPlane
