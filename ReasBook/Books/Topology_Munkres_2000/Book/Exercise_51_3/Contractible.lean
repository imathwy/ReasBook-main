module

public import Topology_Munkres_2000.Book.Notation_51_2
public import Mathlib.Analysis.Convex.Contractible

public section

universe u v

namespace unitInterval

/-- The unit interval is contractible. -/
instance instContractibleSpace : ContractibleSpace unitInterval := by
  -- The interval is a nonempty convex subset of the real line.
  exact (convex_Icc (0 : ℝ) 1).contractibleSpace (Set.nonempty_Icc.mpr zero_le_one)

end unitInterval

namespace ContinuousMap

/-- Any two continuous maps into a contractible space are homotopic. -/
theorem homotopic_of_contractible_codomain {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace Y]
    (f g : C(X, Y)) : f.Homotopic g := by
  -- Compose the contraction of `Y` with each map to reach one common constant map.
  obtain ⟨y, contraction⟩ := id_nullhomotopic Y
  have hf : f.Homotopic (ContinuousMap.const X y) := by
    simpa using contraction.comp (.refl f)
  have hg : g.Homotopic (ContinuousMap.const X y) := by
    simpa using contraction.comp (.refl g)
  -- Concatenate through that common constant map.
  exact hf.trans hg.symm

/-- Any two continuous maps from a contractible space into a path-connected space are
homotopic. -/
theorem homotopic_of_contractible_domain {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
    [PathConnectedSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  -- Contract the domain to one point, reducing both maps to constant maps.
  obtain ⟨x, contraction⟩ := id_nullhomotopic X
  have hf : f.Homotopic (ContinuousMap.const X (f x)) := by
    simpa using (.comp (.refl f) contraction)
  have hg : g.Homotopic (ContinuousMap.const X (g x)) := by
    simpa using (.comp (.refl g) contraction)
  -- Path connectedness joins the two values and hence the corresponding constant maps.
  have hconst : (ContinuousMap.const X (f x)).Homotopic (ContinuousMap.const X (g x)) :=
    ContinuousMap.homotopic_const_iff.mpr (PathConnectedSpace.joined (f x) (g x))
  exact hf.trans (hconst.trans hg.symm)

end ContinuousMap

namespace ContinuousMap.Homotopic.Quotient

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Ordinary homotopy classes of maps into a contractible space form a subsingleton. -/
instance instSubsingletonOfContractibleCodomain [ContractibleSpace Y] :
    Subsingleton ⟦X, Y⟧ₕ where
  allEq a b := by
    obtain ⟨f, rfl⟩ := mk_surjective a
    obtain ⟨g, rfl⟩ := mk_surjective b
    exact eq.mpr (ContinuousMap.homotopic_of_contractible_codomain f g)

/-- Ordinary homotopy classes of maps from a contractible space to a path-connected space form a
subsingleton. -/
instance instSubsingletonOfContractibleDomain [ContractibleSpace X] [PathConnectedSpace Y] :
    Subsingleton ⟦X, Y⟧ₕ where
  allEq a b := by
    obtain ⟨f, rfl⟩ := mk_surjective a
    obtain ⟨g, rfl⟩ := mk_surjective b
    exact eq.mpr (ContinuousMap.homotopic_of_contractible_domain f g)

/-- Ordinary homotopy classes of maps into a contractible space have exactly one element. -/
theorem nonemptyUniqueOfContractibleCodomain [ContractibleSpace Y] :
    Nonempty (Unique ⟦X, Y⟧ₕ) := by
  rw [unique_iff_subsingleton_and_nonempty]
  exact ⟨inferInstance, ⟨mk (ContinuousMap.const X (Classical.choice inferInstance))⟩⟩

/-- Ordinary homotopy classes of maps from a contractible space to a path-connected space have
exactly one element. -/
theorem nonemptyUniqueOfContractibleDomain [ContractibleSpace X] [PathConnectedSpace Y] :
    Nonempty (Unique ⟦X, Y⟧ₕ) := by
  rw [unique_iff_subsingleton_and_nonempty]
  exact ⟨inferInstance, ⟨mk (ContinuousMap.const X (Classical.choice inferInstance))⟩⟩

end ContinuousMap.Homotopic.Quotient
