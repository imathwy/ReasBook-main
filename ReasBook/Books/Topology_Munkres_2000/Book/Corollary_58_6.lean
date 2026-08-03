module

public import Topology_Munkres_2000.Book.Corollary_58_5
public import Mathlib.Topology.Homotopy.Contractible

public section

universe u v

open FundamentalGroup.LeftToRight

/-- Helper for Corollary 58.6: a constant map sends every loop class to the
constant loop class. -/
private lemma quotientMap_const
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} (p : Path.Homotopic.Quotient x₀ x₀) (y : Y) :
    Path.Homotopic.Quotient.map p (ContinuousMap.const X y) =
      Path.Homotopic.Quotient.refl y := by
  -- Reduce to a representative and identify its constant image pointwise.
  induction p using Path.Homotopic.Quotient.ind with
  | mk path =>
      rw [← Path.Homotopic.Quotient.mk_map]
      congr 1

namespace FundamentalGroup.LeftToRight

/-- Helper for Corollary 58.6: the homomorphism induced by a constant map is
the trivial homomorphism. -/
lemma map_const
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y : Y) : ((ContinuousMap.const X y)₍x₀₎)₊ = 1 := by
  -- Compare values after removing the opposite-group wrapper.
  ext p
  apply MulOpposite.unop_injective
  rw [map_apply, FundamentalGroup.map_apply, quotientMap_const]
  exact FundamentalGroup.one_def.symm

end FundamentalGroup.LeftToRight

/-- Corollary 58.6. A nullhomotopic continuous map induces the trivial
fundamental-group homomorphism at every chosen source basepoint. -/
theorem fundamentalGroupMap_eq_one_of_nullhomotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X, Y)) (x₀ : X) (h_nullhomotopic : h.Nullhomotopic) :
    (h₍x₀₎)₊ = 1 := by
  -- Express the nullhomotopy as a homotopy to a constant map.
  obtain ⟨y, homotopic⟩ := h_nullhomotopic
  -- Reverse that homotopy and transport the constant map's triviality by Corollary 58.5.
  exact fundamentalGroupMap_eq_one_of_homotopic
    (ContinuousMap.const X y) h x₀ homotopic.symm (FundamentalGroup.LeftToRight.map_const x₀ y)
