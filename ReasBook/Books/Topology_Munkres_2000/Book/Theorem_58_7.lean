module

public import Topology_Munkres_2000.Book.Lemma_58_4
public import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv

public section

universe u v

namespace ContinuousMap.HomotopyEquiv

/-- Helper for Theorem 58.7: with reflexive basepoint equality, `mapOfEq` is the
ordinary induced map at the source basepoint. -/
private lemma fundamentalGroupMapOfEq_refl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  -- Evaluate both homomorphisms on a loop and remove the reflexive endpoint cast.
  ext γ
  simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Theorem 58.7. A homotopy equivalence `e : X ≃ₕ Y` carrying `x₀` to `y₀`
induces a bijective homomorphism from `π₁(X, x₀)` to `π₁(Y, y₀)`. -/
theorem fundamentalGroupMapOfEq_bijective {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (x₀ : X) (y₀ : Y) (hxy : e x₀ = y₀) :
    Function.Bijective (FundamentalGroup.mapOfEq e.toFun hxy) := by
  -- Identify the named target basepoint with the actual image of `x₀`.
  cases hxy
  -- Normalize the now-reflexive transport and invoke bijectivity at the image basepoint.
  rw [fundamentalGroupMapOfEq_refl]
  exact fundamentalGroupMap_bijective e x₀

end ContinuousMap.HomotopyEquiv

end
