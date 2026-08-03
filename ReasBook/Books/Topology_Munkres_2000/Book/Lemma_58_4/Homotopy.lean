module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

universe u v

namespace FundamentalGroup

open CategoryTheory

/-- Homotopic continuous maps induce fundamental-group homomorphisms related by
basepoint change along the path obtained by evaluating the homotopy. -/
theorem map_eq_basepointChange_comp_of_homotopy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {h k : C(X, Y)}
    (H : h.Homotopy k) (x₀ : X) :
    map k x₀ =
      (fundamentalGroupMulEquivOfPath (H.evalAt x₀)).toMonoidHom.comp (map h x₀) := by
  ext p
  let α : FundamentalGroupoid.mk (h x₀) ⟶ FundamentalGroupoid.mk (k x₀) := ⟦H.evalAt x₀⟧
  have naturality : (map h x₀) p ≫ α = α ≫ (map k x₀) p :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality p
  have basepointChange_apply :
      (fundamentalGroupMulEquivOfPath (H.evalAt x₀)).toMonoidHom ((map h x₀) p) =
        Groupoid.inv α ≫ (map h x₀) p ≫ α := rfl
  -- Naturality moves the loop across the path traced by `x₀`.
  rw [MonoidHom.comp_apply]
  have loop_eq :
      (map k x₀) p = Groupoid.inv α ≫ (map h x₀) p ≫ α := by
    calc
      (map k x₀) p = Groupoid.inv α ≫ α ≫ (map k x₀) p := by simp
      _ = Groupoid.inv α ≫ ((map h x₀) p ≫ α) := by rw [naturality]
  exact loop_eq.trans basepointChange_apply.symm

end FundamentalGroup
