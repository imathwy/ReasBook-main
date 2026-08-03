module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap
import Topology_Munkres_2000.Book.Lemma_58_4.Homotopy

public section

universe u v

namespace FundamentalGroup

/-- Lemma 58.4. Homotopic continuous maps induce fundamental-group homomorphisms
related by basepoint change along the path traced by the source basepoint. -/
theorem exists_path_map_eq_basepointChange_comp_of_homotopic
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x₀ : X) (homotopic : h.Homotopic k) :
    ∃ α : Path (h x₀) (k x₀),
      (k₍x₀₎)₊ = (LeftToRight.mulEquivOfPath α).toMonoidHom.comp (h₍x₀₎)₊ := by
  -- Expose the homotopy whose trace at `x₀` supplies the basepoint-change path.
  rcases homotopic with ⟨H⟩
  refine ⟨H.evalAt x₀, ?_⟩
  -- Transport the canonical induced-map identity to the book's left-to-right convention.
  exact congrArg MonoidHom.op (map_eq_basepointChange_comp_of_homotopy H x₀)

end FundamentalGroup
