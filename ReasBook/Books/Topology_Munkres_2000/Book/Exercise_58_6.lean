module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Topology.Homotopy.Contractible

public section

universe u

namespace Set

variable {X : Type u} [TopologicalSpace X] [ContractibleSpace X] {A : Set X}

namespace Retraction

/-- A concrete retraction of a contractible space has contractible target. -/
theorem contractibleSpace (r : Retraction A) : ContractibleSpace A := by
  rw [contractible_iff_id_nullhomotopic]
  let inclusion : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have h_null : (r.toContinuousMap.comp inclusion).Nullhomotopic :=
    (id_nullhomotopic X).comp_right r.toContinuousMap |>.comp_left inclusion
  have h_comp : r.toContinuousMap.comp inclusion = ContinuousMap.id A := by
    ext a
    exact congrArg Subtype.val (r.apply_coe a)
  simpa only [h_comp] using h_null

end Retraction

namespace IsRetract

/-- Exercise 58.6: A retract of a contractible space is contractible. -/
theorem contractibleSpace (hA : IsRetract A) : ContractibleSpace A := by
  rw [isRetract_iff] at hA
  obtain ⟨r, hr⟩ := hA
  exact (Retraction.mk r hr).contractibleSpace

end IsRetract

end Set

end
