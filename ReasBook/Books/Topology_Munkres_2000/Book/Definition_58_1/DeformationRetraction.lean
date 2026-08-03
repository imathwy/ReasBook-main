module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Topology.Homotopy.Basic

public section

universe u

namespace Set

open unitInterval

variable {X : Type u} [TopologicalSpace X]

namespace Retraction

/-- The ambient self-map obtained by following a retraction with the subtype inclusion. -/
@[expose]
def toAmbient {A : Set X} (r : Retraction A) : C(X, X) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp r.toContinuousMap

/-- Evaluating the ambient self-map of a retraction gives the underlying point in `X`. -/
@[simp]
theorem toAmbient_apply {A : Set X} (r : Retraction A) (x : X) :
    r.toAmbient x = r.apply x := rfl

end Retraction

/-- Concrete data of a deformation retraction of `X` onto `A`. -/
structure DeformationRetraction (A : Set X) where
  /-- The endpoint retraction onto `A`. -/
  toRetraction : Retraction A
  /-- A homotopy from the identity to the ambient endpoint map, fixed on `A`. -/
  toHomotopyRel : ContinuousMap.HomotopyRel
    (ContinuousMap.id X) toRetraction.toAmbient A

namespace DeformationRetraction

/-- Construct a deformation retraction from endpoint and relative-homotopy data. -/
def ofHomotopyRel {A : Set X} (r : Retraction A)
    (H : ContinuousMap.HomotopyRel (ContinuousMap.id X) r.toAmbient A) :
    DeformationRetraction A :=
  ⟨r, H⟩

/-- Evaluate a deformation retraction through its underlying homotopy. -/
@[expose]
def apply {A : Set X} (H : DeformationRetraction A) (t : unitInterval) (x : X) : X :=
  H.toHomotopyRel (t, x)

/-- A deformation retraction starts at the identity map. -/
@[simp]
theorem apply_zero {A : Set X} (H : DeformationRetraction A) (x : X) :
    H.apply 0 x = x := H.toHomotopyRel.apply_zero x

/-- A deformation retraction ends at the ambient map of its retraction. -/
@[simp]
theorem apply_one {A : Set X} (H : DeformationRetraction A) (x : X) :
    H.apply 1 x = H.toRetraction.toAmbient x := H.toHomotopyRel.apply_one x

/-- The endpoint of a deformation retraction lies in its target subset. -/
theorem apply_one_mem {A : Set X} (H : DeformationRetraction A) (x : X) :
    H.apply 1 x ∈ A := by
  rw [H.apply_one]
  exact (H.toRetraction.apply x).2

/-- A deformation retraction fixes every point of the target subset throughout. -/
@[simp]
theorem apply_of_mem {A : Set X} (H : DeformationRetraction A)
    {x : X} (hx : x ∈ A) (t : unitInterval) : H.apply t x = x :=
  H.toHomotopyRel.eq_fst t hx

end DeformationRetraction

/-- A subset is a deformation retract when it admits deformation-retraction data. -/
def IsDeformationRetract (A : Set X) : Prop :=
  Nonempty (DeformationRetraction A)

/-- A subset is a deformation retract exactly when a retraction and a relative homotopy exist. -/
theorem isDeformationRetract_iff (A : Set X) :
    IsDeformationRetract A ↔
      ∃ r : Retraction A,
        ContinuousMap.HomotopicRel (ContinuousMap.id X) r.toAmbient A := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toRetraction, ⟨H.toHomotopyRel⟩⟩
  · rintro ⟨r, ⟨H⟩⟩
    exact ⟨DeformationRetraction.ofHomotopyRel r H⟩

/-- Every deformation retract is a retract. -/
theorem IsDeformationRetract.isRetract {A : Set X} (hA : IsDeformationRetract A) :
    IsRetract A := by
  apply (isRetract_iff A).2
  obtain ⟨H⟩ := hA
  exact ⟨H.toRetraction.toContinuousMap, H.toRetraction.leftInverse⟩

end Set
