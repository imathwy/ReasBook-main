module

public import Mathlib.GroupTheory.Finiteness

public section

universe u v

namespace Group

/-- An indexed family generates a group when its range generates the top subgroup. -/
def Generates {G : Type u} [Group G] {J : Type v} (a : J → G) : Prop :=
  Subgroup.closure (Set.range a) = ⊤

/-- The defining closure condition for an indexed generating family. -/
theorem generates_iff {G : Type u} [Group G] {J : Type v} (a : J → G) :
    Generates a ↔ Subgroup.closure (Set.range a) = ⊤ :=
  Iff.rfl

/-- An indexed family generates a group exactly when evaluation from the free group is
surjective. -/
theorem generates_iff_lift_surjective {G : Type u} [Group G] {J : Type v} (a : J → G) :
    Generates a ↔ Function.Surjective (FreeGroup.lift a) := by
  rw [generates_iff, ← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]

/-- A finite indexed generating family makes the ambient group finitely generated. -/
theorem Generates.fg {G : Type u} [Group G] {J : Type v} {a : J → G}
    (h : Generates a) [Finite J] : Group.FG G :=
  Group.fg_iff.mpr ⟨Set.range a, h, Set.finite_range a⟩

end Group
