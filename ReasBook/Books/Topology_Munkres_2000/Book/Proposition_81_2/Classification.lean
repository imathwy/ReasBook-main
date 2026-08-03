module

public import Topology_Munkres_2000.Book.Proposition_81_2.Covering
public import Topology_Munkres_2000.Book.Definition_79_2.Conjugacy
public import Topology_Munkres_2000.Book.Theorem_79_4

public section

universe u v

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B]

/-- The conjugacy class of the subgroup induced by a connected covering and a chosen point over
the base point. -/
@[expose]
noncomputable def subgroupClassAt (C : ConnectedCovering.{u} B) (b₀ : B) (e : C.Total)
    (he : C.proj e = b₀) : Subgroup.ConjClasses (FundamentalGroup B b₀) :=
  Subgroup.mkConjClass
    (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ he).range

/-- The subgroup class at a chosen point is represented by the range of the induced
fundamental-group homomorphism. -/
theorem subgroupClassAt_eq_mkConjClass (C : ConnectedCovering.{u} B) (b₀ : B)
    (e : C.Total) (he : C.proj e = b₀) :
    subgroupClassAt C b₀ e he =
      Subgroup.mkConjClass
        (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ he).range := rfl

/-- The induced subgroup class does not depend on the chosen point over the base point. -/
theorem subgroupClassAt_eq (C : ConnectedCovering.{u} B) (b₀ : B)
    (e e' : C.Total) (he : C.proj e = b₀) (he' : C.proj e' = b₀) :
    subgroupClassAt C b₀ e he = subgroupClassAt C b₀ e' he' := by
  -- A path between the two points conjugates their induced fundamental-group ranges.
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  rw [subgroupClassAt_eq_mkConjClass, subgroupClassAt_eq_mkConjClass,
    Subgroup.mkConjClass_eq_iff]
  exact C.isCoveringMap.fundamentalGroupMapRange_isConj_of_path he' he
    (PathConnectedSpace.somePath e' e)

/-- The conjugacy class of the fundamental-group subgroup induced by a connected covering. -/
noncomputable def subgroupClass (C : ConnectedCovering.{u} B) (b₀ : B) :
    Subgroup.ConjClasses (FundamentalGroup B b₀) :=
  subgroupClassAt C b₀ (C.surjective b₀).choose (C.surjective b₀).choose_spec

/-- Every point over the base point computes the public induced subgroup class. -/
theorem subgroupClass_mk (C : ConnectedCovering.{u} B) (b₀ : B)
    (e : C.Total) (he : C.proj e = b₀) :
    subgroupClass C b₀ = subgroupClassAt C b₀ e he := by
  -- Independence of the chosen fiber point identifies the selected representative with `e`.
  exact subgroupClassAt_eq C b₀ (C.surjective b₀).choose e
    (C.surjective b₀).choose_spec he

/-- Equivalent connected coverings determine the same conjugacy class of subgroups. -/
theorem subgroupClass_eq_of_equivalent {C D : ConnectedCovering.{u} B} (b₀ : B)
    (h : Equivalent C D) : subgroupClass C b₀ = subgroupClass D b₀ := by
  -- Choose fiber points and apply the conjugacy criterion for equivalent connected coverings.
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  letI : LocallyPathConnectedSpace C.Total := C.locallyPathConnectedSpace
  letI : PathConnectedSpace D.Total := D.pathConnectedSpace
  letI : LocallyPathConnectedSpace D.Total := D.locallyPathConnectedSpace
  obtain ⟨e, he⟩ := C.surjective b₀
  obtain ⟨e', he'⟩ := D.surjective b₀
  rw [subgroupClass_mk C b₀ e he, subgroupClass_mk D b₀ e' he',
    subgroupClassAt_eq_mkConjClass, subgroupClassAt_eq_mkConjClass,
    Subgroup.mkConjClass_eq_iff]
  exact (C.isCoveringMap.equivalent_iff_fundamentalGroupMapRange_isConj
    D.isCoveringMap e e' b₀ he he').mp
      ((CoveringMap.equivalent_iff.trans equivalent_iff.symm).mpr h)

/-- The classification map from equivalence classes of connected coverings to conjugacy classes
of fundamental-group subgroups. -/
noncomputable def classification (B : Type v) [TopologicalSpace B] (b₀ : B) :
    Class.{v, u} B → Subgroup.ConjClasses (FundamentalGroup B b₀) :=
  Quotient.lift (fun C ↦ subgroupClass C b₀) fun _ _ h ↦
    subgroupClass_eq_of_equivalent b₀ (equivalentSetoid_iff.mp h)

/-- The classification map sends a representative covering to its induced subgroup class. -/
theorem classification_mk (C : ConnectedCovering.{u} B) (b₀ : B) :
    classification B b₀ (Quotient.mk (equivalentSetoid B) C) = subgroupClass C b₀ := by
  -- The quotient lift evaluates to its defining function on representatives.
  rfl

end ConnectedCovering
