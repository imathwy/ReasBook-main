module

public import Topology_Munkres_2000.Book.Proposition_81_2.Covering
public import Topology_Munkres_2000.Book.Proposition_81_2.Classification
public import Topology_Munkres_2000.Book.Theorem_79_4

public section

universe u v

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B]

/-- Helper for Proposition 81.2: equality of the subgroup classes determined at chosen fiber
points is equivalent to equivalence of the connected coverings. -/
private lemma subgroupClassAt_eq_iff_equivalent (C D : ConnectedCovering.{u} B) (b₀ : B)
    (e : C.Total) (e' : D.Total) (he : C.proj e = b₀) (he' : D.proj e' = b₀) :
    subgroupClassAt C b₀ e he = subgroupClassAt D b₀ e' he' ↔ Equivalent C D := by
  -- Supply the connectedness hypotheses carried by the two covering structures.
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  letI : LocallyPathConnectedSpace C.Total := C.locallyPathConnectedSpace
  letI : PathConnectedSpace D.Total := D.pathConnectedSpace
  letI : LocallyPathConnectedSpace D.Total := D.locallyPathConnectedSpace
  -- Normalize both classes to induced ranges and invoke the earlier equivalence criterion.
  rw [subgroupClassAt_eq_mkConjClass, subgroupClassAt_eq_mkConjClass,
    Subgroup.mkConjClass_eq_iff]
  calc
    _ ↔ CoveringMap.Equivalent C.proj D.proj :=
      (C.isCoveringMap.equivalent_iff_fundamentalGroupMapRange_isConj
        D.isCoveringMap e e' b₀ he he').symm
    _ ↔ Equivalent C D :=
      CoveringMap.equivalent_iff.trans equivalent_iff.symm

/-- Helper for Proposition 81.2: two connected coverings determine the same subgroup conjugacy
class exactly when they are equivalent. -/
lemma subgroupClass_eq_iff_equivalent (C D : ConnectedCovering.{u} B) (b₀ : B) :
    subgroupClass C b₀ = subgroupClass D b₀ ↔ Equivalent C D := by
  -- Choose representatives over the base point, which exist by surjectivity.
  obtain ⟨e, he⟩ := C.surjective b₀
  obtain ⟨e', he'⟩ := D.surjective b₀
  -- Independence of the chosen fiber points reduces the result to the pointed criterion.
  rw [subgroupClass_mk C b₀ e he, subgroupClass_mk D b₀ e' he',
    subgroupClassAt_eq_iff_equivalent]

end ConnectedCovering

/-- Proposition 81.2. For a path-connected, locally path-connected based space `B`, the
correspondence from equivalence classes of connected coverings of `B` to conjugacy classes of
subgroups of `π₁(B, b₀)` is injective. -/
theorem ConnectedCovering.classification_injective {B : Type v} [TopologicalSpace B]
    [PathConnectedSpace B] [LocallyPathConnectedSpace B] (b₀ : B) :
    Function.Injective
      (ConnectedCovering.classification B b₀ :
        ConnectedCovering.Class.{v, u} B →
          Subgroup.ConjClasses (FundamentalGroup B b₀)) := by
  intro x y hxy
  -- Work with representatives of both quotient classes simultaneously.
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro C D hCD
  -- Equality of images gives equivalence of representatives, hence equality in the quotient.
  rw [ConnectedCovering.classification_mk, ConnectedCovering.classification_mk] at hCD
  exact ConnectedCovering.class_mk_eq_mk_iff.mpr
    ((ConnectedCovering.subgroupClass_eq_iff_equivalent C D b₀).mp hCD)
