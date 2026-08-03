module

public import Topology_Munkres_2000.Book.Proposition_81_2.Classification

public section

universe u v

namespace ConnectedCovering

/-- Surjectivity of the classification of connected coverings of `B` by conjugacy classes of
subgroups of `π₁(B, b₀)`. -/
def IsClassificationSurjective {B : Type v} [TopologicalSpace B] (b₀ : B) : Prop :=
  Function.Surjective
    (classification B b₀ : Class.{v, u} B →
      Subgroup.ConjClasses (FundamentalGroup B b₀))

/-- The connected-covering classification is surjective exactly when every subgroup conjugacy
class is represented by an equivalence class of connected coverings. -/
theorem isClassificationSurjective_iff {B : Type v} [TopologicalSpace B] (b₀ : B) :
    IsClassificationSurjective.{u, v} b₀ ↔
      ∀ subgroupClass : Subgroup.ConjClasses (FundamentalGroup B b₀),
        ∃ coveringClass : Class.{v, u} B,
          classification B b₀ coveringClass = subgroupClass := Iff.rfl

end ConnectedCovering
