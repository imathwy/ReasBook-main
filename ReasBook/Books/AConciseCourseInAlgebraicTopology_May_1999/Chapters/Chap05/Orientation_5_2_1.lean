import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.CompactlyGenerated

universe u w

/- Orientation 5.2.1

Passing to quotient spaces is a major source of point-set pathology. For this
section, the canonical mathlib surfaces that control this behavior are the
compactly generated replacement topology `TopologicalSpace.compactlyGenerated`,
the class `UCompactlyGeneratedSpace.{u}`, the quotient-stability instance for
compactly generated spaces, and the category `CompactlyGenerated.{u, w}`.
-/

recall TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] :
    TopologicalSpace X
recall UCompactlyGeneratedSpace (X : Type w) [TopologicalSpace X] : Prop
recall CompactlyGenerated : Type _
recall CompactlyGenerated.of (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    CompactlyGenerated.{u, w}

section

variable {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] (S : Setoid X)

/- Quotients preserve the compactly generated hypothesis through mathlib's canonical instance. -/
#synth UCompactlyGeneratedSpace.{u} (Quotient S)

end
