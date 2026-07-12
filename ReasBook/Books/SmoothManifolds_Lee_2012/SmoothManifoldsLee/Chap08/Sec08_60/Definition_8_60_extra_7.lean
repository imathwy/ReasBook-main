import Mathlib
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap08.Sec08_55.Definition_8_55_extra_3
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Corollary_8_38
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Definition_8_60_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Notation_8_60_extra_6

open scoped Manifold ContDiff

noncomputable section

universe u𝕜 uE uH uM uG

variable {H : Type uH} [TopologicalSpace H]

section Parallelizable

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {ι : Type uE} {X : ι → (x : M) → TangentSpace I x}

/- Definition 8.60-extra-7 (1) is recall-only.

The chapter's canonical owner for a smooth global frame is the specialization
`IsLocalFrameOn I E ∞ X Set.univ`, and the corresponding parallelizability predicate is
`parallelizable I M`. -/
recall IsLocalFrameOn
recall parallelizable
#check (IsLocalFrameOn I E ∞ X Set.univ : Prop)

end Parallelizable

section LeftInvariantFrame

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I ∞ G]
variable {ι : Type uE} {u : Set G}

-- Domain sampling pass:
-- * primary domain: smooth frames on Lie groups and left-invariant vector fields;
-- * sampled owners: `IsLocalFrameOn`, `parallelizable`, `VectorField.IsLeftInvariant`, and
--   `left_invariant_rough_vector_field_eq_mulInvariantVectorField`;
-- * source-facing owner: `VectorField.IsLeftInvariant`;
-- * core/canonical bridge: `mulInvariantVectorField`, written as `vᴸ`.

/-- Definition 8.60-extra-7 (2): a local or global frame on a Lie group whose vector fields are
left-invariant is called a left-invariant frame. On the canonical local-frame owner
`IsLocalFrameOn I E ∞ X u`, this is the additional requirement that each constituent vector field
is left-invariant in the sense of Definition 8.60-extra-1. Under the stronger Lie-group
assumptions, the equivalent `vᴸ` description is a derived bridge theorem. -/
def IsLeftInvariantFrameOn
    (X : ι → (x : G) → TangentSpace I x) (u : Set G) : Prop :=
  IsLocalFrameOn I E ∞ X u ∧ ∀ i, VectorField.IsLeftInvariant (X i)

namespace IsLeftInvariantFrameOn

theorem isLocalFrameOn
    {X : ι → (x : G) → TangentSpace I x} (hX : IsLeftInvariantFrameOn X u) :
    IsLocalFrameOn I E ∞ X u :=
  hX.1

theorem isLeftInvariantVectorField
    {X : ι → (x : G) → TangentSpace I x} (hX : IsLeftInvariantFrameOn X u) (i : ι) :
    VectorField.IsLeftInvariant (X i) :=
  hX.2 i

section

variable [LieGroup I (minSmoothness 𝕜 3) G]

theorem eq_mulInvariantVectorField
    {X : ι → (x : G) → TangentSpace I x} (hX : IsLeftInvariantFrameOn X u) (i : ι) :
    X i = (X i 1)ᴸ :=
  left_invariant_rough_vector_field_eq_mulInvariantVectorField
    (X i) (hX.isLeftInvariantVectorField i)

end

/-- A left-invariant smooth global frame makes the Lie group parallelizable. -/
theorem parallelizable
    {X : ι → (x : G) → TangentSpace I x} (hX : IsLeftInvariantFrameOn X Set.univ) :
    parallelizable I G :=
  hX.isLocalFrameOn.parallelizable

end IsLeftInvariantFrameOn

end LeftInvariantFrame

end
