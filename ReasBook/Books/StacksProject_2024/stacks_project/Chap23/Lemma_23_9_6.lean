import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_33_2
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap23.Definition_23_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum Set

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]
variable [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B]

/-
Semantic recall note: `lean_leansearch` only surfaced generic closed-point and local-spectrum hits
for this item, so the owner choice was fixed against the verified local Chapter 23/15 API
`IsLocalCompleteIntersectionRing`, `RingHom.IsLocalCompleteIntersection`, and the reformulation
inputs `Proposition_23_9_2`, `Lemma_23_9_5`, and the closed-point image criterion shape used in
`Lemma_10_39_16`.
-/

/-- The target-side package in Lemma 23.9.6: `B` is a local complete intersection ring and
`B`, viewed as an `A`-module, has finite tor dimension. -/
class TargetLocalCompleteIntersectionFiniteTor
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop where
  /-- The target ring is a local complete intersection ring. -/
  targetLci : IsLocalCompleteIntersectionRing B
  /-- The target algebra has finite tor dimension over the source. -/
  finiteTor : CategoryTheory.ModuleHasFiniteTorDimension (ModuleCat.of A B)

/-- The source-side package in Lemma 23.9.6: `A` is a local complete intersection ring and the
map `A → B` is a local complete intersection map. -/
class SourceLocalCompleteIntersectionMap
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop where
  /-- The source ring is a local complete intersection ring. -/
  sourceLci : IsLocalCompleteIntersectionRing A
  /-- The structure map is a local complete intersection map. -/
  mapLci : RingHom.IsLocalCompleteIntersection (algebraMap A B)

/-- Lemma 23.9.6: let `A` be a Noetherian ring and let `A → B` be a finite type ring map such
that the image of `Spec(B) → Spec(A)` contains all closed points of `Spec(A)`. Then the following
are equivalent: `B` is a complete intersection and `A → B` has finite tor dimension; `A` is a
complete intersection and `A → B` is a local complete intersection in the sense of More on
Algebra, Definition `15.33.2`. -/
@[stacks 09QF]
theorem target_isLocalCompleteIntersectionRing_and_finiteTorDimension_iff_source_and_map
    (hclosed :
      closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B))) :
    TargetLocalCompleteIntersectionFiniteTor A B ↔
      SourceLocalCompleteIntersectionMap A B := sorry

end
