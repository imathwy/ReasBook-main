import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v w

/- Domain-style sampling for topological rings and modules:
- primitive owner data for topological `R`-modules: `ContinuousAdd`, `ContinuousSMul`
- linearly topologized owner: `IsLinearTopology R M`
- adic-topology owner: `IsAdic I`
- complete separated adic owner: `IsAdicComplete I R`

Layer triage:
- `source-facing`: ideals of definition, preadmissible rings, admissible rings, preadic rings,
  adic rings
- `core/canonical`: `ContinuousAdd`, `ContinuousSMul`, `IsLinearTopology`, `IsAdic`,
  `IsAdicComplete`
- `bridge/view`: preadic and adic rings are source-facing existence predicates whose canonical
  ambient owners are `IsAdic` and `IsAdicComplete`

Definition 15.36.1 is source-facing for the five ring notions above, but the ambient owners for
linear topology, adic topology, and adic completeness already live upstream. The refined API below
therefore keeps the source distinctions `preadmissible` vs `preadic` and `admissible` vs `adic`,
while using `IsAdic` and `IsAdicComplete` only as bridge data. -/
recall IsLinearTopology

/- Companion recall: a topological commutative ring is expressed by the canonical class
`IsTopologicalRing`. -/
recall IsTopologicalRing

/- Companion recall: the canonical owner for the statement that the topology on a ring is the
`I`-adic topology is `IsAdic I`. -/
recall IsAdic

/- Companion recall: once the topology is `I`-adic, completeness and separatedness are owned by
`IsAdicComplete I R`. -/
#check IsAdic.isAdicComplete_iff

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]

/- Companion recall: an unbundled topological `R`-module is expressed by continuity of addition
and scalar multiplication. -/
#check (ContinuousAdd M : Prop)
#check (ContinuousSMul R M : Prop)

/- Companion recall: a linearly topologized module has a neighborhood basis of `0` consisting of
open submodules. -/
#check isLinearTopology_iff_hasBasis_open_submodule

/- Companion recall: homomorphisms of topological `R`-modules are continuous linear maps. -/
#check (M →L[R] N)

end

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]
variable [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]

/- Companion recall: a linearly topologized commutative ring has a neighborhood basis of `0`
consisting of open ideals. -/
#check isLinearTopology_iff_hasBasis_open_ideal

/- Companion recall: homomorphisms of topological commutative rings are morphisms in
`TopCommRingCat`. -/
#check (TopCommRingCat.of R ⟶ TopCommRingCat.of S)

end

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

namespace Ideal

/-- An ideal of definition is an open ideal whose powers are cofinal among neighborhoods of `0`.
-/
def IsIdealOfDefinition (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧ ∀ U ∈ 𝓝 (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U

-- Proof sketch: unfold `Ideal.IsIdealOfDefinition`; the statement is exactly the conjunction of
-- openness and the cofinality of the powers `I ^ n` in the neighborhood filter of `0`.
/-- Unfolding the topological-ring notion of an ideal of definition. -/
theorem isIdealOfDefinition_iff (I : Ideal R) :
    Ideal.IsIdealOfDefinition I ↔
      IsOpen (I : Set R) ∧
        ∀ U ∈ 𝓝 (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U :=
  Iff.rfl

/-- An adic ideal is an ideal of definition. -/
theorem isIdealOfDefinition_of_isAdic [IsTopologicalRing R] {I : Ideal R} (hI : IsAdic I) :
    Ideal.IsIdealOfDefinition I := by
  rcases (isAdic_iff.mp hI) with ⟨hopen, hcofinal⟩
  exact ⟨by simpa using hopen 1, hcofinal⟩

end Ideal

/-- Definition 15.36.1 (Topological rings): a pre-admissible topological ring is a linearly
topologized topological ring with an ideal of definition. -/
@[stacks 07E8]
class IsPreadmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R, IsLinearTopology R R where
  /-- A pre-admissible ring admits an ideal of definition. -/
  exists_ideal_isIdealOfDefinition : ∃ I : Ideal R, Ideal.IsIdealOfDefinition I

/-- A pre-adic topological ring is linearly topologized and admits an ideal whose associated adic
topology is the ambient topology. Its linear topology is derived from that adic owner. -/
class IsPreadicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R where
  /-- A pre-adic ring admits an ideal whose associated adic topology is the ambient topology. -/
  exists_ideal_isAdic : ∃ I : Ideal R, IsAdic I

/-- An admissible topological ring is a pre-admissible ring that is complete and separated for its
ambient topology. -/
class IsAdmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsPreadmissibleRing R where
  /-- An admissible ring is separated. -/
  isT2 : T2Space R
  /-- An admissible ring is complete for the ambient additive uniformity. -/
  isComplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

instance instT2Space [IsAdmissibleRing R] : T2Space R :=
  (inferInstance : IsAdmissibleRing R).isT2

/-- An admissible topological ring is complete for its ambient additive uniformity. -/
instance instCompleteSpace [IsAdmissibleRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) :=
  (inferInstance : IsAdmissibleRing R).isComplete

/-- An adic topological ring admits a defining adic ideal for which the ambient ring is complete
and separated. -/
class IsAdicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R where
  /-- An adic ring admits an ideal whose adic topology is the ambient topology and for which the
  ambient ring is adically complete. -/
  exists_ideal_isAdicComplete : ∃ I : Ideal R, IsAdic I ∧ IsAdicComplete I R

/-- Helper for Definition 15.36.1 (Topological rings): adic completeness yields ambient
completeness and separatedness for the additive uniformity attached to the topological ring. -/
theorem complete_space_and_t2_of_is_adic_complete [IsTopologicalRing R] {I : Ideal R}
    (hI : IsAdic I) (hIComplete : IsAdicComplete I R) :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) ∧ T2Space R := by
  -- Pass to the canonical additive uniformity so that `IsAdicComplete` can be unpacked directly.
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact hI.isAdicComplete_iff.mp hIComplete

/-- Every pre-adic ring is pre-admissible, since an adic ideal is an ideal of definition. -/
instance instIsPreadmissibleRing [IsPreadicRing R] : IsPreadmissibleRing R where
  toIsTopologicalRing := inferInstance
  toIsLinearTopology := by
    rcases (inferInstance : IsPreadicRing R).exists_ideal_isAdic with ⟨I, hI⟩
    exact hI ▸ Ideal.isLinearTopology I
  exists_ideal_isIdealOfDefinition := by
    rcases (inferInstance : IsPreadicRing R).exists_ideal_isAdic with ⟨I, hI⟩
    exact ⟨I, Ideal.isIdealOfDefinition_of_isAdic hI⟩

/-- An adic ring is pre-adic after forgetting completeness and separatedness. -/
instance instIsPreadicRing [IsAdicRing R] : IsPreadicRing R where
  toIsTopologicalRing := inferInstance
  exists_ideal_isAdic := by
    rcases (inferInstance : IsAdicRing R).exists_ideal_isAdicComplete with ⟨I, hI, _⟩
    exact ⟨I, hI⟩

/-- An adic ring is separated. -/
instance instT2SpaceOfIsAdicRing [IsAdicRing R] : T2Space R := by
  rcases (inferInstance : IsAdicRing R).exists_ideal_isAdicComplete with ⟨I, hI, hIComplete⟩
  -- The helper isolates the canonical `IsAdicComplete` bridge; here we keep only the `T2` half.
  exact (complete_space_and_t2_of_is_adic_complete hI hIComplete).2

/-- An adic ring is complete for its ambient additive uniformity. -/
instance instCompleteSpaceOfIsAdicRing [IsAdicRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := by
  rcases (inferInstance : IsAdicRing R).exists_ideal_isAdicComplete with ⟨I, hI, hIComplete⟩
  -- The same bridge theorem provides completeness for the ambient additive uniformity.
  exact (complete_space_and_t2_of_is_adic_complete hI hIComplete).1

/-- An adic ring is admissible after forgetting the chosen adic ideal. -/
instance instIsAdmissibleRing [IsAdicRing R] : IsAdmissibleRing R where
  toIsPreadmissibleRing := inferInstance
  isT2 := inferInstance
  isComplete := inferInstance

end

end TopologicalRing
