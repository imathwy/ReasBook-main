import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_36_1_Topological_rings (from Chap15) -/
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

/-- A pre-admissible topological ring is a linearly topologized topological ring with an ideal of
definition. -/
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
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (hI.isAdicComplete_iff.mp hIComplete).2

/-- An adic ring is complete for its ambient additive uniformity. -/
instance instCompleteSpaceOfIsAdicRing [IsAdicRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := by
  rcases (inferInstance : IsAdicRing R).exists_ideal_isAdicComplete with ⟨I, hI, hIComplete⟩
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (hI.isAdicComplete_iff.mp hIComplete).1

/-- An adic ring is admissible after forgetting the chosen adic ideal. -/
instance instIsAdmissibleRing [IsAdicRing R] : IsAdmissibleRing R where
  toIsPreadmissibleRing := inferInstance
  isT2 := inferInstance
  isComplete := inferInstance

end

end TopologicalRing

/-! ### Lemma_15_36_2 (from Chap15) -/
open scoped Topology

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.36.2:
- primary domain: adic topologies on commutative rings and continuity of ring homomorphisms.
- inspected owner declarations:
  * `Ideal.adicTopology`
  * `Ideal.hasBasis_nhds_zero_adic`
  * `Ideal.WithIdeal.uniformContinuous_of_map_le`
- best owner abstraction: the ambient topologies are owned by `Ideal.adicTopology`; the Stacks
  lemma itself is a source-facing continuity criterion and should live on `RingHom`.
- source/core/bridge triage:
  * `source-facing`: the iff criterion for continuity from the `I`-adic topology to the
    `J`-adic topology;
  * `core/canonical`: `Ideal.adicTopology` and the basis theorem
    `Ideal.hasBasis_nhds_zero_adic`;
  * `bridge/view`: `Ideal.WithIdeal.uniformContinuous_of_map_le` for the one-sided
    map-into-the-defining-ideal criterion when the source and target carry preferred ideals.
- primitive data: the ring homomorphism `φ` and the ideals `I`, `J`.
- derived API: the continuity criterion below and the direct downstream monotonicity lemma for
  adic topologies.
-/

namespace RingHom

-- Proof sketch: for the forward direction, continuity at `0` for the additive homomorphism `φ`
-- means some basic open neighborhood `J` of `0` in the `J`-adic topology has open preimage, and
-- the `I`-adic basis identifies that preimage condition with `I ^ n ⊆ φ ⁻¹' J`, i.e.
-- `Ideal.map φ (I ^ n) ≤ J`. For the reverse direction, such an inclusion gives continuity at `0`
-- from the neighborhood bases, and `continuous_of_continuousAt_zero` upgrades this to continuity
-- of the ring homomorphism.
/-- Lemma 15.36.2: a ring homomorphism from `R` with the `I`-adic topology to `S` with the
`J`-adic topology is continuous if and only if the image of some power of `I` is contained in
`J`. -/
theorem continuous_adic_iff_exists_pow_map_le
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace S := J.adicTopology
    Continuous φ ↔
      ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J := by
  letI : TopologicalSpace R := I.adicTopology
  letI : TopologicalSpace S := J.adicTopology
  constructor
  · intro hφ
    have hzero : Filter.Tendsto φ (𝓝 (0 : R)) (𝓝 (0 : S)) := by
      simpa [ContinuousAt, map_zero] using (hφ.continuousAt : ContinuousAt φ (0 : R))
    rw [I.hasBasis_nhds_zero_adic.tendsto_iff J.hasBasis_nhds_zero_adic] at hzero
    obtain ⟨n, -, hn⟩ := hzero 1 trivial
    refine ⟨n, ?_⟩
    simpa [pow_one] using
      (Ideal.map_le_iff_le_comap.mpr hn : Ideal.map φ (I ^ n) ≤ J ^ 1)
  · rintro ⟨n, hmap⟩
    apply continuous_of_continuousAt_zero φ
    rw [ContinuousAt, map_zero, I.hasBasis_nhds_zero_adic.tendsto_iff J.hasBasis_nhds_zero_adic]
    intro m _
    refine ⟨n * m, trivial, ?_⟩
    intro x hx
    have hpow : Ideal.map φ (I ^ (n * m)) ≤ J ^ m := by
      calc
        Ideal.map φ (I ^ (n * m)) = Ideal.map φ ((I ^ n) ^ m) := by rw [pow_mul]
        _ = Ideal.map φ (I ^ n) ^ m := by rw [Ideal.map_pow]
        _ ≤ J ^ m := Ideal.pow_right_mono hmap m
    exact (Ideal.map_le_iff_le_comap.mp hpow) hx

end RingHom

namespace Ideal

/-- If `I ≤ J`, then the `I`-adic topology is finer than the `J`-adic topology. -/
theorem adicTopology_mono {I J : Ideal R} (hIJ : I ≤ J) :
    I.adicTopology ≤ J.adicTopology := by
  have hid : @Continuous R R I.adicTopology J.adicTopology (RingHom.id R) := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    exact ⟨1, by simpa using hIJ⟩
  simpa [induced_id] using (continuous_iff_le_induced.mp hid)

end Ideal

/-! ### Lemma_15_36_3_Baire_category_theorem (from Chap15) -/
open scoped Topology

universe u

/- Domain-style sampling for the Baire category theorem in topological additive groups:
- primary domain: Baire spaces for complete topological additive groups with a countably generated
  neighborhood filter at `0`
- owner declarations inspected: `BaireSpace`, `dense_iInter_of_isOpen`,
  `BaireSpace.of_completelyPseudoMetrizable`, `uniformity_eq_comap_nhds_zero'`,
  `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
- best owner abstraction: `BaireSpace`

Layer triage:
- `source-facing`: the complete first-countable topological additive-group specialization of the
  Stacks lemma, restated at the source-faithful local countability-at-`0` level
- `core/canonical`: `BaireSpace` together with `dense_iInter_of_isOpen`
- `bridge/view`: the canonical right-uniform-space route from `uniformity_eq_comap_nhds_zero'`,
  countable generation of `𝓝 0`, and completeness to complete pseudometrizability, hence to
  `BaireSpace`

Primitive data is only the family `U : ℕ+ → Set M` together with the proofs that each `U n` is
open and dense. The countably generated uniformity, complete pseudometrizability, and resulting
`BaireSpace` structure are derived API from the canonical owner abstraction, so this file should
package that bridge once and then reuse the canonical Baire-space declarations directly. -/

section

variable {M : Type u} [TopologicalSpace M] [AddGroup M] [IsTopologicalAddGroup M]
  [(𝓝 (0 : M)).IsCountablyGenerated]
  [@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]
variable {U : ℕ+ → Set M}

/-- A complete topological additive group with countably generated `𝓝 0` is a Baire space. This
is the chapter-level bridge from the Stacks hypotheses to the canonical `BaireSpace` owner. -/
instance baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup : BaireSpace M := by
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  letI : CompleteSpace M := ‹@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)›
  haveI : (uniformity M).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero']
    exact Filter.comap.isCountablyGenerated _ _
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace M := inferInstance
  infer_instance

attribute [instance 100] baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup

/-- Lemma 15.36.3 (Baire category theorem): in a complete topological additive group whose
neighborhood filter at `0` is countably generated, the intersection of countably many open dense
subsets is dense. This is the source-facing specialization of the canonical Baire-space theorem,
so the linear-topology hypothesis from the surrounding Stacks context is intentionally omitted from
the statement. -/
theorem dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup
    (hU_open : ∀ n, IsOpen (U n)) (hU_dense : ∀ n, Dense (U n)) : Dense (⋂ n, U n) :=
  dense_iInter_of_isOpen hU_open hU_dense

end

/-! ### Lemma_15_36_4 (from Chap15) -/
open scoped Topology

universe u

/- Domain-style sampling for countable closed covers in complete topological additive groups:
- primary domain: Baire-category consequences for complete topological additive groups, together
  with the canonical openness criterion for additive subgroups
- sampled owner-level declarations:
  `baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup`,
  `nonempty_interior_of_iUnion_of_closed`,
  `AddSubgroup.isOpen_of_mem_nhds`,
  `BaireSpace`
- best owner abstraction: the chapter-level `BaireSpace` bridge from Lemma `15.36.3`, together
  with the canonical consequence `nonempty_interior_of_iUnion_of_closed`; subgroup openness is
  then derived from `AddSubgroup.isOpen_of_mem_nhds`
- primitive data: a countable family of closed additive subgroups covering the ambient group
- derived API: the complete pseudometrizable/Baire-space packaging obtained from completeness and
  countable generation of `𝓝 0`

Layer triage:
- `source-facing`: the Stacks lemma asserting that one closed subgroup in a countable cover is open
- `core/canonical`: `nonempty_interior_of_iUnion_of_closed` and
  `AddSubgroup.isOpen_of_mem_nhds`, organized by the ambient owner abstraction `BaireSpace`
- `bridge/view`: the right-uniform-space route from countably generated `𝓝 0` and completeness to
  the Baire-space owner abstraction
-/

/- Lemma 15.36.4: under the assumptions of the Baire category theorem for a linearly
topologized complete topological additive group with a countable fundamental system of
neighbourhoods of `0`, if `M` is the union of countably many closed subgroups, then one of those
subgroups is open. -/
-- Proof sketch: apply the Baire theorem from Lemma 15.36.3, equivalently mathlib's
-- `nonempty_interior_of_iUnion_of_closed`, to the closed sets `(N n : Set M)`. This gives some
-- `n` together with a point of `interior (N n)`. For a subgroup, membership in its interior at
-- any point already gives openness via `AddSubgroup.isOpen_of_mem_nhds`.
section

variable {ι : Type*} {M : Type u} [Countable ι]
variable [TopologicalSpace M] [AddGroup M] [IsTopologicalAddGroup M]
variable [(𝓝 (0 : M)).IsCountablyGenerated]
variable [@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]

namespace AddSubgroup

/-- Lemma 15.36.4: if a complete topological additive group with countably generated `𝓝 0` is the
union of countably many closed additive subgroups, then one of those subgroups is open. As in
Lemma `15.36.3`, the linear-topology hypothesis from the surrounding Stacks context is omitted
from the statement because the argument only uses the induced `BaireSpace` owner abstraction. -/
theorem exists_isOpen_of_iUnion_eq_univ_of_isClosed
    (N : ι → AddSubgroup M) (hN_closed : ∀ i, IsClosed (N i : Set M))
    (hcover : (⋃ i, (N i : Set M)) = Set.univ) :
    ∃ i, IsOpen (N i : Set M) := by
  rcases nonempty_interior_of_iUnion_of_closed hN_closed hcover with ⟨i, _, hx⟩
  exact ⟨i, (N i).isOpen_of_mem_nhds <| mem_interior_iff_mem_nhds.1 hx⟩

end AddSubgroup

end

/-! ### Lemma_15_36_5_Open_mapping_lemma (from Chap15) -/
universe u v

open scoped Topology

/- Domain-style sampling for the open mapping lemma in linearly topologized additive groups:
- primary domain: topological additive groups with linear/nonarchimedean topology and open-map
  phenomena
- sampled owner-level declarations:
  `IsLinearTopology.hasBasis_open_submodule`,
  `OpenAddSubgroup`,
  `dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup`,
  `AddSubgroup.exists_isOpen_of_iUnion_eq_univ_of_isClosed`
- best owner abstraction: `IsLinearTopology ℤ N` is the chapter/mathlib owner for a linearly
  topologized abelian group, `OpenAddSubgroup N` is the canonical owner for open subgroups, and
  `IsOpenMap` remains the owner for the open-map conclusion
- primitive data: the continuous additive homomorphism `u`, the source linear-topology and
  completeness hypotheses, and the separated target topological additive group
- derived API: the Baire-space consequences of completeness and countable generation of `𝓝 0`,
  already packaged in the preceding chapter lemmas, so they should not be restated as primitive
  public data here

Layer triage:
- `source-facing`: the Stacks either/or open-mapping statement below
- `core/canonical`: `IsLinearTopology ℤ N` for the linearly topologized source, and `IsOpenMap`
  for the openness alternative
- `bridge/view`: the chapter bridge from completeness plus countable generation to Baire-category
  consequences, used through Lemmas `15.36.3` and `15.36.4`
-/

section

variable {N : Type u} {M : Type v}
variable [TopologicalSpace N] [AddCommGroup N] [IsTopologicalAddGroup N] [IsLinearTopology ℤ N]
  [(𝓝 (0 : N)).IsCountablyGenerated]
  [@CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N)]
variable [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [T2Space M]

/-- Lemma 15.36.5 (Open mapping lemma): a continuous homomorphism from a complete linearly
topologized abelian group with a countable fundamental system of neighbourhoods of `0` to a
separated topological abelian group is either open, or the image of some open subgroup is nowhere
dense. -/
-- Proof sketch: choose a decreasing countable basis of open subgroups in `N`; if no image of such
-- a subgroup is nowhere dense, then the closures of these images form a neighborhood basis in `M`.
-- Use completeness of `N` to lift an arbitrary point of the first closure by an infinite sum, and
-- use separatedness of `M` to identify the limit with its image under `u`, proving openness.
theorem isOpenMap_or_exists_nowhereDense_image_openAddSubgroup
    (u : N →ₜ+ M) :
    IsOpenMap u ∨ ∃ N₀ : OpenAddSubgroup N, IsNowhereDense (u '' N₀) := sorry

end
