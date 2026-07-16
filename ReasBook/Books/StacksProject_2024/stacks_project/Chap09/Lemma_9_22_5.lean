import Mathlib
import StacksProject_2024.stacks_project.Chap09.Lemma_9_21_8
import StacksProject_2024.stacks_project.Chap09.Lemma_9_22_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open AlgEquiv InfiniteGalois

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [IsGalois K L] [Normal K M]

/-
Domain-style sampling:
* primary domain: topological short exact sequences of Galois groups in the Krull topology;
* sampled owner declarations:
  `TopologicalGroup.IsSES`,
  `galoisTowerRestrictionShortExact`,
  `InfiniteGalois.restrictNormalHom_continuous`,
  `continuous_of_continuous_galois_action`;
* best owner abstraction: the algebraic exactness data is owned by the canonical group extension
  `galoisTowerRestrictionShortExact M`, whose `inl` and `rightHom` are the inclusion and
  restriction homomorphisms underlying the topological short exact sequence;
* primitive data: the canonical inclusion and restriction homomorphisms packaged by that group
  extension, together with the primitive normality hypothesis `[Normal K M]` needed for the
  restriction map;
* derived API: injectivity, surjectivity, and range/kernel exactness from
  `galoisTowerRestrictionShortExact`; continuity from the Krull-topology API; and closed/open
  quotient properties from compact Hausdorff topological group facts.

Layer triage:
* `source-facing`: the short exact sequence statement for Galois groups as topological groups;
* `core/canonical`: `TopologicalGroup.IsSES` together with the canonical inclusion/restriction maps;
* `bridge/view`: `galoisTowerRestrictionShortExact`, which packages the algebraic exactness reused
  here but is not kept as the public owner for the topological statement.
-/
/-- Lemma 9.22.5 (Tag 0BMM): for an intermediate field `M` of a Galois extension `L/K`, the
canonical inclusion `Gal(L / M) → Gal(L / K)` and restriction map
`Gal(L / K) → Gal(M / K)` form a short exact sequence of profinite topological groups. The source
states this with `M/K` Galois, but the exact-sequence statement uses only the primitive normality
hypothesis `[Normal K M]`. -/
theorem galoisTower_isSES :
    TopologicalGroup.IsSES
      (MulSemiringAction.toAlgAut Gal(L / M) K L)
      (restrictNormalHom M) := by
  let S := galoisTowerRestrictionShortExact M
  have hcont_inl : Continuous (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    letI : TopologicalSpace L := ⊥
    letI : DiscreteTopology L := ⟨rfl⟩
    exact continuous_of_continuous_galois_action (MulSemiringAction.toAlgAut Gal(L / M) K L)
      (continuous_smul : Continuous fun p : Gal(L / M) × L ↦ p.1 • p.2)
  have hquotient : Topology.IsQuotientMap (restrictNormalHom M) :=
    IsQuotientMap.of_surjective_continuous
      S.rightHom_surjective (restrictNormalHom_continuous M)
  refine
    { isClosedEmbedding := hcont_inl.isClosedEmbedding S.inl_injective
      isOpenQuotientMap := MonoidHom.isOpenQuotientMap_of_isQuotientMap hquotient
      mulExact := ?_ }
  rw [MonoidHom.mulExact_iff]
  exact S.range_inl_eq_ker_rightHom.symm

end
