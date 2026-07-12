import Mathlib
import StacksProject_2024.Chap09.Lemma_9_21_8
import StacksProject_2024.Chap09.Lemma_9_22_1

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
@[stacks 0BMM]
theorem galoisTower_isSES :
    TopologicalGroup.IsSES
      (MulSemiringAction.toAlgAut Gal(L / M) K L)
      (restrictNormalHom M) := by
  -- Route correction: the deleted packaged short exact sequence theorem is replaced by a direct
  -- `IsSES` proof from the current continuity, quotient, and kernel/range owner lemmas.
  have hInclusionContinuous :
      Continuous (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    -- Lemma 9.22.1 applies once the ambient field is viewed with the discrete topology locally.
    letI : TopologicalSpace L := ⊥
    letI : DiscreteTopology L := ⟨rfl⟩
    refine continuous_of_continuous_galois_action
      (g := MulSemiringAction.toAlgAut Gal(L / M) K L) ?_
    simpa using (continuous_smul : Continuous fun p : Gal(L / M) × L ↦ p.1 • p.2)
  have hInclusionRange :
      (MulSemiringAction.toAlgAut Gal(L / M) K L).range = M.fixingSubgroup := by
    -- The image consists exactly of automorphisms fixing `M` pointwise.
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      simpa using τ.commutes ⟨x, hx⟩
    · intro hσ
      refine ⟨IntermediateField.fixingSubgroupEquiv M ⟨σ, hσ⟩, ?_⟩
      ext x
      rfl
  have hInclusionInjective :
      Function.Injective (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    -- Equality in `Gal(L / K)` is equality of the underlying maps on `L`.
    intro σ τ hστ
    ext x
    exact congrArg (fun f : Gal(L / K) => f x) hστ
  have hInclusionClosedEmbedding :
      Topology.IsClosedEmbedding (MulSemiringAction.toAlgAut Gal(L / M) K L) := by
    -- A continuous injection from the compact group `Gal(L / M)` into the Hausdorff group
    -- `Gal(L / K)` is automatically a closed embedding.
    exact Continuous.isClosedEmbedding hInclusionContinuous hInclusionInjective
  have hRestrictOpenQuotient :
      IsOpenQuotientMap (restrictNormalHom M : Gal(L / K) →* Gal(M / K)) := by
    -- The restriction map is a continuous surjection between compact Hausdorff groups.
    apply MonoidHom.isOpenQuotientMap_of_isQuotientMap
    exact IsQuotientMap.of_surjective_continuous
      (by
        simpa using (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L)))
      (by
        simpa using (InfiniteGalois.restrictNormalHom_continuous (k := K) (K := L) M))
  refine TopologicalGroup.IsSES.mk hInclusionClosedEmbedding hRestrictOpenQuotient ?_
  -- Algebraic exactness is the standard kernel computation rewritten via the inclusion image.
  rw [MonoidHom.mulExact_iff, IntermediateField.restrictNormalHom_ker, hInclusionRange]

end
