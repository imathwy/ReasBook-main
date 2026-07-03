import Mathlib
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_22_1 (from Chap09) -/
open scoped Topology
open AlgEquiv Filter

universe u v w

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsIntegral F E]
variable [TopologicalSpace E] [DiscreteTopology E]

instance : ContinuousSMul Gal(E / F) E :=
  (continuousSMul_iff_stabilizer_isOpen).2 stabilizer_isOpen_of_isIntegral

end

section

variable {F : Type u} {E : Type v} {X : Type w}
variable [Field F] [Field E] [Algebra F E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace X]

/-
Domain-style sampling:
* primary domain: Krull-topological Galois groups and continuity of their action on the ambient
  field;
* sampled owner declarations:
  `krullTopology_mem_nhds_one_iff`,
  `continuousSMul_iff_stabilizer_isOpen`,
  `stabilizer_isOpen_of_isIntegral`,
  `InfiniteGalois.profiniteGalGrp`;
* best owner abstractions: the action side is owned by `ContinuousSMul Gal(E / F) E`, while the
  profinite-group side is owned by `InfiniteGalois.profiniteGalGrp F E`;
* primitive data: the forward continuity criterion uses only the Krull-topology neighborhood basis
  through finite intermediate fields and the discrete topology on `E`, while the converse
  direction is primitive at the `ContinuousSMul` layer;
* derived API: `stabilizer_isOpen_of_isIntegral` gives the canonical open-stabilizer criterion used
  to build the needed `ContinuousSMul` proof in algebraic situations, and `profiniteGalGrp`
  packages the profinite structure.

Layer triage:
* `source-facing`: continuity of `g : X → Gal(E / F)` from continuity of the action map
  `X × E → E`;
* `core/canonical`: the owner class `ContinuousSMul Gal(E / F) E` and the bundled profinite group
  `InfiniteGalois.profiniteGalGrp F E`;
* `bridge/view`: the algebraicity bridge from `stabilizer_isOpen_of_isIntegral` to
  `ContinuousSMul`.
-/
/-- Helper for Lemma 9.22.1: if every evaluation map `x ↦ g x • y` is continuous, then
`g : X → Gal(E / F)` is continuous. This is the pointwise-evaluation bridge behind
Lemma 9.22.1 (1), and the source-facing action-map formulation follows by
`continuous_prod_of_discrete_right`. -/
theorem continuous_of_continuous_galois_eval
    (g : X → Gal(E/F))
    (hg_eval : ∀ y : E, Continuous fun x ↦ g x • y) :
    Continuous g := by
  -- Continuity into the Krull-topological Galois group is checked at each point.
  rw [continuous_iff_continuousAt]
  intro x₀
  let δ : X → Gal(E/F) := fun x ↦ (g x₀)⁻¹ * g x
  -- Translate continuity at `x₀` into convergence of the normalized cocycle `δ` to the identity.
  have hmul : Tendsto δ (𝓝 x₀) (𝓝 (1 : Gal(E/F))) := by
    rw [tendsto_def]
    intro U hU
    rcases (krullTopology_mem_nhds_one_iff F E U).1 hU with ⟨L, hLfin, hL⟩
    letI : FiniteDimensional F L := hLfin
    let b := Module.Basis.ofVectorSpace F L
    have hbasis : (⋂ i, {x : X | g x • (b i : E) = g x₀ • (b i : E)}) ∈ 𝓝 x₀ := by
      rw [iInter_mem]
      intro i
      let V : Set X := {x : X | g x • (b i : E) = g x₀ • (b i : E)}
      have hV : IsOpen V := by
        change IsOpen ((fun x : X ↦ g x • (b i : E)) ⁻¹' {g x₀ • (b i : E)})
        exact (isOpen_discrete _).preimage (hg_eval (b i : E))
      exact hV.mem_nhds rfl
    refine mem_of_superset hbasis ?_
    intro x hx
    -- Membership in the Krull neighborhood is reduced to fixing a finite intermediate field.
    apply hL
    change δ x ∈ L.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hfix : ∀ i, δ x (b i : E) = (b i : E) := by
      intro i
      have hi : g x • (b i : E) = g x₀ • (b i : E) := Set.mem_iInter.mp hx i
      calc
        δ x (b i : E) = (g x₀)⁻¹ • (g x • (b i : E)) := rfl
        _ = (g x₀)⁻¹ • (g x₀ • (b i : E)) := by rw [hi]
        _ = (b i : E) := by simp
    let incl : L →ₗ[F] E := (IsScalarTower.toAlgHom F L E).toLinearMap
    let φ : L →ₗ[F] E := (δ x).toLinearMap.comp incl
    have hlin : φ = incl := by
      apply b.ext
      intro i
      exact hfix i
    let yL : L := ⟨y, hy⟩
    have hy_fix : δ x y = y := by
      have h := congrArg (fun f : L →ₗ[F] E ↦ f yL) hlin
      simpa [φ, incl] using h
    exact hy_fix
  -- Undo the normalization by left multiplication with `g x₀`.
  simpa [ContinuousAt, mul_assoc, δ] using hmul.const_mul (g x₀)

/-- Lemma 9.22.1 (1): the source Galois statement is a specialization of this Krull-topological
result. The Krull topology on `Gal(E/F)` is the
coarsest topology for which the action on the discrete space `E` is continuous. Hence, for a
family `g : X → Gal(E/F)`, continuity of the action map `X × E → E` forces continuity of `g`. -/
theorem continuous_of_continuous_galois_action
    (g : X → Gal(E/F))
    (hact : Continuous fun p : X × E ↦ g p.1 • p.2) :
    Continuous g := by
  -- On a discrete right factor, continuity of the action map is equivalent to pointwise continuity.
  exact continuous_of_continuous_galois_eval g <| continuous_prod_of_discrete_right.mp hact

end

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E]

variable [IsGalois F E]

/- Lemma 9.22.1 (2): for a Galois extension, the Krull-topological Galois group `Gal(E/F)` is the
canonical profinite group `InfiniteGalois.profiniteGalGrp F E`. -/
recall InfiniteGalois.profiniteGalGrp

end

/-! ### Lemma_9_22_2 (from Chap09) -/
universe u v

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [Normal K L] [Normal K M]

/-
Domain-style sampling:
* primary domain: restriction morphisms between Galois groups and the Krull topology;
* sampled owner declarations:
  `AlgEquiv.restrictNormalHom`,
  `AlgEquiv.restrictNormalHom_surjective`,
  `InfiniteGalois.restrictNormalHom_continuous`,
  `galoisTowerRestrictionShortExact`;
* best owner abstraction: the canonical restriction homomorphism
  `AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)`;
* primitive data: a field tower `K ⟶ M ⟶ L` and normality of `L/K` and `M/K`;
* derived API: surjectivity and continuity are the canonical theorem-level consequences above.

Layer triage:
* `source-facing`: Lemma 9.22.2 states that the canonical restriction map is surjective and
  continuous;
* `core/canonical`: `AlgEquiv.restrictNormalHom`;
* `bridge/view`: the source-facing statement is the conjunction of the two canonical owner-level
  facts `AlgEquiv.restrictNormalHom_surjective` and
  `InfiniteGalois.restrictNormalHom_continuous`.

The source text assumes both extensions are Galois, but separability is redundant for these two
canonical properties, so the public context is lowered to the primitive normality hypotheses.
-/
-- Proof sketch: use the canonical restriction homomorphism `AlgEquiv.restrictNormalHom M`;
-- surjectivity is exactly `AlgEquiv.restrictNormalHom_surjective M`, and continuity is exactly
-- `InfiniteGalois.restrictNormalHom_continuous M`.
/-- Lemma 9.22.2: for a tower `L/M/K` with `L/K` and `M/K` normal, the canonical restriction map
`Gal(L / K) → Gal(M / K)` is surjective and continuous for the Krull topologies. -/
theorem restrictNormalHom_surjective_and_continuous :
    Function.Surjective (AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)) ∧
      Continuous (AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)) := by
  constructor
  · -- The algebraic half is exactly the standard surjectivity theorem for restriction.
    exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L)
  · -- The topological half is exactly the standard continuity theorem for restriction.
    exact InfiniteGalois.restrictNormalHom_continuous (k := K) (K := L) M

end

/-! ### Lemma_9_22_3 (from Chap09) -/
universe u v

open CategoryTheory

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]

/- Domain-style sampling for Lemma 9.22.3:
- primary domain: infinite Galois theory and profinite limits of finite Galois groups;
- sampled owner declarations:
  `FiniteGaloisIntermediateField`,
  `FiniteGaloisIntermediateField.adjoin`,
  `InfiniteGalois.asProfiniteGaloisGroupFunctor`,
  `InfiniteGalois.profiniteGalGrpIsoLimit`;
- best owner abstractions: the indexing system is the lattice of finite Galois intermediate
  fields, and the limit statement is owned by the canonical profinite-group isomorphism
  `InfiniteGalois.profiniteGalGrpIsoLimit`;
- primitive data: the finite Galois intermediate fields of `L/K`, ordered by inclusion, together
  with the restriction maps on their finite Galois groups;
- derived API: directedness of the indexing system, containment of finite subsets in finite Galois
  intermediate fields, the inverse system of finite Galois groups, and the profinite limit
  identification of `Gal(L / K)`.

Source/core/bridge triage:
- `source-facing`: the directed system of finite Galois subextensions and the inverse system of
  their Galois groups;
- `core/canonical`: `FiniteGaloisIntermediateField K L` and
  `InfiniteGalois.profiniteGalGrpIsoLimit`;
- `bridge/view`: the topological-group-level equivalence
  `InfiniteGalois.continuousMulEquivToLimit`.

This item is not a pure recall: the directed-system and filtered-union clauses are most naturally
recorded as companion theorem skeletons, while the limit identification itself is already owned by
the canonical `InfiniteGalois` API. -/

/- Companion check: the indexing type of finite Galois subextensions of `L/K` is the canonical
mathlib type `FiniteGaloisIntermediateField K L`. It is ordered by inclusion, and the inverse
system of Galois groups uses the opposite order, i.e. reverse inclusion. -/
#check (FiniteGaloisIntermediateField K L)

-- Proof sketch: use the lattice structure on `FiniteGaloisIntermediateField K L`, where the
-- supremum of two finite Galois intermediate fields is again finite Galois and contains both.
/-- The finite Galois intermediate fields of a Galois extension form a directed system under
inclusion. -/
theorem finiteGaloisIntermediateField_directed :
    Directed (· ≤ ·) (fun E : FiniteGaloisIntermediateField K L ↦
      (E : IntermediateField K L)) := by
  intro E₁ E₂
  refine ⟨E₁ ⊔ E₂, ?_, ?_⟩
  · -- Pass the lattice inequality on finite Galois intermediate fields across the coercion.
    exact (FiniteGaloisIntermediateField.le_iff E₁ (E₁ ⊔ E₂)).mp le_sup_left
  · -- The symmetric lattice inequality gives the second containment.
    exact (FiniteGaloisIntermediateField.le_iff E₂ (E₁ ⊔ E₂)).mp le_sup_right

variable [IsGalois K L]

/- Companion recall: the canonical owner for a finite subset `s ⊆ L` is
`FiniteGaloisIntermediateField.adjoin K s`, and the inclusion of `s` into that finite Galois
intermediate field is `FiniteGaloisIntermediateField.subset_adjoin K s`. -/
recall FiniteGaloisIntermediateField.adjoin

recall FiniteGaloisIntermediateField.subset_adjoin

-- Proof sketch: take the canonical finite Galois intermediate field
-- `FiniteGaloisIntermediateField.adjoin K s`, obtained from the normal closure of the field
-- generated by the finite set `s`.
/-- Every finite subset of a Galois extension is contained in a finite Galois intermediate field. -/
theorem exists_finiteGaloisIntermediateField_of_finite_subset (s : Set L) [Finite s] :
    ∃ E : FiniteGaloisIntermediateField K L, s ⊆ (E : IntermediateField K L) := by
  refine ⟨FiniteGaloisIntermediateField.adjoin K s, ?_⟩
  -- The canonical finite Galois closure of the field generated by `s` contains every element of `s`.
  simpa using FiniteGaloisIntermediateField.subset_adjoin K s

/- Companion recall: the inverse system of finite Galois groups attached to the finite Galois
intermediate fields of `L/K` is the profinite-group-valued functor
`InfiniteGalois.asProfiniteGaloisGroupFunctor K L`; its transition maps are the usual restriction
homomorphisms, hence surjective for finite Galois towers. -/
recall InfiniteGalois.asProfiniteGaloisGroupFunctor :
    (FiniteGaloisIntermediateField K L)ᵒᵖ ⥤ ProfiniteGrp

/- Companion recall: the topological-group-level limit identification is the continuous
multiplicative equivalence `InfiniteGalois.continuousMulEquivToLimit`, whose component maps are the
restriction homomorphisms `Gal(L / K) → Gal(E / K)` from Lemma 9.22.2. -/
recall InfiniteGalois.continuousMulEquivToLimit

/- Lemma 9.22.3: for a Galois extension `L/K`, the finite Galois intermediate fields form the
canonical inverse system of finite Galois groups, and the full Galois group `Gal(L/K)` is the
inverse limit of that system as a profinite group. The bundled canonical owner of this statement is
`InfiniteGalois.profiniteGalGrpIsoLimit`. -/
recall InfiniteGalois.profiniteGalGrpIsoLimit

end

/-! ### Theorem_9_22_4_Fundamental_theorem_of_infinite_Galois_theory (from Chap09) -/
universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/- Domain-style sampling for Theorem 9.22.4:
- primary domain: infinite Galois theory and the Krull-topological Galois correspondence;
- sampled owner declarations:
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`,
  `InfiniteGalois.fixedField_bot`,
  `InfiniteGalois.isOpen_iff_finite`,
  `InfiniteGalois.normal_iff_isGalois`;
- best owner abstraction: the order isomorphism
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`, whose primitive data are the canonical
  maps `IntermediateField.fixingSubgroup` and `IntermediateField.fixedField`;
- derived API: the `K = L^G` clause, the open-subgroup/finite-extension criterion, and the
  normal-subgroup/Galois-subextension criterion are theorem-level consequences of that owner.

Source/core/bridge triage:
- `source-facing`: the infinite Galois correspondence between intermediate fields and closed
  subgroups, together with its standard corollaries;
- `core/canonical`: `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`;
- `bridge/view`: the companion theorems `InfiniteGalois.fixedField_bot`,
  `InfiniteGalois.isOpen_iff_finite`, and `InfiniteGalois.normal_iff_isGalois`.

This item is a pure canonical recall: there is no extra source-facing wrapper to keep once the
owner declaration is identified. -/

/- Theorem 9.22.4 (Fundamental theorem of infinite Galois theory): for a Galois extension `L/K`,
with `Gal(L/K)` equipped with its canonical profinite topology, the infinite Galois correspondence
is the order isomorphism
`InfiniteGalois.IntermediateFieldEquivClosedSubgroup : IntermediateField K L ≃o
    (ClosedSubgroup Gal(L/K))ᵒᵈ`,
sending an intermediate field `M` to the closed subgroup `M.fixingSubgroup` of `Gal(L/K)` and a
closed subgroup `H` to the fixed field `IntermediateField.fixedField H`. -/
recall InfiniteGalois.IntermediateFieldEquivClosedSubgroup

/- Companion recall: the textbook equality `K = L^G` for `G = Gal(L/K)` is encoded by the infinite
Galois theorem `InfiniteGalois.fixedField_bot`, which states that the fixed field of the whole
Galois group, namely `IntermediateField.fixedField ⊤`, is the bottom intermediate field. -/
recall InfiniteGalois.fixedField_bot

/- Companion recall: under the infinite Galois correspondence, the finite intermediate fields are
exactly those whose fixing subgroup is open; this is `InfiniteGalois.isOpen_iff_finite`. -/
recall InfiniteGalois.isOpen_iff_finite

/- Companion recall: under the infinite Galois correspondence, normal closed subgroups correspond
exactly to intermediate fields that are Galois over the base field; this is
`InfiniteGalois.normal_iff_isGalois`. -/
recall InfiniteGalois.normal_iff_isGalois

end

/-! ### Lemma_9_22_5 (from Chap09) -/
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
