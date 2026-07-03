import Mathlib
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.MonCat.Colimits
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp_
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.GroupTopology
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Monoidal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_30_1 (from Chap05) -/
universe u v

/- Domain-style sampling for topological groups:
- inspected owner declarations: `IsTopologicalGroup`, `ContinuousMul`, `ContinuousInv`,
  `ContinuousMonoidHom`
- core/canonical owner: `IsTopologicalGroup`
- primitive data: `ContinuousMul`, `ContinuousInv`
- canonical morphism owner and surface: `ContinuousMonoidHom`, written `G →ₜ* H`
- source-facing bridge: `isTopologicalGroup_iff_continuousMul_continuousInv`

Layer triage:
- `source-facing`: continuity of multiplication and inversion
- `core/canonical`: `IsTopologicalGroup`
- `bridge/view`: the companion theorem unpacking the owner into its primitive mixins

This item should keep the canonical owner as the main entry, use the primitive mixins only as
companion data, and state the morphism notion by the canonical type expression `G →ₜ* H`.
-/

/- Definition 5.30.1 (1): the Stacks notion of a topological group is the canonical mathlib
typeclass `IsTopologicalGroup`. -/
recall IsTopologicalGroup

/- Primitive data for the canonical owner `IsTopologicalGroup`: continuity of multiplication. -/
recall ContinuousMul

/- Primitive data for the canonical owner `IsTopologicalGroup`: continuity of inversion. -/
recall ContinuousInv

/-
Definition 5.30.1 (2): the canonical owner for homomorphisms of topological groups is
`ContinuousMonoidHom`.
-/
recall ContinuousMonoidHom

variable {G : Type u} [TopologicalSpace G] [Group G]

/-- Definition 5.30.1 (1): a topological group is exactly a group with a topology for which
multiplication and inversion are continuous. -/
theorem isTopologicalGroup_iff_continuousMul_continuousInv :
    IsTopologicalGroup G ↔ ContinuousMul G ∧ ContinuousInv G := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hMul, hInv⟩
    exact { toContinuousMul := hMul, toContinuousInv := hInv }

variable {H : Type v} [TopologicalSpace H] [Group H]

/- Definition 5.30.1 (2): a homomorphism of topological groups is written `G →ₜ* H`. -/
#check (G →ₜ* H)

/-! ### Example_5_30_2 (from Chap05) -/
open scoped Topology
open ContinuousMap Topology

universe u

/- Domain-style sampling for compact-open automorphism groups:
- primary domain: compact-open topology on self-homeomorphism spaces, together with the
  discrete-space bridge to permutation groups;
- sampled owner declarations:
  `ContinuousMap.compactOpen`,
  `ContinuousMap.continuous_comp'`,
  `ContinuousMonoidHom.isInducing_toContinuousMap`,
  `Homeomorph.ofDiscrete`;
- core/canonical owner: the self-homeomorphism type `E ≃ₜ E`, viewed inside the compact-open
  function space `C(E, E)`;
- primitive data: the group structure on `E ≃ₜ E` and the canonical forgetful map
  `(E ≃ₜ E) → C(E, E)`;
- derived API: the discrete-space bridge `Equiv.Perm E ≃ E ≃ₜ E` coming from
  `Homeomorph.ofDiscrete`, and the induced topological-group structure in the discrete case.

Layer triage:
- `source-facing`: Example 5.30.2, asserting that the compact-open topology on `Aut(E)` makes the
  self-homeomorphism group into a topological group;
- `core/canonical`: the compact-open topology and composition on `ContinuousMap`;
- `bridge/view`: the discrete identification `Homeomorph.ofDiscrete : Equiv.Perm E → E ≃ₜ E`.

This item should keep `E ≃ₜ E` as the public owner of `Aut(E)`, package the compact-open choice as
an explicit group topology on that owner, and relegate permutations to a thin induced-topology
bridge rather than a second ambient owner.
-/

section

variable {E : Type u} [TopologicalSpace E]

instance : Group (E ≃ₜ E) where
  one := Homeomorph.refl E
  mul f g := g.trans f
  inv := Homeomorph.symm
  mul_assoc f g h := by
    ext x
    rfl
  one_mul f := by
    ext x
    rfl
  mul_one f := by
    ext x
    rfl
  inv_mul_cancel f := by
    ext x
    exact Homeomorph.symm_apply_apply f x

/-- The compact-open topology on the self-homeomorphism group, induced from the ambient
compact-open self-map space `C(E, E)`. -/
abbrev homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E) :=
  TopologicalSpace.induced ((↑) : (E ≃ₜ E) → C(E, E)) ContinuousMap.compactOpen

end

section

variable {E : Type u} [TopologicalSpace E] [DiscreteTopology E]

/-- For a discrete space, a permutation is canonically a self-homeomorphism. -/
def permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E) where
  toFun := Homeomorph.ofDiscrete
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem continuous_apply_homeomorph (x : E) :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    Continuous fun h : E ≃ₜ E ↦ h x := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
  let e : C(E, E) ≃ₜ (E → E) := ContinuousMap.homeoFnOfDiscrete
  have hcont : Continuous (((↑) : (E ≃ₜ E) → C(E, E))) :=
    continuous_induced_dom
  simpa using (continuous_apply x).comp (e.continuous.comp hcont)

private theorem continuous_inv_homeomorphCompactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    Continuous fun h : E ≃ₜ E ↦ h⁻¹ := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
  refine continuous_induced_rng.2 ?_
  let e : C(E, E) ≃ₜ (E → E) := ContinuousMap.homeoFnOfDiscrete
  refine e.isInducing.continuous_iff.2 ?_
  refine continuous_pi fun x : E ↦ ?_
  rw [continuous_discrete_rng]
  intro y
  convert (isOpen_discrete {x}).preimage (continuous_apply_homeomorph y) using 1
  ext h
  simpa [eq_comm] using (h.symm_apply_eq : h⁻¹ x = y ↔ x = h y)

/-- For a discrete space `E`, the compact-open topology on the homeomorphism group `E ≃ₜ E`
is a group topology. -/
def homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E) where
  toTopologicalSpace := homeomorphCompactOpenTopology
  toIsTopologicalGroup := by
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    refine
      { continuous_mul := by
          have hcont : Continuous (((↑) : (E ≃ₜ E) → C(E, E))) :=
            continuous_induced_dom
          have hfst : Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦ (p.2 : C(E, E)) :=
            hcont.comp continuous_snd
          have hsnd : Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦ (p.1 : C(E, E)) :=
            hcont.comp continuous_fst
          refine continuous_induced_rng.2 ?_
          have hpair :
              Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦
                ((p.2 : C(E, E)), (p.1 : C(E, E))) :=
            hfst.prodMk hsnd
          simpa using (ContinuousMap.continuous_comp'.comp hpair)
        continuous_inv := continuous_inv_homeomorphCompactOpen }

/-- Example 5.30.2: for a discrete space `E`, the compact-open topology on the self-homeomorphism
group `E ≃ₜ E` makes `Aut(E)` into a topological group. -/
theorem selfHomeomorphGroup_isTopologicalGroup_compactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    IsTopologicalGroup (E ≃ₜ E) :=
by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  exact (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toIsTopologicalGroup

/-- Under the discrete identification `Equiv.Perm E ≃ E ≃ₜ E`, the permutation presentation
inherits the compact-open topology as the induced bridge topology from the canonical owner
`E ≃ₜ E`. -/
theorem permutationGroup_compactOpen_isHomeomorph :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    letI : TopologicalSpace (Equiv.Perm E) :=
      TopologicalSpace.induced
        ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
    IsHomeomorph ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  letI : TopologicalSpace (Equiv.Perm E) :=
    TopologicalSpace.induced
      ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
  refine (isHomeomorph_iff_isEmbedding_surjective).2 ?_
  refine ⟨⟨⟨rfl⟩, ?_⟩, ?_⟩
  · intro σ τ hστ
    change Homeomorph.ofDiscrete σ = Homeomorph.ofDiscrete τ at hστ
    exact congrArg Homeomorph.toEquiv hστ
  · intro h
    refine ⟨h.toEquiv, ?_⟩
    ext x
    rfl

/-- Bridge form of Example 5.30.2: under the discrete identification
`Equiv.Perm E ≃ E ≃ₜ E`, the permutation model carries the induced compact-open group topology. -/
theorem permutationGroup_isTopologicalGroup_compactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    letI : TopologicalSpace (Equiv.Perm E) :=
      TopologicalSpace.induced
        ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
    IsTopologicalGroup (Equiv.Perm E) := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  letI : IsTopologicalGroup (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toIsTopologicalGroup
  letI : TopologicalSpace (Equiv.Perm E) :=
    TopologicalSpace.induced
      ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
  exact topologicalGroup_induced (permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E))

end

/-! ### Lemma_5_30_3 (from Chap05) -/
universe v u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Monoidal MonoidalCategory CartesianMonoidalCategory MonObj

/- Domain-style sampling for topological groups:
- primary domain: category-theoretic limits of topological groups, organized canonically as group
  objects in `TopCat`.
- sampled owner declarations:
  `Grp TopCat`,
  `Grp.forget TopCat`,
  `Functor.mapGrp`,
  `grpTypeEquivalenceGrp`.
- best owner abstraction: `Grp TopCat` is the core/canonical owner. The only extra data this file
  needs is the bridge from `Grp TopCat` to `GrpCat`, obtained by forgetting `TopCat` to `Type` and
  then using `grpTypeEquivalenceGrp`.

Layer triage:
- `source-facing`: Lemma 5.30.3, asserting that the category of topological groups has limits and
  that the forgetful functors to `TopCat` and `GrpCat` preserve them.
- `core/canonical`: `Grp TopCat` together with the generic `Grp`-limits machinery.
- `bridge/view`: the concrete-category bridge via `ContinuousMonoidHom` and the forgetful functor
  `forget₂ (Grp TopCat) GrpCat`.

Primitive data already lives in the owner `Grp TopCat`. The `GrpCat` bridge and the preservation
results are derived API and should not force an extra public wrapper category; only the concrete
morphism realization by `ContinuousMonoidHom` is needed to build the canonical forgetful functor to
`GrpCat`.
-/

instance (X : Grp TopCat.{u}) : Group X.X where
  one := (TopCat.Hom.hom η[X.X]) PUnit.unit
  mul x y := (TopCat.Hom.hom μ[X.X]) (x, y)
  inv x := (TopCat.Hom.hom ι[X.X]) x
  one_mul x := by
    change (ConcreteCategory.hom (η[X.X] ▷ X.X ≫ μ[X.X])) (PUnit.unit, x) =
      (ConcreteCategory.hom (λ_ X.X).hom) (PUnit.unit, x)
    exact ConcreteCategory.congr_hom (MonObj.one_mul X.X) (PUnit.unit, x)
  mul_one x := by
    change (ConcreteCategory.hom (X.X ◁ η[X.X] ≫ μ[X.X])) (x, PUnit.unit) =
      (ConcreteCategory.hom (ρ_ X.X).hom) (x, PUnit.unit)
    exact ConcreteCategory.congr_hom (MonObj.mul_one X.X) (x, PUnit.unit)
  mul_assoc x y z := by
    change (ConcreteCategory.hom (μ[X.X] ▷ X.X ≫ μ[X.X])) ((x, y), z) =
      (ConcreteCategory.hom ((α_ X.X X.X X.X).hom ≫ X.X ◁ μ[X.X] ≫ μ[X.X])) ((x, y), z)
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc X.X) ((x, y), z)
  inv_mul_cancel x := by
    change (ConcreteCategory.hom (lift ι[X.X] (𝟙 X.X) ≫ μ[X.X])) x =
      (ConcreteCategory.hom (toUnit X.X ≫ η[X.X])) x
    exact ConcreteCategory.congr_hom (GrpObj.left_inv X.X) x

instance instIsMonHomOfContinuousMonoidHom {X Y : Grp TopCat.{u}} (f : X.X →ₜ* Y.X) :
    IsMonHom (show X.X ⟶ Y.X from TopCat.ofHom f.toContinuousMap) where
  one_hom := by
    ext x
    change f 1 = (1 : Y.X)
    simp
  mul_hom := by
    ext x
    change f (x.1 * x.2) = f x.1 * f x.2
    simp

/-- The underlying continuous group homomorphism of a morphism in `Grp TopCat`. -/
private abbrev homToContinuousMonoidHom {X Y : Grp TopCat.{u}} (f : X ⟶ Y) :
    X.X →ₜ* Y.X where
  toFun := f.hom.hom
  map_one' := by
    change (ConcreteCategory.hom (η[X.X] ≫ f.hom.hom)) PUnit.unit =
      (ConcreteCategory.hom η[Y.X]) PUnit.unit
    exact ConcreteCategory.congr_hom (IsMonHom.one_hom f.hom.hom) PUnit.unit
  map_mul' x y := by
    change (ConcreteCategory.hom (μ[X.X] ≫ f.hom.hom)) (x, y) =
      (ConcreteCategory.hom ((f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[Y.X])) (x, y)
    exact ConcreteCategory.congr_hom (IsMonHom.mul_hom f.hom.hom) (x, y)
  continuous_toFun := (TopCat.Hom.hom f.hom.hom).continuous

instance : ConcreteCategory (Grp TopCat.{u}) (fun X Y ↦ X.X →ₜ* Y.X) where
  hom := homToContinuousMonoidHom
  ofHom := by
    intro X Y f
    exact Grp.homMk (show X.X ⟶ Y.X from TopCat.ofHom f.toContinuousMap)
  hom_ofHom := by
    intro X Y f
    ext x
    rfl
  ofHom_hom := by
    intro X Y f
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    rfl

noncomputable instance : HasForget₂ (Grp TopCat.{u}) GrpCat.{u} :=
  { forget₂ := by
      let _ : (forget TopCat.{u}).Monoidal :=
        Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
      exact (forget TopCat.{u}).mapGrp ⋙ grpTypeEquivalenceGrp.functor
    forget_comp := rfl }

/- The proof of preservation to `GrpCat` factors through the internal-group forgetful functor to
`Grp (Type u)`. This helper is implementation-only; the public surface should use
`forget₂ (Grp TopCat) GrpCat`. -/
private noncomputable abbrev topologicalGroupToGrpType : Grp TopCat.{u} ⥤ Grp (Type u) := by
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  exact (forget TopCat.{u}).mapGrp

private noncomputable def topologicalGroupToGrpType_mapConeIsLimit
    {J : Type v} [Category.{w} J] [Small.{u} J]
    (F : J ⥤ Grp TopCat.{u}) :
    IsLimit (topologicalGroupToGrpType.mapCone (limit.cone F)) := by
  dsimp [topologicalGroupToGrpType]
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  apply isLimitOfReflects (Grp.forget (Type u))
  change IsLimit ((forget TopCat.{u}).mapCone ((Grp.forget TopCat.{u}).mapCone (limit.cone F)))
  exact isLimitOfPreserves (forget TopCat.{u})
    (isLimitOfPreserves (Grp.forget TopCat.{u}) (limit.isLimit F))

/-- Lemma 5.30.3 (1): the canonical category `Grp TopCat` of topological groups has limits. -/
instance topologicalGroupCat_hasLimits : HasLimits (Grp TopCat.{u}) :=
  { has_limits_of_shape := fun J _ ↦ by
      let _ : Small.{u} J := inferInstance
      infer_instance }

/-- Lemma 5.30.3 (2): the forgetful functor from topological groups to `TopCat` preserves
limits. -/
instance topologicalGroupCat_forgetToTopCat_preservesLimits :
    PreservesLimits (Grp.forget TopCat.{u}) :=
  { preservesLimitsOfShape := fun {J} _ ↦ by
      simpa using (inferInstance : PreservesLimitsOfShape J (Grp.forget TopCat.{u})) }

/-- Lemma 5.30.3 (3): the forgetful functor to `GrpCat` preserves limits. -/
instance topologicalGroupCat_forgetToGrpCat_preservesLimits :
    PreservesLimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesLimitsOfShape := by
    intro J _
    let _ : Small.{u} J := inferInstance
    exact
      { preservesLimit := fun {F} ↦ by
          exact preservesLimit_of_preserves_limit_cone (limit.isLimit F) <| by
            let _ : (grpTypeEquivalenceGrp.{u}.functor).IsEquivalence := inferInstance
            simpa [topologicalGroupToGrpType] using
              (isLimitOfPreserves grpTypeEquivalenceGrp.functor
                (topologicalGroupToGrpType_mapConeIsLimit F)) }

/-! ### Lemma_5_30_4 (from Chap05) -/
open CategoryTheory Limits

universe u

/- Domain-style sampling for profinite topological groups:
- primary domain: profinite topological groups and their canonical finite-quotient limit
  presentation;
- inspected owner declarations:
  `ProfiniteGrp.of`,
  `ProfiniteGrp.ofContinuousMulEquiv`,
  `ProfiniteGrp.toFiniteQuotientFunctor`,
  `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`.

Best owner abstraction:
- `ProfiniteGrp`, with the bridge predicate `∃ P : ProfiniteGrp, Nonempty (G ≃ₜ* P)` for an
  arbitrary topological group `G`.

Primitive data vs derived API:
- primitive data: the topological-group structure on `G`, plus compactness and total
  disconnectedness packaged canonically by `ProfiniteGrp.of`;
- derived API: forgetting to a profinite space, and the finite-discrete inverse-system
  presentation via `toFiniteQuotientFunctor` and
  `continuousMulEquivLimittoFiniteQuotientFunctor`.

Layer triage:
- `source-facing`: the three-way equivalence in Lemma 5.30.4;
- `core/canonical`: `ProfiniteGrp`;
- `bridge/view`: the equivalence between the source-facing profinite-space clause and the canonical
  bundled profinite-group clause.

The profinite-space condition is not a second owner in the group setting: for topological groups it
is exactly the forgetful view of the canonical `ProfiniteGrp` owner. The finite-group limit clauses
are derived from the owner theorem on open normal finite quotients, so this file should route
through that owner instead of keeping a parallel local construction.
-/

section

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is homeomorphic to a profinite space exactly when it is topologically
isomorphic to a bundled profinite group. -/
theorem exists_profinite_iff_exists_profiniteGrp :
    (∃ P : Profinite.{u}, Nonempty (G ≃ₜ P)) ↔
      ∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P) := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    let _ : CompactSpace G := e.symm.compactSpace
    let _ : TotallyDisconnectedSpace G := e.symm.totallyDisconnectedSpace
    exact ⟨ProfiniteGrp.of G, ⟨ContinuousMulEquiv.refl G⟩⟩
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨P.toProfinite, ⟨e.toHomeomorph⟩⟩

/-- A topological group is topologically isomorphic to a profinite group exactly when it is compact
and totally disconnected. -/
theorem exists_profiniteGrp_iff_compact_totallyDisconnected :
    (∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P)) ↔
      CompactSpace G ∧ TotallyDisconnectedSpace G := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨e.symm.compactSpace, e.symm.totallyDisconnectedSpace⟩
  · rintro ⟨hCompact, hTot⟩
    let _ : CompactSpace G := hCompact
    let _ : TotallyDisconnectedSpace G := hTot
    exact ⟨ProfiniteGrp.of G, ⟨ContinuousMulEquiv.refl G⟩⟩

-- Proof sketch: route the profinite-space clause through the canonical owner
-- `∃ P : ProfiniteGrp, Nonempty (G ≃ₜ* P)`. The cofiltered limit clause is then the canonical
-- finite-quotient presentation of a profinite group given by
-- `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`; forgetting cofilteredness gives
-- the non-cofiltered clause, and any exhibited limit of finite discrete groups is automatically a
-- profinite group.
/-- Lemma 5.30.4: for a topological group, the following are equivalent: the canonical profinite
space condition that `G` be homeomorphic to a bundled profinite space; being topologically
isomorphic to a limit of finite groups endowed with the discrete topology; and admitting such a
presentation over a cofiltered index category. -/
theorem topologicalGroup_profinite_tfae :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (G ≃ₜ P),
        ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ FiniteGrp.{u}),
          Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)),
        ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ FiniteGrp.{u}),
          Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)) ] := by
  tfae_have 1 → 3 := by
    rintro h
    rcases (exists_profinite_iff_exists_profiniteGrp G).1 h with ⟨P, ⟨e⟩⟩
    let _ : Nonempty (OpenNormalSubgroup P) := ⟨{
      toOpenSubgroup := ⊤
      isNormal' := by
        simp }⟩
    refine ⟨OpenNormalSubgroup P, inferInstance, inferInstance, P.toFiniteQuotientFunctor, ?_⟩
    change Nonempty (G ≃ₜ* ProfiniteGrp.limit (P.diagram))
    exact ⟨e.trans (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P)⟩
  tfae_have 3 → 2 := by
    rintro ⟨J, _, _, F, hF⟩
    exact ⟨J, inferInstance, F, hF⟩
  tfae_have 2 → 1 := by
    rintro ⟨J, _, F, ⟨e⟩⟩
    exact
      (exists_profinite_iff_exists_profiniteGrp G).2
        ⟨ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp), ⟨e⟩⟩
  tfae_finish

end

/-! ### Definition_5_30_5 (from Chap05) -/
/- Domain-style sampling for Definition 5.30.5:
- primary domain: profinite topological groups;
- inspected owner declarations:
  `Profinite`,
  `ProfiniteGrp`,
  `ProfiniteGrp.of`,
  `ProfiniteGrp.ofContinuousMulEquiv`.

Best owner abstraction:
- `ProfiniteGrp`; the source-facing profinite-space clause for a topological group is the
  corresponding forgetful view of this bundled owner.

Primitive data vs derived API:
- primitive owner data: a bundled profinite group;
- derived API: the source-facing existence of a homeomorphism to a profinite space, and the
  equivalent existence of a topological-group isomorphism to a bundled profinite group.

Layer triage:
- `source-facing`: the textbook profinite condition for an arbitrary topological group, expressed
  through existence of a topological-group isomorphism to a bundled profinite group;
- `core/canonical`: `ProfiniteGrp`;
- `bridge/view`: `exists_profinite_iff_exists_profiniteGrp`.
-/

/- Lemma 5.30.4: for a topological group, the canonical profinite-space condition is equivalent to
admitting a presentation as a limit of finite discrete groups, and to admitting such a
presentation over a cofiltered index category. -/
recall topologicalGroup_profinite_tfae

/- Companion recall: the bundled owner for profinite spaces. -/
recall Profinite

/- Definition 5.30.5: the canonical owner abstraction for profinite topological groups is the
bundled type `ProfiniteGrp`. The source-text criterion for an arbitrary topological group is the
derived bridge theorem recalled below. -/
recall ProfiniteGrp

/-
Companion source-facing bridge for Definition 5.30.5: a topological group is profinite exactly
when it is topologically isomorphic to a bundled profinite group.
-/
recall exists_profinite_iff_exists_profiniteGrp

/-
Companion form of Definition 5.30.5: a topological group is topologically isomorphic to an object
of `ProfiniteGrp` exactly when it is compact and totally disconnected.
-/
recall exists_profiniteGrp_iff_compact_totallyDisconnected

/-! ### Lemma_5_30_6 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Monoidal MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/- Domain-style sampling for topological groups:
- primary domain: category-theoretic colimits of topological groups, organized canonically as
  group objects in `TopCat`
- sampled declarations in the same owner layer:
  `Grp TopCat`,
  `GroupTopology.coinduced`,
  `MonCat.Colimits.colimitCocone`,
  `MonCat.Colimits.colimitIsColimit`,
  `preservesColimit_of_preserves_colimit_cocone`
- best owner abstraction: `Grp TopCat`, with the underlying `GrpCat` colimit as primitive algebraic
  data and the coarsest compatible group topology as the topological bridge

Layer triage:
- `source-facing`: Lemma 5.30.6 asserts that `Grp TopCat` has colimits and that the forgetful
  functor to `GrpCat` preserves them
- `core/canonical`: the owner `Grp TopCat` and the forgetful bridge `forget₂ (Grp TopCat) GrpCat`
- `bridge/view`: the underlying `MonCat` colimit equipped first with its induced group structure and
  then with the infimum of the coinduced group topologies from the cocone maps

Primitive-vs-derived split:
- primitive data: the `MonCat` colimit carrier for the underlying group diagram, the induced
  inversion, and the resulting coinduced `GroupTopology` on that carrier
- derived API: the owner instances `HasColimits (Grp TopCat)` and
  `PreservesColimits (forget₂ (Grp TopCat) GrpCat)`
- the public surface should therefore install those owner instances directly, with the conjunction
  theorem kept only as a secondary summary
-/

namespace TopologicalGroupCat

noncomputable section

open MonCat.Colimits

variable {J : Type u} [Category.{u} J]

private abbrev underlyingMonoidDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u} ⋙ forget₂ GrpCat.{u} MonCat.{u}

private abbrev underlyingGrpDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u}

/-- Helper for Lemma 5.30.6: every object in the underlying monoid diagram already carries the
ambient group structure coming from `GrpCat`. -/
private instance underlyingMonoidDiagram_obj_group (F : J ⥤ Grp TopCat.{u}) (j : J) :
    Group ((underlyingMonoidDiagram F).obj j) := by
  change Group ((underlyingGrpDiagram F).obj j)
  infer_instance

/-- Helper for Lemma 5.30.6: align the group structure on the topological carrier with the one
seen after forgetting to `GrpCat`. -/
private instance (priority := 100) carrierGroupFromUnderlyingGrpDiagram
    (F : J ⥤ Grp TopCat.{u}) (j : J) : Group (F.obj j).X := by
  change Group ((underlyingGrpDiagram F).obj j)
  infer_instance

/-- Helper for Lemma 5.30.6: the multiplication used on the topological carrier. -/
private abbrev carrierMul (X : Grp TopCat.{u}) : X.X → X.X → X.X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) (a, b)

/-- Helper for Lemma 5.30.6: the multiplication used after forgetting a topological group to
`GrpCat`. -/
private abbrev forgetMul (X : Grp TopCat.{u}) :
    (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X →
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X →
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) ((a : X.X), (b : X.X))

/-- Helper for Lemma 5.30.6: the multiplication used by the `mapGrp` presentation of the forgotten
topological space. -/
private abbrev mapGrpMul (X : Grp TopCat.{u}) [_instMonoidal : (forget TopCat.{u}).Monoidal] :
    ((forget TopCat.{u}).mapGrp.obj X).X →
      ((forget TopCat.{u}).mapGrp.obj X).X →
      ((forget TopCat.{u}).mapGrp.obj X).X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) ((a : X.X), (b : X.X))

/-- Helper for Lemma 5.30.6: multiplying in the topological carrier and then forgetting to
`GrpCat` agrees with multiplying in the forgotten group object. -/
private theorem carrier_mul_as_forget_mul (X : Grp TopCat.{u}) (a b : X.X) :
    ((carrierMul X a b : X.X) : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) =
      forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) := by
  rfl

/-- Helper for Lemma 5.30.6: multiplying in the forgotten group object and then reading the
result back on the topological carrier agrees with the carrier multiplication. -/
private theorem forget_mul_as_carrier_mul (X : Grp TopCat.{u})
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    ((forgetMul X a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X) =
      carrierMul X (a : X.X) (b : X.X) := by
  rfl

/-- Helper for Lemma 5.30.6: the monoidal comparison map for `forget TopCat` sends a pair to the
same pair on underlying types. -/
private theorem forget_monoidal_mu_eq_pair (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : ((forget TopCat.{u}).mapGrp.obj X).X) :
    Functor.LaxMonoidal.μ (forget TopCat.{u}) X.X X.X (a, b) = ((a : X.X), (b : X.X)) := by
  -- The product comparison for the forgetful functor preserves both projections.
  apply Prod.ext
  · simpa using congrFun (Functor.Monoidal.μ_fst (F := forget TopCat.{u}) X.X X.X) (a, b)
  · simpa using congrFun (Functor.Monoidal.μ_snd (F := forget TopCat.{u}) X.X X.X) (a, b)

/-- Helper for Lemma 5.30.6: the explicit forgotten multiplication agrees with the native
`GrpCat` multiplication on the same carrier. -/
private theorem forgetMul_eq_native_mul (X : Grp TopCat.{u})
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    forgetMul X a b = a * b := by
  -- The forgotten `GrpCat` carrier is the `mapGrp` carrier equipped with the native group law.
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  have hmul :=
    congrFun (Functor.comp_mapGrp_mul (F := forget TopCat.{u}) (G := 𝟭 (Type u)) X) (a, b)
  simpa [forgetMul, forget_monoidal_mu_eq_pair (X := X) a b] using hmul.symm

/-- Helper for Lemma 5.30.6: multiplying on the carrier and then viewing the result in the
`mapGrp` presentation agrees with multiplying there directly. -/
private theorem carrier_mul_as_mapGrp_mul (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : X.X) :
    ((carrierMul X a b : X.X) : ((forget TopCat.{u}).mapGrp.obj X).X) =
      mapGrpMul X (a : ((forget TopCat.{u}).mapGrp.obj X).X)
        (b : ((forget TopCat.{u}).mapGrp.obj X).X) := by
  rfl

/-- Helper for Lemma 5.30.6: the explicit `mapGrp` multiplication agrees with the native group
law on the `mapGrp` carrier. -/
private theorem mapGrpMul_eq_native_mul (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : ((forget TopCat.{u}).mapGrp.obj X).X) :
    mapGrpMul X a b = a * b := by
  -- The native multiplication on the `mapGrp` carrier is the transported multiplication from
  -- `X.X`, with the monoidal comparison supplying the pair identification.
  have hmul :=
    congrFun (Functor.comp_mapGrp_mul (F := forget TopCat.{u}) (G := 𝟭 (Type u)) X) (a, b)
  simpa [mapGrpMul, forget_monoidal_mu_eq_pair (X := X) a b] using hmul.symm

/-- Helper for Lemma 5.30.6: the forgotten multiplication is the same binary operation as the
carrier multiplication, viewed on `X.X`. -/
private theorem forget_mul_operation_eq_carrier_mul (X : Grp TopCat.{u}) :
    (fun a b : X.X ↦
      forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) =
      fun a b : X.X ↦ ((carrierMul X a b : X.X) :
        (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) := by
  funext a b
  rfl

/-- Helper for Lemma 5.30.6: the carrier multiplication is the same binary operation as the
forgotten multiplication read back on `X.X`. -/
private theorem carrier_mul_operation_eq_forget_mul (X : Grp TopCat.{u}) :
    (fun a b : X.X ↦
      ((forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
          (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
          (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X)) =
      carrierMul X := by
  funext a b
  rfl

/-- Helper for Lemma 5.30.6: after applying a map out of the forgotten group object, an equality
with carrier multiplication is equivalent to the same equality with forgotten multiplication. -/
private theorem map_eq_carrier_mul_iff_map_eq_forget_mul (X : Grp TopCat.{u}) {β : Sort*}
    (f : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X → β) (a b : X.X) (rhs : β) :
    f (((carrierMul X a b : X.X) : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) = rhs ↔
      f (forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) = rhs := by
  -- This packages the definitional identification of the two source multiplications as a rewrite
  -- on equality propositions after applying an external map.
  rw [carrier_mul_as_forget_mul]

/-- Helper for Lemma 5.30.6: an equality with multiplication read from the forgotten group object
is equivalent to the corresponding equality with carrier multiplication. -/
private theorem eq_forget_mul_iff_eq_carrier_mul (X : Grp TopCat.{u}) (lhs : X.X)
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    lhs = ((forgetMul X a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X) ↔
      lhs = carrierMul X (a : X.X) (b : X.X) := by
  -- This is the codomain-side transport needed after reading forgotten products back on `X.X`.
  rw [forget_mul_as_carrier_mul]

private def prequotientInv {F : J ⥤ Grp TopCat.{u}} :
    Prequotient (underlyingMonoidDiagram F) → Prequotient (underlyingMonoidDiagram F)
  | .of j x => .of j x⁻¹
  | .one => .one
  | .mul x y => .mul (prequotientInv y) (prequotientInv x)

/-- Helper for Lemma 5.30.6: inversion respects the quotient relation used for the monoid colimit. -/
private theorem prequotientInv_rel {F : J ⥤ Grp TopCat.{u}}
    {x y : Prequotient (underlyingMonoidDiagram F)}
    (h : Relation (underlyingMonoidDiagram F) x y) :
    Relation (underlyingMonoidDiagram F) (prequotientInv x) (prequotientInv y) := by
  induction h with
  | refl x =>
      exact Relation.refl _ 
  | symm x y hxy ih =>
      exact Relation.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.trans _ _ _ ihxy ihyz
  | map j j' f x =>
      let g : (underlyingMonoidDiagram F).obj j →* (underlyingMonoidDiagram F).obj j' :=
        ((underlyingMonoidDiagram F).map f).hom
      have hmap :
          g x⁻¹ = (g x)⁻¹ := by
        exact map_inv g x
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j' (((underlyingMonoidDiagram F).map f x)⁻¹))
          (Prequotient.of j x⁻¹)
      rw [← hmap]
      exact Relation.map (F := underlyingMonoidDiagram F) j j' f x⁻¹
  | mul j x y =>
      have hmul : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j ((x * y)⁻¹))
          (Prequotient.mul (Prequotient.of j y⁻¹) (Prequotient.of j x⁻¹))
      rw [hmul]
      exact Relation.mul (F := underlyingMonoidDiagram F) j y⁻¹ x⁻¹
  | one j =>
      have hone : ((1 : (underlyingMonoidDiagram F).obj j)⁻¹) = 1 := inv_one
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j ((1 : (underlyingMonoidDiagram F).obj j)⁻¹))
          Prequotient.one
      rw [hone]
      exact Relation.one (F := underlyingMonoidDiagram F) j
  | mul_1 x x' y h ih =>
      exact Relation.mul_2 _ _ _ ih
  | mul_2 x y y' h ih =>
      exact Relation.mul_1 _ _ _ ih
  | mul_assoc x y z =>
      exact Relation.symm _ _ (Relation.mul_assoc _ _ _)
  | one_mul x =>
      simpa using (Relation.mul_one (prequotientInv x))
  | mul_one x =>
      simpa using (Relation.one_mul (prequotientInv x))

/-- Helper for Lemma 5.30.6: every prequotient expression multiplied by its formal inverse is
equivalent to the unit. -/
private theorem prequotient_inv_mul_rel_one {F : J ⥤ Grp TopCat.{u}} :
    ∀ x : Prequotient (underlyingMonoidDiagram F),
      Relation (underlyingMonoidDiagram F) (.mul (prequotientInv x) x) .one
    := by
  intro x
  induction x with
  | of j x =>
      exact Relation.trans _ _ _
        (Relation.symm _ _ (Relation.mul (F := underlyingMonoidDiagram F) j x⁻¹ x))
        (inv_mul_cancel x ▸
          (Relation.one (F := underlyingMonoidDiagram F) j :
            Relation (underlyingMonoidDiagram F)
              (Prequotient.of j (1 : (underlyingMonoidDiagram F).obj j)) Prequotient.one))
  | one =>
      simpa using (Relation.one_mul (Prequotient.one : Prequotient (underlyingMonoidDiagram F)))
  | mul x y ihx ihy =>
      have h1 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (Prequotient.mul (prequotientInv y) (prequotientInv x))
              (Prequotient.mul x y))
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (prequotientInv x) (Prequotient.mul x y))) :=
        Relation.mul_assoc _ _ _
      have h2 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (prequotientInv x) (Prequotient.mul x y)))
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (Prequotient.mul (prequotientInv x) x) y)) :=
        Relation.mul_2 _ _ _ (Relation.symm _ _ (Relation.mul_assoc _ _ _))
      have h3 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (Prequotient.mul (prequotientInv x) x) y))
            (Prequotient.mul (prequotientInv y) (Prequotient.mul Prequotient.one y)) :=
        Relation.mul_2 _ _ _ (Relation.mul_1 _ _ _ ihx)
      have h4 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y) (Prequotient.mul Prequotient.one y))
            (Prequotient.mul (prequotientInv y) y) :=
        Relation.mul_2 _ _ _ (Relation.one_mul _)
      exact Relation.trans _ _ _
        h1
        (Relation.trans _ _ _
          h2
          (Relation.trans _ _ _
            h3
            (Relation.trans _ _ _
              h4
              ihy)))

private instance colimitInv (F : J ⥤ Grp TopCat.{u}) :
    Inv (ColimitType (underlyingMonoidDiagram F)) where
  inv x :=
    Quotient.liftOn x
      (fun a ↦ Quotient.mk _ (prequotientInv a))
      (fun _ _ h ↦ by
        apply Quotient.sound
        exact prequotientInv_rel h)

private noncomputable instance colimitGroup (F : J ⥤ Grp TopCat.{u}) :
    Group (ColimitType (underlyingMonoidDiagram F)) where
  inv := (colimitInv F).inv
  inv_mul_cancel := by
    -- The quotient group law is checked on prequotient expressions.
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk _ (Prequotient.mul (prequotientInv a) a) = Quotient.mk _ Prequotient.one
    exact Quotient.sound (prequotient_inv_mul_rel_one a)

private noncomputable def grpColimit (F : J ⥤ Grp TopCat.{u}) : GrpCat.{u} :=
  GrpCat.of (ColimitType (underlyingMonoidDiagram F))

private noncomputable def grpColimitCocone (F : J ⥤ Grp TopCat.{u}) :
    Cocone (underlyingGrpDiagram F) where
  pt := grpColimit F
  ι.app j := GrpCat.ofHom ((MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.app j).hom
  ι.naturality i j f := by
    apply (forget₂ GrpCat MonCat).map_injective
    simpa [underlyingGrpDiagram, underlyingMonoidDiagram] using
      (MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.naturality f

private def grpColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (grpColimitCocone F) := by
  -- Route correction: reuse the already-constructed monoid colimit and reflect it to groups.
  apply isColimitOfReflects (forget₂ GrpCat MonCat)
  simpa [grpColimitCocone, grpColimit, underlyingGrpDiagram, underlyingMonoidDiagram] using
    (MonCat.Colimits.colimitIsColimit (underlyingMonoidDiagram F))

private def admissibleGroupTopologies {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Set (GroupTopology c.pt) :=
  { t | ∀ j,
      GroupTopology.coinduced (fun x : (F.obj j).X ↦ (c.ι.app j).hom x) ≤ t }

private def coinducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : GroupTopology c.pt :=
  sInf (admissibleGroupTopologies c)

/-- Helper for Lemma 5.30.6: the underlying function of a group-valued cocone leg, viewed on the
original topological-group carrier. -/
private abbrev coconeLegFun {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) : (F.obj j).X → c.pt :=
  fun x ↦ (c.ι.app j).hom x

/-- Helper for Lemma 5.30.6: a continuous map into a group topology yields an upper bound for the
coinduced group topology. -/
private theorem groupTopology_coinduced_le_of_continuous {α β : Type*}
    [tα : TopologicalSpace α] [Group β] (f : α → β) (t : GroupTopology β)
    (hf : @Continuous α β tα t.toTopologicalSpace f) :
    GroupTopology.coinduced f ≤ t := by
  rw [GroupTopology.coinduced]
  exact sInf_le (show t ∈ { b : GroupTopology β | TopologicalSpace.coinduced f tα ≤ b.toTopologicalSpace } from
    continuous_iff_coinduced_le.1 hf)

/-- Helper for Lemma 5.30.6: the final group topology is above each stagewise coinduced
topology. -/
private theorem stagewise_coinduced_le_coinducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    GroupTopology.coinduced (coconeLegFun c j) ≤ coinducedGroupTopology c := by
  rw [coinducedGroupTopology]
  exact le_sInf fun t ht => ht j

/-- Helper for Lemma 5.30.6: any topological group gives a group object in `TopCat`. -/
private instance topCatGrpObjOfTopologicalGroup (α : Type u) [Group α] [TopologicalSpace α]
    [IsTopologicalGroup α] : GrpObj (TopCat.of α) where
  one := TopCat.ofHom ⟨fun _ ↦ (1 : α), continuous_const⟩
  mul := TopCat.ofHom ⟨fun p : α × α ↦ p.1 * p.2, continuous_mul⟩
  one_mul := by
    apply TopCat.ext
    intro x
    change (1 : α) * x.2 = x.2
    exact _root_.one_mul x.2
  mul_one := by
    apply TopCat.ext
    intro x
    change x.1 * (1 : α) = x.1
    exact _root_.mul_one x.1
  mul_assoc := by
    apply TopCat.ext
    intro x
    change (x.1.1 * x.1.2) * x.2 = x.1.1 * (x.1.2 * x.2)
    exact _root_.mul_assoc x.1.1 x.1.2 x.2
  inv := TopCat.ofHom ⟨fun x : α ↦ x⁻¹, continuous_inv⟩
  left_inv := by
    apply TopCat.ext
    intro x
    change x⁻¹ * x = (1 : α)
    exact inv_mul_cancel x
  right_inv := by
    apply TopCat.ext
    intro x
    change x * x⁻¹ = (1 : α)
    exact mul_inv_cancel x

/-- Helper for Lemma 5.30.6: the carrier of an object of `Grp TopCat` is a topological group. -/
private instance carrierIsTopologicalGroup (X : Grp TopCat.{u}) : IsTopologicalGroup X.X where
  continuous_mul := by
    simpa using (TopCat.Hom.hom μ[X.X]).continuous
  continuous_inv := by
    simpa using (TopCat.Hom.hom ι[X.X]).continuous

private def topologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Grp TopCat.{u} :=
  let t := coinducedGroupTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalGroup c.pt := t.toIsTopologicalGroup
  { X := TopCat.of c.pt }

/-- Helper for Lemma 5.30.6: each cocone leg is continuous for the final group topology. -/
private theorem continuous_to_topologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    @Continuous (F.obj j).X c.pt (F.obj j).X.str (coinducedGroupTopology c).toTopologicalSpace
      (coconeLegFun c j) := by
  -- The final topology is built to dominate every stagewise coinduced topology.
  have hstage :
      GroupTopology.coinduced (coconeLegFun c j) ≤ coinducedGroupTopology c :=
    stagewise_coinduced_le_coinducedGroupTopology c j
  let tStage : GroupTopology c.pt := GroupTopology.coinduced (coconeLegFun c j)
  have hcont :
      @Continuous (F.obj j).X c.pt (F.obj j).X.str tStage.toTopologicalSpace (coconeLegFun c j) :=
    GroupTopology.coinduced_continuous (coconeLegFun c j)
  exact continuous_le_rng hstage hcont

/-- Helper for Lemma 5.30.6: each cocone leg still sends the unit to the unit after equipping the
colimit carrier with the final topology. -/
private theorem coconeLegFun_map_one {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    coconeLegFun c j (1 : (F.obj j).X) = (1 : c.pt) := by
  -- The cocone leg is a group homomorphism on the underlying carrier.
  let one' : (underlyingGrpDiagram F).obj j := 1
  have hone : (one' : (underlyingGrpDiagram F).obj j) = (1 : (F.obj j).X) := rfl
  rw [← hone]
  simpa [coconeLegFun, one'] using (c.ι.app j).hom.map_one

/-- Helper for Lemma 5.30.6: each cocone leg still respects multiplication after equipping the
colimit carrier with the final topology. -/
private theorem coconeLegHom_map_mul {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J)
    (x y : (underlyingGrpDiagram F).obj j) :
    (c.ι.app j).hom (x * y) = (c.ι.app j).hom x * (c.ι.app j).hom y := by
  -- On the forgotten `GrpCat` domain, multiplicativity is exactly the bundled homomorphism law.
  exact (c.ι.app j).hom.map_mul x y

private theorem coconeLegFun_map_mul {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) (x y : (F.obj j).X) :
    coconeLegFun c j (x * y) = coconeLegFun c j x * coconeLegFun c j y := by
  -- Route correction: rewrite the source multiplication onto the forgotten `GrpCat` carrier and
  -- then apply multiplicativity of the algebraic cocone leg.
  exact
    (map_eq_carrier_mul_iff_map_eq_forget_mul (X := F.obj j) ((c.ι.app j).hom) x y
      ((c.ι.app j).hom (x : (underlyingGrpDiagram F).obj j) *
        (c.ι.app j).hom (y : (underlyingGrpDiagram F).obj j))).2
      (by
        -- We rewrite the explicit forgotten product to the native `GrpCat` multiplication.
        rw [forgetMul_eq_native_mul]
        exact
          coconeLegHom_map_mul (c := c) (j := j) (x := (x : (underlyingGrpDiagram F).obj j))
            (y := (y : (underlyingGrpDiagram F).obj j)))

/-- Helper for Lemma 5.30.6: a cocone leg in `GrpCat` can be viewed directly as a bundled
monoid hom on the original topological-group carrier. -/
private abbrev coconeLegMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) : (F.obj j).X →* c.pt :=
  { toFun := coconeLegFun c j
    map_one' := coconeLegFun_map_one c j
    map_mul' := coconeLegFun_map_mul c j }

/-- Helper for Lemma 5.30.6: each cocone leg becomes a continuous monoid hom into the final
topological colimit. -/
private def coconeLegContinuousMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    (F.obj j).X →ₜ* (topologicalColimit c).X :=
  { toFun := coconeLegFun c j
    map_one' := coconeLegFun_map_one c j
    map_mul' := coconeLegFun_map_mul c j
    continuous_toFun := continuous_to_topologicalColimit c j }

private def toTopologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    F.obj j ⟶ topologicalColimit c :=
  ConcreteCategory.ofHom (C := Grp TopCat.{u}) (coconeLegContinuousMonoidHom c j)

/-- Helper for Lemma 5.30.6: the topological colimit legs inherit naturality from the algebraic
cocone legs. -/
private theorem toTopologicalColimit_naturality {F : J ⥤ Grp TopCat.{u}}
    {i j : J} (f : i ⟶ j) :
    F.map f ≫ toTopologicalColimit (grpColimitCocone F) j =
      toTopologicalColimit (grpColimitCocone F) i := by
  -- The concrete realization preserves the underlying function, so extensionality reduces
  -- naturality to the `GrpCat` cocone identity.
  ext x
  simpa [toTopologicalColimit, coconeLegContinuousMonoidHom, coconeLegFun] using
    ConcreteCategory.congr_hom ((grpColimitCocone F).ι.naturality f) x

private def topologicalColimitCocone (F : J ⥤ Grp TopCat.{u}) : Cocone F where
  pt := topologicalColimit (grpColimitCocone F)
  ι.app j := toTopologicalColimit (grpColimitCocone F) j
  ι.naturality _ _ f := toTopologicalColimit_naturality (F := F) f

/-- Helper for Lemma 5.30.6: the algebraic universal map from the group colimit to any target
cocone point. -/
private abbrev algebraicDesc {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F ⟶ (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt :=
  (grpColimitIsColimit F).desc ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s)

/-- Helper for Lemma 5.30.6: the algebraic desc map viewed as a function to the target carrier. -/
private abbrev algebraicDescFun {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F → s.pt.X :=
  fun x ↦ (algebraicDesc (F := F) s).hom x

/-- Helper for Lemma 5.30.6: reading the forgotten target multiplication of the algebraic desc map
back on the topological carrier recovers the carrier multiplication. -/
private theorem algebraicDesc_forget_mul_as_carrier_mul {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) (x y : grpColimit F) :
    ((forgetMul s.pt ((algebraicDesc (F := F) s).hom x)
        ((algebraicDesc (F := F) s).hom y) :
        (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) : s.pt.X) =
      carrierMul s.pt ((algebraicDesc (F := F) s).hom x : s.pt.X)
        ((algebraicDesc (F := F) s).hom y : s.pt.X) := by
  -- This is the codomain transport from the forgotten group object back to `s.pt.X`.
  exact
    forget_mul_as_carrier_mul (X := s.pt)
      ((algebraicDesc (F := F) s).hom x)
      ((algebraicDesc (F := F) s).hom y)

/-- Helper for Lemma 5.30.6: the algebraic desc map sends the unit to the unit. -/
private theorem algebraicDescFun_map_one {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    algebraicDescFun (F := F) s 1 = (1 : s.pt.X) := by
  -- This is the unit law for the algebraic desc map, read on the topological carrier.
  change ((algebraicDesc (F := F) s).hom 1 :
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
    (1 : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
  exact (algebraicDesc (F := F) s).hom.map_one

/-- Helper for Lemma 5.30.6: the algebraic desc map respects multiplication on the carrier. -/
private theorem algebraicDescFun_map_mul {F : J ⥤ Grp TopCat.{u}} (s : Cocone F)
    (x y : grpColimit F) :
    algebraicDescFun (F := F) s (x * y) =
      algebraicDescFun (F := F) s x * algebraicDescFun (F := F) s y := by
  -- The desc map is already a group homomorphism on the underlying carrier.
  -- We first use multiplicativity in the forgotten `GrpCat` codomain and then rewrite that
  -- product back to the carrier multiplication on `s.pt.X`.
  exact
    (eq_forget_mul_iff_eq_carrier_mul (X := s.pt)
      ((algebraicDesc (F := F) s).hom (x * y))
      ((algebraicDesc (F := F) s).hom x)
      ((algebraicDesc (F := F) s).hom y)).1
      (by
        -- This `change` rewrites the codomain product into the explicit forgotten multiplication.
        change
          ((algebraicDesc (F := F) s).hom (x * y) :
              (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
            forgetMul s.pt ((algebraicDesc (F := F) s).hom x)
              ((algebraicDesc (F := F) s).hom y)
        rw [forgetMul_eq_native_mul]
        exact (algebraicDesc (F := F) s).hom.map_mul x y)

/-- Helper for Lemma 5.30.6: the algebraic desc map viewed as a bundled monoid hom to the target
topological-group carrier. -/
private abbrev algebraicDescMonoidHom {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F →* s.pt.X where
  toFun := algebraicDescFun (F := F) s
  map_one' := algebraicDescFun_map_one (F := F) s
  map_mul' := algebraicDescFun_map_mul (F := F) s

/-- Helper for Lemma 5.30.6: the algebraic desc map factors each algebraic cocone leg through the
corresponding target cocone leg. -/
private theorem algebraicDesc_comp_coconeLeg {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) (j : J) :
    algebraicDescFun (F := F) s ∘ coconeLegFun (grpColimitCocone F) j =
      fun x ↦ s.ι.app j x := by
  -- The group-colimit factorization gives the required carrier-level equality.
  funext x
  simpa [algebraicDescFun, algebraicDesc, coconeLegFun, Function.comp] using
    ConcreteCategory.congr_hom
      ((grpColimitIsColimit F).fac ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) j) x

/-- Helper for Lemma 5.30.6: a cocone leg of the target cocone is continuous on the underlying
carriers. -/
private theorem continuous_targetCoconeLeg {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) (j : J) :
    Continuous (fun x : (F.obj j).X ↦ s.ι.app j x) := by
  -- The concrete-category realization of a morphism in `Grp TopCat` is a continuous monoid hom.
  change Continuous (ConcreteCategory.hom (s.ι.app j))
  exact (ConcreteCategory.hom (s.ι.app j)).continuous

/-- Helper for Lemma 5.30.6: the topology induced on the algebraic colimit by the algebraic desc
map to a target cocone point. -/
private def descInducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : GroupTopology (grpColimit F) :=
  { toTopologicalSpace := TopologicalSpace.induced (algebraicDescFun (F := F) s) s.pt.X.str
    toIsTopologicalGroup := topologicalGroup_induced (algebraicDescMonoidHom (F := F) s) }

/-- Helper for Lemma 5.30.6: the topology induced by the algebraic desc map is admissible for the
final-topology construction on the algebraic colimit. -/
private theorem descInducedGroupTopology_admissible {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) :
    coinducedGroupTopology (grpColimitCocone F) ≤ descInducedGroupTopology (F := F) s := by
  -- Each stage leg becomes continuous into the induced topology because its composite with the
  -- desc map is the given continuous target cocone leg.
  rw [coinducedGroupTopology, admissibleGroupTopologies]
  refine sInf_le ?_
  intro j
  apply groupTopology_coinduced_le_of_continuous (t := descInducedGroupTopology (F := F) s)
  rw [descInducedGroupTopology]
  rw [continuous_iff_le_induced]
  rw [induced_compose]
  have hscont : Continuous (algebraicDescFun (F := F) s ∘ coconeLegFun (grpColimitCocone F) j) := by
    -- The algebraic factorization identifies the composite with the given target cocone leg.
    simpa [algebraicDesc_comp_coconeLeg (F := F) s j, Function.comp] using
      continuous_targetCoconeLeg (F := F) s j
  exact continuous_iff_le_induced.1 hscont

/-- Helper for Lemma 5.30.6: the algebraic desc map is continuous from the final group topology on
the colimit carrier. -/
private theorem continuous_algebraicDesc {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    @Continuous (grpColimit F) s.pt.X
      (coinducedGroupTopology (grpColimitCocone F)).toTopologicalSpace s.pt.X.str
      (algebraicDescFun (F := F) s) := by
  -- Continuity is exactly the comparison between the final source topology and the induced one.
  rw [continuous_iff_le_induced]
  simpa [descInducedGroupTopology] using
    (descInducedGroupTopology_admissible (F := F) s)

/-- Helper for Lemma 5.30.6: the universal map to any target cocone is a continuous monoid hom. -/
private def topologicalColimitDescContinuousMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : (topologicalColimit (grpColimitCocone F)).X →ₜ* s.pt.X :=
  { toFun := algebraicDescFun (F := F) s
    map_one' := (algebraicDescMonoidHom (F := F) s).map_one
    map_mul' := (algebraicDescMonoidHom (F := F) s).map_mul
    continuous_toFun := continuous_algebraicDesc (F := F) s }

/-- Helper for Lemma 5.30.6: the universal morphism from the constructed topological colimit to
any target cocone. -/
private def topologicalColimitDesc {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : topologicalColimit (grpColimitCocone F) ⟶ s.pt :=
  ConcreteCategory.ofHom (C := Grp TopCat.{u}) (topologicalColimitDescContinuousMonoidHom s)

/-- Helper for Lemma 5.30.6: a morphism of topological groups remains multiplicative after reading
its values in the forgotten `GrpCat` codomain. -/
private theorem forgetful_hom_map_mul {F : J ⥤ Grp TopCat.{u}} (s : Cocone F)
    (m : (topologicalColimitCocone F).pt ⟶ s.pt) :
    ∀ x y : grpColimit F,
      (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom (x * y)) :
          (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
        ((((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x) :
            (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) *
          (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) :
            (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)) := by
  intro x y
  -- Package multiplicativity of the continuous monoid hom through the carrier-to-forgetful
  -- coercion on the codomain.
  have h :=
    congrArg
      (fun z : s.pt.X ↦ (z : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt))
      ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).map_mul x y)
  exact h

private def topologicalColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (topologicalColimitCocone F) where
  desc s := topologicalColimitDesc (F := F) s
  fac s i := by
    -- The topological factorization is the algebraic factorization on underlying carriers.
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    simpa [topologicalColimitCocone, toTopologicalColimit, topologicalColimitDesc,
      topologicalColimitDescContinuousMonoidHom, coconeLegContinuousMonoidHom,
      coconeLegFun, algebraicDescFun, algebraicDesc] using
      ConcreteCategory.congr_hom
        ((grpColimitIsColimit F).fac ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) i) x
  uniq s m hm := by
    -- Forgetting to `GrpCat` reduces uniqueness to the algebraic colimit.
    let _ : (forget TopCat.{u}).Monoidal :=
      Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
    let mGrp : grpColimit F ⟶ (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt :=
      GrpCat.ofHom
        { toFun := fun x ↦
            (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x) :
              (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
          map_one' := by
            change (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom 1) :
                (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
              (1 : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
            exact (ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom.map_one
          map_mul' := by
            -- Route correction: prove multiplicativity on `s.pt.X` first and then transport the
            -- resulting equality to the `mapGrp` carrier presentation.
            intro x y
            -- We cast the carrier-level multiplicativity statement into the `mapGrp` presentation
            -- and then rewrite the codomain product via the explicit `mapGrp` multiplication.
            have h_cast :
                (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom (x * y) : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) =
                  ((carrierMul s.pt ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                      ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) := by
              exact
                congrArg
                  (fun z : s.pt.X ↦ (z : ((forget TopCat.{u}).mapGrp.obj s.pt).X))
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).map_mul x y)
            have h_mapGrp :
                ((carrierMul s.pt ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                    ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) : s.pt.X) :
                  ((forget TopCat.{u}).mapGrp.obj s.pt).X) =
                mapGrpMul s.pt
                  (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)
                  (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) := by
              exact
                carrier_mul_as_mapGrp_mul (X := s.pt)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y)
            exact h_cast.trans <| h_mapGrp.trans <| by
              simpa using
                (mapGrpMul_eq_native_mul (X := s.pt)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)) }
    have hm' : ∀ j, (grpColimitCocone F).ι.app j ≫ mGrp =
        ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s).ι.app j := by
      intro j
      ext x
      simpa [mGrp, topologicalColimitCocone, toTopologicalColimit, coconeLegContinuousMonoidHom,
        topologicalColimitDesc, topologicalColimitDescContinuousMonoidHom, coconeLegFun,
        algebraicDescFun, algebraicDesc] using ConcreteCategory.congr_hom (hm j) x
    have huniq : mGrp = algebraicDesc (F := F) s :=
      (grpColimitIsColimit F).uniq ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) mGrp hm'
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    simpa [mGrp, topologicalColimitDesc, topologicalColimitDescContinuousMonoidHom,
      algebraicDescFun, algebraicDesc] using ConcreteCategory.congr_hom huniq x

/-- Helper for Lemma 5.30.6: equip a group with the indiscrete topology and view it as an object of
`Grp TopCat`. -/
private noncomputable def trivialGrp : GrpCat.{u} ⥤ Grp TopCat.{u} := by
  let _ : TopCat.trivial.IsRightAdjoint := ⟨_, ⟨TopCat.adj₂⟩⟩
  let _ : PreservesFiniteProducts TopCat.trivial := inferInstance
  let _ : TopCat.trivial.Monoidal := Functor.Monoidal.ofChosenFiniteProducts TopCat.trivial
  exact grpTypeEquivalenceGrp.inverse ⋙ TopCat.trivial.mapGrp

/-- Helper for Lemma 5.30.6: the forgetful functor to groups is left adjoint to the indiscrete
topology functor on groups. -/
private noncomputable def trivialGrpAdj :
    forget₂ (Grp TopCat.{u}) GrpCat.{u} ⊣ trivialGrp := by
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  let _ : TopCat.trivial.IsRightAdjoint := ⟨_, ⟨TopCat.adj₂⟩⟩
  let _ : PreservesFiniteProducts TopCat.trivial := inferInstance
  let _ : TopCat.trivial.Monoidal := Functor.Monoidal.ofChosenFiniteProducts TopCat.trivial
  simpa [trivialGrp, Functor.comp_assoc] using
    ((CategoryTheory.Adjunction.mapGrp TopCat.adj₂).comp grpTypeEquivalenceGrp.toAdjunction)

instance hasColimitsOfShape (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (Grp TopCat.{u}) where
  has_colimit F := ⟨⟨topologicalColimitCocone F, topologicalColimitIsColimit F⟩⟩

/-- Lemma 5.30.6 (1): the category of topological groups has colimits of every small shape. -/
instance hasColimits : HasColimits (Grp TopCat.{u}) where
  has_colimits_of_shape K _ := by
    infer_instance

instance forgetToGrpCat_preservesColimitsOfShape (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimit := fun {F} ↦ by
    -- The forgetful functor is a left adjoint, hence it preserves colimits.
    let _ : PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) :=
      Adjunction.leftAdjoint_preservesColimits trivialGrpAdj
    infer_instance

/-- Lemma 5.30.6 (2): the forgetful functor from topological groups to groups preserves colimits. -/
instance forgetToGrpCat_preservesColimits :
    PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimitsOfShape {J} := by
    infer_instance

end

end TopologicalGroupCat

/-- Summary theorem collecting the colimit existence and preservation instances for
`Grp TopCat`. -/
theorem topologicalGroupCat_hasColimits_and_forgetToGrpCat_preservesColimits :
    HasColimits (Grp TopCat.{u}) ∧
      PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := by
  exact ⟨TopologicalGroupCat.hasColimits, TopologicalGroupCat.forgetToGrpCat_preservesColimits⟩

/-! ### Definition_5_30_7 (from Chap05) -/
universe u

/- Domain-style sampling for topological rings:
- primary domain: topological algebra of rings and the bundled category of topological
  commutative rings
- sampled mathlib owner declarations:
  `IsTopologicalRing`,
  `ContinuousAdd`,
  `ContinuousMul`,
  `TopCommRingCat.of`
- sampled neighboring project declarations:
  `Lemma_5_30_8.topologicalRingCat_hasLimits_and_forget_preservesLimits`,
  `Definition_5_30_10`,
  `Definition_15_36_1_Topological_rings`
- best owner abstraction: `IsTopologicalRing` for the unbundled notion, with `TopCommRingCat` as
  the bundled owner for morphisms

Layer triage:
- `source-facing`: the Stacks restatement that, for commutative rings, the topological-ring
  condition is
  equivalent to continuity of addition and multiplication
- `core/canonical`: `IsTopologicalRing` and `TopCommRingCat`
- `bridge/view`: the iff theorem below, which explicitly unfolds the primitive continuity data of
  the canonical owner without introducing any parallel wrapper

Primitive data for the owner `IsTopologicalRing` is exactly `ContinuousAdd` and `ContinuousMul`,
while continuity of negation is derived in the ring setting. The hom type in part (2) is derived
categorical API from the bundled owner `TopCommRingCat`.
-/

/-
Clause (1): in the Stacks convention, rings are commutative with `1`, and the canonical
mathlib notion of a topological ring is the typeclass `IsTopologicalRing`. For commutative
rings, this is the same as requiring addition and multiplication to be continuous, since
continuity of negation follows automatically. -/
recall IsTopologicalRing

/- Primitive data for the canonical owner `IsTopologicalRing`: continuity of addition. -/
recall ContinuousAdd

/- Primitive data for the canonical owner `IsTopologicalRing`: continuity of multiplication. -/
recall ContinuousMul

/- Companion recall: topological commutative rings form the canonical bundled category
`TopCommRingCat`. -/
recall TopCommRingCat

/- The canonical constructor for bundling an unbundled topological commutative ring is
`TopCommRingCat.of`. -/
recall TopCommRingCat.of

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- Definition 5.30.7 (1): a topological ring is exactly a ring with a topology for which
addition and multiplication are continuous. -/
theorem isTopologicalRing_iff_continuousAdd_continuousMul :
    IsTopologicalRing R ↔ ContinuousAdd R ∧ ContinuousMul R := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hAdd, hMul⟩
    let _ : IsTopologicalSemiring R := { toContinuousAdd := hAdd, toContinuousMul := hMul }
    exact IsTopologicalSemiring.toIsTopologicalRing inferInstance

end

section

variable {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
variable [IsTopologicalRing R] [IsTopologicalRing S]

/- Definition 5.30.7 (2): a homomorphism of topological rings from `R` to `S` is a morphism in
the canonical category `TopCommRingCat`, whose hom type is realized in mathlib by continuous ring
homomorphisms. -/
#check (TopCommRingCat.of R ⟶ TopCommRingCat.of S)

end
