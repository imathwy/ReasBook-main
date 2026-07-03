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


/-! ### Lemma_5_30_8 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace

-- In the Stacks Project convention, a “ring” is commutative. The canonical bundled mathlib
-- owner abstraction for topological rings is therefore `TopCommRingCat`.

/- Domain-style sampling for topological rings:
- primary domain: category-theoretic limits in `TopCommRingCat` and preservation by the canonical
  forgetful functors to `TopCat` and `CommRingCat`.
- sampled canonical declarations:
  `TopCommRingCat`,
  `CommRingCat.limitCone`,
  `CommRingCat.limitConeIsLimit`,
  `TopCat.isLimitConeOfForget`,
  `TopModuleCat.ofCone`,
  `TopModuleCat.isLimit`.
- best owner abstraction: `TopCommRingCat` for the source-facing result, with the underlying
  `CommRingCat` limit cone as primitive data and the induced topology as derived owner data.

Primitive-vs-derived split:
- primitive data: the underlying `CommRingCat` limit cone and the induced topology on its cone
  point;
- derived API: the resulting `HasLimitsOfSize` / `HasLimits` and `PreservesLimitsOfSize` /
  `PreservesLimits` instances for `TopCommRingCat` and its forgetful functors.

Layer triage:
- `source-facing`: Lemma 5.30.8, asserting existence of limits in `TopCommRingCat` and
  preservation by the two forgetful functors.
- `core/canonical`: the canonical owner instances `HasLimits` / `HasLimitsOfSize` for
  `TopCommRingCat` and `PreservesLimits` / `PreservesLimitsOfSize` for the forgetful functors.
- `bridge/view`: the induced topology on the underlying `CommRingCat` limit cone and its
  comparison with the corresponding `TopCat` limit cone.
-/

namespace TopCommRingCat

noncomputable section

universe v u w

variable {J : Type v} [Category.{w} J]

private abbrev underlyingDiagram (F : J ⥤ TopCommRingCat.{u}) :=
  F ⋙ forget₂ TopCommRingCat CommRingCat

private instance objTopologicalSpace (F : J ⥤ TopCommRingCat.{u}) (j : J) :
    TopologicalSpace ((underlyingDiagram F).obj j) :=
  TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)

private def induced {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) :
    TopCommRingCat.{u} :=
  letI : TopologicalSpace c.pt := ⨅ j,
    TopologicalSpace.induced (show c.pt → F.obj j from (c.π.app j).hom) inferInstance
  letI : ContinuousAdd c.pt := continuousAdd_iInf fun j ↦
    continuousAdd_induced (show c.pt →+* F.obj j from (c.π.app j).hom)
  letI : ContinuousMul c.pt := continuousMul_iInf fun j ↦
    continuousMul_induced (show c.pt →+* F.obj j from (c.π.app j).hom)
  letI : IsTopologicalSemiring c.pt :=
    { toContinuousAdd := inferInstance, toContinuousMul := inferInstance }
  letI : IsTopologicalRing c.pt := IsTopologicalSemiring.toIsTopologicalRing inferInstance
  TopCommRingCat.of c.pt

private def fromInduced {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) (j : J) :
    induced c ⟶ F.obj j :=
  ⟨show induced c →+* F.obj j from (c.π.app j).hom,
    continuous_iff_le_induced.mpr (iInf_le _ j)⟩

private def ofCone {F : J ⥤ TopCommRingCat.{u}} (c : Cone (underlyingDiagram F)) : Cone F where
  pt := induced c
  π :=
    { app := fromInduced c
      naturality := by
        intro i j f
        apply Subtype.ext
        change
          CommRingCat.Hom.hom (((Functor.const J).obj c.pt).map f ≫ c.π.app j) =
            CommRingCat.Hom.hom (c.π.app i ≫ (underlyingDiagram F).map f)
        simpa using congrArg CommRingCat.Hom.hom (c.π.naturality f) }

private def isLimit {F : J ⥤ TopCommRingCat.{u}} {c : Cone (underlyingDiagram F)}
    (hc : IsLimit c) : IsLimit (ofCone c) :=
  IsLimit.ofFaithful (forget₂ TopCommRingCat CommRingCat)
    (by
      simpa [ofCone, fromInduced] using hc)
    (fun s ↦
      ⟨show s.pt →+* induced c from (hc.lift ((forget₂ TopCommRingCat CommRingCat).mapCone s)).hom,
        by
          rw [continuous_iff_coinduced_le]
          refine le_iInf fun j ↦ ?_
          exact (coinduced_le_iff_le_induced).2 <| by
            rw [← continuous_iff_le_induced]
            refine (continuous_induced_rng).2 ?_
            let g : s.pt →+* F.obj j :=
              ((hc.lift ((forget₂ TopCommRingCat CommRingCat).mapCone s)) ≫ c.π.app j).hom
            change Continuous g
            have hg : g = (s.π.app j).1 := by
              ext x
              exact congrArg (fun f ↦ f x)
                (congrArg CommRingCat.Hom.hom
                  (hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCone s) j))
            simpa [hg] using (s.π.app j).2⟩)
    fun _ ↦ rfl

private instance hasLimit (F : J ⥤ TopCommRingCat.{u}) [HasLimit (underlyingDiagram F)] :
    HasLimit F :=
  ⟨_, isLimit (limit.isLimit (underlyingDiagram F))⟩

/-- `TopCommRingCat` has limits of all small shapes. -/
instance hasLimitsOfShape (J : Type v) [Category.{w} J] [Small.{u} J] :
    HasLimitsOfShape J TopCommRingCat.{u} where
  has_limit F := by infer_instance

/-- `TopCommRingCat` has all small limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} TopCommRingCat.{u} where
  has_limits_of_shape K _ := by
    let _ : Small.{u} K := inferInstance
    infer_instance

/-- Lemma 5.30.8 (1): the category of topological rings has all small limits. -/
instance hasLimits : HasLimits TopCommRingCat.{u} where
  has_limits_of_shape K _ := by
    let _ : Small.{u} K := inferInstance
    infer_instance

/-- Auxiliary preservation of a fixed limit cone by the forgetful functor to `TopCat`. -/
private instance forgetToTopCat_preservesLimit {F : J ⥤ TopCommRingCat.{u}}
    [HasLimit (underlyingDiagram F)] [PreservesLimit (underlyingDiagram F) (forget CommRingCat)] :
    PreservesLimit F (forget₂ TopCommRingCat.{u} TopCat.{u}) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit (underlyingDiagram F))) <| by
    let cTop : Cone ((F ⋙ forget₂ TopCommRingCat TopCat) ⋙ forget TopCat) :=
      (forget CommRingCat).mapCone (limit.cone (underlyingDiagram F))
    have hcTop : IsLimit cTop := by
      simpa [cTop] using
        (isLimitOfPreserves (forget CommRingCat) (limit.isLimit (underlyingDiagram F)))
    simpa [ofCone, fromInduced, induced, cTop] using TopCat.isLimitConeOfForget cTop hcTop

instance forgetToTopCat_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ TopCommRingCat.{u} TopCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    exact { preservesLimit := fun {F} ↦ inferInstance }

/-- Lemma 5.30.8 (2): the forgetful functor from topological rings to topological spaces preserves
all small limits. -/
instance forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    infer_instance

private instance forgetToCommRingCat_preservesLimit {F : J ⥤ TopCommRingCat.{u}}
    [HasLimit (underlyingDiagram F)] :
    PreservesLimit F (forget₂ TopCommRingCat.{u} CommRingCat.{u}) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit (underlyingDiagram F))) <| by
    simpa [ofCone, fromInduced, induced] using (limit.isLimit (underlyingDiagram F))

instance forgetToCommRingCat_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    exact { preservesLimit := fun {F} ↦ inferInstance }

/-- Lemma 5.30.8 (3): the forgetful functor from topological rings to commutative rings preserves
all small limits. -/
instance forgetToCommRingCat_preservesLimits :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesLimitsOfShape := by
    intro K _
    let _ : Small.{u} K := inferInstance
    infer_instance

end

end TopCommRingCat

/-! ### Lemma_5_30_9 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits

universe u

/- Domain-style sampling for topological rings:
- primary domain: category-theoretic colimits in `TopCommRingCat`, built from the canonical
  `CommRingCat` colimit and the lattice of ring topologies.
- sampled canonical declarations:
  `CommRingCat.Colimits.colimitCocone`,
  `CommRingCat.Colimits.colimitIsColimit`,
  `RingTopology.coinduced`,
  `continuous_induced_rng`,
  `preservesColimit_of_preserves_colimit_cocone`.
- best owner abstraction: the `CommRingCat` colimit cocone is the primitive algebraic data; the
  topological-ring structure on its cocone point is derived from the canonical `RingTopology`
  lattice by taking the infimum of the admissible ring topologies making all cocone maps
  continuous.

Layer triage:
- `source-facing`: Lemma 5.30.9, asserting colimits in `TopCommRingCat` and preservation by the
  forgetful functor to `CommRingCat`.
- `core/canonical`: `HasColimitsOfShape` / `HasColimitsOfSize` for `TopCommRingCat` and
  `PreservesColimitsOfShape` / `PreservesColimitsOfSize` for
  `forget₂ TopCommRingCat CommRingCat`.
- `bridge/view`: the infimum of the admissible ring topologies on the `CommRingCat` colimit.
-/

namespace TopCommRingCat

noncomputable section

variable {J : Type u} [Category.{u} J]

private abbrev underlyingDiagram (F : J ⥤ TopCommRingCat.{u}) :=
  F ⋙ forget₂ TopCommRingCat CommRingCat

private def admissibleRingTopologies {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : Set (RingTopology c.pt) :=
  { t | ∀ j,
      letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
        TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
      RingTopology.coinduced (c.ι.app j).hom ≤ t }

private def coinducedRingTopology {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : RingTopology c.pt :=
  sInf (admissibleRingTopologies c)

private def coinduced {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : TopCommRingCat.{u} :=
  let t := coinducedRingTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalRing c.pt := t.toIsTopologicalRing
  TopCommRingCat.of c.pt

private def toCoinduced {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) (j : J) : F.obj j ⟶ coinduced c :=
  ⟨(c.ι.app j).hom, by
    letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
      TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
    change @Continuous (F.obj j) c.pt (F.obj j).isTopologicalSpace
      (coinducedRingTopology c).toTopologicalSpace (c.ι.app j).hom
    refine continuous_sInf_rng.2 fun _ ht ↦ ?_
    rcases ht with ⟨t, ht, rfl⟩
    exact continuous_iff_coinduced_le.2 <|
      (continuous_iff_coinduced_le.1 (RingTopology.coinduced_continuous (c.ι.app j).hom)).trans
        (ht j)⟩

private def ofCocone {F : J ⥤ TopCommRingCat.{u}}
    (c : Cocone (underlyingDiagram F)) : Cocone F where
  pt := coinduced c
  ι :=
    { app := toCoinduced c
      naturality := by
        intro i j f
        apply Subtype.ext
        simpa using congrArg CommRingCat.Hom.hom (c.ι.naturality f) }

private def inducedRingTopology {F : J ⥤ TopCommRingCat.{u}}
    {c : Cocone (underlyingDiagram F)} {R : TopCommRingCat.{u}} (h : c.pt →+* R) :
    RingTopology c.pt :=
  let t : TopologicalSpace c.pt := TopologicalSpace.induced h inferInstance
  letI : TopologicalSpace c.pt := t
  letI : IsTopologicalSemiring c.pt :=
    { toContinuousAdd := continuousAdd_induced h, toContinuousMul := continuousMul_induced h }
  RingTopology.mk t (IsTopologicalSemiring.toIsTopologicalRing inferInstance)

private theorem inducedRingTopology_mem {F : J ⥤ TopCommRingCat.{u}}
    {c : Cocone (underlyingDiagram F)} {R : TopCommRingCat.{u}} (h : c.pt →+* R)
    (hh : ∀ j, Continuous (fun x : F.obj j ↦ h ((c.ι.app j).hom x))) :
    inducedRingTopology h ∈ admissibleRingTopologies c := by
  intro j
  letI : TopologicalSpace ((underlyingDiagram F).obj j) :=
    TopCommRingCat.forgetToCommRingCatTopologicalSpace (F.obj j)
  change RingTopology.coinduced (c.ι.app j).hom ≤ inducedRingTopology h
  change sInf { t : RingTopology c.pt |
      TopologicalSpace.coinduced (c.ι.app j).hom (F.obj j).isTopologicalSpace ≤
        t.toTopologicalSpace } ≤ inducedRingTopology h
  refine sInf_le ?_
  change TopologicalSpace.coinduced (c.ι.app j).hom (F.obj j).isTopologicalSpace ≤
    TopologicalSpace.induced h inferInstance
  exact continuous_iff_coinduced_le.1 (continuous_induced_rng.2 (hh j))

private def isColimit {F : J ⥤ TopCommRingCat.{u}} {c : Cocone (underlyingDiagram F)}
    (hc : IsColimit c) : IsColimit (ofCocone c) :=
  IsColimit.ofFaithful (forget₂ TopCommRingCat CommRingCat)
    (by
      simpa [ofCocone, toCoinduced, coinduced] using hc)
    (fun s ↦
      let h := hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)
      ⟨h.hom, by
        rw [continuous_iff_le_induced]
        exact sInf_le ⟨inducedRingTopology h.hom, inducedRingTopology_mem h.hom <| by
          intro j
          change Continuous (show F.obj j → s.pt from (c.ι.app j ≫ h).hom)
          rw [hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCocone s) j]
          exact (s.ι.app j).2, rfl⟩⟩)
    fun _ ↦ rfl

private instance hasColimit (F : J ⥤ TopCommRingCat.{u}) : HasColimit F :=
  ⟨⟨ofCocone (colimit.cocone (underlyingDiagram F)), isColimit (colimit.isColimit _)⟩⟩

/-- `TopCommRingCat` has colimits of all small shapes. -/
instance hasColimitsOfShape (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J TopCommRingCat.{u} where
  has_colimit F := by infer_instance

/-- Lemma 5.30.9 (1): the category of topological rings has all colimits. -/
instance hasColimits : HasColimits TopCommRingCat.{u} where
  has_colimits_of_shape K _ := by infer_instance

instance forgetToCommRingCat_preservesColimitsOfShape (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesColimit := fun {F} ↦
    preservesColimit_of_preserves_colimit_cocone
      (isColimit (colimit.isColimit (underlyingDiagram F))) <| by
        simpa [ofCocone, toCoinduced, coinduced] using (colimit.isColimit (underlyingDiagram F))

/-- Lemma 5.30.9 (2): the forgetful functor from topological rings to commutative rings preserves
colimits. -/
instance forgetToCommRingCat_preservesColimits :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesColimitsOfShape {J} := by infer_instance

end

end TopCommRingCat

/-- Summary theorem collecting the colimit existence and preservation instances for
`TopCommRingCat`. -/
theorem topologicalRingCat_has_colimits_and_forget_to_commRing_preserves_colimits :
    HasColimits TopCommRingCat.{u} ∧
      PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) :=
  ⟨inferInstance, inferInstance⟩

/-! ### Definition_5_30_10 (from Chap05) -/
universe u v w

/- Domain-style sampling for topological modules:
- bundled owner abstraction: `TopModuleCat R`
- owner object fields: `IsTopologicalAddGroup`, `ContinuousSMul`
- source-facing constructor data for `TopModuleCat.of`: `ContinuousAdd`, `ContinuousSMul`
- canonical constructor from unbundled data: `TopModuleCat.of`
- canonical morphism owner: `ContinuousLinearMap`, written `M →L[R] N`

Layer triage:
- `source-facing`: the Stacks condition that addition and scalar multiplication are continuous
- `core/canonical`: `TopModuleCat R` and `ContinuousLinearMap`
- `bridge/view`: the theorem below identifying the source-facing additive datum `ContinuousAdd`
  with the additive-group field `IsTopologicalAddGroup` used by the owner

For the source-facing unbundled notion of topological `R`-module, the primitive data is
`ContinuousAdd` together with `ContinuousSMul`. The bundled owner `TopModuleCat R` stores the
additive part as `IsTopologicalAddGroup`; over a ring, continuity of negation is derived from
scalar multiplication by `-1`, so `TopModuleCat.of` is the canonical bridge from the source-facing
data to the owner.
-/

/- Definition 5.30.10: the canonical bundled category of topological `R`-modules over a
topological ring is `TopModuleCat R`. -/
recall TopModuleCat

/- Source-facing additive constructor datum for topological `R`-modules: continuity of addition. -/
recall ContinuousAdd

/- Scalar-action datum for topological `R`-modules, both in the source-facing formulation and in
the owner `TopModuleCat R`: continuity of scalar multiplication. -/
recall ContinuousSMul

/- The canonical constructor `TopModuleCat.of` packages the source-facing data into the owner
`TopModuleCat R`. -/
recall TopModuleCat.of

/- The canonical morphism owner for topological `R`-modules is `ContinuousLinearMap`. -/
recall ContinuousLinearMap

section

/-- Definition 5.30.10: in an `R`-module with continuous scalar multiplication, the source-facing
continuity-of-addition condition is equivalent to the additive-group field
`IsTopologicalAddGroup M` used by `TopModuleCat.of`. -/
theorem continuousAdd_iff_isTopologicalAddGroup
    (R : Type u) [Ring R] [TopologicalSpace R]
    {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M] :
    ContinuousAdd M ↔ IsTopologicalAddGroup M := by
  constructor
  · intro hAdd
    exact
      { toContinuousAdd := hAdd
        toContinuousNeg := ContinuousNeg.of_continuousConstSMul R M }
  · intro hAddGroup
    exact hAddGroup.toContinuousAdd

end

section

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousSMul R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul R N]

/- Definition 5.30.10: a homomorphism of topological `R`-modules is the canonical bundled type
`M →L[R] N` of continuous linear maps. -/
#check (M →L[R] N)

end

/-! ### Lemma_5_30_11 (from Chap05) -/
universe u

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [Ring R] [TopologicalSpace R]

/- Domain-style sampling for topological modules:
- primary domain: categorical limits in `TopModuleCat R` and preservation by its canonical
  forgetful functors
- sampled mathlib owner declarations:
  `TopModuleCat`,
  the instance `HasLimits (TopModuleCat R)`,
  the instance `PreservesLimits (forget₂ (TopModuleCat R) TopCat)`,
  the instance `(forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint`
- sampled neighboring project declarations:
  `Definition_5_30_10` fixes `TopModuleCat` as the chapter owner for topological modules;
  `Lemma_5_30_8.topologicalRingCat_hasLimits_and_forget_preservesLimits` gives the analogous
  split source-facing declarations for topological rings;
  `Lemma_5_30_12.topModuleCat_hasColimits_and_forgetToModuleCat_preservesColimits` gives the
  analogous source-facing colimit statement.

- best owner abstraction: `TopModuleCat R`, with its object data bundled in the owner and its
  limit and preservation statements supplied by canonical instances and adjunctions

Layer triage:
- `source-facing`: the textbook lemma split into atomic limit and preservation declarations
- `core/canonical`: the owner `TopModuleCat R` and the canonical `HasLimits`/`PreservesLimits`
  instances attached to it
- `bridge/view`: none; this item is already a direct owner-level reuse

Primitive data lives in the owner `TopModuleCat R` itself: the topology, the topological additive
group structure, and scalar continuity on each object. The limit-existence and
forgetful-preservation statements are derived categorical API, so this file should stay a thin
reuse of the canonical instances rather than introduce any parallel local wrapper.

The source phrases the result for a topological ring. The sampled owner-level API, together with
the chapter's own `Definition_5_30_10`, shows that this lemma only uses the ring structure and the
ambient topology on `R`; the stronger `IsTopologicalRing R` hypothesis is therefore redundant here
and is removed from the public statement. The declaration does not generalize below `[Ring R]`
because the canonical owner `TopModuleCat R` in mathlib is itself ring-based.
-/

/-- Lemma 5.30.11 (1): the category `TopModuleCat R` of topological `R`-modules has all small
limits. -/
instance topModuleCat_hasLimits : HasLimits (TopModuleCat R) :=
  inferInstance

/-- Lemma 5.30.11 (2): the forgetful functor from `TopModuleCat R` to `TopCat` preserves all
small limits. -/
instance topModuleCat_forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ (TopModuleCat R) TopCat) :=
  inferInstance

/-- Lemma 5.30.11 (3): the forgetful functor from `TopModuleCat R` to `ModuleCat R` preserves all
small limits. -/
instance topModuleCat_forgetToModuleCat_preservesLimits :
    PreservesLimits (forget₂ (TopModuleCat R) (ModuleCat R)) :=
  inferInstance

/-! ### Lemma_5_30_12 (from Chap05) -/
open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R] [TopologicalSpace R]

/- Domain-style sampling for topological modules:
- primary domain: categorical colimits in `TopModuleCat R` and preservation by its canonical
  forgetful functor to `ModuleCat R`
- sampled mathlib owner declarations:
  `TopModuleCat`,
  the instance `HasColimits (TopModuleCat R)`,
  `TopModuleCat.indiscreteAdj`,
  the instance `(forget₂ (TopModuleCat R) (ModuleCat R)).IsLeftAdjoint`
- sampled neighboring project declarations:
  `Definition_5_30_10` fixes `TopModuleCat` as the chapter owner for topological modules;
  `Lemma_5_30_11.topModuleCat_hasLimits_and_forget_preservesLimits` packages the analogous limit
  consequences directly from canonical instances.

- best owner abstraction: `TopModuleCat R`

Layer triage:
- `source-facing`: this lemma packages the source consequence that `TopModuleCat R` has colimits
  and that the forgetful functor to `ModuleCat R` preserves them
- `core/canonical`: the owner `TopModuleCat R`, its canonical `HasColimits` instance, and the
  left-adjoint structure on `forget₂ (TopModuleCat R) (ModuleCat R)`
- `bridge/view`: none; the item is already a thin consequence of the owner-level API

Primitive data lives in the owner `TopModuleCat R`: topology, additive continuity, and scalar
continuity on each module. Colimit existence and preservation by the forgetful functor are derived
categorical API, so this file should only package the canonical instances rather than duplicate
them behind a local wrapper.

As in the neighboring limit lemma, the stronger `IsTopologicalRing R` hypothesis is redundant for
this statement: the sampled owner-level colimit and adjunction API only requires `[Ring R]` and
`[TopologicalSpace R]`.
-/

/-- Lemma 5.30.12: for a ring `R` with a topology, the category `TopModuleCat R` of topological
modules over `R` has arbitrary colimits, and the forgetful functor to `ModuleCat R` preserves
these colimits. -/
theorem topModuleCat_hasColimits_and_forgetToModuleCat_preservesColimits :
    HasColimits (TopModuleCat R) ∧
      PreservesColimits (forget₂ (TopModuleCat R) (ModuleCat R)) :=
  ⟨inferInstance, inferInstance⟩
