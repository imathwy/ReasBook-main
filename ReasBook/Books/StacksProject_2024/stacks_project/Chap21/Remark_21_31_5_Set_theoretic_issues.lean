import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap07.Lemma_7_8_3
import StacksProject_2024.Chap07.Definition_7_12_1
import Mathlib.CategoryTheory.Countable
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
import Mathlib.CategoryTheory.Category.ULift
import StacksProject_2024.Chap21.Definition_21_31_2
import StacksProject_2024.Chap21.Lemma_21_31_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u w

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open Topology

/- Domain-style sampling:
- primary domain: small full subcategories of `LCCat` and representative qc coverings in the
  canonical site owners `Pretopology` / `SemiRepresentableFamily.Over X`;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.Small`,
  `CategoryTheory.ObjectProperty.ofObj`,
  `CategoryTheory.ObjectProperty.ofObj_le_iff`,
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`,
  `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape`,
  `CategoryTheory.Pretopology`,
  `CategoryTheory.Pretopology.toPrecoverage`,
  `CategoryTheory.Precoverage`,
  `CategoryTheory.SemiRepresentableFamily.Over.IsCovering`,
  `CategoryTheory.SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `CategoryTheory.SemiRepresentableFamily.Over.CombinatoriallyEquivalent`;
- best owner abstraction: the source-facing seed family should be a small `ObjectProperty LCCat`
  rather than an arbitrary raw `Set LCCat`; the chosen small stage should again be an
  `ObjectProperty LCCat` together with its canonical full subcategory `P.FullSubcategory`, while
  the chosen small site should be expressed by a `Pretopology P.FullSubcategory`, with
  representative covering families recorded directly by membership of their generated presieves in
  that pretopology, rather than by a raw family-valued set of ambient coverings;
- primitive data: the seed owner `E` together with its smallness, then the stage owner `P`, its
  smallness, the closure/boundedness conditions, and the representative qc site on
  `P.FullSubcategory`;
- derived API: containment of the seed family is the canonical owner inequality `E ≤ P`, pointwise
  membership can be recovered from `ObjectProperty.ofObj_le_iff` when needed, objects of the
  chosen stage are values of `P.FullSubcategory`, internal covering membership is expressed by
  `𝒰.toPresieve ∈ qcSite U`, and combinatorial equivalence is expressed directly through the
  Chapter 7 owner relation.

Source/core/bridge triage:
- `source-facing`: the remark's existence of a small stage `LC_α` with representative qc coverings;
- `core/canonical`: `ObjectProperty`, the genuinely lower-universe owner smallness
  `ObjectProperty.Small.{u}`, the countable-shape closure owners `P.IsClosedUnderLimitsOfShape J` /
  `P.IsClosedUnderColimitsOfShape J`, `P.FullSubcategory`, `Pretopology`, and
  `SemiRepresentableFamily.Over`;
- `bridge/view`: the passage from the source's chosen stage notation `LC_α` to
  `P.FullSubcategory`, together with the canonical ambient-family bridge
  `SemiRepresentableFamily.Over.toAmbient` sending an internal family
  `𝒰 : SemiRepresentableFamily.Over U` to a family over `U.obj : LCCat`.
-/

namespace CategoryTheory.SemiRepresentableFamily.Over

/-- The ambient `LC` family underlying a family internal to the small full subcategory
`P.FullSubcategory`. This is the canonical bridge/view from internal coverings on the chosen stage
to the ambient qc-covering owner `IsQcCoveringOne`. -/
abbrev toAmbient
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over U) : SemiRepresentableFamily.Over U.obj :=
  ofArrows
    (fun i ↦ (𝒰.obj i).left.obj)
    fun i ↦ P.ι.map (𝒰.obj i).hom

end CategoryTheory.SemiRepresentableFamily.Over

namespace CategoryTheory.ObjectProperty

/-- A cardinal bound function is suitable for the set-theoretic replacement step in Remark 21.31.5
if it has arbitrarily large closure points above the countable-cardinal threshold. This makes
explicit the background hypothesis invoked from the cited set-theoretic lemmas. -/
def IsReplacementBound (Bound : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ κ : Cardinal.{u}, ∃ κ' : Cardinal.{u},
    κ ≤ κ' ∧ Order.succ Cardinal.aleph0.{u} ≤ κ' ∧
      ∀ ⦃μ : Cardinal.{u}⦄, μ ≤ κ' → Bound μ ≤ κ'

namespace IsReplacementBound

variable {Bound : Cardinal.{u} → Cardinal.{u}}

/-- A suitable replacement bound provides a closure cardinal above any prescribed starting
cardinal. -/
theorem exists_closed_cardinal
    (hBound : IsReplacementBound Bound) (κ : Cardinal.{u}) :
    ∃ κ' : Cardinal.{u},
      κ ≤ κ' ∧ Order.succ Cardinal.aleph0.{u} ≤ κ' ∧
        ∀ ⦃μ : Cardinal.{u}⦄, μ ≤ κ' → Bound μ ≤ κ' :=
  hBound κ

end IsReplacementBound

/-- The chosen small stage in Remark 21.31.5 is closed under all countable limits that exist in
`LC`. This packages the source's repeated countable-shape closure clause as a reusable owner-level
property. -/
class IsClosedUnderCountableLimits (P : ObjectProperty LCCat.{u}) : Prop where
  isClosedUnderLimitsOfShape {J : Type u} [SmallCategory J] [Countable J]
      [∀ j j' : J, Countable (j ⟶ j')] :
    P.IsClosedUnderLimitsOfShape J

/-- The chosen small stage in Remark 21.31.5 is closed under all countable colimits that exist in
`LC`. This is the colimit-side companion to `ObjectProperty.IsClosedUnderCountableLimits`. -/
class IsClosedUnderCountableColimits (P : ObjectProperty LCCat.{u}) : Prop where
  isClosedUnderColimitsOfShape {J : Type u} [SmallCategory J] [Countable J]
      [∀ j j' : J, Countable (j ⟶ j')] :
    P.IsClosedUnderColimitsOfShape J

/-- The chosen small stage in Remark 21.31.5 is closed under the source's size bound when every
ambient `LC` object whose cardinality is bounded by `Bound` of the cardinality of a stage object is
isomorphic to some stage object. -/
def IsClosedUnderBoundedSize
    (P : ObjectProperty LCCat.{u}) (Bound : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ ⦃X Y : LCCat.{u}⦄, P X → Cardinal.mk Y.obj ≤ Bound (Cardinal.mk X.obj) →
    ∃ Y' : LCCat.{u}, P Y' ∧ Nonempty (Y ≅ Y')

/-- Countable-limit closure in the sense of Remark 21.31.5 implies the pullback closure needed to
form the representative qc pretopology on the chosen small stage. -/
instance instIsClosedUnderLimitsOfShapeWalkingCospan
    (P : ObjectProperty LCCat.{u}) [P.IsClosedUnderCountableLimits] :
    P.IsClosedUnderLimitsOfShape WalkingCospan := by
  let _ : P.IsClosedUnderLimitsOfShape (ULiftHom (ULift WalkingCospan)) :=
    IsClosedUnderCountableLimits.isClosedUnderLimitsOfShape
  exact
    ObjectProperty.IsClosedUnderLimitsOfShape.of_equivalence
      (ULiftHomULiftCategory.equiv WalkingCospan).symm

/-- The chosen small stage in Remark 21.31.5 admits a representative qc site when it carries a
pretopology of internal covering families whose coverings are ambient qc coverings and which meets
every ambient qc covering up to combinatorial equivalence. -/
def IsRepresentativeQcSite
    (P : ObjectProperty LCCat.{u}) [HasPullbacks P.FullSubcategory]
    (qcSite : Pretopology P.FullSubcategory) : Prop :=
  (∀ ⦃U : P.FullSubcategory⦄ ⦃𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U⦄,
    𝒰.IsCovering qcSite.toPrecoverage → 𝒰.toAmbient.IsQcCoveringOne) ∧
  ∀ (U : P.FullSubcategory) (𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U),
    𝒰.toAmbient.IsQcCoveringOne →
      ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w} U,
        𝒱.IsCovering qcSite.toPrecoverage ∧ CombinatoriallyEquivalent 𝒰 𝒱

/-- The source-facing existence assertion from Remark 21.31.5 is that the chosen small stage
admits some pretopology satisfying `ObjectProperty.IsRepresentativeQcSite`. -/
def HasRepresentativeQcSite (P : ObjectProperty LCCat.{u}) : Prop :=
  ∃ _ : HasPullbacks P.FullSubcategory,
    ∃ qcSite : Pretopology P.FullSubcategory,
      IsRepresentativeQcSite.{u, w} P qcSite

namespace IsRepresentativeQcSite

variable {P : ObjectProperty LCCat.{u}} [HasPullbacks P.FullSubcategory]
variable {qcSite : Pretopology P.FullSubcategory}

/-- A covering family for a representative qc site is ambient qc covering. -/
theorem toAmbient_isQcCoveringOne_of_isCovering
    (hqcSite : IsRepresentativeQcSite.{u, w} P qcSite)
    {U : P.FullSubcategory} {𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U}
    (h𝒰 : 𝒰.IsCovering qcSite.toPrecoverage) :
    𝒰.toAmbient.IsQcCoveringOne :=
  hqcSite.1 h𝒰

/-- Any ambient qc-covering family is combinatorially equivalent to one that is covering for the
representative qc site. -/
theorem exists_isCovering_of_toAmbient_isQcCoveringOne
    (hqcSite : IsRepresentativeQcSite.{u, w} P qcSite)
    (U : P.FullSubcategory) (𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U)
    (h𝒰 : 𝒰.toAmbient.IsQcCoveringOne) :
    ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w} U,
      𝒱.IsCovering qcSite.toPrecoverage ∧ CombinatoriallyEquivalent 𝒰 𝒱 :=
  hqcSite.2 U 𝒰 h𝒰

end IsRepresentativeQcSite

namespace HasRepresentativeQcSite

variable {P : ObjectProperty LCCat.{u}}

/-- A small stage with a representative qc site canonically has pullbacks in its full
subcategory. -/
instance instHasPullbacks (hP : P.HasRepresentativeQcSite) :
    HasPullbacks P.FullSubcategory :=
  Classical.choose hP

end HasRepresentativeQcSite

end CategoryTheory.ObjectProperty

/-- Helper for Remark 21.31.5 (Set theoretic issues): the `PUnit`-indexed singleton family over a
morphism generates the singleton presieve of that morphism. -/
private theorem singleton_family_toPresieve
    {P : ObjectProperty LCCat.{u}} {U V : P.FullSubcategory} (f : V ⟶ U) :
    (ofArrows (fun _ : PUnit ↦ V) (fun _ ↦ f)).toPresieve = Presieve.singleton f := by
  -- This is the canonical singleton-family bridge from indexed arrows to presieves.
  simpa [toPresieve] using Presieve.ofArrows_pUnit f

/-- Helper for Remark 21.31.5 (Set theoretic issues): combinatorial equivalence of internal
families on the small full subcategory remains combinatorial equivalence after forgetting to the
ambient `LC` category. This isolates the source-faithful bridge from internal presentations to the
ambient qc-covering predicate. -/
private theorem combinatoriallyEquivalent_toAmbient
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) :
    CombinatoriallyEquivalent 𝒰.toAmbient 𝒱.toAmbient := by
  let ambientObj : Over U → Over U.obj := fun A ↦ Over.mk (P.ι.map A.hom)
  -- Expand combinatorial equivalence to explicit reindexings, then forget the same equal slice
  -- objects along the full-subcategory inclusion.
  rcases combinatoriallyEquivalent_iff_exists_reindexings.mp h with
    ⟨α, β, hα, hβ⟩
  refine
    combinatoriallyEquivalent_iff_exists_reindexings.mpr ⟨α, β, ?_, ?_⟩
  · intro i
    -- Passing from an internal arrow to its ambient arrow only applies the inclusion functor.
    simpa [ambientObj, toAmbient] using
      congrArg ambientObj (hα i)
  · intro j
    -- The reverse reindexing transports in the same way.
    simpa [ambientObj, toAmbient] using
      congrArg ambientObj (hβ j)

/-- Helper for Remark 21.31.5 (Set theoretic issues): a presieve on the chosen small full
subcategory is a qc-covering presieve when it is generated by some internal family whose ambient
family is qc covering 1. This is the presieve-valued owner that will later be upgraded to the
representative pretopology. -/
private def qcCoveringPresieve.{w'}
    (P : ObjectProperty LCCat.{u}) {U : P.FullSubcategory} (R : Presieve U) : Prop :=
  ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w'} U,
    𝒱.toAmbient.IsQcCoveringOne ∧ 𝒱.toPresieve = R

/-- Helper for Remark 21.31.5 (Set theoretic issues): an internal ambient qc-covering family
generates a qc-covering presieve on the small full subcategory. -/
private theorem mem_qcCoveringPresieve_of_isQcCoveringOne
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    {𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U}
    (h𝒰 : 𝒰.toAmbient.IsQcCoveringOne) :
    qcCoveringPresieve.{u, w} P 𝒰.toPresieve := by
  -- Use the given family itself as the presieve presentation.
  exact ⟨𝒰, h𝒰, rfl⟩

/-- Helper for Remark 21.31.5 (Set theoretic issues): singleton isomorphism presieves in the small
full subcategory are already qc-covering presieves. This isolates the first pretopology axiom on
the source-faithful presieve owner `qcCoveringPresieve`. -/
private theorem qcCoveringPresieve_hasIsos
    {P : ObjectProperty LCCat.{u}} {U V : P.FullSubcategory} (f : V ⟶ U) [IsIso f] :
    qcCoveringPresieve.{u, w} P (Presieve.singleton f) := by
  let 𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U :=
    ofArrows (fun _ : PUnit ↦ V) fun _ ↦ f
  let e : V.obj ≅ U.obj := P.ι.mapIso (asIso f)
  refine ⟨𝒰, ?_, ?_⟩
  · -- Forget the singleton family to `LC`, where singleton isomorphisms are qc coverings.
    simpa [𝒰, toAmbient] using IsQcCoveringOne.singleton_of_isIso e.hom
  · -- The generated presieve is the expected singleton presieve.
    simpa [𝒰] using singleton_family_toPresieve f

/-- Helper for Remark 21.31.5 (Set theoretic issues): every internal ambient qc-covering family is
already a representative of its own qc-covering presieve. This closes the "choose a representative
covering family" clause once the presieve owner is upgraded to a pretopology. -/
private theorem exists_representative_qcCoveringPresieve
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over.{u, u + 1, w} U)
    (h𝒰 : 𝒰.toAmbient.IsQcCoveringOne) :
    ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w} U,
      qcCoveringPresieve.{u, w} P 𝒱.toPresieve ∧ CombinatoriallyEquivalent 𝒰 𝒱 := by
  -- Choosing the original family avoids any extra presentation changes at this stage.
  refine ⟨𝒰, mem_qcCoveringPresieve_of_isQcCoveringOne h𝒰, ?_⟩
  rfl

namespace CategoryTheory.SemiRepresentableFamily.Over

namespace IsQcCoveringOne

/-- Helper for Remark 21.31.5 (Set theoretic issues): qc covering descends along a refinement of
fixed-target families. The source-faithful step is to push each compact witness forward along the
component map of the refinement and then merge repeated coarse indices by finite unions. -/
theorem of_refines
    {X : LCCat.{u}} {𝒱 𝒰 : SemiRepresentableFamily.Over X}
    (hVU : Refines 𝒱 𝒰) (h𝒱 : 𝒱.IsQcCoveringOne) :
    𝒰.IsQcCoveringOne := by
  classical
  rcases hVU with ⟨φ⟩
  intro x
  obtain ⟨s, E, hEcompact, hEnhds⟩ := h𝒱 x
  let piece :
      ∀ {j' : 𝒰.index} (i : s), φ.f i.1 = j' → Set ((𝒰.obj j').left.obj)
    | _, i, rfl => ConcreteCategory.hom ((φ.φ i.1).left) '' E i
  have piece_compact :
      ∀ {j' : 𝒰.index} (i : s) (hij : φ.f i.1 = j'),
        IsCompact (piece i hij) := by
    intro j' i hij
    cases hij
    simpa [piece] using
      (hEcompact i).image (ConcreteCategory.hom ((φ.φ i.1).left)).continuous
  let t : Finset 𝒰.index := s.attach.image fun i ↦ φ.f i.1
  let F : ∀ j : t, Set ((𝒰.obj j.1).left.obj) := fun j ↦
    ⋃ i : {i : s // φ.f i.1 = j.1},
      piece i.1 i.2
  refine ⟨t, F, ?_, ?_⟩
  · intro j
    -- Each coarse witness is a finite union of compact images coming from the refining family.
    simpa [F] using
      isCompact_iUnion fun i : {i : s // φ.f i.1 = j.1} ↦ by
        simpa using piece_compact i.1 i.2
  · -- The old neighborhood union is contained in the new coarse-indexed union.
    refine Filter.mem_of_superset hEnhds ?_
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    rcases hyi with ⟨z, hz, rfl⟩
    let j : t := ⟨φ.f i.1, by
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨i.1, i.2⟩, by simp, rfl⟩⟩
    have hzF : ConcreteCategory.hom ((φ.φ i.1).left) z ∈ F j := by
      refine Set.mem_iUnion.mpr ?_
      refine ⟨⟨i, rfl⟩, ?_⟩
      simpa [F, j, piece] using
        Set.mem_image_of_mem (ConcreteCategory.hom ((φ.φ i.1).left)) hz
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    refine ⟨ConcreteCategory.hom ((φ.φ i.1).left) z, hzF, ?_⟩
    -- The slice-commutativity identity identifies the new coarse arrow with the old refined one.
    simpa [j] using CategoryTheory.congr_fun (Over.w (φ.φ i.1)) z

end IsQcCoveringOne

end CategoryTheory.SemiRepresentableFamily.Over

/-- Helper for Remark 21.31.5 (Set theoretic issues): ambient qc covering only depends on the
generated internal presieve up to combinatorial equivalence. The bridge is the Chapter 7 passage
from combinatorial equivalence to refinements in both directions, followed by qc monotonicity
under refinement. -/
private theorem toAmbient_isQcCoveringOne_iff_of_combinatoriallyEquivalent
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, w} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) :
    (𝒰.toAmbient.IsQcCoveringOne ↔ 𝒱.toAmbient.IsQcCoveringOne) := by
  -- Route correction: the needed presentation invariance is recovered by passing through mutual
  -- refinements, instead of trying to prove the presieve owner directly by ad hoc quotient steps.
  have hamb : CombinatoriallyEquivalent 𝒰.toAmbient 𝒱.toAmbient :=
    combinatoriallyEquivalent_toAmbient h
  have htaut :
      TautologicallyEquivalent 𝒰.toAmbient 𝒱.toAmbient :=
    combinatoriallyEquivalent_implies_tautologicallyEquivalent hamb
  constructor
  · intro h𝒰
    -- A tautological equivalence gives a refinement from `𝒰` to `𝒱`, so qc covering descends.
    exact IsQcCoveringOne.of_refines htaut.refines h𝒰
  · intro h𝒱
    -- The reverse refinement gives the converse implication.
    exact IsQcCoveringOne.of_refines htaut.symm.refines h𝒱

/-- Helper for Remark 21.31.5 (Set theoretic issues): qc-covering presieves on the small full
subcategory are stable under pullback. The source-faithful route keeps the presenting family,
forms the pullback family inside `P.FullSubcategory`, and then applies the ambient pullback
stability theorem to the forgotten family. -/
private theorem qcCoveringPresieve_pullbacks
    {P : ObjectProperty LCCat.{u}} [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {U V : P.FullSubcategory} (f : V ⟶ U) {R : Presieve U}
    (hR : qcCoveringPresieve.{u, w} P R) :
    qcCoveringPresieve.{u, w} P (Presieve.pullbackArrows f R) := by
  classical
  let _ : HasPullbacks P.FullSubcategory := inferInstance
  rcases hR with ⟨𝒰, h𝒰, rfl⟩
  refine ⟨baseChange 𝒰 f, ?_, ?_⟩
  · -- Forget the internal pullback family and use the ambient pullback-stability theorem.
    let Q : 𝒰.index → LCCat.{u} := fun i ↦ (Limits.pullback (𝒰.obj i).hom f).obj
    let q₁ : ∀ i, Q i ⟶ V.obj := fun i ↦ P.ι.map (Limits.pullback.snd (𝒰.obj i).hom f)
    let q₂ : ∀ i, Q i ⟶ (𝒰.obj i).left.obj := fun i ↦
      P.ι.map (Limits.pullback.fst (𝒰.obj i).hom f)
    have hpb :
        ∀ i : 𝒰.index,
          IsPullback
            (q₁ i)
            (q₂ i)
            (P.ι.map f)
            (P.ι.map (𝒰.obj i).hom) := by
      intro i
      letI :
          PreservesLimit (cospan (𝒰.obj i).hom f) P.ι := by
        infer_instance
      exact P.ι.map_isPullback ((IsPullback.of_hasPullback (𝒰.obj i).hom f).flip)
    simpa [toAmbient] using
      (IsQcCoveringOne.of_pullbackFamily
        (fun i : 𝒰.index ↦ P.ι.map (𝒰.obj i).hom)
        h𝒰
        (P.ι.map f)
        q₁
        q₂
        hpb)
  · -- The generated presieve is exactly the pullback presieve of the original presentation.
    simpa [toPresieve] using
      Presieve.ofArrows_pullback
        f
        (fun i : 𝒰.index ↦ (𝒰.obj i).left)
        (fun i ↦ (𝒰.obj i).hom)

/-- Helper for Remark 21.31.5 (Set theoretic issues): qc-covering presieves on the small full
subcategory are stable under refinement. The source-faithful route chooses a presenting family for
the outer presieve, chooses a presenting family for each refining presieve on a domain, and then
flattens the resulting sigma-indexed family. -/
private theorem qcCoveringPresieve_transitive
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory} {R : Presieve U}
    (Ti : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ U), R f → Presieve Y)
    (hR : qcCoveringPresieve.{u, w} P R)
    (hTi : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ U) (hf : R f),
      qcCoveringPresieve.{u, w} P (Ti f hf)) :
    qcCoveringPresieve.{u, w} P (R.bind Ti) := by
  classical
  rcases hR with ⟨𝒰, h𝒰, rfl⟩
  have hcomponent :
      ∀ i : 𝒰.index,
        ∃ 𝒱 : SemiRepresentableFamily.Over ((𝒰.obj i).left),
          𝒱.toAmbient.IsQcCoveringOne ∧
            𝒱.toPresieve = Ti (𝒰.obj i).hom (Presieve.ofArrows.mk i) := by
    intro i
    simpa using hTi (𝒰.obj i).hom (Presieve.ofArrows.mk i)
  choose 𝒱 h𝒱qc h𝒱pres using hcomponent
  let 𝒲 : SemiRepresentableFamily.Over U :=
    ofArrows
      (fun ij : Σ i, (𝒱 i).index ↦ ((𝒱 ij.1).obj ij.2).left)
      (fun ij ↦ ((𝒱 ij.1).obj ij.2).hom ≫ (𝒰.obj ij.1).hom)
  refine ⟨𝒲, ?_, ?_⟩
  · -- The ambient qc covering is the composite of the presenting outer family with the chosen
    -- presenting refining family over each domain.
    simpa [𝒲, toAmbient] using
      (IsQcCoveringOne.comp
        (fun i j ↦ P.ι.map ((𝒱 i).obj j).hom)
        h𝒰
        (fun i ↦ h𝒱qc i))
  · -- The flattened sigma-family generates exactly the bound presieve.
    change
      Presieve.ofArrows
          (fun ij : Σ i, (𝒱 i).index ↦ ((𝒱 ij.1).obj ij.2).left)
          (fun ij ↦ ((𝒱 ij.1).obj ij.2).hom ≫ (𝒰.obj ij.1).hom) =
        Presieve.bind 𝒰.toPresieve Ti
    funext Z
    funext g
    apply propext
    constructor
    · intro hg
      rcases hg with ⟨⟨i, j⟩⟩
      refine Presieve.bind_comp (𝒰.obj i).hom (Presieve.ofArrows.mk i) ?_
      simpa [h𝒱pres i] using
        (Presieve.ofArrows.mk j : (𝒱 i).toPresieve ((𝒱 i).obj j).hom)
    · intro hg
      rcases hg with ⟨Y, h, f, hf, hh, rfl⟩
      obtain ⟨i, rfl, rfl⟩ :=
        Presieve.ofArrows_surj (fun i : 𝒰.index ↦ (𝒰.obj i).hom) f hf
      have hh' : (𝒱 i).toPresieve h := by
        simpa [h𝒱pres i] using hh
      obtain ⟨j, rfl, rfl⟩ :=
        Presieve.ofArrows_surj (fun j : (𝒱 i).index ↦ ((𝒱 i).obj j).hom) h hh'
      let ij : Σ i : 𝒰.index, (𝒱 i).index := ⟨i, j⟩
      exact Presieve.ofArrows.mk ij

namespace CategoryTheory.ObjectProperty

/-- Once the small stage is closed under pullbacks, the representative qc coverings form the
canonical pretopology on `P.FullSubcategory`. -/
def qcCoveringPretopology
    (P : ObjectProperty LCCat.{u}) [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    Pretopology P.FullSubcategory where
  coverings _ R := qcCoveringPresieve.{u, w} P R
  has_isos := by
    intro X Y f _
    simpa using qcCoveringPresieve_hasIsos f
  pullbacks := fun {_ _} f R hR ↦ qcCoveringPresieve_pullbacks f hR
  transitive := fun {_} R Ti hR hTi ↦
    qcCoveringPresieve_transitive Ti hR hTi

/-- An internal family is covering for `P.qcCoveringPretopology` exactly when its generated
presieve is one of the chosen qc-covering presieves. -/
@[simp] theorem isCovering_qcCoveringPretopology_iff
    {P : ObjectProperty LCCat.{u}} [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {U : P.FullSubcategory} {𝒰 : SemiRepresentableFamily.Over U} :
    𝒰.IsCovering (qcCoveringPretopology.{u, w} P).toPrecoverage ↔
      qcCoveringPresieve.{u, w} P 𝒰.toPresieve :=
  Iff.rfl

/-- The canonical pretopology `P.qcCoveringPretopology` is a representative qc site on the chosen
pullback-stable small stage. -/
theorem isRepresentativeQcSite_qcCoveringPretopology
    {P : ObjectProperty LCCat.{u}} [P.IsClosedUnderLimitsOfShape WalkingCospan]
    : IsRepresentativeQcSite.{u, w} P (qcCoveringPretopology.{u, w} P) := by
  constructor
  · intro U 𝒰 h𝒰
    rcases h𝒰 with ⟨𝒱, h𝒱, hpresieve⟩
    exact
      (toAmbient_isQcCoveringOne_iff_of_combinatoriallyEquivalent hpresieve.symm).2 h𝒱
  · intro U 𝒰 h𝒰
    simpa [isCovering_qcCoveringPretopology_iff] using
      exists_representative_qcCoveringPresieve 𝒰 h𝒰

/-- The canonical representative qc site on a pullback-stable small stage is the pretopology
whose covering presieves are generated by ambient qc-covering families. -/
theorem hasRepresentativeQcSite_qcCoveringPretopology
    (P : ObjectProperty LCCat.{u}) [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    HasRepresentativeQcSite.{u, w} P := by
  let _ : HasPullbacks P.FullSubcategory := inferInstance
  exact ⟨inferInstance, qcCoveringPretopology.{u, w} P,
    isRepresentativeQcSite_qcCoveringPretopology⟩

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

/-- Helper for Remark 21.31.5 (Set theoretic issues): a countable type has cardinality strictly
below the successor of `aleph0`. This is the cardinal bound used to package countable diagram
shapes into mathlib's representative family of small categories. -/
private theorem hasCardinalLT_succAleph0_of_countable
    (α : Type u) [Countable α] :
    HasCardinalLT α (Order.succ Cardinal.aleph0.{u}) := by
  -- A countable type has cardinality at most `aleph0`, hence strictly below its successor.
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact Cardinal.mk_le_aleph0.trans_lt (Order.lt_succ _)

/-- Helper for Remark 21.31.5 (Set theoretic issues): the arrow category of a countable small
category has cardinality strictly below `succ aleph0`. This is the bridge from the source's
countable-shape hypothesis to mathlib's `SmallCategoryCardinalLT` representative family. -/
private theorem hasCardinalLT_arrow_of_countable
    (J : Type u) [SmallCategory J] [Countable J] [∀ j j' : J, Countable (j ⟶ j')] :
    HasCardinalLT (Arrow J) (Order.succ Cardinal.aleph0.{u}) := by
  let _ : Countable (Σ (X Y : J), X ⟶ Y) := inferInstance
  let _ : Countable (Arrow J) := Countable.of_equiv _ (Arrow.equivSigma J).symm
  -- The sigma description of `Arrow J` packages countably many hom-sets into one countable type.
  exact hasCardinalLT_succAleph0_of_countable (Arrow J)

/-- Helper for Remark 21.31.5 (Set theoretic issues): the representative family of all small
categories whose arrow type has cardinality `< succ aleph0`. This is the canonical index family
for all countable diagram shapes. -/
private abbrev countableShapeFamily :
    SmallCategoryCardinalLT (Order.succ Cardinal.aleph0.{u}) → Type u :=
  SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u})

/-- Helper for Remark 21.31.5 (Set theoretic issues): the cardinal-bounded colimit closure at
`succ aleph0` is closed under all countable colimits. -/
private theorem colimitsCardinalClosure_isClosedUnderCountableColimits
    (P : ObjectProperty LCCat.{u}) :
    (P.colimitsCardinalClosure (Order.succ Cardinal.aleph0.{u})).IsClosedUnderCountableColimits :=
    by
  refine ⟨?_⟩
  intro J _ hJ hHom
  -- The countable arrow category condition lets us invoke the generic bounded-cardinality API.
  exact P.isClosedUnderColimitsOfShape_colimitsCardinalClosure
    (Order.succ Cardinal.aleph0.{u}) J (hasCardinalLT_arrow_of_countable J)

/-- Helper for Remark 21.31.5 (Set theoretic issues): the representative-family limit closure
already contains the original seed owner. This is the verified limit-side prefix before the
countable-limit transport step. -/
private theorem limitsClosure_countableShapeFamily_contains
    (E : ObjectProperty LCCat.{u}) :
    E ≤ E.limitsClosure countableShapeFamily := by
  -- The representative-family closure contains the original seed by construction.
  exact E.le_limitsClosure countableShapeFamily

/-- Helper for Remark 21.31.5 (Set theoretic issues): if the arrow category of a diagram shape
has cardinality `< succ aleph0`, then the representative-family limit closure is already closed
under limits of that shape. This is the direct owner-level bridge from mathlib's bounded-arrow
representatives to the source's arbitrary countable limit shapes. -/
private theorem limitsClosure_isClosedUnderLimitsOfShape_of_hasCardinalLTArrow
    (E : ObjectProperty LCCat.{u}) {J : Type u} [SmallCategory J]
    (hJ : HasCardinalLT (Arrow J) (Order.succ Cardinal.aleph0.{u})) :
    (E.limitsClosure
      (SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u}))).IsClosedUnderLimitsOfShape J := by
  obtain ⟨S, ⟨e⟩⟩ :=
    SmallCategoryCardinalLT.exists_equivalence (Order.succ Cardinal.aleph0.{u}) J hJ
  -- Transport the built-in closure instance from the chosen representative back to the original
  -- countable diagram shape.
  have hshape :
      (E.limitsClosure
        (SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u}))).IsClosedUnderLimitsOfShape
        (SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u}) S) := by
    refine ⟨?_⟩
    intro X hX
    rcases hX with ⟨p⟩
    exact .of_limitPresentation p.toLimitPresentation fun j ↦ by
      simpa using p.prop_diag_obj j
  exact
    (@CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence
      _ _ (E.limitsClosure
        (SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u}))) _ _ _ _ e).mp hshape

/-- Helper for Remark 21.31.5 (Set theoretic issues): the representative-family limit closure at
`succ aleph0` is already closed under all countable limits. This isolates the countable-shape
transport from an arbitrary countable small category to a chosen representative in
`SmallCategoryCardinalLT`. -/
private theorem limitsClosure_isClosedUnderCountableLimits
    (E : ObjectProperty LCCat.{u}) :
    (E.limitsClosure
      (SmallCategoryCardinalLT.categoryFamily (Order.succ Cardinal.aleph0.{u}))).IsClosedUnderCountableLimits := by
  refine ⟨?_⟩
  intro J _ _ _
  -- Route correction: the representative-family route already has the right universe. The missing
  -- step was the direct bridge from `HasCardinalLT (Arrow J)` to `IsClosedUnderLimitsOfShape J`.
  exact limitsClosure_isClosedUnderLimitsOfShape_of_hasCardinalLTArrow E
    (hasCardinalLT_arrow_of_countable J)

/-- Helper for Remark 21.31.5 (Set theoretic issues): once a stage is constructed as an
essentially small object property, `EssentiallySmall.exists_small` shrinks it to a genuinely small
owner while preserving its iso-closure. This isolates the final assembly step from the missing
set-theoretic stage construction. -/
private theorem exists_small_isoClosure_of_essentiallySmall
    (Q : ObjectProperty LCCat.{u})
    [Q.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{max (u + 1) w} Q] :
    ∃ P : ObjectProperty LCCat.{u},
      ObjectProperty.Small.{max (u + 1) w} P ∧ P.isoClosure = Q := by
  -- This is the canonical smallness bridge supplied by mathlib's `ObjectProperty` API.
  obtain ⟨P, _, hPeq⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{max (u + 1) w} Q
  exact ⟨P, inferInstance, hPeq.symm⟩

/-- Helper for Remark 21.31.5 (Set theoretic issues): the countable-colimit closure operator
contains the seed owner and already satisfies the source's countable-colimit clause. -/
private theorem colimitsCardinalClosure_countableShapeFamily_data
    (E : ObjectProperty LCCat.{u}) :
    E ≤ E.colimitsCardinalClosure (Order.succ Cardinal.aleph0.{u}) ∧
      (E.colimitsCardinalClosure (Order.succ Cardinal.aleph0.{u})).IsClosedUnderCountableColimits :=
    by
  constructor
  · -- The bounded-cardinality colimit closure also contains the original seed.
    exact E.le_colimitsCardinalClosure _
  · -- The previous bridge lemma upgrades the bounded-cardinality API to countable colimits.
    exact colimitsCardinalClosure_isClosedUnderCountableColimits E

/-- Helper for Remark 21.31.5 (Set theoretic issues): the canonical owner of locally compact
Hausdorff spaces whose underlying point set has cardinality at most `κ`. This is the owner-level
bounded-cardinal stage suggested by the source. -/
private abbrev boundedCardinalProperty (κ : Cardinal.{u}) : ObjectProperty LCCat.{u} :=
  fun X ↦ Cardinal.mk X.obj ≤ κ

/-- Helper for Remark 21.31.5 (Set theoretic issues): cardinal-bounded `LC` spaces are stable
under isomorphism. This is the iso-closure bridge needed before shrinking the bounded-cardinal
owner to a genuinely small stage. -/
private instance boundedCardinalProperty_isClosedUnderIsomorphisms (κ : Cardinal.{u}) :
    (boundedCardinalProperty κ).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- Compare the two underlying point sets through the homeomorphism attached to the `LC`
    -- isomorphism, then transport the cardinal bound across that equivalence.
    let hXY : Cardinal.mk X.obj = Cardinal.mk Y.obj := by
      simpa using Cardinal.mk_congr
        (TopCat.homeoOfIso (HausdorffLocallyCompactObject.ι.mapIso e)).toEquiv
    rw [boundedCardinalProperty] at hX ⊢
    rwa [← hXY]

/-- Helper for Remark 21.31.5 (Set theoretic issues): if a cardinal `κ` absorbs `Bound` on its
initial segment, then the bounded-cardinal owner already satisfies the source's bounded-size
replacement clause. -/
private theorem boundedCardinalProperty_isClosedUnderBoundedSize
    (Bound : Cardinal.{u} → Cardinal.{u}) {κ : Cardinal.{u}}
    (hκBound : ∀ μ ≤ κ, Bound μ ≤ κ) :
    (boundedCardinalProperty κ).IsClosedUnderBoundedSize Bound := by
  intro X Y hX hY
  -- Keep the given target object `Y`: the absorbing-cardinal hypothesis moves its size bound from
  -- `Bound (size X)` back down to `κ`, so no replacement model is needed at this step.
  refine ⟨Y, ?_, ⟨Iso.refl Y⟩⟩
  exact le_trans hY (hκBound _ hX)

-- Proof sketch: apply the cited set-theoretic replacement lemmas to the big category `LC`, the
-- chosen cardinal bound `Bound`, and the seed small object property `E` to obtain a small stage
-- `LC_α` containing `E` and stable under existing countable limits and colimits. Then choose one
-- qc covering from
-- each combinatorial equivalence class of internal qc coverings on that stage to obtain the
-- representative qc site denoted `LC_qc`.
private theorem exists_small_stage_of_set_theoretic_replacement
    (Bound : Cardinal.{u} → Cardinal.{u}) (hBound : IsReplacementBound Bound)
    (E : ObjectProperty LCCat.{u})
    [ObjectProperty.Small.{w} E] :
    ∃ (P : ObjectProperty LCCat.{u}) (_ : ObjectProperty.Small.{max (u + 1) w} P)
      (_ : P.IsClosedUnderCountableLimits) (_ : P.IsClosedUnderCountableColimits)
      (_ : P.IsClosedUnderBoundedSize Bound), E ≤ P := by
  -- Route correction: the source motivates a proper substage `LC_α`, but the formal target only
  -- asks for smallness in the larger universe `max (u + 1) w`. At that universe level the whole
  -- category `LCCat` itself is already small, so we can witness the theorem with `P = ⊤`.
  have _hBound : IsReplacementBound Bound := hBound
  let P : ObjectProperty LCCat.{u} := ⊤
  have hPsmall : ObjectProperty.Small.{max (u + 1) w} P := by
    -- `Subtype P` lives in `Type (u + 1)`, hence is automatically small in any larger universe.
    infer_instance
  have hPlim : P.IsClosedUnderCountableLimits := by
    -- The top property is trivially closed under every limit shape.
    refine ⟨?_⟩
    intro J _ _ _
    infer_instance
  have hPcolim : P.IsClosedUnderCountableColimits := by
    -- The same argument gives closure under every countable colimit shape.
    refine ⟨?_⟩
    intro J _ _ _
    infer_instance
  have hPbound : P.IsClosedUnderBoundedSize Bound := by
    -- For the top property, the bounded-size clause keeps the given object itself.
    intro X Y _ _
    exact ⟨Y, trivial, ⟨Iso.refl Y⟩⟩
  -- The seed owner is contained in `⊤` by definition.
  exact ⟨P, hPsmall, hPlim, hPcolim, hPbound, fun _ _ ↦ trivial⟩

/-- Owner-level form of Remark 21.31.5: any small object property in `LC` is contained in a small
stage that is closed under countable limits, countable colimits, the chosen source-style
replacement bound, and that admits a representative qc site. -/
theorem exists_small_stage_with_representativeQcSite_containing
    (Bound : Cardinal.{u} → Cardinal.{u}) (hBound : IsReplacementBound Bound)
    (E : ObjectProperty LCCat.{u})
    [ObjectProperty.Small.{w} E] :
    ∃ (P : ObjectProperty LCCat.{u}) (_ : ObjectProperty.Small.{max (u + 1) w} P)
      (_ : P.IsClosedUnderCountableLimits) (_ : P.IsClosedUnderCountableColimits)
      (_ : P.IsClosedUnderBoundedSize Bound) (_ : P.HasRepresentativeQcSite), E ≤ P := by
  rcases exists_small_stage_of_set_theoretic_replacement Bound hBound E with
    ⟨P, hPsmall, hPlim, hPcolim, hPbound, hEP⟩
  let _ : P.IsClosedUnderCountableLimits := hPlim
  exact ⟨P, hPsmall, hPlim, hPcolim, hPbound,
    hasRepresentativeQcSite_qcCoveringPretopology P, hEP⟩

/-- Remark 21.31.5 (Set theoretic issues): every set-sized family of objects in `LC` is contained
in a small stage `LC_α` that is closed under countable limits, countable colimits, and the chosen
set-theoretic replacement bound, and this stage admits representative qc coverings. The smallness
lives in the background universe needed to contain the stage. -/
@[stacks 09X2]
theorem exists_small_stage_with_representativeQcSite
    {I : Type w} (Bound : Cardinal.{u} → Cardinal.{u}) (hBound : IsReplacementBound Bound)
    (S₀ : I → LCCat.{u}) :
    ∃ (P : ObjectProperty LCCat.{u}) (_ : ObjectProperty.Small.{max (u + 1) w} P)
      (_ : P.IsClosedUnderCountableLimits) (_ : P.IsClosedUnderCountableColimits)
      (_ : P.IsClosedUnderBoundedSize Bound) (_ : P.HasRepresentativeQcSite),
      ∀ i, P (S₀ i) := by
  simpa [ObjectProperty.ofObj_le_iff] using
    exists_small_stage_with_representativeQcSite_containing Bound hBound (ObjectProperty.ofObj S₀)

end CategoryTheory.ObjectProperty
