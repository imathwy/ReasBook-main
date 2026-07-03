import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_31_1 (from Chap21) -/
universe u

open CategoryTheory CategoryTheory.Limits

/-- The category `LC` has a terminal object, corresponding to the one-point space. -/
instance : HasTerminal LCCat.{u} := by
  sorry

/-- The category `LC` has pullbacks. -/
instance : HasPullbacks LCCat.{u} := by
  sorry

/-- The category `LC` has finite limits because it has a terminal object and pullbacks. -/
instance : HasFiniteLimits LCCat.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

-- Proof sketch: use the chosen pullback object in `LC` and view it in `TopCat`. Its underlying
-- space is identified with the closed subspace `{(x, y) | f x = g y}` of `X.obj × Y.obj`, because
-- `Z.obj` is Hausdorff. If `X` and `Y` are quasi-compact, then `X.obj × Y.obj` is quasi-compact by
-- Tychonov, and a closed subspace of a quasi-compact space is quasi-compact.
/-- Lemma 21.31.1: for morphisms `X ⟶ Z` and `Y ⟶ Z` in `LC`, if `X` and `Y` are quasi-compact,
then the fiber product `X ×[Z] Y` is quasi-compact. -/
instance compactSpace_pullback
    {X Y Z : LCCat.{u}} [CompactSpace X.obj] [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    CompactSpace (pullback f g).obj := by
  sorry

/-- Companion formulation of Lemma 21.31.1 as compactness of the universal set. -/
theorem isCompact_univ_pullback_of_compact
    {X Y Z : LCCat.{u}} [CompactSpace X.obj] [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsCompact (Set.univ : Set ((pullback f g).obj)) :=
  isCompact_univ

/-! ### Definition_21_31_2 (from Chap21) -/
universe u v

open CategoryTheory
open Topology
open CategoryTheory.SemiRepresentableFamily.Over

/- Domain-style sampling for Definition 21.31.2:
- primary domain: fixed-target families in the `LC` category and the qc-covering condition they
  satisfy near each point of the target;
- inspected owner declarations:
  `CategoryTheory.SemiRepresentableFamily.Over`,
  `CategoryTheory.SemiRepresentableFamily.Over.ofArrows`,
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`;
- best owner abstraction: the source-facing owner should be a predicate on the canonical fixed-
  target family object `SemiRepresentableFamily.Over X`, not a parallel raw pair of an index type
  and arrow family;
- primitive vs derived:
  primitive data are only the fixed-target family `𝒰 : SemiRepresentableFamily.Over X`;
  the finite compact-image neighborhood condition is the owner predicate itself, while the
  indexed-arrow presentation is only a bridge via `ofArrows`.

Source/core/bridge triage:
- `source-facing`: qc coverings 1 in `LC`;
- `core/canonical`: `SemiRepresentableFamily.Over X`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows`, which recovers the textbook indexed
  family presentation from the owner object.
-/

/-- The object property on `TopCat` selecting Hausdorff weakly locally compact spaces. -/
abbrev HausdorffWeaklyLocallyCompactObject : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ WeaklyLocallyCompactSpace X

/-- The category of Hausdorff weakly locally compact spaces, equivalently Hausdorff locally
quasi-compact spaces, used for the `LC` site. -/
abbrev LCCat : Type (u + 1) :=
  HausdorffWeaklyLocallyCompactObject.FullSubcategory

section

variable {X : LCCat.{u}}

namespace CategoryTheory.SemiRepresentableFamily.Over

/-- Definition 21.31.2: a fixed-target family in `LC` is a qc covering 1 if every point of the
target has a neighborhood contained in a finite union of images of quasi-compact subsets of the
source spaces. -/
def IsQcCoveringOne (𝒰 : Over X) : Prop :=
  ∀ x : X.obj, ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
    (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x

-- Proof sketch: unfold `IsQcCoveringOne` at the point `x` and read off the finite index set, the
-- compact subsets upstairs, and the neighborhood condition for their image union.
/-- A qc covering 1 provides, around each point, finitely many source indices and compact subsets
whose images form a neighborhood of that point. -/
theorem IsQcCoveringOne.exists_finite_compact_image_neighborhood
    {𝒰 : Over X} (h : 𝒰.IsQcCoveringOne) (x : X.obj) :
    ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
      (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x :=
  h x

/-- The owner-level qc-covering predicate on `SemiRepresentableFamily.Over X` recovers the
textbook indexed-arrow formulation via `ofArrows`. -/
theorem ofArrows_isQcCoveringOne_iff {I : Type v} (X_ : I → LCCat.{u}) (f : ∀ i, X_ i ⟶ X) :
    (ofArrows X_ f).IsQcCoveringOne ↔
      ∀ x : X.obj, ∃ s : Finset I, ∃ E : ∀ i : s, Set ((X_ i.1).obj),
        (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, f i.1 '' E i) ∈ 𝓝 x :=
  Iff.rfl

end CategoryTheory.SemiRepresentableFamily.Over

end

/-! ### Lemma_21_31_3 (from Chap21) -/
universe u v w

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

/-
Domain-style sampling for Lemma 21.31.3:
- primary domain: qc-covering families in `LC`, together with their stability under isomorphism,
  refinement, and pullback;
- inspected declarations:
  `SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `SemiRepresentableFamily.Over.IsQcCoveringOne.exists_finite_compact_image_neighborhood`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `compactSpace_pullback`,
  `isCompact_univ_pullback_of_compact`;
- best owner abstraction: the source-facing owner is the predicate
  `SemiRepresentableFamily.Over.IsQcCoveringOne`; the present file should contribute only closure
  lemmas for that owner rather than parallel wrapper APIs;
- primitive vs derived:
  primitive data are only the fixed-target owner object `ofArrows X_ f` together with the finite
  compact-image neighborhood condition from `IsQcCoveringOne`;
  isomorphism, composition, and base change are derived closure properties, not new packaged data.

Source/core/bridge triage:
- `source-facing`: qc coverings in `LC` and their stability properties from the Stacks text;
- `core/canonical`: the owner predicate `SemiRepresentableFamily.Over.IsQcCoveringOne` together
  with the pullback object in `LCCat`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows` for the indexed-arrow presentation, and
  the direct use of the canonical pullback API from `CategoryTheory.Limits`. -/

section

variable {I : Type v} {J : I → Type w}
variable {X X' : LCCat.{u}} {X_ : I → LCCat.{u}}
variable {f : ∀ i, X_ i ⟶ X}

-- Proof sketch: an isomorphism is a homeomorphism on the underlying spaces, so every point of `X`
-- has a neighborhood equal to the image of the singleton finite family indexed by `PUnit`; take the
-- whole source space, which is quasi-compact in a neighborhood of every point because `X'` lies in
-- `LC`.
/-- Lemma 21.31.3 (1): a singleton family consisting of an isomorphism in `LC` is a qc covering. -/
theorem IsQcCoveringOne.singleton_of_isIso (f : X' ⟶ X) [IsIso f] :
    (ofArrows (fun _ : PUnit ↦ X') (fun _ : PUnit ↦ f)).IsQcCoveringOne := sorry

-- Proof sketch: for a point of `X`, start with finitely many compact subsets witnessing that
-- `fᵢ : Xᵢ ⟶ X` is a qc covering near that point. Then refine each compact subset using the qc
-- covering on `Xᵢ`, extract finite subcovers by compactness, and compose the corresponding maps.
/-- Lemma 21.31.3 (2): a family obtained by refining each member of a qc covering by another qc
covering is again a qc covering. -/
theorem IsQcCoveringOne.comp
    {X__ : ∀ i, J i → LCCat.{u}} (g : ∀ i j, X__ i j ⟶ X_ i)
    (hf : (ofArrows X_ f).IsQcCoveringOne)
    (hg : ∀ i, (ofArrows (X__ i) (g i)).IsQcCoveringOne) :
    (ofArrows
      (fun ij : Sigma J ↦ X__ ij.1 ij.2)
      (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1)).IsQcCoveringOne := sorry

-- Proof sketch: let `x' ∈ X'` map to `x ∈ X`. Choose finitely many compact subsets upstairs over
-- `X` witnessing the qc covering near `x`, then intersect them with a compact neighborhood of `x'`
-- after base change. The pullbacks of compact subsets remain compact by Lemma `21.31.1`, and their
-- images cover a neighborhood of `x'`.
/-- Lemma 21.31.3 (3): qc coverings in `LC` are stable under base change. -/
theorem IsQcCoveringOne.baseChange (hf : (ofArrows X_ f).IsQcCoveringOne) (φ : X' ⟶ X) :
    (ofArrows
      (fun i ↦ pullback φ (f i))
      (fun i ↦ pullback.fst φ (f i))).IsQcCoveringOne := sorry

end

/-! ### Lemma_21_31_4 (from Chap21) -/
universe u

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open Set
open Topology

section

variable {X Y : LCCat.{u}}

/- Domain-style sampling for Lemma 21.31.4:
- primary domain: qc-covering families in `LC` and their interaction with proper maps of
  Hausdorff weakly locally compact spaces;
- sampled owner declarations:
  `SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `SemiRepresentableFamily.Over.IsQcCoveringOne.exists_finite_compact_image_neighborhood`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `quasiProper_closed_iff_isProperMap`,
  `IsProperMap`;
- best owner abstraction: `SemiRepresentableFamily.Over.IsQcCoveringOne` is the source-facing
  owner predicate, so this file should contribute an owner-level closure lemma rather than a
  parallel standalone theorem name;
- primitive vs derived:
  primitive data are the singleton owner family `ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)` and
  the hypotheses `IsProperMap f`, `Function.Surjective f`;
  the qc-covering conclusion is derived API for the owner predicate.

Source/core/bridge triage:
- `source-facing`: the singleton qc covering induced by a proper surjective map in `LC`;
- `core/canonical`: the owner predicate `SemiRepresentableFamily.Over.IsQcCoveringOne` and
  mathlib's proper-map owner `IsProperMap`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows` for the singleton indexed family, with
  no further wrapper layer. -/

-- Proof sketch: for each `y : Y`, use surjectivity to view the fiber over `y` inside `X`. Properness
-- makes this fiber compact, so finitely many compact neighborhoods upstairs cover it. Since proper
-- maps are closed, the complement of the union of the corresponding source opens has closed image,
-- and its complement is the desired neighborhood of `y` contained in the image of one compact
-- subset of `X`.
/-- Lemma 21.31.4: if `f : X ⟶ Y` in `LC` is proper and surjective, then the singleton family
`{f : X ⟶ Y}` is a qc covering 1. -/
theorem IsQcCoveringOne.singleton_of_proper_surjective (f : X ⟶ Y)
    (hf : IsProperMap f) (hsurj : Function.Surjective f) :
    (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).IsQcCoveringOne := by
  letI : T2Space X.obj := X.property.1
  letI : WeaklyLocallyCompactSpace X.obj := X.property.2
  intro y
  have hfiberCompact : IsCompact (f ⁻¹' ({y} : Set Y.obj)) :=
    hf.isCompact_preimage isCompact_singleton
  obtain ⟨V, hV_open, hfiber_subset, hV_compact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hfiberCompact
  have himageNhds : f '' closure V ∈ 𝓝 y := by
    have himageClosed : IsClosed (f '' Vᶜ) :=
      hf.isClosedMap _ hV_open.isClosed_compl
    have hy_not_mem : y ∉ f '' Vᶜ := by
      rintro ⟨x, hxV, rfl⟩
      exact hxV <| hfiber_subset <| by simp
    refine Filter.mem_of_superset (himageClosed.isOpen_compl.mem_nhds hy_not_mem) ?_
    intro z hz
    rcases hsurj z with ⟨x, rfl⟩
    have hxV : x ∈ V := by
      by_contra hxV
      have hz' : f x ∉ f '' Vᶜ := by
        simpa using hz
      exact hz' ⟨x, by simpa using hxV, rfl⟩
    exact ⟨x, subset_closure hxV, rfl⟩
  have hsingletonUnion :
      (⋃ i : ({PUnit.unit} : Finset PUnit),
          (ofArrows (fun _ : PUnit ↦ X) (fun _ ↦ f)).obj i.1 |>.hom '' (fun _ ↦ closure V) i) =
        f '' closure V := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion] at hz
      rcases hz with ⟨i, hz⟩
      exact hz
    · intro hz
      simp only [Set.mem_iUnion]
      exact ⟨⟨PUnit.unit, by simp⟩, hz⟩
  refine ⟨({PUnit.unit} : Finset PUnit), fun _ ↦ closure V, ?_⟩
  constructor
  · intro _
    simpa using hV_compact
  · rw [hsingletonUnion]
    exact himageNhds

end

/-! ### Remark_21_31_5_Set_theoretic_issues (from Chap21) -/
universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

/-- A chosen small full subcategory of `LC` together with a set of representative qc coverings on
each of its objects. This packages the set-theoretic small model denoted `LC_qc` in the remark. -/
structure LCQcSmallSite (Bound : Cardinal → Cardinal) (S₀ : Set LCCat.{u}) where
  /-- The chosen full subcategory `LC_α ⊆ LC`. -/
  carrier : Set LCCat.{u}
  /-- The initial set `S₀` is contained in the chosen stage. -/
  seed_subset : S₀ ⊆ carrier
  /-- The chosen stage is closed under countable limits that exist in `LC`. -/
  closed_under_countable_limits :
    ∀ {J : Type u} [SmallCategory J] [Countable J] (F : J ⥤ LCCat.{u}) [HasLimit F],
      (∀ j, F.obj j ∈ carrier) → limit F ∈ carrier
  /-- The chosen stage is closed under countable colimits that exist in `LC`. -/
  closed_under_countable_colimits :
    ∀ {J : Type u} [SmallCategory J] [Countable J] (F : J ⥤ LCCat.{u}) [HasColimit F],
      (∀ j, F.obj j ∈ carrier) → colimit F ∈ carrier
  /-- Any object of `LC` whose size is bounded in terms of an object already in the chosen stage is
  isomorphic to another object of the chosen stage. -/
  bounded_iso :
    ∀ ⦃X : LCCat.{u}⦄, X ∈ carrier →
      ∀ ⦃Y : LCCat.{u}⦄, Cardinal.mk Y.obj ≤ Bound (Cardinal.mk X.obj) →
        ∃ Z : LCCat.{u}, Z ∈ carrier ∧ Nonempty (Y ≅ Z)
  /-- For each object of the chosen stage, a set of representative qc coverings. -/
  representative_coverings :
    ∀ U : { X : LCCat.{u} // X ∈ carrier },
      Set (SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1)
  /-- Every chosen representative family is a qc covering of its target. -/
  representative_coverings_are_qc :
    ∀ ⦃U : { X : LCCat.{u} // X ∈ carrier }⦄
      ⦃𝒰 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1⦄,
      𝒰 ∈ representative_coverings U →
        𝒰.IsQcCoveringOne
  /-- Every qc covering of an object in the chosen stage is combinatorially equivalent to one of
  the chosen representatives. -/
  qc_covering_has_representative :
    ∀ (U : { X : LCCat.{u} // X ∈ carrier })
      (𝒰 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1),
      𝒰.IsQcCoveringOne →
        ∃ 𝒱 : SemiRepresentableFamily.Over.{u, u + 1, u + 1} U.1,
          𝒱 ∈ representative_coverings U ∧
            SemiRepresentableFamily.Over.CombinatoriallyEquivalent 𝒰 𝒱

-- Proof sketch: apply the cited set-theoretic replacement lemmas to the big category `LC`, the
-- chosen cardinal bound `Bound`, and the seed set `S₀` to obtain a small stage `LC_α` containing
-- `S₀` and stable under existing countable limits and colimits. Then choose one qc covering from
-- each combinatorial equivalence class on that stage to obtain the representative covering system
-- denoted `LC_qc`.
/-- Remark 21.31.5 (Set theoretic issues): after choosing a cardinal bound function `Bound` and an
initial set `S₀` of objects of `LC`, one can choose a small stage `LC_α ⊆ LC` containing `S₀`,
stable under all countable limits and colimits that exist in `LC`, such that any object of `LC`
whose underlying set has cardinality at most `Bound (Cardinal.mk X.obj)` for some `X ∈ LC_α` is
isomorphic to an object of `LC_α`; moreover, for each object of `LC_α` one can choose a set of
representative qc coverings, with every qc covering combinatorially equivalent to one of the
chosen representatives. -/
theorem exists_lc_qc_small_site
    (Bound : Cardinal → Cardinal) (S₀ : Set LCCat.{u}) :
    Nonempty (LCQcSmallSite Bound S₀) := sorry

/-! ### Lemma_21_31_6 (from Chap21) -/
/-
Domain-style sampling for inverse-image sheaves on the small, big-Zariski, and qc sites:
- primary domain: inverse-image functors on sheaf topoi and topological pullback sheaves;
- inspected declarations: `piInverseType`, `epsilonInverseType`, `CategoryTheory.Functor.sheafPullback`,
  `CategoryTheory.Functor.sheafPushforwardContinuousId`,
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'`, and `TopCat.Sheaf.pullback`;
- owner abstraction: the chapter owners `piInverseType JZar πFunctor` and
  `epsilonInverseType JZar JQc`, implemented by the canonical `sheafPullback` functors, together
  with the topological owner `TopCat.Sheaf.pullback`;
- primitive data: the small sheaf `ℱ`, an object `Y : Over X`, and the topological pullback sheaf
  `Y.hom.hom ⁻¹ ℱ`;
- derived API: the objectwise section equivalences, with the global-sections type of the
  topological pullback sheaf written directly rather than through a one-off alias.
- source/core/bridge triage: the source-facing content is the objectwise section formula; the core
  owners are the canonical inverse-image functors above; the bridge is the resulting equivalence
  between their values at `Y` and `Γ(Y, Y.hom.hom ⁻¹ ℱ)`.
-/

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

section

variable {X : LCCat.{u}}
variable (JZar JQc : GrothendieckTopology (Over X))
variable (πFunctor : Opens X.obj ⥤ Over X)
variable [Functor.IsContinuous πFunctor (Opens.grothendieckTopology X.obj) JZar]
variable [(πFunctor.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
  JZar).IsRightAdjoint]
variable [Functor.IsContinuous (𝟭 (Over X)) JZar JQc]
variable [((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint]

-- Proof sketch: this is the Zariski part of the lemma. The morphism of sites `π_X` is set up so
-- that evaluating `π_X^{-1}ℱ` on an object `f : Y ⟶ X` identifies with the global sections of the
-- usual topological pullback sheaf `f^{-1}ℱ` on `Y`.
/-- The big-Zariski inverse image is objectwise the rule `Y ↦ Γ(Y, f^{-1}\mathcal F)`. -/
theorem piInverseOnLCZar_hasPullbackSections
    (ℱ : TopCat.Sheaf (Type u) X.obj) (Y : Over X) :
    IsIsomorphic
      (((πFunctor.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) JZar).obj ℱ).obj.obj
        (op Y))
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj ℱ).obj.obj (op ⊤)) := sorry

-- Proof sketch: `ε_X^{-1}` is the inverse-image functor for the topology comparison from qc to
-- Zariski. Applying it to the Zariski inverse image `π_X^{-1}ℱ` preserves the objectwise
-- description by sections of the ordinary pullback sheaf, so the resulting qc sheaf still has
-- value `Γ(Y, f^{-1}ℱ)` on every object `f : Y ⟶ X`.
/-- Lemma 21.31.6: the qc inverse image `ε_X^{-1} π_X^{-1} \mathcal F` on `LC_qc/X` is
objectwise the rule `(f : Y ⟶ X) ↦ Γ(Y, f^{-1}\mathcal F)`. Consequently this rule defines a
sheaf on `LC_qc/X`, and its restriction to `LC_Zar/X` is `π_X^{-1}\mathcal F`. -/
theorem epsilonInversePiInverseOnLCQc_hasPullbackSections
    (ℱ : TopCat.Sheaf (Type u) X.obj) (Y : Over X) :
    IsIsomorphic
      ((((𝟭 (Over X)).sheafPullback (Type u) JZar JQc).obj
          ((πFunctor.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) JZar).obj ℱ)).obj.obj
        (op Y))
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj ℱ).obj.obj (op ⊤)) := sorry

end

/-! ### Lemma_21_31_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {X Y : LCCat.{u}}

/-- Sheaves of types on the small Zariski site of `X`. -/
abbrev SmallTypeSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf (Type u) X.obj

/-- Sheaves of types on the big Zariski site `LC_{Zar}/X`, represented here by a Grothendieck
topology `J` on `Over X`. -/
abbrev LCZarTypeSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  Sheaf J (Type u)

/-- Sheaves of abelian groups on the small Zariski site of `X`. -/
abbrev SmallAbSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj

/-- Sheaves of abelian groups on the big Zariski site `LC_{Zar}/X`, represented here by a
Grothendieck topology `J` on `Over X`. -/
abbrev LCZarAbSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  Sheaf J AddCommGrpCat.{u + 1}

/-- The inverse-image functor `π_X^{-1}` on sheaves of types, induced by the chosen continuous
functor from the small Zariski site of opens of `X` to the big Zariski site `LC_{Zar}/X`. -/
abbrev piInverseType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    SmallTypeSheaf X ⥤ LCZarTypeSheaf J :=
  π.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) J

/-- The direct-image functor `π_{X,*}` on sheaves of types attached to the same morphism of sites.
-/
abbrev piDirectImageType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J] :
    LCZarTypeSheaf J ⥤ SmallTypeSheaf X :=
  π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj) J

/-- The inverse-image functor `π_X^{-1}` on abelian sheaves, induced by the chosen continuous
functor from the small Zariski site of opens of `X` to the big Zariski site `LC_{Zar}/X`. -/
abbrev piInverseAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint] :
    SmallAbSheaf X ⥤ LCZarAbSheaf J :=
  π.sheafPullback AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) J

/-- The direct-image functor `π_{X,*}` on abelian sheaves attached to the same morphism of sites.
-/
abbrev piDirectImageAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J] :
    LCZarAbSheaf J ⥤ SmallAbSheaf X :=
  π.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) J

/-- The degree-`n` cohomology object obtained from a chosen derived global-sections functor. -/
abbrev derivedCohomologyObject
    {C : Type (u + 1)} [Category.{u} C]
    (RGamma : C ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (K : C) (n : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj (RGamma.obj K)

-- Proof sketch: the coverings of `X` in `LC_{Zar}` are the same open coverings used on the small
-- Zariski site, so the inverse-image sheaf `π_X^{-1}\mathcal F` has the same Čech and derived
-- cohomology as `\mathcal F` on `X`.
/-- Lemma 21.31.7 (1): for an abelian sheaf `\mathcal F` on the small Zariski site of `X`, the
cohomology of `π_X^{-1}\mathcal F` on `LC_{Zar}/X` is canonically isomorphic to the ordinary
Zariski cohomology of `\mathcal F` on `X`. -/
theorem lcZar_piInverse_cohomology_isomorphic
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint]
    [HasWeakSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt (LCZarAbSheaf J)]
    (ℱ : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor J n).obj ((piInverseAb J π).obj ℱ))
      ((Sheaf.cohomologyFunctor (Opens.grothendieckTopology X.obj) n).obj ℱ) := sorry

-- Proof sketch: `π_{X,*}` is the direct-image functor of a morphism of topoi, hence it is a
-- right adjoint. Exactness follows from the fact that this morphism identifies the localized big
-- Zariski site with the ordinary small Zariski site of `X`.
/-- Lemma 21.31.7 (2): the direct-image functor `π_{X,*}` from abelian sheaves on `LC_{Zar}/X` to
abelian sheaves on the small Zariski site of `X` is exact. -/
theorem lcZar_piDirectImage_exact
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] :
    exactFunctor (LCZarAbSheaf J) (SmallAbSheaf X) (piDirectImageAb J π) := sorry

-- Proof sketch: the functor `π_X^{-1}` is obtained from a site morphism whose composite with the
-- direct image is the identity on the small Zariski site; the unit of the adjunction therefore
-- identifies each small sheaf with its pull-push image.
/-- Lemma 21.31.7 (3): the adjunction unit
`id ⟶ π_{X,*} \circ π_X^{-1}` is an isomorphism on sheaves of types. -/
theorem lcZar_pi_adjunction_unit_isIso
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint]
    (adjπ : piInverseType J π ⊣ piDirectImageType J π)
    (ℱ : SmallTypeSheaf X) :
    IsIso (adjπ.unit.app ℱ) := sorry

-- Proof sketch: derive the adjunction `π_X^{-1} ⊣ π_{X,*}` on abelian sheaves. Since the
-- underived unit is an isomorphism and `π_{X,*}` is exact, the derived unit
-- `K ⟶ Rπ_{X,*} π_X^{-1} K` is an isomorphism for every derived object.
/-- Lemma 21.31.7 (4): for `K ∈ D(X)`, the canonical map
`K ⟶ Rπ_{X,*} π_X^{-1} K` is an isomorphism. -/
theorem lcZar_pi_derived_unit_isIso
    (DX : Type (u + 1)) [Category.{u} DX]
    (DLCZarX : Type (u + 1)) [Category.{u} DLCZarX]
    (piInverseDerived : DX ⥤ DLCZarX)
    (piDirectImageDerived : DLCZarX ⥤ DX)
    (adjDerived : piInverseDerived ⊣ piDirectImageDerived)
    (K : DX) :
    IsIso (adjDerived.unit.app K) := sorry

-- Proof sketch: the topological pullback on the small Zariski site and the base-change pullback on
-- the big Zariski site are induced by compatible continuous functors, so their associated inverse
-- image functors form a commuting square in the category of topoi.
/-- Lemma 21.31.7 (5): for a morphism `f : X ⟶ Y` in `LC`, the inverse-image functors on the
small and big Zariski sites are canonically isomorphic after composing around the two sides of the
topos square. -/
theorem lcZar_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JX : GrothendieckTopology (Over X))
    (JY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JY).IsRightAdjoint]
    [HasPullbacks LCCat.{u}]
    [(Over.pullback f).IsContinuous JY JX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JY JX).IsRightAdjoint] :
    IsIsomorphic
      ((TopCat.Sheaf.pullback (Type u) f.hom) ⋙ piInverseType JX πX)
      ((piInverseType JY πY) ⋙ ((Over.pullback f).sheafPullback (Type u) JY JX)) := sorry

-- Proof sketch: use the commutative square from part (5) to identify the pullback of
-- `π_Y^{-1}L` to `LC_{Zar}/X` with `π_X^{-1}(f^{-1}L)`. Part (1) then identifies the resulting
-- hypercohomology on `LC_{Zar}/X` with the ordinary hypercohomology of `f^{-1}L` on `X`.
/-- Lemma 21.31.7 (6): for `L ∈ D^+(Y)`, the hypercohomology of `π_Y^{-1}L` over `X` in the big
Zariski site is canonically isomorphic to the hypercohomology of `f^{-1}L` on the small Zariski
site of `X`, formalized here via chosen pullback and derived global-sections functors. -/
theorem lcZar_pullback_hypercohomology_isomorphic
    (DYplus : Type (u + 1)) [Category.{u} DYplus]
    (DXplus : Type (u + 1)) [Category.{u} DXplus]
    (DLCZarYplus : Type (u + 1)) [Category.{u} DLCZarYplus]
    (DLCZarXplus : Type (u + 1)) [Category.{u} DLCZarXplus]
    (piInverseDerivedPlusY : DYplus ⥤ DLCZarYplus)
    (smallPullbackDerivedPlus : DYplus ⥤ DXplus)
    (lcZarPullbackDerivedPlus : DLCZarYplus ⥤ DLCZarXplus)
    (RGammaSmallX : DXplus ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (RGammaZarX : DLCZarXplus ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (L : DYplus) (n : ℕ) :
    IsIsomorphic
      (derivedCohomologyObject RGammaZarX
        (lcZarPullbackDerivedPlus.obj (piInverseDerivedPlusY.obj L)) n)
      (derivedCohomologyObject RGammaSmallX
        (smallPullbackDerivedPlus.obj L) n) := sorry

-- Proof sketch: for a proper map `f`, proper base change identifies sections of `f_* \mathcal F`
-- after pulling back along any object of `LC_{Zar}/Y` with sections of the pullback object on the
-- corresponding fiber product over `X`. These objectwise identifications assemble into a natural
-- isomorphism of sheaf-valued functors.
/-- Lemma 21.31.7 (7): corresponding to the source's clause `(7a)`, if `f : X ⟶ Y` is proper,
then `π_Y^{-1} \circ f_*` is canonically isomorphic to `f_{Zar,*} \circ π_X^{-1}` as a functor
from sheaves on `X` to sheaves on `LC_{Zar}/Y`. -/
theorem proper_smallPushforward_piInverse_isomorphic_lcZarPushforward_piInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (JX : GrothendieckTopology (Over X))
    (JY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JY).IsRightAdjoint]
    [HasPullbacks LCCat.{u}]
    [(Over.pullback f).IsContinuous JY JX] :
    IsIsomorphic
      ((TopCat.Sheaf.pushforward (Type u) f.hom) ⋙ piInverseType JY πY)
      ((piInverseType JX πX) ⋙
        ((Over.pullback f).sheafPushforwardContinuous (Type u) JY JX)) := sorry

-- Proof sketch: apply the underived proper base-change comparison from part (7) objectwise to the
-- cohomology sheaves of a bounded-below complex and then use the sheafification description of
-- higher direct images to identify the two derived pushforwards.
/-- Lemma 21.31.7 (8): corresponding to the source's clause `(7b)`, if `f : X ⟶ Y` is proper,
then `π_Y^{-1} \circ Rf_*` is canonically isomorphic to `Rf_{Zar,*} \circ π_X^{-1}` as a functor
`D^+(X) ⥤ D^+(LC_{Zar}/Y)`. -/
theorem proper_smallDerivedPushforward_piInverse_isomorphic_lcZarDerivedPushforward_piInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (DXplus : Type (u + 1)) [Category.{u} DXplus]
    (DYplus : Type (u + 1)) [Category.{u} DYplus]
    (DLCZarXplus : Type (u + 1)) [Category.{u} DLCZarXplus]
    (DLCZarYplus : Type (u + 1)) [Category.{u} DLCZarYplus]
    (piInverseDerivedPlusX : DXplus ⥤ DLCZarXplus)
    (piInverseDerivedPlusY : DYplus ⥤ DLCZarYplus)
    (smallPushforwardDerivedPlus : DXplus ⥤ DYplus)
    (lcZarPushforwardDerivedPlus : DLCZarXplus ⥤ DLCZarYplus) :
    IsIsomorphic
      (smallPushforwardDerivedPlus ⋙ piInverseDerivedPlusY)
      (piInverseDerivedPlusX ⋙ lcZarPushforwardDerivedPlus) := sorry

end

/-! ### Lemma_21_31_8 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

section

variable {X Y : LCCat.{u}}

/-- Sheaves of types on the small Zariski site of an `LC` object. -/
abbrev SmallTypeSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf (Type u) X.obj

/-- The inverse-image functor `π_X^{-1}` from the small Zariski site of `X` to a chosen
Grothendieck topology on `Over X`. -/
abbrev piInverseType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    SmallTypeSheaf X ⥤ Sheaf J (Type u) :=
  π.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) J

/-- The inverse-image functor `ε_X^{-1}` for the topology comparison
`ε_X : Sh(LC_{qc}/X) ⟶ Sh(LC_{Zar}/X)`, represented by the identity functor on `Over X`. -/
abbrev epsilonInverseType
    (JZar JQc : GrothendieckTopology (Over X))
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    Sheaf JZar (Type u) ⥤ Sheaf JQc (Type u) :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) JZar JQc := hε_cont
  let _ :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint := hε_adj
  (𝟭 (Over X)).sheafPullback (Type u) JZar JQc

-- Proof sketch: unfold `epsilonInverseType`; it is introduced precisely as the sheaf pullback
-- functor attached to the identity-on-objects site morphism from `LC_{Zar}/X` to `LC_{qc}/X`.
/-- The comparison inverse image `ε_X^{-1}` is the sheaf pullback along the identity functor on
`Over X`. -/
theorem epsilonInverseType_eq
    (JZar JQc : GrothendieckTopology (Over X))
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    epsilonInverseType JZar JQc hε_cont hε_adj =
      (𝟭 (Over X)).sheafPullback (Type u) JZar JQc := sorry

/-- The inverse-image functor `a_X^{-1}` for the composite morphism of topoi
`a_X = π_X ∘ ε_X : Sh(LC_{qc}/X) ⟶ Sh(X)`. -/
abbrev aInverseType
    (JZar JQc : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) JZar]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZar).IsRightAdjoint]
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    SmallTypeSheaf X ⥤ Sheaf JQc (Type u) :=
  piInverseType JZar π ⋙ epsilonInverseType JZar JQc hε_cont hε_adj

-- Proof sketch: unfold `aInverseType`; by definition it is the composite of the small-to-big
-- Zariski inverse image `π_X^{-1}` with the qc/Zariski comparison inverse image `ε_X^{-1}`.
/-- The inverse image `a_X^{-1}` is the composite `ε_X^{-1} ∘ π_X^{-1}` on sheaves of types. -/
theorem aInverseType_eq
    (JZar JQc : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) JZar]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZar).IsRightAdjoint]
    (hε_cont : Functor.IsContinuous (𝟭 (Over X)) JZar JQc)
    (hε_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZar JQc).IsRightAdjoint) :
    aInverseType JZar JQc π hε_cont hε_adj =
      piInverseType JZar π ⋙ epsilonInverseType JZar JQc hε_cont hε_adj := sorry

-- Proof sketch: the localized pullback functors on `LC_{Zar}` and `LC_{qc}` are both induced by
-- `Over.pullback f`, while `ε_X` and `ε_Y` come from the identity functors on the slice
-- categories. The compatibility of these continuous functors gives the desired canonical
-- isomorphism between the two composites of inverse-image functors.
/-- Lemma 21.31.8 (1): for a morphism `f : X ⟶ Y` in `LC`, the comparison morphisms
`ε_X : Sh(LC_{qc}/X) ⟶ Sh(LC_{Zar}/X)` and `ε_Y : Sh(LC_{qc}/Y) ⟶ Sh(LC_{Zar}/Y)` fit into the
canonical commutative square of topoi with horizontal arrows given by the localized morphisms
`f_{qc}` and `f_{Zar}`. -/
theorem lcQc_lcZar_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JZarY JZarX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JZarY JZarX).IsRightAdjoint]
    [(Over.pullback f).IsContinuous JQcY JQcX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX).IsRightAdjoint] :
    IsIsomorphic
      (((Over.pullback f).sheafPullback (Type u) JZarY JZarX) ⋙
        epsilonInverseType JZarX JQcX hεX_cont hεX_adj)
      ((epsilonInverseType JZarY JQcY hεY_cont hεY_adj) ⋙
        ((Over.pullback f).sheafPullback (Type u) JQcY JQcX)) := sorry

-- Proof sketch: compose the inverse-image identification for the small/big Zariski square from
-- Lemma `21.31.7 (5)` with the qc/Zariski comparison square from clause `(1)`. Since
-- `a_X^{-1}` and `a_Y^{-1}` are defined as `ε_X^{-1} ∘ π_X^{-1}` and `ε_Y^{-1} ∘ π_Y^{-1}`,
-- this yields the commutative square relating `Sh(LC_{qc}/X)`, `Sh(LC_{qc}/Y)`, `Sh(X)`, and
-- `Sh(Y)`.
/-- Lemma 21.31.8 (2): with `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`, the localized qc topoi and
the small topoi fit into the canonical commutative square over a morphism `f : X ⟶ Y` in `LC`. -/
theorem lcQc_small_topoi_square_isomorphic
    (f : X ⟶ Y)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JZarX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JZarY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZarX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JZarY).IsRightAdjoint]
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JQcY JQcX]
    [((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX).IsRightAdjoint] :
    IsIsomorphic
      ((TopCat.Sheaf.pullback (Type u) f.hom) ⋙
        aInverseType JZarX JQcX πX hεX_cont hεX_adj)
      ((aInverseType JZarY JQcY πY hεY_cont hεY_adj) ⋙
        ((Over.pullback f).sheafPullback (Type u) JQcY JQcX)) := sorry

-- Proof sketch: first apply the proper base-change comparison from Lemma `21.31.7 (7)` to the
-- composite `π_Y^{-1} ∘ f_*`. Then use that `ε_{Y,*}` reflects isomorphisms and that
-- `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}` and `a_Y^{-1} = ε_Y^{-1} ∘ π_Y^{-1}` to descend the
-- comparison to the qc topologies.
/-- Lemma 21.31.8 (3): if `f : X ⟶ Y` is proper, then the inverse image `a_Y^{-1}` composed with
small direct image along `f` is canonically isomorphic to the qc direct image along `f_{qc}`
composed with `a_X^{-1}`. -/
theorem proper_smallPushforward_aInverse_isomorphic_lcQcPushforward_aInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (JZarX JQcX : GrothendieckTopology (Over X))
    (JZarY JQcY : GrothendieckTopology (Over Y))
    (πX : Opens X.obj ⥤ Over X)
    (πY : Opens Y.obj ⥤ Over Y)
    [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) JZarX]
    [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) JZarY]
    [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      JZarX).IsRightAdjoint]
    [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
      JZarY).IsRightAdjoint]
    (hεX_cont : Functor.IsContinuous (𝟭 (Over X)) JZarX JQcX)
    (hεY_cont : Functor.IsContinuous (𝟭 (Over Y)) JZarY JQcY)
    (hεX_adj :
      ((𝟭 (Over X)).sheafPushforwardContinuous (Type u) JZarX JQcX).IsRightAdjoint)
    (hεY_adj :
      ((𝟭 (Over Y)).sheafPushforwardContinuous (Type u) JZarY JQcY).IsRightAdjoint)
    [HasLimitsOfShape WalkingCospan LCCat.{u}]
    [(Over.pullback f).IsContinuous JQcY JQcX] :
    IsIsomorphic
      ((TopCat.Sheaf.pushforward (Type u) f.hom) ⋙
        aInverseType JZarY JQcY πY hεY_cont hεY_adj)
      ((aInverseType JZarX JQcX πX hεX_cont hεX_adj) ⋙
        ((Over.pullback f).sheafPushforwardContinuous (Type u) JQcY JQcX)) := sorry

end

/-! ### Lemma_21_31_9 (from Chap21) -/
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

/-- Proper maps in `LC` viewed as a morphism property. -/
abbrev lcProperMapProperty : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ IsProperMap f.hom

/-- Membership in `lcProperMapProperty` is exactly topological properness. -/
theorem mem_lcProperMapProperty_iff {X Y : LCCat.{u}} (f : X ⟶ Y) :
    lcProperMapProperty f ↔ IsProperMap f.hom :=
  Iff.rfl

section

variable (τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]

/-- The inverse-image functor `π_X^{-1}` on abelian sheaves from the small Zariski site of `X` to
the big Zariski site `LC_{Zar}/X`. -/
abbrev lcZarPiInverseAb (X : LCCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤
      Sheaf (τzar.over X) AddCommGrpCat.{u + 1} :=
  (πFunctor X).sheafPullback AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) (τzar.over X)

/-- For `X ∈ LC`, the comparison subcategory `A'_X ⊂ Ab(LC_{Zar}/X)` consists of the sheaves in
the essential image of `π_X^{-1}`. -/
abbrev lcZarPiInverseEssImage (X : LCCat.{u}) :
    ObjectProperty (Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :=
  (lcZarPiInverseAb τzar πFunctor X).essImage

/-- Membership in `A'_X` means that the sheaf is isomorphic to one of the form `π_X^{-1}\mathcal
F`. -/
theorem mem_lcZarPiInverseEssImage_iff
    {X : LCCat.{u}} (ℱ : Sheaf (τzar.over X) AddCommGrpCat.{u + 1}) :
    lcZarPiInverseEssImage τzar πFunctor X ℱ ↔
      (lcZarPiInverseAb τzar πFunctor X).essImage ℱ :=
  Iff.rfl

end

section

variable (τqc τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (𝟭 (Over X)) (τzar.over X) (τqc.over X)]
variable [∀ X : LCCat.{u},
  ((𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (τzar.over X) (τqc.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u}, HasInjectiveResolutions (Sheaf (τzar.over X) AddCommGrpCat.{u + 1})]
variable [∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (τzar.over X) (τzar.over Y))]

-- Proof sketch: for each `X`, Lemma `21.31.7` identifies `A'_X` with the essential image of the
-- exact fully faithful functor `π_X^{-1}`, giving the weak LinearRepresentations_Serre_1977 conditions. Proper maps in `LC`
-- are stable under base change, Lemma `21.31.6` shows objects of `A'_X` are already sheaves for
-- the qc topology, Lemma `21.31.7` gives compatibility of inverse image and higher direct images
-- with `π_X^{-1}` for proper maps, and Lemma `21.31.4` supplies the refinement clause for qc
-- coverings.
/-- Lemma 21.31.9: for the comparison morphism `LC_qc ⟶ LC_Zar`, let `P` be the proper maps of
topological spaces and let `A'_X ⊂ Ab(LC_Zar / X)` be the full subcategory consisting of sheaves
of the form `π_X^{-1}\mathcal F`. Then the hypotheses `(1)` through `(5)` of Situation `21.30.1`
hold, formalized as a cohomology comparison situation. -/
theorem lc_qc_lc_zar_cohomology_comparison_situation :
    cohomology_comparison_situation τqc τzar
      lcProperMapProperty (lcZarPiInverseEssImage τzar πFunctor) := sorry

end

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_31_10 (from Chap21) -/
open CategoryTheory
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The object property on `TopCat` selecting Hausdorff weakly locally compact spaces. -/
abbrev HausdorffWeaklyLocallyCompactObject : CategoryTheory.ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ WeaklyLocallyCompactSpace X

/-- The category of Hausdorff locally quasi-compact spaces used for `LC_{qc}`. -/
abbrev LCCat : Type (u + 1) :=
  HausdorffWeaklyLocallyCompactObject.FullSubcategory

namespace CategoryTheory.GrothendieckTopology

section

variable (ZarSheaf QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (ZarSheaf X)]
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, Abelian (ZarSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (ZarSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasInjectiveResolutions (QcSheaf X)]

variable (piInverseAb :
  ∀ X : LCCat.{u}, TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤ ZarSheaf X)
variable (aInverseAb :
  ∀ X : LCCat.{u}, TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj ⥤ QcSheaf X)
variable (epsilonPushforwardAb : ∀ X : LCCat.{u}, QcSheaf X ⥤ ZarSheaf X)
variable [∀ X : LCCat.{u}, Functor.Additive (epsilonPushforwardAb X)]

variable (piInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (ZarSheaf X))
variable (aInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (QcSheaf X))
variable (rEpsilonPushforward :
  ∀ X : LCCat.{u}, DerivedCategory (QcSheaf X) ⥤ DerivedCategory (ZarSheaf X))
variable (smallPushforwardDerived :
  ∀ {X Y : LCCat.{u}} (_ : X ⟶ Y),
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} Y.obj))
variable (qcPushforwardDerived :
  ∀ {X Y : LCCat.{u}} (_ : X ⟶ Y),
    DerivedCategory (QcSheaf X) ⥤ DerivedCategory (QcSheaf Y))

/-- The bounded-below condition on the derived category of small abelian sheaves on an `LC`
object. -/
private def smallAbDerivedBoundedBelow (X : LCCat.{u}) :
    ObjectProperty (DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)) :=
  fun K ↦
    ∃ n : ℤ, ∀ i : ℤ, i < n →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor
          (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) i).obj K)

-- Proof sketch: this is the underived comparison statement obtained by pushing forward the
-- canonical qc pullback `a_X^{-1}\mathcal F` along `\epsilon_X` and identifying the result with
-- the big-Zariski pullback `π_X^{-1}\mathcal F`.
/-- Lemma 21.31.10 (1): for `X ∈ LC_{qc}` and an abelian sheaf `\mathcal F` on `X`, the chosen
comparison pushforward formalizing `\epsilon_{X,*}` sends `a_X^{-1}\mathcal F` to
`π_X^{-1}\mathcal F`. -/
theorem comparisonPushforward_aInverseAb_isomorphic_piInverseAb
    (X : LCCat.{u})
    (ℱ : TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) :
    IsIsomorphic
      ((epsilonPushforwardAb X).obj ((aInverseAb X).obj ℱ))
      ((piInverseAb X).obj ℱ) := sorry

-- Proof sketch: compute the higher right derived functors of the comparison pushforward on the
-- qc pullback `a_X^{-1}\mathcal F`; the comparison situation forces the positive-degree terms to
-- vanish.
/-- Lemma 21.31.10 (2): for `X ∈ LC_{qc}` and an abelian sheaf `\mathcal F` on `X`, the higher
derived direct images `R^i \epsilon_{X,*}(a_X^{-1}\mathcal F)` vanish for `i > 0`. -/
theorem higherComparisonPushforward_aInverseAb_isZero
    (X : LCCat.{u})
    (ℱ : TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero
      (((epsilonPushforwardAb X).rightDerived i).obj ((aInverseAb X).obj ℱ)) := sorry

-- Proof sketch: apply the derived comparison theorem to the bounded-below object `K`. The chosen
-- derived pullbacks formalizing `π_X^{-1}` and `a_X^{-1}` identify the resulting comparison with
-- `π_X^{-1}K \to R\epsilon_{X,*}(a_X^{-1}K)`.
/-- Lemma 21.31.10 (3): for `X ∈ LC_{qc}` and a bounded-below derived abelian sheaf `K` on `X`,
the canonical map `π_X^{-1}K \to R \epsilon_{X,*}(a_X^{-1}K)` is an isomorphism. -/
theorem piInverseDerived_isomorphic_rComparisonPushforward_aInverseDerived
    (X : LCCat.{u})
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIsomorphic
      ((piInverseDerived X).obj K)
      ((rEpsilonPushforward X).obj ((aInverseDerived X).obj K)) := sorry

-- Proof sketch: combine proper base change on the small Zariski site with the derived comparison
-- for `\epsilon_Y`. The chosen derived direct images formalizing `Rf_*` and `R f_{qc,*}` then
-- identify `a_Y^{-1}(Rf_* K)` with `R f_{qc,*}(a_X^{-1}K)`.
/-- Lemma 21.31.10 (4): for a proper morphism `f : X \to Y` in `LC_{qc}` and a bounded-below
derived abelian sheaf `K` on `X`, the inverse image `a_Y^{-1}(Rf_* K)` is canonically
isomorphic to `R f_{qc,*}(a_X^{-1}K)`. -/
theorem proper_aInverseDerived_smallPushforward_isomorphic_qcPushforwardDerived
    {X Y : LCCat.{u}}
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom)
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIsomorphic
      ((aInverseDerived Y).obj ((smallPushforwardDerived f).obj K))
      ((qcPushforwardDerived f).obj ((aInverseDerived X).obj K)) := sorry

end

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_31_11 (from Chap21) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

section

variable (QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]

variable (aInverseDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) ⥤
      DerivedCategory (QcSheaf X))
variable (aPushforwardDerived :
  ∀ X : LCCat.{u},
    DerivedCategory (QcSheaf X) ⥤
      DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))

/-- The bounded-below condition on the derived category `D(X)` of abelian sheaves on the small
site of `X`. -/
private def smallAbDerivedBoundedBelow (X : LCCat.{u}) :
    ObjectProperty (DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj)) :=
  fun K ↦
    ∃ n : ℤ, ∀ i : ℤ, i < n →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor
          (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj) i).obj K)

-- Proof sketch: represent `K` by a bounded-below complex of abelian sheaves. For a single sheaf
-- `ℱ`, Lemma `21.31.6` identifies `a_{X,*} a_X^{-1} ℱ` with `ℱ`, while Lemma `21.31.10`
-- together with the relative Leray spectral sequence and Lemma `21.31.7` kills the higher
-- derived direct images. Leray's acyclicity lemma then upgrades the sheaf-level statement to the
-- bounded-below derived category, proving that the adjunction unit is an isomorphism.
/-- Lemma 21.31.11: for `X ∈ LC_{qc}` and `K ∈ D^+(X)`, the canonical map
`K ⟶ R a_{X,*} a_X^{-1} K` is an isomorphism. Here this map is formalized as the adjunction unit
for the chosen inverse-image functor `a_X^{-1}` on derived categories and the derived direct image
functor `R a_{X,*}` attached to the localization morphism
`a_X : Sh(LC_{qc}/X) ⟶ Sh(X)`. -/
theorem lcQc_localization_derived_unit_isIso
    (X : LCCat.{u})
    (adjA : aInverseDerived X ⊣ aPushforwardDerived X)
    (K : DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u + 1} X.obj))
    (hK : smallAbDerivedBoundedBelow X K) :
    IsIso (adjA.unit.app K) := sorry

end

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_31_12 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

section

variable (SmallSheaf QcSheaf : LCCat.{u} → Type (u + 1))
variable [∀ X : LCCat.{u}, Category.{u} (SmallSheaf X)]
variable [∀ X : LCCat.{u}, Category.{u} (QcSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (SmallSheaf X)]
variable [∀ X : LCCat.{u}, Abelian (QcSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (SmallSheaf X)]
variable [∀ X : LCCat.{u}, HasDerivedCategory (QcSheaf X)]

variable (smallAbelianSheafCohomology :
  ∀ X : LCCat.{u}, SmallSheaf X → ℕ → AddCommGrpCat.{u + 1})
variable (qcAbelianSheafCohomology :
  ∀ X : LCCat.{u}, QcSheaf X → ℕ → AddCommGrpCat.{u + 1})
variable (smallAbelianSheafHypercohomology :
  ∀ X : LCCat.{u}, DerivedCategory (SmallSheaf X) → ℕ → AddCommGrpCat.{u + 1})
variable (qcAbelianSheafHypercohomology :
  ∀ X : LCCat.{u}, DerivedCategory (QcSheaf X) → ℕ → AddCommGrpCat.{u + 1})
variable (smallDplus :
  ∀ X : LCCat.{u}, ObjectProperty (DerivedCategory (SmallSheaf X)))
variable (aInverseAb : ∀ X : LCCat.{u}, SmallSheaf X ⥤ QcSheaf X)
variable (aInverseDerived :
  ∀ X : LCCat.{u}, DerivedCategory (SmallSheaf X) ⥤ DerivedCategory (QcSheaf X))
variable (smallConstantAbelianSheaf :
  ∀ X : LCCat.{u}, AddCommGrpCat.{u + 1} → SmallSheaf X)
variable (qcConstantAbelianSheaf :
  ∀ X : LCCat.{u}, AddCommGrpCat.{u + 1} → QcSheaf X)

-- Proof sketch: apply Lemma `21.31.11` to the degree-zero complex attached to `ℱ` and use
-- Remark `21.14.4` to identify the resulting derived global-sections comparison with the
-- degree-`n` cohomology groups on the small and qc sites.
/-- Lemma 21.31.12 (1): for an abelian sheaf `\mathcal F` on `X ∈ LC_{qc}`, the global
cohomology `H^n(X, \mathcal F)` is canonically isomorphic to the qc cohomology
`H^n_{qc}(X, a_X^{-1}\mathcal F)`. -/
theorem smallCohomology_iso_qcCohomology_of_aInverse
    (X : LCCat.{u}) (ℱ : SmallSheaf X) (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafCohomology X ℱ n)
      (qcAbelianSheafCohomology X ((aInverseAb X).obj ℱ) n) := sorry

-- Proof sketch: combine Lemma `21.31.11`, which identifies `K` with `R a_{X,*} a_X^{-1} K` for
-- bounded-below `K`, with Remark `21.14.4` to compare derived global sections on the small and qc
-- sites, then pass to degree-`n` homology.
/-- Lemma 21.31.12 (2): for `K ∈ D^+(X)`, the degree-`n` hypercohomology `H^n(X, K)` is
canonically isomorphic to the qc hypercohomology `H^n_{qc}(X, a_X^{-1} K)`. -/
theorem smallHypercohomology_iso_qcHypercohomology_of_aInverse
    (X : LCCat.{u})
    (K : DerivedCategory (SmallSheaf X))
    (hK : smallDplus X K)
    (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafHypercohomology X K n)
      (qcAbelianSheafHypercohomology X ((aInverseDerived X).obj K) n) := sorry

-- Proof sketch: apply clause `(1)` to the constant abelian sheaf `\underline A`; the inverse
-- image of a constant sheaf along the qc localization is again the constant sheaf with value `A`.
/-- Lemma 21.31.12 (3): for an abelian group `A`, the cohomology of the constant sheaf
`\underline A` on `X` is canonically isomorphic to the qc cohomology of the constant sheaf
`\underline A` on `LC_{qc}/X`. -/
theorem constantSheaf_smallCohomology_iso_qcCohomology
    (X : LCCat.{u}) (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      (smallAbelianSheafCohomology X (smallConstantAbelianSheaf X A) n)
      (qcAbelianSheafCohomology X (qcConstantAbelianSheaf X A) n) := sorry

end

end CategoryTheory.GrothendieckTopology
