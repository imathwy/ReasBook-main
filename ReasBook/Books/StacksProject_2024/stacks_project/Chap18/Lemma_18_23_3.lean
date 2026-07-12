import StacksProject_2024.Chap17.Definition_17_9_1
import StacksProject_2024.Chap17.Definition_17_10_1
import StacksProject_2024.Chap17.Definition_17_11_1
import StacksProject_2024.Chap18.Definition_18_17_1
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.ObjectProperty

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/- Domain-style sampling for Lemma 18.23.3:
- primary domain: local module-theoretic properties of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory` from `Definition_18_23_1`,
  `SheafOfModules.RingedSite.IsLocallyGeneratedBySections`,
  `SheafOfModules.RingedSite.IsFiniteType`,
  `SheafOfModules.RingedSite.IsQuasicoherent`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction:
  the ambient owner category `ringedSiteModuleCategory J 𝒪` together with the existing
  `SheafOfModules` owner predicates/data on each restriction `ℱ.over U`, and the
  source-facing ringed-site owners from `Definition_18_23_1` for the corresponding
  localized ringed sites;
- primitive data:
  a covering family of the terminal object and the corresponding owner-level property on each
  restriction `ℱ.over (X i)`;
- derived API:
  the fifteen local-on-the-base equivalences stated below.

Source/core/bridge triage:
- `source-facing`: the local-on-the-base criteria in Stacks Lemma 18.23.3;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsLocallyGeneratedBySections`,
  `SheafOfModules.RingedSite.IsFiniteType`,
  `SheafOfModules.RingedSite.IsQuasicoherent`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`;
- `bridge/view`: the restriction operation `ℱ.over (X i)` to localized ringed sites.

Accordingly, this file reuses the canonical owner `ringedSiteModuleCategory` from
`RingedSiteModuleCategoryBasic` and locally restates only the source-facing ringed-site owners
needed for Lemma 18.23.3, avoiding the broken transitive Chapter 18 import chain through
`Definition_18_23_1`. -/

/-- Helper for Lemma 18.23.3: restriction from the ambient ringed site to the localized ringed
site over `U`. -/
noncomputable abbrev ringedSiteLocalizedRestriction (U : C) :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
  SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))

/-- Helper for Lemma 18.23.3: localized restriction is the left adjoint in the standard slice-site
adjunction. -/
instance ringedSiteLocalizedRestriction_isLeftAdjoint (U : C) [HasBinaryProducts C] :
    (ringedSiteLocalizedRestriction (J := J) (𝒪 := 𝒪) U).IsLeftAdjoint := by
  -- Proof comment: the canonical localized adjunction already identifies restriction to `C / U`
  -- with the left adjoint of extension by zero.
  exact (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U).isLeftAdjoint

/-- Helper for Lemma 18.23.3: a sheaf of `\mathcal O`-modules on a ringed site is locally free if
every object admits a covering by slice objects on which the restriction is free. -/
class IsLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is free. -/
  isFree_over (U : C) :
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, ((ℱ.over U).over (X i)).IsFree

/-- Helper for Lemma 18.23.3: a sheaf of `\mathcal O`-modules on a ringed site is finite locally
free if every object admits a covering by slice objects on which the restriction is finite free.
-/
class IsFiniteLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is finite free. -/
  isFiniteFree_over (U : C) :
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, ((ℱ.over U).over (X i)).IsFiniteFree

/-- Helper for Lemma 18.23.3: finite locally free sheaves are locally free. -/
instance isFiniteLocallyFree_to_isLocallyFree (ℱ : ringedSiteModuleCategory J 𝒪)
    [IsFiniteLocallyFree ℱ] :
    IsLocallyFree ℱ := by
  refine ⟨fun U ↦ ?_⟩
  -- Proof comment: reuse the same local cover and forget only the finiteness on each chart.
  obtain ⟨I, X, hX, hfree⟩ := IsFiniteLocallyFree.isFiniteFree_over (ℱ := ℱ) U
  exact ⟨I, X, hX, fun i ↦ inferInstanceAs (((ℱ.over U).over (X i)).IsFree)⟩

/-- Helper for Lemma 18.23.3: a sheaf is locally generated by `r` sections if every object admits
slice charts on which the restriction is generated by `r` global sections. -/
class IsLocallyGeneratedBy (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) : Prop where
  /-- Every object admits a covering on which the restriction of `ℱ` is generated by `r`
  sections. -/
  isGeneratedBy_over (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ((ℱ.over U).over (X i)).IsGeneratedBy r

/-- Helper for Lemma 18.23.3: a sheaf is locally generated by sections if each restriction to a
slice site admits local generator data. -/
abbrev IsLocallyGeneratedBySections (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, Nonempty (ℱ.over U).LocalGeneratorsData)

/-- Helper for Lemma 18.23.3: the local-generator witness of a locally generated-by-sections sheaf
restricts to every slice. -/
instance isLocallyGeneratedBySections_over (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsLocallyGeneratedBySections ℱ] (U : C) :
    Nonempty (ℱ.over U).LocalGeneratorsData :=
  h.1 U

/-- Helper for Lemma 18.23.3: a sheaf is of finite type on the ringed site when every slice
restriction is of finite type. -/
abbrev IsFiniteType (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsFiniteType)

/-- Helper for Lemma 18.23.3: finite type on the ambient ringed site restricts to every slice. -/
instance isFiniteType_over (ℱ : ringedSiteModuleCategory J 𝒪) [h : IsFiniteType ℱ] (U : C) :
    (ℱ.over U).IsFiniteType :=
  h.1 U

/-- Helper for Lemma 18.23.3: a sheaf is quasi-coherent on the ringed site when every slice
restriction is quasi-coherent. -/
abbrev IsQuasicoherent (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsQuasicoherent)

/-- Helper for Lemma 18.23.3: quasi-coherence on the ambient ringed site restricts to every
slice. -/
instance isQuasicoherent_over (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsQuasicoherent ℱ] (U : C) :
    (ℱ.over U).IsQuasicoherent :=
  h.1 U

/-- Helper for Lemma 18.23.3: a sheaf is of finite presentation on the ringed site when every
slice restriction is of finite presentation. -/
abbrev IsFinitePresentation (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  Fact (∀ U : C, (ℱ.over U).IsFinitePresentation)

/-- Helper for Lemma 18.23.3: finite presentation on the ambient ringed site restricts to every
slice. -/
instance isFinitePresentation_over (ℱ : ringedSiteModuleCategory J 𝒪)
    [h : IsFinitePresentation ℱ] (U : C) :
    (ℱ.over U).IsFinitePresentation :=
  h.1 U

/-- Helper for Lemma 18.23.3: a coherent sheaf on a ringed site is finite type and has finite-type
kernels for maps from finite free sheaves on every slice. -/
class IsCoherent (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- A coherent sheaf on a ringed site is of finite type. -/
  toIsFiniteType : IsFiniteType ℱ
  /-- Kernels of maps from finite free modules into local restrictions are of finite type. -/
  isFiniteType_kernel (U : C)
      (r : ℕ)
      (φ :
        (_root_.SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) (ULift.{max u v} (Fin r)) :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)) ⟶
          ℱ.over U) :
      (kernel φ).IsFiniteType

/-- Helper for Lemma 18.23.3: coherence implies finite type on the ambient ringed site. -/
instance isFiniteType_of_isCoherent (ℱ : ringedSiteModuleCategory J 𝒪) [h : IsCoherent ℱ] :
    IsFiniteType ℱ :=
  h.toIsFiniteType

/-- Helper for Lemma 18.23.3: the singleton identity family covers the terminal object of the
slice site over `U`. -/
private theorem identitySingletonCoversTopOver (U : C) :
    (J.over U).CoversTop (fun _ : PUnit => Over.mk (𝟙 U)) := by
  -- Proof comment: the unique member of the family is already the terminal object of `C/U`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have htop :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun _ : PUnit => Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
    ext Z g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.overEquiv_iff]
      exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
  rw [htop]
  exact J.top_mem U

/-- Helper for Lemma 18.23.3: the sieve generated in a slice site by a family of slice objects is
the ordinary sieve generated by their underlying arrows. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type (max u v)} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun i ↦ Over.mk (π i)) (Over.mk (𝟙 U))) =
      Sieve.ofArrows Uᵢ π := by
  -- Proof comment: forgetting the over-structure turns a slice factorization into the same
  -- factorization in the ambient category, and conversely every such factorization lifts.
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 18.23.3: the slice family obtained from all arrows `X i ⟶ U` induces the
same ambient sieve as the object family `X` on `U`. -/
private theorem overSieveOfInducedFamilyEq
    {U : C} {I : Type (max u v)} (X : I → C) (V : Over U) :
    (Sieve.overEquiv V)
        (Sieve.ofObjects
          (fun p : Sigma fun i : I => X i ⟶ U ↦ Over.mk p.2) V) =
      Sieve.ofObjects X V.left := by
  -- TODO(Lemma 18.23.3): prove the induced-cover comparison by rewriting the slice sieve as the
  -- pullback of `Sieve.ofObjects X` along `V.hom`; the current all-arrows index needs a stable
  -- pullback argument rather than the naive factorization used here.
  sorry

/-- Helper for Lemma 18.23.3: local chart data on every slice site can be repackaged into one
ambient covering family. -/
private theorem coversTopOfSigmaCharts
    (P : C → Prop)
    (hP : ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, P (X i).left) :
    ∃ (I : Type (max u v)) (Y : I → C), J.CoversTop Y ∧
      ∀ i : I, P (Y i) := by
  classical
  choose I X hX hprop using hP
  refine ⟨Sigma I, fun a ↦ (X a.1 a.2).left, ?_, ?_⟩
  · intro U
    -- Proof comment: the slice cover chosen over `U` gives a covering sieve on `U`, and every
    -- generator of that sieve lands in the sigma family.
    have hcover :
        Sieve.ofArrows (fun i ↦ (X U i).left) (fun i ↦ (X U i).hom) ∈ J U := by
      have hterminal :
          Sieve.ofObjects (X U) (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
        (GrothendieckTopology.coversTop_iff_of_isTerminal
          (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) (X U)).1 (hX U)
      rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
        (Uᵢ := fun i ↦ (X U i).left) (π := fun i ↦ (X U i).hom)] at hterminal
      exact hterminal
    refine J.superset_covering ?_ hcover
    intro V f hf
    rw [Sieve.mem_ofArrows_iff] at hf
    rw [Sieve.mem_ofObjects_iff]
    rcases hf with ⟨i, g, hg⟩
    exact ⟨⟨U, i⟩, ⟨g⟩⟩
  · intro a
    exact hprop a.1 a.2

/-- Helper for Lemma 18.23.3: a `CoversTop` family on the ambient site induces the expected
covering family in every slice site. -/
private theorem inducedOverCoverOfCoversTop
    {I : Type (max u v)} (X : I → C) (hX : J.CoversTop X) (U : C) :
    (J.over U).CoversTop (fun p : Sigma fun i : I => X i ⟶ U ↦ Over.mk p.2) := by
  -- TODO(Lemma 18.23.3): derive this from pullback stability of the covering sieve
  -- `Sieve.ofObjects X U` and then package the resulting pullback family as a `CoversTop`
  -- witness in the slice site.
  sorry

/-- Helper for Lemma 18.23.3: composing a covering of `U` with coverings of each member yields a
sigma-indexed covering of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type (max u v)} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma K ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: convert both slice covers to ambient covering sieves and compose them with the
  -- transitivity axiom `bindOfArrows`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X).1 hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : I,
        Sieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom) ∈ J (X i).left := by
    intro i
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (J.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal) (Y i)).1 (hY i)
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦ Presieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Lemma 18.23.3: a free sheaf on a ringed site is locally free. -/
private theorem isLocallyFree_of_isFree
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : SheafOfModules.IsFree ℱ) :
    IsLocallyFree ℱ := by
  -- TODO(Lemma 18.23.3): transport local freeness across the chosen isomorphism with a free
  -- sheaf, reusing the iterated-restriction normalization from Definition 18.23.1.
  sorry

/-- Helper for Lemma 18.23.3: a finite free sheaf on a ringed site is finite locally free. -/
private theorem isFiniteLocallyFree_of_isFiniteFree
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : SheafOfModules.IsFiniteFree ℱ) :
    IsFiniteLocallyFree ℱ := by
  -- TODO(Lemma 18.23.3): as in the free case, transfer finite local freeness from a chosen
  -- finite free model after normalizing the restriction to the identity slice.
  sorry

/-- Helper for Lemma 18.23.3: a globally generated sheaf on a ringed site is locally generated by
sections. -/
private theorem isLocallyGeneratedBySections_of_generatingSections
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : Nonempty ℱ.GeneratingSections) :
    IsLocallyGeneratedBySections ℱ := by
  -- TODO(Lemma 18.23.3): transport chosen generating sections across restriction to the identity
  -- slice, then package them as `LocalGeneratorsData`.
  sorry

/-- Helper for Lemma 18.23.3: a sheaf generated by `r` global sections on a ringed site is
locally generated by `r` sections. -/
private theorem isLocallyGeneratedBy_of_isGeneratedBy
    {ℱ : ringedSiteModuleCategory J 𝒪} {r : ℕ} (h : SheafOfModules.IsGeneratedBy ℱ r) :
    IsLocallyGeneratedBy ℱ r := by
  -- TODO(Lemma 18.23.3): normalize the restriction of the chosen epimorphism
  -- `free (ULift (Fin r)) ⟶ ℱ` to the identity slice and reuse it as the local chart witness.
  sorry

/-- Helper for Lemma 18.23.3: finite global generation on a ringed site implies finite type. -/
private theorem isFiniteType_of_finiteGloballyGenerated
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : SheafOfModules.IsFiniteGloballyGenerated ℱ) :
    IsFiniteType ℱ := by
  -- TODO(Lemma 18.23.3): restrict a chosen finite generating family to the identity slice and
  -- certify the resulting singleton local-generator package as finite type.
  sorry

/-- Helper for Lemma 18.23.3: restricting a locally generated-by-sections sheaf to a slice keeps
the same ringed-site property. -/
private theorem isLocallyGeneratedBySections_over_of_isLocallyGeneratedBySections
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : IsLocallyGeneratedBySections ℱ) (U : C) :
    IsLocallyGeneratedBySections (ℱ.over U) := by
  -- Proof comment: a further slice of `ℱ.over U` is definitionally the same as a two-step slice of
  -- `ℱ`, so the ambient `Fact` witness on `ℱ` already provides the needed local data.
  refine ⟨fun V ↦ ?_⟩
  simpa [SheafOfModules.over] using h.1 V.left

/-- Helper for Lemma 18.23.3: restricting a finite-type sheaf to a slice keeps finite type as a
ringed-site property. -/
private theorem isFiniteType_over_of_isFiniteType
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : IsFiniteType ℱ) (U : C) :
    IsFiniteType (ℱ.over U) := by
  -- Proof comment: every iterated slice of `ℱ.over U` is an ambient restriction of `ℱ`.
  refine ⟨fun V ↦ ?_⟩
  simpa [SheafOfModules.over] using h.1 V.left

/-- Helper for Lemma 18.23.3: restricting a quasi-coherent sheaf to a slice keeps quasi-coherence
as a ringed-site property. -/
private theorem isQuasicoherent_over_of_isQuasicoherent
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : IsQuasicoherent ℱ) (U : C) :
    IsQuasicoherent (ℱ.over U) := by
  -- Proof comment: the ambient `Fact` witness already gives quasi-coherence on every iterated
  -- restriction.
  refine ⟨fun V ↦ ?_⟩
  simpa [SheafOfModules.over] using h.1 V.left

/-- Helper for Lemma 18.23.3: restricting a finitely presented sheaf to a slice keeps finite
presentation as a ringed-site property. -/
private theorem isFinitePresentation_over_of_isFinitePresentation
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : IsFinitePresentation ℱ) (U : C) :
    IsFinitePresentation (ℱ.over U) := by
  -- Proof comment: finite presentation is already packaged as a `Fact` over all ambient
  -- restrictions, so the slice inherits it immediately.
  refine ⟨fun V ↦ ?_⟩
  simpa [SheafOfModules.over] using h.1 V.left

/-- Helper for Lemma 18.23.3: restricting a coherent sheaf to a slice keeps coherence as a
ringed-site property. -/
private theorem isCoherent_over_of_isCoherent
    {ℱ : ringedSiteModuleCategory J 𝒪} (h : IsCoherent ℱ) (U : C) :
    IsCoherent (ℱ.over U) := by
  -- Proof comment: finite type and the finite-kernel condition are both stated objectwise, so they
  -- transport directly to the slice site.
  refine ⟨isFiniteType_over_of_isFiniteType (J := J) (𝒪 := 𝒪) h.toIsFiniteType U, ?_⟩
  intro V r φ
  simpa [SheafOfModules.over] using h.isFiniteType_kernel V.left r φ

/-- Helper for Lemma 18.23.3: coherence on a cover member descends to the corresponding induced
slice chart over any ambient object. -/
private theorem isCoherent_over_inducedCoverChart
    {ℱ : ringedSiteModuleCategory J 𝒪}
    {I : Type (max u v)} (X : I → C)
    (hcoh : ∀ i : I, IsCoherent (ℱ.over (X i)))
    {U : C} (p : Sigma fun i : I => X i ⟶ U) :
    let M : ringedSiteModuleCategory ((J.over U).over (Over.mk p.2)) ((𝒪.over U).over (Over.mk p.2)) :=
      (ℱ.over U).over (Over.mk p.2)
    IsCoherent M := by
  -- Proof comment: the induced chart is an iterated restriction of `ℱ` through `X p.1`, so the
  -- coherent restriction on `X p.1` can be restricted once more along the identity slice object.
  simpa [SheafOfModules.over] using
    isCoherent_over_of_isCoherent
      (J := J.over (X p.1)) (𝒪 := 𝒪.over (X p.1))
      (hcoh p.1) (Over.mk (𝟙 (X p.1)))

/-- Helper for Lemma 18.23.3: local generator data on a covering family can be composed into local
generator data on the base slice. -/
private noncomputable def localGeneratorsDataOfCoversTop
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (σ : ∀ i : I, (M.over (X i)).LocalGeneratorsData) :
    M.LocalGeneratorsData where
  I := Sigma fun i : I ↦ (σ i).I
  X := fun a ↦ Over.mk (((σ a.1).X a.2).hom ≫ (X a.1).hom)
  coversTop := coversTopSigmaComp (J := J) (U := U) hX (fun i ↦ (σ i).coversTop)
  generators := fun a ↦ by
    -- Proof comment: on a composed chart, use the generators already chosen on the second-stage
    -- slice and identify the iterated restriction with the corresponding ambient restriction.
    simpa [SheafOfModules.over] using (σ a.1).generators a.2

/-- Helper for Lemma 18.23.3: if each chartwise local-generator package is finite type, the
composed package is finite type as well. -/
private theorem localGeneratorsDataOfCoversTop_isFiniteType
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (σ : ∀ i : I, (M.over (X i)).LocalGeneratorsData)
    (hσ : ∀ i : I, (σ i).IsFiniteType) :
    (localGeneratorsDataOfCoversTop (J := J) (𝒪 := 𝒪) X hX σ).IsFiniteType := by
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk ?_
  rintro ⟨i, j⟩
  -- Proof comment: the generator on a composed chart is literally the generator chosen on the
  -- second-stage chart, so its finiteness is inherited from `hσ i`.
  simpa [localGeneratorsDataOfCoversTop] using (hσ i).1 j

/-- Helper for Lemma 18.23.3: chartwise global presentations on a covering family imply
quasi-coherence on the base slice. -/
private theorem isQuasicoherentOfCoversTopPresentations
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hP : ∀ i : I, Nonempty ((M.over (X i)).Presentation)) :
    M.IsQuasicoherent := by
  classical
  -- Proof comment: bind the chosen chart presentations into one quasicoherent-data package.
  let D : ∀ i : I, (M.over (X i)).QuasicoherentData :=
    fun i ↦ (Classical.choice (hP i)).quasicoherentData
  exact ⟨SheafOfModules.QuasicoherentData.bind M X hX D⟩

/-- Helper for Lemma 18.23.3: chartwise finite presentations on a covering family imply finite
presentation on the base slice. -/
private theorem isFinitePresentationOfCoversTopFinitePresentations
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hfp : ∀ i : I, (M.over (X i)).IsFinitePresentation) :
    M.IsFinitePresentation := by
  -- Proof comment: first glue the chart presentations into one quasicoherent-data package, then
  -- use the chartwise finiteness instances to mark the glued package as finite.
  let D : ∀ i : I, (M.over (X i)).QuasicoherentData := fun i ↦ by
    let _ : (M.over (X i)).IsFinitePresentation := hfp i
    exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (X i))).choose
  let q : M.QuasicoherentData :=
    SheafOfModules.QuasicoherentData.bind M X hX D
  let _ : q.IsFinitePresentation := by
    refine ⟨?_⟩
    intro i
    dsimp [q, D, SheafOfModules.QuasicoherentData.bind]
    infer_instance
  exact ⟨q, inferInstance⟩

/-- Helper for Lemma 18.23.3: chartwise finite type on a covering family implies finite type on
the base slice. -/
private theorem isFiniteTypeOfCoversTopFiniteTypeRestrictions
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hft : ∀ i : I, (M.over (X i)).IsFiniteType) :
    M.IsFiniteType := by
  classical
  -- Proof comment: choose finite local-generator data on each chart and glue those packages along
  -- the given cover.
  let σ : ∀ i : I, (M.over (X i)).LocalGeneratorsData := fun i ↦
    (SheafOfModules.IsFiniteType.exists_localGeneratorsData (M.over (X i))).choose
  let hσ : ∀ i : I, (σ i).IsFiniteType := fun i ↦
    (SheafOfModules.IsFiniteType.exists_localGeneratorsData (M.over (X i))).choose_spec
  exact ⟨localGeneratorsDataOfCoversTop (J := J) (𝒪 := 𝒪) X hX σ,
    localGeneratorsDataOfCoversTop_isFiniteType (J := J) (𝒪 := 𝒪) X hX σ hσ⟩

/-- Helper for Lemma 18.23.3: chartwise quasi-coherence on a covering family implies
quasi-coherence on the base slice. -/
private theorem isQuasicoherentOfCoversTopQuasicoherentRestrictions
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hq : ∀ i : I, (M.over (X i)).IsQuasicoherent) :
    M.IsQuasicoherent := by
  classical
  -- Proof comment: bind one chosen quasi-coherent datum from each chart into a global package on
  -- the base slice.
  let D : ∀ i : I, (M.over (X i)).QuasicoherentData := fun i ↦
    Classical.choice (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
      (M := M.over (X i)))
  exact (SheafOfModules.QuasicoherentData.bind M X hX D).isQuasicoherent

/-- Helper for Lemma 18.23.3: a finite-presentation witness upgrades to the owner predicate. -/
private theorem isFinitePresentation_of_finitePresentationWitness
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (hP : Nonempty {P : M.Presentation // P.IsFinite}) :
    M.IsFinitePresentation := by
  -- Proof comment: the chapter API already provides the owner instance from a chosen finite
  -- presentation witness, so we just install the witness locally and reuse instance search.
  let _ : Nonempty {P : M.Presentation // P.IsFinite} := hP
  infer_instance

/-- Helper for Lemma 18.23.3: `mapFree` identifies the restriction of the ambient free sheaf on
`(C/U, \mathcal O_U)` with the canonical free sheaf on the slice over `V`. -/
private noncomputable abbrev overRestrictionFreeIso
    {U : C} (V : Over U) (I : Type (max u v)) :
    (((_root_.SheafOfModules.free
          (R := ringSheaf (J.over U) (𝒪.over U)) I :
          ringedSiteModuleCategory (J.over U) (𝒪.over U)).over V) :
        ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) ≅
      (_root_.SheafOfModules.free
        (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V)) I :
        ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) :=
  -- Proof comment: the restriction functor is pushforward along the identity comparison of ring
  -- sheaves on the slice site, so `mapFree` supplies the canonical free-source normalization.
  SheafOfModules.mapFree
    (SheafOfModules.pushforward (𝟙 (ringSheaf ((J.over U).over V) ((𝒪.over U).over V))))
    (Iso.refl (SheafOfModules.unit (ringSheaf ((J.over U).over V) ((𝒪.over U).over V))))
    I

/-- Helper for Lemma 18.23.3: restricting along a slice object is the pushforward functor along the
canonical identity comparison of the iterated slice ring sheaf. -/
private abbrev overSliceRestrictionFunctor
    {U : C} (V : Over U) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
      ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V) :=
  SheafOfModules.pushforward
    (SheafOfModules.pushforwardOver (R := ringSheaf (J.over U) (𝒪.over U)) V)

/-- Helper for Lemma 18.23.3: restricting a kernel to a slice agrees with the kernel of the
restricted morphism. -/
private noncomputable def restrictionKernelComparisonIso
    {U : C} {M N : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (θ : M ⟶ N) (V : Over U) :
    ((kernel θ).over V) ≅ kernel ((overSliceRestrictionFunctor (J := J) (𝒪 := 𝒪) V).map θ) := by
  let F : ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
      ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V) :=
    overSliceRestrictionFunctor (J := J) (𝒪 := 𝒪) V
  let _ : F.IsRightAdjoint :=
    (SheafOfModules.overPushforwardOverAdj
      (R := ringSheaf (J.over U) (𝒪.over U)) V).isRightAdjoint
  let _ : PreservesLimit (parallelPair θ 0) F := by
    infer_instance
  -- Proof comment: a right adjoint preserves kernels, so `kernelComparison` gives the canonical
  -- comparison between restricting `kernel θ` and the kernel of the restricted morphism.
  simpa [F, overSliceRestrictionFunctor, SheafOfModules.over] using
    (asIso (CategoryTheory.Limits.kernelComparison θ F))

/-- Helper for Lemma 18.23.3: on a coherent chart, the restriction of the kernel of an ambient
free-source morphism is of finite type. -/
private theorem coherentRestriction_kernel_over_isFiniteType
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (V : Over U) (hV : IsCoherent (M.over V))
    (r : ℕ)
    (φ :
      (_root_.SheafOfModules.free
        (R := ringSheaf (J.over U) (𝒪.over U)) (ULift.{max u v} (Fin r)) :
        ringedSiteModuleCategory (J.over U) (𝒪.over U)) ⟶
        M) :
    ((kernel φ).over V).IsFiniteType := by
  let e := overRestrictionFreeIso
    (J := J) (𝒪 := 𝒪) V (ULift.{max u v} (Fin r))
  let ψ :
      (((_root_.SheafOfModules.free
            (R := ringSheaf (J.over U) (𝒪.over U)) (ULift.{max u v} (Fin r)) :
            ringedSiteModuleCategory (J.over U) (𝒪.over U)).over V) :
          ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) ⟶
        M.over V :=
    (SheafOfModules.pushforward (𝟙 (ringSheaf ((J.over U).over V) ((𝒪.over U).over V)))).map φ
  let φV :
      (_root_.SheafOfModules.free
        (R := ringSheaf ((J.over U).over V) ((𝒪.over U).over V))
          (ULift.{max u v} (Fin r)) :
        ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) ⟶
        M.over V :=
    e.inv ≫ ψ
  have hφV : (kernel φV).IsFiniteType := by
    -- Proof comment: coherence on the chart `V` applied at its identity slice object gives the
    -- finite-type kernel statement for the normalized chart morphism `φV`.
    simpa [φV] using hV.isFiniteType_kernel (Over.mk (𝟙 V.left)) r φV
  let P :
      ObjectProperty
        (ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) :=
    SheafOfModules.IsFiniteType
  have hψ : (kernel ψ).IsFiniteType := by
    -- Proof comment: precomposing by the free-source isomorphism `e.inv` does not change the
    -- kernel up to `kernelIsIsoComp`, so the finite-type property transports to `kernel ψ`.
    simpa [φV] using
      (P.prop_of_iso (CategoryTheory.Limits.kernelIsIsoComp e.inv ψ) hφV)
  -- Route correction: avoid the broken upstream `Lemma_17_11_4` import by using the local
  -- restriction-vs-kernel comparison iso specialized to this iterated slice site.
  -- Proof comment: the local comparison iso identifies the restricted ambient kernel with `kernel
  -- ψ`, so the chartwise finite-type result transports back to `((kernel φ).over V)`.
  exact P.prop_of_iso
    (restrictionKernelComparisonIso (J := J) (𝒪 := 𝒪) φ V).symm hψ

/-- Helper for Lemma 18.23.3: coherence on each member of a cover controls finite type of kernels
on the base slice. -/
private theorem isFiniteTypeKernelOfCoversTopCoherentRestrictions
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hcoh : ∀ i : I, IsCoherent (M.over (X i)))
    (r : ℕ)
    (φ :
      (_root_.SheafOfModules.free
        (R := ringSheaf (J.over U) (𝒪.over U)) (ULift.{max u v} (Fin r)) :
        ringedSiteModuleCategory (J.over U) (𝒪.over U)) ⟶
        M) :
    (kernel φ).IsFiniteType := by
  -- Proof comment: use the chartwise kernel bridge on every member of the cover and then glue the
  -- resulting finite-type restrictions of `kernel φ`.
  exact isFiniteTypeOfCoversTopFiniteTypeRestrictions (J := J) (𝒪 := 𝒪) X hX
    (fun i ↦ coherentRestriction_kernel_over_isFiniteType
      (J := J) (𝒪 := 𝒪) (M := M) (X i) (hcoh i) r φ)

/-- Helper for Lemma 18.23.3: coherence on each member of a cover implies coherence on the base
slice. -/
private theorem isCoherentOfCoversTopCoherentRestrictions
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    {I : Type (max u v)} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hcoh : ∀ i : I, IsCoherent (M.over (X i))) :
    IsCoherent M := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: forget the kernel clause chartwise and glue the resulting finite-type data.
    exact isFiniteTypeOfCoversTopFiniteTypeRestrictions (J := J) (𝒪 := 𝒪) X hX
      (fun i ↦ (hcoh i).toIsFiniteType)
  · intro r φ
    -- Proof comment: the kernel clause is exactly the bridge isolated in the previous helper.
    exact isFiniteTypeKernelOfCoversTopCoherentRestrictions
      (J := J) (𝒪 := 𝒪) X hX hcoh r φ

-- Proof sketch: for `→`, local freeness is already local on a cover, so restrict the chosen local
-- trivializations further along the induced covers. For `←`, a cover by locally free
-- restrictions is exactly the data needed to witness that `ℱ` is locally free.
/-- Lemma 18.23.3 (1): `\mathcal F` is locally free if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is locally free. -/
theorem isLocallyFree_iff_exists_cover_isLocallyFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyFree M := by
  constructor
  · intro h
    -- Proof comment: over each object, use the local free cover from `h` and upgrade every chart
    -- to local freeness on the corresponding slice site.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsLocallyFree (ℱ.over U))
      (fun U ↦ by
        obtain ⟨I, X, hX, hfree⟩ := h.isFree_over U
        exact ⟨I, X, hX, fun i ↦ isLocallyFree_of_isFree (J := J.over U) (𝒪 := 𝒪.over U)
          (hfree i)⟩)
  · rintro ⟨I, X, hX, hloc⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    classical
    choose K Z hZ hfree using
      fun p : Sigma fun i : I => X i ⟶ U ↦
        (hloc p.1).isFree_over (Over.mk (𝟙 (X p.1)))
    refine ⟨Sigma K, fun a ↦ Over.mk ((Z a.1 a.2).hom ≫ a.1.2),
      coversTopSigmaComp (J := J) (U := U) hY hZ, fun a ↦ ?_⟩
    -- Proof comment: on every second-stage chart, the iterated restriction is exactly the free
    -- chart produced by the locally free witness on `ℱ.over (X a.1.1)`.
    simpa [SheafOfModules.over] using hfree a.1 a.2

-- Proof sketch: the forward direction refines the local trivializing cover from the definition of
-- local freeness. For the reverse direction, free restrictions are in particular locally free, so
-- the preceding local criterion applies.
/-- Lemma 18.23.3 (2): `\mathcal F` is locally free if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is free. -/
theorem isLocallyFree_iff_exists_cover_isFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFree (ℱ.over (X i)) := by
  constructor
  · intro h
    -- Proof comment: repackage the slice-wise free charts provided by local freeness into one
    -- ambient covering family.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ SheafOfModules.IsFree (ℱ.over U))
      (fun U ↦ h.isFree_over U)
  · rintro ⟨I, X, hX, hfree⟩
    refine ⟨fun U ↦ ?_⟩
    refine ⟨Sigma fun i : I ↦ X i ⟶ U, fun p ↦ Over.mk p.2,
      inducedOverCoverOfCoversTop (J := J) X hX U, fun p ↦ ?_⟩
    -- Proof comment: the restriction to the chart `X p.1` is definitionally the given free
    -- module `ℱ.over (X p.1)`.
    simpa [SheafOfModules.over] using hfree p.1

-- Proof sketch: as in the locally free case, finite local freeness is stable under restriction and
-- can be checked on a covering family of the terminal object.
/-- Lemma 18.23.3 (3): `\mathcal F` is finite locally free if and only if there is a covering of
the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is finite locally
free. -/
theorem isFiniteLocallyFree_iff_exists_cover_isFiniteLocallyFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFiniteLocallyFree M := by
  constructor
  · intro h
    -- Proof comment: use the local finite free charts supplied by finite local freeness and view
    -- each chart as a finite locally free slice.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsFiniteLocallyFree (ℱ.over U))
      (fun U ↦ by
        obtain ⟨I, X, hX, hfree⟩ := h.isFiniteFree_over U
        exact ⟨I, X, hX, fun i ↦
          isFiniteLocallyFree_of_isFiniteFree (J := J.over U) (𝒪 := 𝒪.over U) (hfree i)⟩)
  · rintro ⟨I, X, hX, hloc⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    classical
    choose K Z hZ hfree using
      fun p : Sigma fun i : I => X i ⟶ U ↦
        (hloc p.1).isFiniteFree_over (Over.mk (𝟙 (X p.1)))
    refine ⟨Sigma K, fun a ↦ Over.mk ((Z a.1 a.2).hom ≫ a.1.2),
      coversTopSigmaComp (J := J) (U := U) hY hZ, fun a ↦ ?_⟩
    -- Proof comment: the composed chart is exactly one of the finite free charts on
    -- `ℱ.over (X a.1.1)`.
    simpa [SheafOfModules.over] using hfree a.1 a.2

-- Proof sketch: the given finite free restrictions directly witness finite local freeness after
-- passing to the corresponding cover, and the converse uses the defining finite free local models.
/-- Lemma 18.23.3 (4): `\mathcal F` is finite locally free if and only if there is a covering of
the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is finite free. -/
theorem isFiniteLocallyFree_iff_exists_cover_isFiniteFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteFree (ℱ.over (X i)) := by
  constructor
  · intro h
    -- Proof comment: directly collect the finite free charts from the definition of finite local
    -- freeness.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ SheafOfModules.IsFiniteFree (ℱ.over U))
      (fun U ↦ h.isFiniteFree_over U)
  · rintro ⟨I, X, hX, hfree⟩
    refine ⟨fun U ↦ ?_⟩
    refine ⟨Sigma fun i : I ↦ X i ⟶ U, fun p ↦ Over.mk p.2,
      inducedOverCoverOfCoversTop (J := J) X hX U, fun p ↦ ?_⟩
    -- Proof comment: every induced slice chart is definitionally the corresponding cover member.
    simpa [SheafOfModules.over] using hfree p.1

-- Proof sketch: local generators remain local generators after restricting to any over-site, and
-- conversely a cover by restrictions which are locally generated by sections already exhibits the
-- required local generator data for `ℱ`.
/-- Lemma 18.23.3 (5): `\mathcal F` is locally generated by sections if and only if there is a
covering of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is
locally generated by sections. -/
theorem isLocallyGeneratedBySections_iff_exists_cover_isLocallyGeneratedBySections_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyGeneratedBySections ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyGeneratedBySections M := by
  constructor
  · intro h
    -- Proof comment: unpack the local generator data on each slice and turn every chosen chart
    -- generator family into a locally-generated restriction.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsLocallyGeneratedBySections (ℱ.over U))
      (fun U ↦ by
        rcases h.1 U with ⟨σ⟩
        exact ⟨σ.I, σ.X, σ.coversTop, fun i ↦
          isLocallyGeneratedBySections_of_generatingSections
            (J := J.over U) (𝒪 := 𝒪.over U) (σ.generators i)⟩)
  · rintro ⟨I, X, hX, hloc⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    have hσ :
        ∀ p : Sigma fun i : I => X i ⟶ U,
          Nonempty (((ℱ.over U).over (Y p)).LocalGeneratorsData) := by
      intro p
      -- Proof comment: specialize the chartwise ringed-site witness at the identity object of the
      -- chart slice and normalize the resulting iterated restriction.
      simpa [Y, SheafOfModules.over] using
        (hloc p.1).1 (Over.mk (𝟙 (X p.1)))
    classical
    let σ : ∀ p : Sigma fun i : I => X i ⟶ U, ((ℱ.over U).over (Y p)).LocalGeneratorsData :=
      fun p ↦ Classical.choice (hσ p)
    -- Proof comment: gluing the local generator data on the induced slice cover produces the
    -- required local generator package on `ℱ.over U`.
    exact ⟨localGeneratorsDataOfCoversTop (J := J) (𝒪 := 𝒪) Y hY σ⟩

-- Proof sketch: if `ℱ` is locally generated by sections, refine the local-generator cover to one
-- where the restrictions are globally generated. Conversely, global generators on a covering
-- family give local generators by definition.
/-- Lemma 18.23.3 (6): `\mathcal F` is locally generated by sections if and only if there is a
covering of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is
globally generated by sections. -/
theorem isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyGeneratedBySections ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty (ℱ.over (X i)).GeneratingSections := by
  constructor
  · intro h
    -- Proof comment: the chosen local generator package on each slice already provides globally
    -- generating sections on every member of its covering family.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ Nonempty (ℱ.over U).GeneratingSections)
      (fun U ↦ by
        rcases h.1 U with ⟨σ⟩
        exact ⟨σ.I, σ.X, σ.coversTop, σ.generators⟩)
  · rintro ⟨I, X, hX, hgen⟩
    -- Proof comment: global generators on each chart are, in particular, local generators there,
    -- so the previous clause applies directly.
    exact (isLocallyGeneratedBySections_iff_exists_cover_isLocallyGeneratedBySections_over
      (J := J) (𝒪 := 𝒪) ℱ).2
      ⟨I, X, hX, fun i ↦
        isLocallyGeneratedBySections_of_generatingSections
          (J := J.over (X i)) (𝒪 := 𝒪.over (X i)) (hgen i)⟩

-- Proof sketch: local generation by `r` sections is preserved by restriction, and a cover by
-- restrictions which are locally generated by `r` sections is exactly the local data demanded by
-- the definition.
/-- Lemma 18.23.3 (7): for a fixed `r : ℕ`, `\mathcal F` is locally generated by `r` sections if
and only if there is a covering of the terminal object such that each restriction
`\mathcal F|_{\mathcal C / X_i}` is locally generated by `r` sections. -/
theorem isLocallyGeneratedBy_iff_exists_cover_isLocallyGeneratedBy_over
    (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) :
    IsLocallyGeneratedBy ℱ r ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyGeneratedBy M r := by
  constructor
  · intro h
    -- Proof comment: the local `r`-generator covers in the definition already provide the desired
    -- chartwise ringed-site property after repackaging.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsLocallyGeneratedBy (ℱ.over U) r)
      (fun U ↦ by
        obtain ⟨I, X, hX, hgen⟩ := h.isGeneratedBy_over U
        exact ⟨I, X, hX, fun i ↦
          isLocallyGeneratedBy_of_isGeneratedBy
            (J := J.over U) (𝒪 := 𝒪.over U) (r := r) (hgen i)⟩)
  · rintro ⟨I, X, hX, hloc⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    classical
    choose K Z hZ hgen using
      fun p : Sigma fun i : I => X i ⟶ U ↦
        (hloc p.1).isGeneratedBy_over (Over.mk (𝟙 (X p.1)))
    refine ⟨Sigma K, fun a ↦ Over.mk ((Z a.1 a.2).hom ≫ a.1.2),
      coversTopSigmaComp (J := J) (U := U) hY hZ, fun a ↦ ?_⟩
    -- Proof comment: after composing the two-stage cover, each resulting chart is one of the
    -- chartwise `r`-generator witnesses coming from the localized hypothesis.
    simpa [SheafOfModules.over] using hgen a.1 a.2

-- Proof sketch: a local surjection `\mathcal O_U^{\oplus r} \to \mathcal F|_U` on a further
-- cover yields global generation by `r` sections on each member of that cover, and the converse
-- is immediate from the definition of local generation by `r` sections.
/-- Lemma 18.23.3 (8): for a fixed `r : ℕ`, `\mathcal F` is locally generated by `r` sections if
and only if there is a covering of the terminal object such that each restriction
`\mathcal F|_{\mathcal C / X_i}` is globally generated by `r` sections. -/
theorem isLocallyGeneratedBy_iff_exists_cover_isGloballyGeneratedBy_over
    (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) :
    IsLocallyGeneratedBy ℱ r ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsGeneratedBy (ℱ.over (X i)) r := by
  constructor
  · intro h
    -- Proof comment: the defining local `r`-generator cover of each slice already exhibits chart
    -- restrictions that are globally generated by `r` sections.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ SheafOfModules.IsGeneratedBy (ℱ.over U) r)
      (fun U ↦ h.isGeneratedBy_over U)
  · rintro ⟨I, X, hX, hgen⟩
    -- Proof comment: each globally generated chart is automatically locally generated by `r`
    -- sections, so the previous clause reduces the backward direction to that case.
    exact (isLocallyGeneratedBy_iff_exists_cover_isLocallyGeneratedBy_over
      (J := J) (𝒪 := 𝒪) ℱ r).2
      ⟨I, X, hX, fun i ↦
        isLocallyGeneratedBy_of_isGeneratedBy
          (J := J.over (X i)) (𝒪 := 𝒪.over (X i)) (r := r) (hgen i)⟩

-- Proof sketch: finite type is defined by finite local generator data, so restricting a witness
-- keeps finite type on each over-site; conversely, a covering by finite type restrictions is the
-- local criterion for finite type.
/-- Lemma 18.23.3 (9): `\mathcal F` is of finite type if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is of finite type. -/
theorem isFiniteType_iff_exists_cover_isFiniteType_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteType ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFiniteType M := by
  constructor
  · intro h
    -- Proof comment: finite type is already a ringed-site owner property on every restriction, so
    -- the identity chart on each slice is enough for the forward direction.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsFiniteType (ℱ.over U))
      (fun U ↦ ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identitySingletonCoversTopOver (J := J) U,
        fun _ ↦ isFiniteType_over_of_isFiniteType (J := J) (𝒪 := 𝒪) h U⟩)
  · rintro ⟨I, X, hX, hft⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    -- Proof comment: pull back the ambient cover to `U`, normalize each chartwise finite-type
    -- witness to the fixed-site shape, and glue them on the slice.
    exact isFiniteTypeOfCoversTopFiniteTypeRestrictions (J := J) (𝒪 := 𝒪) Y hY
      (fun p ↦ by
        simpa [Y, SheafOfModules.over] using
          (hft p.1).1 (Over.mk (𝟙 (X p.1))))

-- Proof sketch: finite type means locally generated by finitely many sections, and after choosing
-- a rank on each local piece one obtains the stated owner-level cover; conversely such a cover
-- directly implies finite type.
/-- Lemma 18.23.3 (10): `\mathcal F` is of finite type if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is globally generated
by finitely many sections. -/
theorem isFiniteType_iff_exists_cover_isFiniteGloballyGenerated_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteType ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteGloballyGenerated (ℱ.over (X i)) := by
  constructor
  · intro h
    -- Proof comment: choose finite local-generator data on each slice and read each finite chart
    -- package as finite global generation on that chart.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ SheafOfModules.IsFiniteGloballyGenerated (ℱ.over U))
      (fun U ↦ by
        obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (ℱ.over U)
        refine ⟨σ.I, σ.X, σ.coversTop, fun i ↦ ?_⟩
        exact (SheafOfModules.isFiniteGloballyGenerated_iff_nonempty_finiteGeneratingSections
          (𝒪 := ringSheaf (J.over U) (𝒪.over U)) ((ℱ.over U).over (σ.X i))).2
          ⟨⟨σ.generators i, (hσ.1 i)⟩⟩)
  · rintro ⟨I, X, hX, hgen⟩
    -- Proof comment: finite global generation on each chart implies finite type there, so the
    -- previous finite-type criterion closes the backward direction.
    exact (isFiniteType_iff_exists_cover_isFiniteType_over (J := J) (𝒪 := 𝒪) ℱ).2
      ⟨I, X, hX, fun i ↦
        isFiniteType_of_finiteGloballyGenerated
          (J := J.over (X i)) (𝒪 := 𝒪.over (X i)) (hgen i)⟩

-- Proof sketch: quasi-coherent data restricts to quasi-coherent data on every over-site, while a
-- cover by quasi-coherent restrictions is precisely the local criterion built into the definition
-- of quasi-coherence.
/-- Lemma 18.23.3 (11): `\mathcal F` is quasi-coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is quasi-coherent. -/
theorem isQuasicoherent_iff_exists_cover_isQuasicoherent_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsQuasicoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsQuasicoherent M := by
  constructor
  · intro h
    -- Proof comment: quasi-coherence is already a ringed-site owner on every slice, so the
    -- singleton identity cover suffices in the forward direction.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsQuasicoherent (ℱ.over U))
      (fun U ↦ ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identitySingletonCoversTopOver (J := J) U,
        fun _ ↦ isQuasicoherent_over_of_isQuasicoherent (J := J) (𝒪 := 𝒪) h U⟩)
  · rintro ⟨I, X, hX, hq⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    -- Proof comment: after pulling back the ambient cover to the slice over `U`, the chartwise
    -- ringed-site hypotheses normalize to fixed-site quasi-coherence and can be glued directly.
    exact isQuasicoherentOfCoversTopQuasicoherentRestrictions (J := J) (𝒪 := 𝒪) Y hY
      (fun p ↦ by
        simpa [Y, SheafOfModules.over] using
          (hq p.1).1 (Over.mk (𝟙 (X p.1))))

-- Proof sketch: by choosing local presentations for a quasi-coherent sheaf and refining along the
-- site axioms, one gets a cover on which each restriction has a global presentation; conversely,
-- these global presentations are exactly the local presentation data needed for quasi-coherence.
/-- Lemma 18.23.3 (12): `\mathcal F` is quasi-coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` has a global
presentation. -/
theorem isQuasicoherent_iff_exists_cover_hasGlobalPresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsQuasicoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty (ℱ.over (X i)).Presentation := by
  constructor
  · intro h
    classical
    -- Proof comment: choose one quasi-coherent datum on each slice and read its local
    -- presentations as the desired chartwise global presentations.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ Nonempty (ℱ.over U).Presentation)
      (fun U ↦ by
        let q : (ℱ.over U).QuasicoherentData :=
          Classical.choice (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
            (M := ℱ.over U))
        exact ⟨q.I, q.X, q.coversTop, fun i ↦ ⟨q.presentation i⟩⟩)
  · rintro ⟨I, X, hX, hP⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    -- Proof comment: chartwise global presentations on the pulled-back cover are exactly the data
    -- glued by the presentation-based quasi-coherence helper.
    exact isQuasicoherentOfCoversTopPresentations (J := J) (𝒪 := 𝒪) Y hY
      (fun p ↦ by
        simpa [Y, SheafOfModules.over] using hP p.1)

-- Proof sketch: finite presentation on a ringed site is defined by finite local presentations, so
-- it is preserved by restriction and detected on a covering family of the terminal object.
/-- Lemma 18.23.3 (13): `\mathcal F` is of finite presentation if and only if there is a covering
of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is of finite
presentation. -/
theorem isFinitePresentation_iff_exists_cover_isFinitePresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFinitePresentation ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFinitePresentation M := by
  constructor
  · intro h
    -- Proof comment: finite presentation is already a ringed-site owner on each restriction, so
    -- the identity chart on each slice is enough for the forward direction.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsFinitePresentation (ℱ.over U))
      (fun U ↦ ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identitySingletonCoversTopOver (J := J) U,
        fun _ ↦ isFinitePresentation_over_of_isFinitePresentation (J := J) (𝒪 := 𝒪) h U⟩)
  · rintro ⟨I, X, hX, hfp⟩
    refine ⟨fun U ↦ ?_⟩
    let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
    have hY : (J.over U).CoversTop Y :=
      inducedOverCoverOfCoversTop (J := J) X hX U
    -- Proof comment: once the ambient cover is pulled back to `U`, the fixed-site finite
    -- presentation gluing helper applies chartwise after terminal-slice normalization.
    exact isFinitePresentationOfCoversTopFinitePresentations (J := J) (𝒪 := 𝒪) Y hY
      (fun p ↦ by
        simpa [Y, SheafOfModules.over] using
          (hfp p.1).1 (Over.mk (𝟙 (X p.1))))

-- Proof sketch: finite local presentations refine to a cover by restrictions with finite
-- presentations, and such a cover is exactly the local datum appearing in the definition of finite
-- presentation.
/-- Lemma 18.23.3 (14): `\mathcal F` is of finite presentation if and only if there is a covering
of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` has a finite
global presentation. -/
theorem isFinitePresentation_iff_exists_cover_finitePresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFinitePresentation ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty {P : (ℱ.over (X i)).Presentation // P.IsFinite} := by
  constructor
  · intro h
    classical
    -- Proof comment: choose finite-presentation local data on each slice and keep the explicit
    -- finite presentation carried by every chart of that datum.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ Nonempty {P : (ℱ.over U).Presentation // P.IsFinite})
      (fun U ↦ by
        let q : (ℱ.over U).QuasicoherentData :=
          (SheafOfModules.IsFinitePresentation.exists_quasicoherentData (ℱ.over U)).choose
        let hq : q.IsFinitePresentation :=
          (SheafOfModules.IsFinitePresentation.exists_quasicoherentData (ℱ.over U)).choose_spec
        exact ⟨q.I, q.X, q.coversTop, fun i ↦ ⟨⟨q.presentation i, hq.isFinite_presentation i⟩⟩⟩)
  · rintro ⟨I, X, hX, hP⟩
    -- Proof comment: every finite presentation witness upgrades to finite presentation on that
    -- chart, so the previous clause closes the backward direction.
    exact (isFinitePresentation_iff_exists_cover_isFinitePresentation_over
      (J := J) (𝒪 := 𝒪) ℱ).2
      ⟨I, X, hX, fun i ↦
        isFinitePresentation_of_finitePresentationWitness
          (J := J.over (X i)) (𝒪 := 𝒪.over (X i)) (hP i)⟩

-- Proof sketch: coherence is local on the base in the sense of the source lemma, so restricting a
-- coherent sheaf along a cover keeps coherence; conversely, coherence on a covering family
-- supplies the local criterion for the original sheaf.
/-- Lemma 18.23.3 (15): `\mathcal F` is coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is coherent. -/
theorem isCoherent_iff_exists_cover_isCoherent_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsCoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsCoherent M := by
  constructor
  · intro h
    -- Proof comment: coherence is itself stable under restriction, so the identity chart on each
    -- slice gives the forward cover criterion.
    exact coversTopOfSigmaCharts (J := J)
      (P := fun U ↦ IsCoherent (ℱ.over U))
      (fun U ↦ ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identitySingletonCoversTopOver (J := J) U,
        fun _ ↦ isCoherent_over_of_isCoherent (J := J) (𝒪 := 𝒪) h U⟩)
  · rintro ⟨I, X, hX, hcoh⟩
    refine ⟨?_, ?_⟩
    · refine ⟨fun U ↦ ?_⟩
      let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
      have hY : (J.over U).CoversTop Y :=
        inducedOverCoverOfCoversTop (J := J) X hX U
      -- Proof comment: pull back the coherent cover to the slice over `U`, upgrade the pulled-back
      -- charts to coherent restrictions, and then forget to finite type.
      exact (isCoherentOfCoversTopCoherentRestrictions (J := J) (𝒪 := 𝒪) Y hY
        (fun p ↦ isCoherent_over_inducedCoverChart
          (J := J) (𝒪 := 𝒪) (ℱ := ℱ) (X := X) hcoh (U := U) p)).toIsFiniteType
    · intro U r φ
      let Y : Sigma fun i : I => X i ⟶ U → Over U := fun p ↦ Over.mk p.2
      have hY : (J.over U).CoversTop Y :=
        inducedOverCoverOfCoversTop (J := J) X hX U
      let hcohU : IsCoherent (ℱ.over U) :=
        isCoherentOfCoversTopCoherentRestrictions (J := J) (𝒪 := 𝒪) Y hY
          (fun p ↦ isCoherent_over_inducedCoverChart
            (J := J) (𝒪 := 𝒪) (ℱ := ℱ) (X := X) hcoh (U := U) p)
      -- Proof comment: once `ℱ.over U` is coherent by the fixed-site helper, its kernel condition
      -- specialized at the identity chart is exactly the required kernel statement for `φ`.
      simpa [SheafOfModules.over] using
        hcohU.isFiniteType_kernel (Over.mk (𝟙 U)) r φ

end SheafOfModules.RingedSite
