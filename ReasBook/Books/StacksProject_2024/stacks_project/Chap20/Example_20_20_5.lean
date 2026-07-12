import StacksProject_2024.Chap06.Definition_6_30_2
import StacksProject_2024.Chap06.Extension_by_zero_by_the_initial_object
import StacksProject_2024.Chap20.Lemma_20_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Set TopCat TopologicalSpace Topology
open CategoryTheory.Sheaf (Γ ΓRes)
open Topology.WithLowerSet Topology.IsLowerSet

noncomputable section

local notation "X" => TopCat.of (WithLowerSet ℕ+)
local notation "AbSheaf" => TopCat.Sheaf AddCommGrpCat X

/- Domain-style sampling for Example 20.20.5:
- primary domain: sheaves on an Alexandrov lower-set chain and their restriction inverse systems;
- sampled canonical declarations in this domain:
  `WithLowerSet`,
  `TopCat.of`,
  `Sheaf.ΓRes`,
  `Functor.IsEquivalence`;
- best owner abstraction: the canonical lower-set space `X` together with the restriction functor
  `countableInitialSegmentSheafToInverseSystem : AbSheaf ⥤ (ℕ+)ᵒᵖ ⥤ AddCommGrpCat`;
- primitive-vs-derived split: the source-facing primitive data are the opens `U_n`; the compact
  open packaging, restriction morphisms, inverse system, and global-sections cone are derived API.

Layer triage:
- `source-facing`: the opens `U_n`, the classification of opens, and the cohomology statements;
- `core/canonical`: `X`, the lower-set topology API, and the functor-equivalence owner
  `Functor.IsEquivalence`;
- `bridge/view`: `countableInitialSegmentOpen`, `countableInitialSegmentCompactOpen`, and the
  inverse-system functor built from a sheaf by restricting to the chain `U_n`, together with the
  canonical cone from global sections to that inverse system.
-/

/-- The basic open subset `U_n = { i | i ≤ n }` in the countable initial-segment topology. -/
@[reducible] def countableInitialSegmentBasicOpen (n : ℕ+) :
    Set X :=
  Set.Iic (toLowerSet n)

-- Proof sketch: `U_n = Iic (toLowerSet n)` is a lower set, hence open in the canonical
-- Alexandrov lower-set topology on `WithLowerSet ℕ+`.
/-- Each finite initial segment `U_n` is open in the topology of Example 20.20.5. -/
theorem countableInitialSegmentBasicOpen_isOpen (n : ℕ+) :
    IsOpen (countableInitialSegmentBasicOpen n) := by
  simpa [countableInitialSegmentBasicOpen] using
    (isOpen_iff_isLowerSet.2 (isLowerSet_Iic (toLowerSet n)))

private theorem countableInitialSegmentBasicOpen_isCompact (n : ℕ+) :
    IsCompact (countableInitialSegmentBasicOpen n) := by
  have hfinite : Finite (countableInitialSegmentBasicOpen n) := by
    simpa [countableInitialSegmentBasicOpen, ofLowerSetOrderIso.preimage_Iic] using
      (Set.finite_Iic n).preimage_embedding ofLowerSetOrderIso.toEquiv.toEmbedding
  exact Set.Finite.isCompact hfinite

/-- The basic open `U_n` as an object of `Opens X` for the space of Example 20.20.5. -/
@[reducible] def countableInitialSegmentOpen (n : ℕ+) :
    Opens X :=
  ⟨countableInitialSegmentBasicOpen n, countableInitialSegmentBasicOpen_isOpen n⟩

/-- The basic open `U_n` as a compact open of the space from Example 20.20.5. -/
def countableInitialSegmentCompactOpen (n : ℕ+) :
    CompactOpens X :=
  ⟨⟨countableInitialSegmentBasicOpen n, countableInitialSegmentBasicOpen_isCompact n⟩,
    countableInitialSegmentBasicOpen_isOpen n⟩

-- Proof sketch: if `m ≤ n`, then every point with index at most `m` also has index at most `n`,
-- so `U_m ⊆ U_n`.
/-- The basic opens are nested in the same order as their indices. -/
theorem countableInitialSegmentOpen_mono {m n : ℕ+} (h : m ≤ n) :
    countableInitialSegmentOpen m ≤ countableInitialSegmentOpen n := by
  intro x hx
  exact le_trans hx (by simpa using h)

private theorem countableInitialSegmentBasicOpen_isTopologicalBasis :
    IsTopologicalBasis (Set.range countableInitialSegmentBasicOpen) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (fun U hU ↦ by
      rcases hU with ⟨n, rfl⟩
      exact countableInitialSegmentBasicOpen_isOpen n)
    ?_
  intro x U hxU hU
  refine ⟨countableInitialSegmentBasicOpen (ofLowerSet x), ?_, ?_, ?_⟩
  · exact ⟨ofLowerSet x, rfl⟩
  · change x ≤ x
    simp
  · intro y hy
    exact (isOpen_iff_isLowerSet.mp hU) hy hxU

private theorem countableInitialSegmentOpen_isBasis :
    Opens.IsBasis (Set.range countableInitialSegmentOpen) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  refine ⟨countableInitialSegmentOpen (ofLowerSet x), ?_, ?_, ?_⟩
  · exact ⟨ofLowerSet x, rfl⟩
  · change x ≤ x
    simp
  · intro y hy
    exact (isOpen_iff_isLowerSet.mp U.2) hy hx

private theorem countableInitialSegmentOpen_injective :
    Function.Injective countableInitialSegmentOpen := by
  intro m n hmn
  apply le_antisymm
  · have hm : toLowerSet m ∈ (countableInitialSegmentOpen m : Set X) := by
      change toLowerSet m ≤ toLowerSet m
      simp
    have hm' : toLowerSet m ∈ (countableInitialSegmentOpen n : Set X) := by
      simpa [hmn] using hm
    simpa [countableInitialSegmentOpen, countableInitialSegmentBasicOpen] using hm'
  · have hn : toLowerSet n ∈ (countableInitialSegmentOpen n : Set X) := by
      change toLowerSet n ≤ toLowerSet n
      simp
    have hn' : toLowerSet n ∈ (countableInitialSegmentOpen m : Set X) := by
      simpa [hmn] using hn
    simpa [countableInitialSegmentOpen, countableInitialSegmentBasicOpen] using hn'

private abbrev countableInitialSegmentBasis : Set (Opens X) :=
  Set.range countableInitialSegmentOpen

private noncomputable def countableInitialSegmentBasisIndex
    (U : BasisOpen countableInitialSegmentBasis) : ℕ+ :=
  Classical.choose U.2

private theorem countableInitialSegmentBasisIndex_spec
    (U : BasisOpen countableInitialSegmentBasis) :
    countableInitialSegmentOpen (countableInitialSegmentBasisIndex U) = U.obj :=
  Classical.choose_spec U.2

private noncomputable def countableInitialSegmentBasisToPNat :
    BasisOpen countableInitialSegmentBasis ⥤ ℕ+ where
  obj U := countableInitialSegmentBasisIndex U
  map {U V} f :=
    homOfLE <| by
      have hx : toLowerSet (countableInitialSegmentBasisIndex U) ∈ (U.obj : Set X) := by
        rw [← countableInitialSegmentBasisIndex_spec U]
        change toLowerSet (countableInitialSegmentBasisIndex U) ≤
          toLowerSet (countableInitialSegmentBasisIndex U)
        exact le_rfl
      have hx' : toLowerSet (countableInitialSegmentBasisIndex U) ∈ (V.obj : Set X) :=
        (leOfHom f.hom) hx
      rw [← countableInitialSegmentBasisIndex_spec V] at hx'
      simpa [countableInitialSegmentOpen, countableInitialSegmentBasicOpen] using hx'

private abbrev pnatToCountableInitialSegmentBasis :
    ℕ+ ⥤ BasisOpen countableInitialSegmentBasis where
  obj n := ⟨countableInitialSegmentOpen n, ⟨n, rfl⟩⟩
  map f := ObjectProperty.homMk (homOfLE (countableInitialSegmentOpen_mono (leOfHom f)))

private noncomputable def countableInitialSegmentBasisEquiv :
    BasisOpen countableInitialSegmentBasis ≌ ℕ+ where
  functor := countableInitialSegmentBasisToPNat
  inverse := pnatToCountableInitialSegmentBasis
  unitIso := NatIso.ofComponents
    (fun U ↦ eqToIso <| by
      ext x
      change x ∈ (U.obj : Set X) ↔
        x ∈ (countableInitialSegmentOpen (countableInitialSegmentBasisIndex U) : Set X)
      rw [countableInitialSegmentBasisIndex_spec U])
    fun {_ _} _ ↦ by
      subsingleton
  counitIso := NatIso.ofComponents
    (fun n ↦ eqToIso <| by
      apply countableInitialSegmentOpen_injective
      exact
        countableInitialSegmentBasisIndex_spec
          (pnatToCountableInitialSegmentBasis.obj n))
    fun {_ _} _ ↦ by
      subsingleton

private theorem countableInitialSegmentOpen_le_of_mem
    {n : ℕ+} {U : Opens X}
    (hU : IsOpen (U : Set X)) (hx : toLowerSet n ∈ (U : Set X)) :
    countableInitialSegmentOpen n ≤ U := by
  intro y hy
  exact (isOpen_iff_isLowerSet.mp hU) hy hx

private theorem countableInitialSegmentBasisCover_exists_self
    {U : BasisOpen countableInitialSegmentBasis}
    (𝒰 : BasisCover countableInitialSegmentBasis U) :
    ∃ i : 𝒰.ι, 𝒰.obj i = U := by
  let n := countableInitialSegmentBasisToPNat.obj U
  have hxU : toLowerSet n ∈ (U.obj : Set X) := by
    rw [← countableInitialSegmentBasisIndex_spec U]
    change toLowerSet n ≤ toLowerSet n
    exact le_rfl
  rw [𝒰.iUnion_eq] at hxU
  rcases Set.mem_iUnion.mp hxU with ⟨i, hxi⟩
  refine ⟨i, ?_⟩
  ext x
  constructor
  · intro hx
    exact (leOfHom (𝒰.hom i).hom) hx
  · intro hx
    have hle : countableInitialSegmentOpen n ≤ (𝒰.obj i).obj :=
      countableInitialSegmentOpen_le_of_mem (𝒰.obj i).obj.2 hxi
    have hx' := hx
    dsimp [n] at hx'
    rw [← countableInitialSegmentBasisIndex_spec U] at hx'
    exact hle hx'

private instance countableInitialSegmentBasisInclusion_isCoverDense :
    (basisOpenInclusion countableInitialSegmentBasis).IsCoverDense
      (Opens.grothendieckTopology X) :=
  basisOpenInclusion_isCoverDense countableInitialSegmentOpen_isBasis

private instance countableInitialSegmentBasisInclusion_isContinuous :
    Functor.IsContinuous (basisOpenInclusion countableInitialSegmentBasis)
      (basisGrothendieckTopology countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis)
      (Opens.grothendieckTopology X) :=
  Functor.IsCoverDense.isContinuous
    (basisGrothendieckTopology countableInitialSegmentBasis
      countableInitialSegmentOpen_isBasis)
    (Opens.grothendieckTopology X)
    (basisOpenInclusion countableInitialSegmentBasis)
    (Functor.inducedTopology_coverPreserving
      (basisOpenInclusion countableInitialSegmentBasis)
      (Opens.grothendieckTopology X))

private def countableInitialSegmentBasisCoverOfSieve
    {U : BasisOpen countableInitialSegmentBasis} (S : Sieve U)
    (hS :
      S ∈ basisGrothendieckTopology countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis U) :
    BasisCover countableInitialSegmentBasis U where
  family := {
    I := Σ V : BasisOpen countableInitialSegmentBasis, { f : V ⟶ U // S f }
    obj := fun a ↦ Over.mk a.2.1 }
  iUnion_eq := by
    ext x
    constructor
    · intro hx
      have hS' :
          S ∈ (basisOpenInclusion countableInitialSegmentBasis).inducedTopology
            (Opens.grothendieckTopology X) U := by
        simpa [basisGrothendieckTopology] using hS
      have hPush :
          S.functorPushforward (basisOpenInclusion countableInitialSegmentBasis) ∈
            Opens.grothendieckTopology X U.obj := by
        rwa [Functor.mem_inducedTopology_sieves_iff] at hS'
      obtain ⟨W, g, hg, hxW⟩ := hPush x hx
      obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVW⟩ :=
        countableInitialSegmentOpen_isBasis.exists_subset_of_mem_open hxW W.2
      let VB : BasisOpen countableInitialSegmentBasis := ⟨V, hVB⟩
      let f : VB ⟶ U := ⟨homOfLE (le_trans hVW (leOfHom g))⟩
      have hVPush :
          (S.functorPushforward (basisOpenInclusion countableInitialSegmentBasis))
            ((basisOpenInclusion countableInitialSegmentBasis).map f) := by
        simpa [f] using
          (S.functorPushforward (basisOpenInclusion countableInitialSegmentBasis)).downward_closed
            hg (homOfLE hVW)
      have hf : S f := by
        change
          (S.arrows.functorPushforward (basisOpenInclusion countableInitialSegmentBasis))
            ((basisOpenInclusion countableInitialSegmentBasis).map f) at hVPush
        rwa [Sieve.mem_functorPushforward_iff_of_full_of_faithful] at hVPush
      exact Set.mem_iUnion.mpr ⟨⟨VB, ⟨f, hf⟩⟩, hxV⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
      exact (leOfHom a.2.1.hom) hx

private theorem countableInitialSegmentBasisGrothendieckTopology_eq_trivial :
    basisGrothendieckTopology countableInitialSegmentBasis countableInitialSegmentOpen_isBasis =
      GrothendieckTopology.trivial (BasisOpen countableInitialSegmentBasis) := by
  apply le_antisymm
  · intro U S hS
    let 𝒰 := countableInitialSegmentBasisCoverOfSieve S hS
    obtain ⟨i, hi⟩ := countableInitialSegmentBasisCover_exists_self 𝒰
    have hSi : S (𝒰.hom i) := by
      simpa [𝒰, BasisCover.hom, BasisCover.obj] using i.2.2
    have hId : S (𝟙 U) := by
      have hEq : 𝒰.hom i = eqToHom hi := by
        ext
        apply Subsingleton.elim
      have hDown : S (eqToHom hi.symm ≫ 𝒰.hom i) :=
        S.downward_closed hSi (eqToHom hi.symm)
      have hComp : eqToHom hi.symm ≫ 𝒰.hom i = 𝟙 U := by
        rw [hEq]
        rfl
      rw [hComp] at hDown
      exact hDown
    change S = ⊤
    ext V f
    constructor
    · intro _
      trivial
    · intro _
      exact S.downward_closed hId f
  · intro U S hS
    change S = ⊤ at hS
    rw [hS]
    exact
      (basisGrothendieckTopology countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis).top_mem U

private noncomputable abbrev countableInitialSegmentBasisRestriction :
    AbSheaf ⥤
      BasisSiteSheaf AddCommGrpCat countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis := by
  exact
    (basisOpenInclusion countableInitialSegmentBasis).sheafPushforwardContinuous
      AddCommGrpCat
      (basisGrothendieckTopology countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis)
      (Opens.grothendieckTopology X)

private instance countableInitialSegmentBasisRestriction_isEquivalence :
    Functor.IsEquivalence countableInitialSegmentBasisRestriction := by
  simpa [countableInitialSegmentBasisRestriction] using inferInstanceAs
    (((basisOpenInclusion countableInitialSegmentBasis).sheafPushforwardContinuous
      AddCommGrpCat
      (basisGrothendieckTopology countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis)
      (Opens.grothendieckTopology X)).IsEquivalence)

private noncomputable abbrev countableInitialSegmentBasisSiteToInverseSystem :
    BasisSiteSheaf AddCommGrpCat countableInitialSegmentBasis
        countableInitialSegmentOpen_isBasis ⥤
      ((ℕ+)ᵒᵖ ⥤ AddCommGrpCat) := by
  let eSheaf :
      BasisSiteSheaf AddCommGrpCat countableInitialSegmentBasis
          countableInitialSegmentOpen_isBasis ≌
        ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat) := by
    change
      Sheaf
          (basisGrothendieckTopology countableInitialSegmentBasis
            countableInitialSegmentOpen_isBasis)
          AddCommGrpCat ≌
        ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat)
    rw [countableInitialSegmentBasisGrothendieckTopology_eq_trivial,
      GrothendieckTopology.trivial_eq_bot]
    exact CategoryTheory.sheafBotEquivalence AddCommGrpCat
  let ePresheaf :
      ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat) ≌
        ((ℕ+)ᵒᵖ ⥤ AddCommGrpCat) := by
    exact (countableInitialSegmentBasisEquiv.op).congrLeft
  exact eSheaf.functor ⋙ ePresheaf.functor

private instance countableInitialSegmentBasisSiteToInverseSystem_isEquivalence :
    Functor.IsEquivalence countableInitialSegmentBasisSiteToInverseSystem := by
  let eSheaf :
      BasisSiteSheaf AddCommGrpCat countableInitialSegmentBasis
          countableInitialSegmentOpen_isBasis ≌
        ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat) := by
    change
      Sheaf
          (basisGrothendieckTopology countableInitialSegmentBasis
            countableInitialSegmentOpen_isBasis)
          AddCommGrpCat ≌
        ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat)
    rw [countableInitialSegmentBasisGrothendieckTopology_eq_trivial,
      GrothendieckTopology.trivial_eq_bot]
    exact CategoryTheory.sheafBotEquivalence AddCommGrpCat
  let ePresheaf :
      ((BasisOpen countableInitialSegmentBasis)ᵒᵖ ⥤ AddCommGrpCat) ≌
        ((ℕ+)ᵒᵖ ⥤ AddCommGrpCat) := by
    exact (countableInitialSegmentBasisEquiv.op).congrLeft
  simpa [countableInitialSegmentBasisSiteToInverseSystem] using inferInstanceAs
    (Functor.IsEquivalence (eSheaf.functor ⋙ ePresheaf.functor))

instance countableInitialSegmentSpace_prespectral : PrespectralSpace X :=
  PrespectralSpace.of_isTopologicalBasis'
    countableInitialSegmentBasicOpen_isTopologicalBasis
    countableInitialSegmentBasicOpen_isCompact

instance countableInitialSegmentSpace_quasiSeparated :
    QuasiSeparatedSpace X :=
  QuasiSeparatedSpace.of_isTopologicalBasis
    countableInitialSegmentBasicOpen_isTopologicalBasis
    fun m n ↦ by
      rcases le_total m n with hmn | hnm
      · have hinter :
            countableInitialSegmentBasicOpen m ∩ countableInitialSegmentBasicOpen n =
              countableInitialSegmentBasicOpen m := by
          ext x
          constructor
          · intro hx
            exact hx.1
          · intro hx
            exact ⟨hx, le_trans hx (by simpa using hmn)⟩
        simpa [hinter] using countableInitialSegmentBasicOpen_isCompact m
      · have hinter :
            countableInitialSegmentBasicOpen m ∩ countableInitialSegmentBasicOpen n =
              countableInitialSegmentBasicOpen n := by
          ext x
          constructor
          · intro hx
            exact hx.2
          · intro hx
            exact ⟨le_trans hx (by simpa using hnm), hx⟩
        simpa [hinter] using countableInitialSegmentBasicOpen_isCompact n

/-- Example 20.20.5 (2), source-facing owner: restricting an abelian sheaf on `X` to the chain of
basic opens `U_n` gives the associated inverse system `n ↦ F(U_n)`. -/
@[stacks 0BX0]
def countableInitialSegmentSheafToInverseSystem :
    AbSheaf ⥤ ((ℕ+)ᵒᵖ ⥤ AddCommGrpCat) :=
  countableInitialSegmentBasisRestriction ⋙ countableInitialSegmentBasisSiteToInverseSystem

/-- The restriction morphism `F(U_m) ⟶ F(U_n)` for `U_n ⊆ U_m`. -/
private abbrev countableInitialSegmentSectionsTransition
    (F : AbSheaf) {m n : ℕ+} (h : n ≤ m) :
    F.presheaf.obj (op (countableInitialSegmentOpen m)) ⟶
      F.presheaf.obj (op (countableInitialSegmentOpen n)) :=
  F.presheaf.map (homOfLE (countableInitialSegmentOpen_mono h)).op

-- Proof sketch: for the identity inequality `n ≤ n`, the inclusion `U_n ⊆ U_n` is the identity,
-- so the associated restriction morphism is the identity section map.
/-- Restriction to the same basic open is the identity map. -/
private theorem countableInitialSegmentSectionsTransition_id
    (F : AbSheaf) (n : ℕ+) :
    countableInitialSegmentSectionsTransition F le_rfl =
      𝟙 (F.presheaf.obj (op (countableInitialSegmentOpen n))) := sorry

-- Proof sketch: the inclusion `U_n ⊆ U_ℓ` factors through `U_m` whenever `n ≤ m ≤ ℓ`, and the
-- presheaf restriction maps compose functorially along inclusions of opens.
/-- The restriction maps along the chain of basic opens compose as expected. -/
private theorem countableInitialSegmentSectionsTransition_comp
    (F : AbSheaf)
    {ℓ m n : ℕ+} (hnm : n ≤ m) (hmℓ : m ≤ ℓ) :
    countableInitialSegmentSectionsTransition F (le_trans hnm hmℓ) =
      countableInitialSegmentSectionsTransition F hmℓ ≫
        countableInitialSegmentSectionsTransition F hnm := sorry

/-- The inverse system `n ↦ F(U_n)` attached to an abelian sheaf on the countable
initial-segment space. -/
def countableInitialSegmentSectionsInverseSystem
    (F : AbSheaf) :
    (ℕ+)ᵒᵖ ⥤ AddCommGrpCat :=
  { obj := fun n ↦ F.presheaf.obj (op (countableInitialSegmentOpen n.unop))
    map := fun f ↦ countableInitialSegmentSectionsTransition F (leOfHom f.unop)
    map_id := fun n ↦ countableInitialSegmentSectionsTransition_id F n.unop
    map_comp := fun f g ↦
      countableInitialSegmentSectionsTransition_comp F (leOfHom g.unop) (leOfHom f.unop) }

/-- The owner functor
`countableInitialSegmentSheafToInverseSystem` agrees with the explicit restriction inverse system
`n ↦ F(U_n)` for a fixed sheaf `F`. -/
theorem countableInitialSegmentSheafToInverseSystem_obj_eq_sectionsInverseSystem
    (F : AbSheaf) :
    countableInitialSegmentSheafToInverseSystem.obj F =
      countableInitialSegmentSectionsInverseSystem F := by
  sorry

-- Proof sketch: both routes around the square are the restriction from `X` to `U_n`, with the
-- left-bottom route factoring through the intermediate restriction from `X` to `U_m`; presheaf
-- functoriality identifies the resulting composites.
private theorem countableInitialSegmentGlobalSectionsCone_commSq
    (F : AbSheaf) {m n : (ℕ+)ᵒᵖ} (f : m ⟶ n) :
    CommSq
      (((Functor.const ((ℕ+)ᵒᵖ)).obj
          ((Γ (Opens.grothendieckTopology X) AddCommGrpCat).obj F)).map f)
      (ΓRes F (op (countableInitialSegmentOpen m.unop)))
      (ΓRes F (op (countableInitialSegmentOpen n.unop)))
      ((countableInitialSegmentSectionsInverseSystem F).map f) := by
  refine CommSq.mk ?_
  sorry

/-- The canonical cone from global sections `Γ(X, F)` to the inverse system `n ↦ F(U_n)`. -/
def countableInitialSegmentGlobalSectionsCone
    (F : AbSheaf) :
    Cone (countableInitialSegmentSectionsInverseSystem F) where
  pt := (Γ (Opens.grothendieckTopology X) AddCommGrpCat).obj F
  π :=
    { app := fun n ↦
        ΓRes F (op (countableInitialSegmentOpen n.unop))
      naturality := fun _ _ f ↦
        (countableInitialSegmentGlobalSectionsCone_commSq F f).w }

-- Proof sketch: the sheaf condition on the increasing cover `X = ⋃_n U_n` identifies compatible
-- families of sections on the chain with a unique global section on `X`.
private theorem countableInitialSegmentGlobalSectionsCone_hasLimit
    (F : AbSheaf) :
    Nonempty (IsLimit (countableInitialSegmentGlobalSectionsCone F)) := by
  sorry

/-- Example 20.20.5 (2), proposition-level owner form of
`Γ(X, F) ≅ lim_n F(U_n)`.

This file keeps the comparison at the source-facing `IsIsomorphic` surface rather than adding a
chosen concrete isomorphism built from an existence proof. -/
@[stacks 0BX0]
theorem countableInitialSegmentGlobalSections_isomorphic_limit
    (F : AbSheaf) :
    IsIsomorphic
      ((Γ (Opens.grothendieckTopology X) AddCommGrpCat).obj F)
      (limit (countableInitialSegmentSectionsInverseSystem F)) := by
  obtain ⟨hlimit⟩ := countableInitialSegmentGlobalSectionsCone_hasLimit F
  exact ⟨hlimit.conePointUniqueUpToIso (limit.isLimit _)⟩

section Cohomology

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

-- Proof sketch: classify the opens of the topology as `∅`, `X`, and the basic finite initial
-- segments `U_n`; arbitrary unions of basic opens are again either a basic open or all of `X`,
-- so no additional opens occur.
omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Example 20.20.5 (1): the opens of `X` are exactly `∅`, `X`, and the basic initial segments
`U_n = { i | i ≤ n }`. -/
@[stacks 0BX0]
theorem countableInitialSegmentTopology_isOpen_iff
    (s : Set X) :
    IsOpen s ↔
      s = ∅ ∨ s = Set.univ ∨ ∃ n : ℕ+, s = countableInitialSegmentBasicOpen n := sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Example 20.20.5 (2), first sentence: an abelian sheaf on `X` is the same as an inverse system
of abelian groups `A_n = F(U_n)`, expressed canonically by the restriction functor to the chain
`U_n`. -/
@[stacks 0BX0]
instance countableInitialSegmentSheafToInverseSystem_isEquivalence :
    Functor.IsEquivalence countableInitialSegmentSheafToInverseSystem := by
  simpa [countableInitialSegmentSheafToInverseSystem] using inferInstanceAs
    (Functor.IsEquivalence
      (countableInitialSegmentBasisRestriction ⋙
        countableInitialSegmentBasisSiteToInverseSystem))

-- Proof sketch: translate abelian sheaves on this topology into inverse systems of abelian
-- groups using the previous limit description, then choose a short exact sequence of inverse
-- systems whose inverse limit is not exact; the corresponding long exact cohomology sequence
-- produces a sheaf with nonzero `H^1`.
/-- Example 20.20.5 (3): there exists an abelian sheaf on `X` whose first cohomology group is
nonzero. -/
@[stacks 0BX0]
theorem exists_countableInitialSegmentAbelianSheaf_with_nontrivial_firstCohomology :
    ∃ F : AbSheaf, ¬ IsZero (F.H' 1 (⊤ : Opens X)) := sorry

-- Proof sketch: for a basic open `U_n`, the extension-by-zero sheaf
-- `j!ℤ[(countableInitialSegmentCompactOpen n).toOpens]`
-- is supported on a compact open chain segment; restriction to smaller basic opens stays in the
-- same class, so the higher global cohomology vanishes by the explicit calculation on this
-- one-dimensional inverse-system model.
/-- Example 20.20.5 (4): for the inclusion of a basic open `U_n ⊆ X`, the lower-shriek sheaf
`j!ℤ[(countableInitialSegmentCompactOpen n)]` has
vanishing higher cohomology in every positive degree. -/
@[stacks 0BX0]
theorem countableInitialSegment_extensionByZeroConstantIntegerSheaf_higherCohomology_isZero
    (n : ℕ+) (p : ℕ) (hp : 0 < p) :
    IsZero
      (((j!ℤ[(countableInitialSegmentCompactOpen n).toOpens]).H' p
        (⊤ : Opens X))) := sorry

end Cohomology

-- Proof sketch: the open sets `U_n = { i | i ≤ n }` cover `X`, but any finite subfamily has a
-- largest index `N` and therefore unions to `U_N`, which still misses every point `m > N`.
/-- Companion source-facing conclusion from Example 20.20.5: the countable initial-segment space
fails the quasi-compactness hypothesis of Lemma `20.20.4`, expressed canonically as
`¬ CompactSpace X`. -/
theorem countableInitialSegmentSpace_not_compact :
    ¬ CompactSpace X := sorry
