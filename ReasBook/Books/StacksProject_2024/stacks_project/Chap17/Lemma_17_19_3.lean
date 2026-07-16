import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_5
import StacksProject_2024.stacks_project.Chap06.Lemma_6_29_3
import StacksProject_2024.stacks_project.Chap05.Definition_5_8_6
import StacksProject_2024.stacks_project.Chap05.Lemma_5_23_14
import StacksProject_2024.stacks_project.Chap05.Lemma_5_24_5
import StacksProject_2024.stacks_project.Chap05.Lemma_5_24_6
import StacksProject_2024.stacks_project.Chap17.«17_19_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.19.3:
- primary domain: set-valued sheaves on spectral spaces, descended along spectral maps to finite
  sober spaces;
- sampled owner declarations:
  `HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation`,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`,
  `IsSpectralMap`,
  `QuasiSober`;
- best owner abstraction: the source-facing hypothesis should use the Chapter 17 owner predicate
  `HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation`, while the spectral-space input
  is governed upstream by the chapter-5 directed-limit characterization
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`; the chapter-5 owner for the sober
  conclusion is the pair `T0Space Y ∧ QuasiSober Y`, so the finite stage returned here should
  expose both pieces directly;
- primitive data: a compact-open finite lower-shriek constant coequalizer presentation of `ℱ`;
- derived API: the descended finite `T₀` space `Y`, the spectral map `f : X ⟶ Y`, the model sheaf
  `𝒢`, its finite stalk condition, and the resulting inverse-image isomorphism.

Source/core/bridge triage:
- `source-facing`: the existence of a finite sober model for a constructible sheaf presentation,
  expressed canonically as `Finite Y` together with `T0Space Y ∧ QuasiSober Y`;
- `core/canonical`: the Chapter 17 compact-open presentation owner,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`, `IsSpectralMap`, and `QuasiSober`;
- `bridge/view`: the comparison isomorphism identifying `ℱ` with the inverse image of `𝒢` along the
  spectral map `f`.
-/

section

variable {X : TopCat.{u}} [SpectralSpace X]
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

local instance (Y : TopCat.{u}) (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (TopCat.Sheaf (Type u) Y) := by
  let _ : HasColimitsOfShape (Discrete ι) (Type u) := by infer_instance
  change HasColimitsOfShape (Discrete ι)
    (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u))
  exact CategoryTheory.Sheaf.instHasColimitsOfShape

/-- Helper for Lemma 17.19.3: an irreducible subset covered by finitely many closed sets is
already contained in one member of the cover. -/
private theorem irreducible_subset_iUnion_closed_of_finset
    {Y : Type u} [TopologicalSpace Y] [Finite Y] {S : Set Y} (hS : IsIrreducible S)
    (t : Finset Y) (C : Y → Set Y) (hCclosed : ∀ y, y ∈ t → IsClosed (C y))
    (hcover : S ⊆ ⋃ y, ⋃ (_ : y ∈ t), C y) :
    ∃ y ∈ t, S ⊆ C y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      -- The empty closed cover cannot contain a nonempty irreducible set.
      exfalso
      obtain ⟨x, hx⟩ := hS.nonempty
      have hxCover : x ∈ ⋃ y, ⋃ (_ : y ∈ (∅ : Finset Y)), C y := hcover hx
      simpa using hxCover
  | @insert a t ha IH =>
      have hRestClosed : IsClosed (⋃ y, ⋃ (_ : y ∈ t), C y) := by
        -- Finite spaces are Alexandrov, so arbitrary unions of closed sets remain closed.
        letI : AlexandrovDiscrete Y := inferInstance
        exact isClosed_iUnion fun y ↦
          isClosed_iUnion fun hy ↦ hCclosed y (Finset.mem_insert_of_mem hy)
      have hcover' : S ⊆ C a ∪ ⋃ y, ⋃ (_ : y ∈ t), C y := by
        -- Split the finite cover into the distinguished closed set and the remaining union.
        intro x hx
        have hxCover : x ∈ ⋃ y, ⋃ (_ : y ∈ insert a t), C y := hcover hx
        rcases Set.mem_iUnion.mp hxCover with ⟨y, hyCover⟩
        rcases Set.mem_iUnion.mp hyCover with ⟨hy, hxC⟩
        rcases Finset.mem_insert.mp hy with rfl | hyt
        · exact Or.inl hxC
        · exact Or.inr (Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyt, hxC⟩⟩)
      rcases
          (isPreirreducible_iff_isClosed_union_isClosed.1 hS.isPreirreducible)
            (C a) (⋃ y, ⋃ (_ : y ∈ t), C y)
            (hCclosed a (Finset.mem_insert_self a t)) hRestClosed hcover' with
        hSa | hSt
      · exact ⟨a, Finset.mem_insert_self a t, hSa⟩
      · -- If the distinguished summand does not already contain `S`, recurse on the tail cover.
        obtain ⟨y, hyt, hyS⟩ := IH (fun y hy ↦ hCclosed y (Finset.mem_insert_of_mem hy)) hSt
        exact ⟨y, Finset.mem_insert_of_mem hyt, hyS⟩

/-- Helper for Lemma 17.19.3: a finite `T₀` space is quasi-sober because every irreducible closed
subset is covered by finitely many singleton closures, so one of those closures is already the
whole subset. -/
private theorem finite_t0_quasiSober
    {Y : Type u} [TopologicalSpace Y] [Finite Y] [T0Space Y] : QuasiSober Y := by
  rw [quasiSober_iff_forall_irreducibleCloseds_exists_genericPoint]
  intro Z
  classical
  let t : Finset Y := (Set.toFinite (Z : Set Y)).toFinset
  have hcover : (Z : Set Y) ⊆ ⋃ y, ⋃ (_ : y ∈ t), closure ({y} : Set Y) := by
    intro y hyZ
    have hyt : y ∈ t := (Set.toFinite (Z : Set Y)).mem_toFinset.mpr hyZ
    -- Each point of `Z` lies in the closure of its own singleton.
    refine Set.mem_iUnion.2 ⟨y, ?_⟩
    refine Set.mem_iUnion.2 ⟨hyt, ?_⟩
    exact subset_closure (by simp)
  obtain ⟨ξ, hξt, hξcover⟩ :=
    irreducible_subset_iUnion_closed_of_finset
      (S := (Z : Set Y)) Z.isIrreducible t
      (fun y ↦ closure ({y} : Set Y))
      (fun _ _ ↦ isClosed_closure) hcover
  have hξZ : ξ ∈ (Z : Set Y) := (Set.toFinite (Z : Set Y)).mem_toFinset.mp hξt
  have hclosure_subset : closure ({ξ} : Set Y) ⊆ (Z : Set Y) :=
    Z.isClosed.closure_subset_iff.2 (by simp [hξZ])
  -- The chosen point has singleton closure equal to `Z`, hence is a generic point.
  exact ⟨ξ, by
    rw [isGenericPoint_def]
    exact subset_antisymm hclosure_subset hξcover⟩

/-- Helper for Lemma 17.19.3: a homeomorphism between spectral spaces is a spectral map. -/
private theorem isSpectralMap_of_homeomorph {Y Z : TopCat.{u}} [SpectralSpace Y] [SpectralSpace Z]
    (e : Y ≃ₜ Z) : IsSpectralMap e := by
  -- A homeomorphism is continuous, and compact opens stay compact under the inverse map.
  refine ⟨e.continuous, ?_⟩
  intro s hs_open hs_comp
  simpa [e.toEquiv.image_symm_eq_preimage s] using hs_comp.image e.symm.continuous

/-- Helper for Lemma 17.19.3: every spectral space admits a spectral map to one finite sober
stage of its directed finite-space presentation. -/
private theorem exists_finite_sober_spectral_factor :
    ∃ (Y : TopCat.{u}) (_ : Finite Y) (hY : T0Space Y ∧ QuasiSober Y) (f : X ⟶ Y),
      IsSpectralMap f := by
  classical
  -- Start from the canonical inverse-limit presentation of a spectral space by finite `T₀` stages.
  obtain ⟨J, _instJ, hJne, _instDir, F, hFin, hT0, hX⟩ :=
    (spectralSpace_iff_homeomorphic_directed_limit_finite_sober (X := X)).1 inferInstance
  letI : Preorder J := _instJ
  letI : Nonempty J := hJne
  letI : IsDirectedOrder J := _instDir
  letI : ∀ j : Jᵒᵈ, SpectralSpace (F.obj j) := fun j ↦
    { toT0Space := hT0 j
      toCompactSpace := inferInstance
      toQuasiSober := finite_t0_quasiSober
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  rcases hX with ⟨eX⟩
  have hF : ∀ ⦃j k : Jᵒᵈ⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := by
    -- On finite spaces, every open inverse image is compact because the domain is noetherian.
    intro j k a
    refine ⟨(F.map a).hom.continuous, ?_⟩
    intro s hs_open hs_comp
    exact NoetherianSpace.isCompact ((F.map a) ⁻¹' s)
  letI : SpectralSpace ↥(limit F) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF
  -- Route correction: `Jᵒᵈ` here is `OrderDual J`, so stage indices are converted by
  -- `OrderDual.toDual` and `OrderDual.ofDual`, not by `Opposite.op`.
  let j : Jᵒᵈ := OrderDual.toDual (Classical.choice hJne)
  let eTop : X ≅ limit F := TopCat.isoOfHomeo eX
  let Y : TopCat.{u} := F.obj j
  let f : X ⟶ Y := eTop.hom ≫ limit.π F j
  have hY_quasiSober : QuasiSober Y := by
    exact finite_t0_quasiSober
  have hY : T0Space Y ∧ QuasiSober Y := ⟨hT0 j, hY_quasiSober⟩
  have hIso : IsSpectralMap eTop.hom := by
    -- Transport spectrality across the homeomorphism identifying `X` with the limit.
    simpa [eTop] using isSpectralMap_of_homeomorph eX
  have hProj : IsSpectralMap (limit.π F j) := by
    -- The limit projections are spectral for cofiltered spectral diagrams.
    exact isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (hC := limit.isLimit F) hF j
  have hf : IsSpectralMap f := hProj.comp hIso
  exact ⟨Y, hFin j, hY, f, hf⟩

/-- Helper for Lemma 17.19.3: an open subset with compact carrier determines a compact open. -/
private noncomputable def compact_open_of_open
    {Y : TopCat.{u}} (U : Opens Y) (hU : IsCompact (U : Set Y)) : CompactOpens Y :=
  ⟨⟨(U : Set Y), hU⟩, U.isOpen⟩

/-- Helper for Lemma 17.19.3: compact opens transport across a homeomorphism. -/
private noncomputable def compact_open_map_homeomorph
    {Y Z : TopCat.{u}} (e : Y ≃ₜ Z) (U : Opens Y) (hU : IsCompact (U : Set Y)) :
    CompactOpens Z :=
  (compact_open_of_open U hU).map e e.continuous e.isOpenMap

/-- Helper for Lemma 17.19.3: a finite family in a directed preorder admits a common upper bound.
-/
private theorem exists_upper_bound_of_finite_family
    {J σ : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J] [Finite σ]
    (s : σ → J) :
    ∃ j : J, ∀ t, s t ≤ j := by
  classical
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ₁ σ₂ e IH =>
      -- Transport the family across the finite equivalence before applying the induction
      -- hypothesis.
      obtain ⟨j, hj⟩ := IH (s ∘ e)
      exact ⟨j, e.forall_congr_right.mp hj⟩
  | h_empty =>
      -- The empty family is bounded by any chosen stage.
      exact ⟨Classical.choice ‹Nonempty J›, fun t ↦ PEmpty.elim t⟩
  | @h_option σ _ IH =>
      -- First bound the previously descended family, then dominate that bound together with the
      -- new distinguished stage.
      obtain ⟨j₀, hj₀⟩ := IH (s ∘ Option.some)
      obtain ⟨j, hnone, hj₀j⟩ := exists_ge_ge (s none) j₀
      refine ⟨j, ?_⟩
      intro t
      cases t with
      | none =>
          exact hnone
      | some t =>
          exact le_trans (hj₀ t) hj₀j

/-- Helper for Lemma 17.19.3: finitely many compact opens on the inverse limit descend to a single
common stage of the directed system. -/
private theorem exists_common_stage_for_compact_open_families
    {J ι κ : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : Jᵒᵈ ⥤ TopCat.{u}) [∀ j : Jᵒᵈ, SpectralSpace (F.obj j)]
    (hF : ∀ ⦃j k : Jᵒᵈ⦄ (a : j ⟶ k), IsSpectralMap (F.map a))
    [Finite ι] [Finite κ]
    (U : ι → CompactOpens ↥(limit F)) (V : κ → CompactOpens ↥(limit F)) :
    ∃ (i : Jᵒᵈ) (Ui : ι → CompactOpens (F.obj i)) (Vi : κ → CompactOpens (F.obj i)),
      (∀ a, (U a : Set ↥(limit F)) = (limit.π F i) ⁻¹' (Ui a : Set (F.obj i))) ∧
        ∀ b, (V b : Set ↥(limit F)) = (limit.π F i) ⁻¹' (Vi b : Set (F.obj i)) := by
  classical
  -- Descend each compact open individually to some stage by Lemma `5.24.6`.
  have hF' : ∀ ⦃i j : Jᵒᵈ⦄ (a : j ⟶ i), IsSpectralMap (F.map a) := by
    intro i j a
    exact hF a
  have hUdesc :
      ∀ a, ∃ (j : Jᵒᵈ) (Uj : CompactOpens (F.obj j)),
        (U a : Set ↥(limit F)) = (limit.π F j) ⁻¹' (Uj : Set (F.obj j)) := by
    intro a
    exact compact_open_eq_preimage_of_limit (J := Jᵒᵈ) (F := F) hF' (U a)
  have hVdesc :
      ∀ b, ∃ (j : Jᵒᵈ) (Vj : CompactOpens (F.obj j)),
        (V b : Set ↥(limit F)) = (limit.π F j) ⁻¹' (Vj : Set (F.obj j)) := by
    intro b
    exact compact_open_eq_preimage_of_limit (J := Jᵒᵈ) (F := F) hF' (V b)
  choose jU Uj hUj using hUdesc
  choose jV Vj hVj using hVdesc
  -- Replace the finitely many stage choices by one common upper bound in the original directed
  -- index preorder, hence by one common refinement stage in the opposite indexing category.
  let stageChoice : Sum ι κ → J := fun t ↦
    match t with
    | Sum.inl a => OrderDual.ofDual (jU a)
    | Sum.inr b => OrderDual.ofDual (jV b)
  obtain ⟨i₀, hi₀⟩ := exists_upper_bound_of_finite_family (J := J) (σ := Sum ι κ) stageChoice
  -- Passing back to the inverse-system index uses the order-dual constructor.
  let i : Jᵒᵈ := OrderDual.toDual i₀
  let aiU : ∀ a, i ⟶ jU a := fun a ↦
    homOfLE (show i ≤ jU a from hi₀ (Sum.inl a))
  let aiV : ∀ b, i ⟶ jV b := fun b ↦
    homOfLE (show i ≤ jV b from hi₀ (Sum.inr b))
  -- Pull the descended stage opens back to the common refinement stage.
  let Ui : ι → CompactOpens (F.obj i) := fun a ↦
    ⟨⟨(F.map (aiU a)) ⁻¹' (Uj a : Set (F.obj (jU a))),
        (hF (aiU a)).isCompact_preimage_of_isOpen (Uj a).isOpen (Uj a).isCompact⟩,
      (Uj a).isOpen.preimage (F.map (aiU a)).hom.continuous⟩
  let Vi : κ → CompactOpens (F.obj i) := fun b ↦
    ⟨⟨(F.map (aiV b)) ⁻¹' (Vj b : Set (F.obj (jV b))),
        (hF (aiV b)).isCompact_preimage_of_isOpen (Vj b).isOpen (Vj b).isCompact⟩,
      (Vj b).isOpen.preimage (F.map (aiV b)).hom.continuous⟩
  refine ⟨i, Ui, Vi, ?_⟩
  constructor
  · intro a
    -- Rewrite the original descended equation through the canonical limit relation
    -- `π_i ≫ F.map (aiU a) = π_(jU a)`.
    ext x
    rw [hUj a]
    change
      (limit.π F (jU a) x ∈ (Uj a : Set (F.obj (jU a)))) ↔
        (F.map (aiU a) (limit.π F i x) ∈ (Uj a : Set (F.obj (jU a))))
    simpa [CategoryTheory.comp_apply] using
      congrArg
        (fun f : limit F ⟶ F.obj (jU a) ↦
          f x ∈ (Uj a : Set (F.obj (jU a))))
        (limit.w F (aiU a)).symm
  · intro b
    -- The same limit-cone rewrite works for the second finite family.
    ext x
    rw [hVj b]
    change
      (limit.π F (jV b) x ∈ (Vj b : Set (F.obj (jV b)))) ↔
        (F.map (aiV b) (limit.π F i x) ∈ (Vj b : Set (F.obj (jV b))))
    simpa [CategoryTheory.comp_apply] using
      congrArg
        (fun f : limit F ⟶ F.obj (jV b) ↦
          f x ∈ (Vj b : Set (F.obj (jV b))))
        (limit.w F (aiV b)).symm

/-- Helper for Lemma 17.19.3: after transporting the finite lower-shriek constant presentation of
`ℱ` to an inverse-limit model of `X`, all finitely many compact opens and section families descend
to one finite stage, whose stagewise coequalizer pulls back to `ℱ` and has finite stalks. -/
private noncomputable def pullback_fixed_stage_coproduct_iso
    {J ι : Type u} [Preorder J]
    (F : Jᵒᵈ ⥤ TopCat.{u}) (i : Jᵒᵈ) (U : ι → CompactOpens (F.obj i)) (S : ι → Type u) :
    (((limit.π F i)⁻¹).obj
        (∐ fun a : ι ↦ j![(U a).toOpens, S a])) ≅
      ∐ fun a : ι ↦
        (((limit.π F i)⁻¹).obj
          (j![(U a).toOpens, S a])) := by
  let D : Discrete ι ⥤ Sh(F.obj i) :=
    Discrete.functor fun a : ι ↦
      j![(U a).toOpens, S a]
  -- Pullback is a left adjoint, so it preserves the fixed-stage finite coproduct used in the
  -- source proof before the adjoint section families are descended.
  simpa [D] using (preservesColimitIso (((limit.π F i)⁻¹)) D).symm

/-- Helper for Lemma 17.19.3: after transporting the finite lower-shriek constant presentation of
`ℱ` to an inverse-limit model of `X`, all finitely many compact opens and section families descend
to one finite stage, whose stagewise coequalizer pulls back to `ℱ` and has finite stalks. -/
private theorem exists_limit_stage_sheaf_model_of_constructible_presentation
    {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : Jᵒᵈ ⥤ TopCat.{u}) (hFin : ∀ j : Jᵒᵈ, Finite (F.obj j))
    (hT0 : ∀ j : Jᵒᵈ, T0Space (F.obj j)) (eX : X ≃ₜ ↥(limit F))
    (ℱ : Sh(X)) (hℱ : HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation ℱ) :
    ∃ (i : Jᵒᵈ) (𝒢 : Sh(F.obj i))
      (descIso : ((((TopCat.isoOfHomeo eX).hom ≫ limit.π F i)⁻¹).obj 𝒢) ≅ ℱ),
      ∀ y : F.obj i, Finite (𝒢.presheaf.stalk y) :=
by
  classical
  letI : ∀ j : Jᵒᵈ, SpectralSpace (F.obj j) := fun j ↦
    { toT0Space := hT0 j
      toCompactSpace := inferInstance
      toQuasiSober := finite_t0_quasiSober
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  have hF : ∀ ⦃j k : Jᵒᵈ⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := by
    -- Every transition map between finite `T₀` stages is spectral because stage opens are
    -- automatically quasi-compact.
    intro j k a
    refine ⟨(F.map a).hom.continuous, ?_⟩
    intro s hs_open hs_comp
    exact NoetherianSpace.isCompact ((F.map a) ⁻¹' s)
  letI : SpectralSpace ↥(limit F) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF
  let eTop : X ≅ limit F := TopCat.isoOfHomeo eX
  rcases hℱ with
    ⟨ι, κ, _hι, _hκ, U, V, S, T, left, right, eℱ, hU, hV, hS, hT⟩
  let Ulim : ι → CompactOpens ↥(limit F) := fun a ↦
    compact_open_map_homeomorph eX (U a) (hU a)
  let Vlim : κ → CompactOpens ↥(limit F) := fun b ↦
    compact_open_map_homeomorph eX (V b) (hV b)
  -- First descend the finitely many compact-open supports to one common stage `i₀`.
  obtain ⟨i0, Ui0, Vi0, hUi0, hVi0⟩ :=
    exists_common_stage_for_compact_open_families
      (J := J) (F := F) hF Ulim Vlim
  let A0 : Sh(F.obj i0) :=
    ∐ fun a : ι ↦ j![(Ui0 a).toOpens, S a]
  let B0 : Sh(F.obj i0) :=
    ∐ fun b : κ ↦ j![(Vi0 b).toOpens, T b]
  have hA0pull :
      ((((limit.π F i0)⁻¹).obj A0) ≅
        ∐ fun a : ι ↦
          (((limit.π F i0)⁻¹).obj
            (j![(Ui0 a).toOpens, S a]))) := by
    -- First normalize the fixed-stage target sheaf to the pulled-back coproduct of its summands.
    simpa [A0] using pullback_fixed_stage_coproduct_iso F i0 Ui0 S
  have hB0pull :
      ((((limit.π F i0)⁻¹).obj B0) ≅
        ∐ fun b : κ ↦
          (((limit.π F i0)⁻¹).obj
            (j![(Vi0 b).toOpens, T b]))) := by
    -- The source proof uses the same fixed-stage pullback normalization on the domain coproduct.
    simpa [B0] using pullback_fixed_stage_coproduct_iso F i0 Vi0 T
  -- Route correction: keep the fixed stage target sheaf `A0` visible, then descend the finitely
  -- many adjoint section representatives for `left` and `right` via
  -- `limitPullbackSectionsColimitMap_isIso` instead of descending the whole sheaf system at once.
  -- TODO: transport the presentation `eℱ` across `eTop`, use `hA0pull` and `hB0pull` to rewrite
  -- the pulled-back fixed-stage coproducts, descend the finitely many adjoint section families
  -- over `Vi0` to one refinement stage, rebuild the stagewise parallel pair by adjunction, and
  -- then form its coequalizer to obtain `𝒢`.
  sorry

-- Proof sketch: combine the finite coequalizer presentation from `17.19.2.1` with the directed
-- inverse-limit presentation of a spectral space by finite `T₀` stages from Lemma `5.23.14`,
-- together with the canonical sober-space owner form `T0Space Y ∧ QuasiSober Y`.
-- Descend the finitely many quasi-compact opens and the finitely many structure maps defining the
-- coequalizer to one finite `T₀` stage, then take on that stage the corresponding coequalizer
-- sheaf `𝒢`; its stalks are finite because it is built from finitely many finite constant sheaves
-- by finite colimits, and inverse image along the projection recovers `ℱ`.
/-- Lemma 17.19.3: a sheaf of sets on a spectral space admitting the finite coequalizer
presentation of `17.19.2.1` is the inverse image of a sheaf with finite stalks along some spectral
map to a finite sober topological space, expressed canonically by `Finite Y` together with the
sober-space owner `T0Space Y ∧ QuasiSober Y`. The source-facing hypothesis is the Chapter 17 owner
predicate `HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation`, which keeps exactly the
Equation `17.19.2.1` data on the public surface without repeating it in each downstream header. -/
theorem exists_finite_sober_sheaf_model_of_constructible_set_presentation
    (ℱ : Sh(X))
    (hℱ : HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation ℱ) :
    ∃ (Y : TopCat.{u}) (_ : Finite Y) (hY : T0Space Y ∧ QuasiSober Y) (f : X ⟶ Y)
      (_ : IsSpectralMap f) (𝒢 : Sh(Y)) (descIso : ((f⁻¹).obj 𝒢) ≅ ℱ),
      ∀ y : Y, Finite (𝒢.presheaf.stalk y) := by
  classical
  -- Route correction: the source proof does not fix an arbitrary finite stage first. Instead, it
  -- keeps the full inverse-limit presentation of `X` in view until all finitely many opens and
  -- section families have descended to a common stage.
  obtain ⟨J, _instJ, hJne, _instDir, F, hFin, hT0, hX⟩ :=
    (spectralSpace_iff_homeomorphic_directed_limit_finite_sober (X := X)).1 inferInstance
  letI : Preorder J := _instJ
  letI : Nonempty J := hJne
  letI : IsDirectedOrder J := _instDir
  letI : ∀ j : Jᵒᵈ, SpectralSpace (F.obj j) := fun j ↦
    { toT0Space := hT0 j
      toCompactSpace := inferInstance
      toQuasiSober := finite_t0_quasiSober
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  rcases hX with ⟨eX⟩
  have hF : ∀ ⦃j k : Jᵒᵈ⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := by
    -- Finite `T₀` stages are noetherian, so inverse images of opens are automatically compact.
    intro j k a
    refine ⟨(F.map a).hom.continuous, ?_⟩
    intro s hs_open hs_comp
    exact NoetherianSpace.isCompact ((F.map a) ⁻¹' s)
  letI : SpectralSpace ↥(limit F) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF
  -- Descend the whole finite presentation to one common stage of the inverse system.
  obtain ⟨i, 𝒢, descIso, hstalk⟩ :=
    exists_limit_stage_sheaf_model_of_constructible_presentation
      (X := X) F hFin hT0 eX ℱ hℱ
  let Y : TopCat.{u} := F.obj i
  let f : X ⟶ Y := (TopCat.isoOfHomeo eX).hom ≫ limit.π F i
  have hY_quasiSober : QuasiSober Y := by
    exact finite_t0_quasiSober
  have hY : T0Space Y ∧ QuasiSober Y := ⟨hT0 i, hY_quasiSober⟩
  have hIso : IsSpectralMap (TopCat.isoOfHomeo eX).hom := by
    -- The homeomorphism identifying `X` with the limit is spectral.
    simpa using isSpectralMap_of_homeomorph eX
  have hProj : IsSpectralMap (limit.π F i) := by
    -- The projection from the inverse limit to the chosen stage is spectral.
    exact isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (hC := limit.isLimit F) hF i
  have hf : IsSpectralMap f := hProj.comp hIso
  exact ⟨Y, hFin i, hY, f, hf, 𝒢, descIso, hstalk⟩

end
