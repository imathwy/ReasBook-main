import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap06.Lemma_6_21_5
import StacksProject_2024.Chap06.Lemma_6_32_1
import StacksProject_2024.Chap06.Lemma_6_32_3
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

local notation "sZ" => X.subsetInclusion Z
local notation "iZ" => X.closedSubsetInclusion Z

/- Definition 17.5.1 provides the canonical support owner for abelian sheaves. -/
recall abelianSheafSupport

/- A point lies in `abelianSheafSupport` exactly when the stalk at that point is nonzero. -/
recall mem_abelianSheafSupport_iff

-- Proof sketch: pushforward along the closed inclusion is a right adjoint, so it preserves finite
-- limits. The stalkwise closed-subset argument shows that it also sends exact short complexes to
-- exact short complexes, hence it preserves epimorphisms and is right exact. Therefore it
-- preserves finite colimits too, so `exactFunctor_iff` gives exactness.

/-- Helper for Lemma 17.6.1: stalkwise surjectivity detects epimorphisms of abelian sheaves. -/
private lemma addCommGrpSheaf_epi_iff_stalk_surjective
    {Y : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    {A B : Y.Sheaf AddCommGrpCat.{u}} (φ : A ⟶ B) :
    Epi φ ↔
      ∀ y : Y,
        Function.Surjective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ.hom).hom) :=
    by
  -- Proof comment: for additive sheaves, epimorphy is the same as local surjectivity, and local
  -- surjectivity is detected on all stalks.
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-- Helper for Lemma 17.6.1: the presheaf-level stalk comparison for pushforward is natural in the
sheaf morphism. -/
private theorem closedSubsetStalkPushforward_naturality
    {ℱ 𝒢 : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) (z : TopCat.of Z) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (iZ z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).map φ.hom)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ 𝒢.presheaf z =
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ ℱ.presheaf z ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom) := by
  -- Proof comment: compare both stalk morphisms after precomposing with every germ from the
  -- pushed-forward presheaf, then rewrite both germ composites to the same sectionwise formula.
  refine TopCat.Presheaf.stalk_hom_ext
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ.presheaf) ?_
  intro U hzU
  ext s
  calc
    ((((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ.presheaf).germ U (iZ z) hzU) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (iZ z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).map φ.hom)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ 𝒢.presheaf z) s
      =
        (𝒢.presheaf.germ ((TopologicalSpace.Opens.map iZ).obj U) z hzU)
          ((φ.hom.app (Opposite.op ((TopologicalSpace.Opens.map iZ).obj U))) s) := by
            rw [Category.assoc,
              TopCat.Presheaf.stalkFunctor_map_germ_apply U (iZ z) hzU
                ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).map φ.hom) s,
              TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} iZ 𝒢.presheaf U z hzU]
    _ =
        ((((TopCat.Presheaf.pushforward AddCommGrpCat.{u} iZ).obj ℱ.presheaf).germ U (iZ z) hzU) ≫
            TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ ℱ.presheaf z ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom)) s := by
              rw [Category.assoc,
                TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} iZ ℱ.presheaf U z hzU,
                TopCat.Presheaf.stalkFunctor_map_germ_apply
                  ((TopologicalSpace.Opens.map iZ).obj U) z hzU φ.hom s]

/-- Helper for Lemma 17.6.1: on points of the closed subset, pushforward preserves stalkwise
surjectivity of epimorphisms. -/
private theorem closedSubsetPushforward_stalkSurjective_of_mem
    {ℱ 𝒢 : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) [Epi φ] (z : TopCat.of Z) :
    Function.Surjective
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (iZ z)).map
          (((Sheaf.pushforward AddCommGrpCat.{u} iZ).map φ).hom)).hom) := by
  let ψℱ := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ ℱ.presheaf z
  let ψ𝒢 := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} iZ 𝒢.presheaf z
  haveI : IsIso ψℱ :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} Topology.IsInducing.subtypeVal ℱ.presheaf z
  haveI : IsIso ψ𝒢 :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} Topology.IsInducing.subtypeVal 𝒢.presheaf z
  have hstalk :
      Function.Surjective
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom).hom) :=
    (addCommGrpSheaf_epi_iff_stalk_surjective φ).1 inferInstance z
  have hcomm :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (iZ z)).map
          (((Sheaf.pushforward AddCommGrpCat.{u} iZ).map φ).hom)) ≫
        ψ𝒢 =
      ψℱ ≫ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom) := by
    -- Proof comment: the stalk-pushforward comparison is natural in the sheaf morphism.
    simpa [ψℱ, ψ𝒢] using closedSubsetStalkPushforward_naturality (φ := φ) z
  have hψℱ_surj : Function.Surjective ψℱ :=
    (ConcreteCategory.bijective_of_isIso ψℱ).2
  have hψ𝒢_inj : Function.Injective ψ𝒢 :=
    (ConcreteCategory.bijective_of_isIso ψ𝒢).1
  -- Proof comment: transport a chosen preimage on the source stalk back across the two comparison
  -- isomorphisms and cancel the target comparison isomorphism by injectivity.
  intro y
  obtain ⟨x₀, hx₀⟩ := hstalk (ψ𝒢 y)
  obtain ⟨x, hx⟩ := hψℱ_surj x₀
  refine ⟨x, hψ𝒢_inj ?_⟩
  calc
    ψ𝒢
        ((((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (iZ z)).map
          (((Sheaf.pushforward AddCommGrpCat.{u} iZ).map φ).hom)).hom) x)
      =
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom).hom) (ψℱ x) := by
          exact congrArg (fun k ↦ k x) hcomm
    _ = (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map φ.hom).hom) x₀ := by
          rw [hx]
    _ = ψ𝒢 y := hx₀

/-- Helper for Lemma 17.6.1: outside the closed subset, the stalk of a pushforward abelian sheaf
is zero, so every induced stalk map is surjective. -/
private theorem closedSubsetPushforward_stalkSurjective_of_not_mem
    (hZ : IsClosed Z) {ℱ 𝒢 : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) {x : X}
    (hx : x ∉ Z) :
    Function.Surjective
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((Sheaf.pushforward AddCommGrpCat.{u} iZ).map φ).hom)).hom) := by
  let hzero :
      IsZero (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj 𝒢).presheaf.stalk x) :=
    closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem hZ 𝒢 hx
  let hsub :
      Subsingleton (((Sheaf.pushforward AddCommGrpCat.{u} iZ).obj 𝒢).presheaf.stalk x) :=
    (AddCommGrpCat.isZero_iff_subsingleton).1 hzero
  -- Proof comment: once the target stalk is zero, every element has the same chosen preimage `0`.
  intro y
  refine ⟨0, ?_⟩
  exact hsub.elim _ _

/-- Helper for Lemma 17.6.1: pushforward along the closed inclusion preserves epimorphisms of
abelian sheaves. -/
private theorem closedSubsetAbelianSheafPushforward_preservesEpimorphisms
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    (hZ : IsClosed Z) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ :
      ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ⥤ X.Sheaf AddCommGrpCat.{u}).PreservesEpimorphisms :=
    by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ hφ
  letI : Epi φ := hφ
  -- Proof comment: detect epimorphy of the pushed-forward map stalkwise and split according to
  -- whether the ambient point lies on the closed subset.
  refine (addCommGrpSheaf_epi_iff_stalk_surjective
    ((Sheaf.pushforward AddCommGrpCat.{u} iZ).map φ)).2 ?_
  intro x
  by_cases hx : x ∈ Z
  · let z : TopCat.of Z := ⟨x, hx⟩
    simpa [z] using closedSubsetPushforward_stalkSurjective_of_mem (φ := φ) z
  · exact closedSubsetPushforward_stalkSurjective_of_not_mem (hZ := hZ) (φ := φ) hx

/-- Lemma 17.6.1 (1): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` on abelian sheaves is exact. -/
@[stacks 01AX]
theorem closedSubsetAbelianSheafPushforward_exact
    (hZ : IsClosed Z)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] :
    exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (Sheaf.pushforward AddCommGrpCat.{u} iZ) := by
  let F : ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ⥤ X.Sheaf AddCommGrpCat.{u} :=
    Sheaf.pushforward AddCommGrpCat.{u} iZ
  let _ : F.IsRightAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iZ).isRightAdjoint
  let _ : PreservesFiniteLimits F := by infer_instance
  let _ : F.PreservesEpimorphisms :=
    closedSubsetAbelianSheafPushforward_preservesEpimorphisms (X := X) (Z := Z) hZ
  let _ : PreservesFiniteColimits F :=
    Functor.preservesFiniteColimits_of_preservesHomology F
      (Functor.preservesHomology_of_preservesEpis_and_kernels F)
  -- Proof comment: exactness is exactly preservation of finite limits and finite colimits.
  exact (CategoryTheory.exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

/- Lemma 17.6.1 (2): for the inclusion `i : Z → X` of a closed subset, the direct-image functor
`i_* : Ab(Z) ⥤ Ab(X)` is fully faithful. This is the `AddCommGrpCat` specialization of
`subsetSheafPushforward_fullyFaithful`. -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: by Lemma `closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem`,
-- an abelian sheaf lies in the essential image of `i_*` exactly when every stalk outside `Z` is
-- zero. Unfolding `abelianSheafSupport`, this is exactly the condition that the support be
-- contained in `Z`.
/-- Lemma 17.6.1 (3): the essential image of `i_* : Ab(Z) ⥤ Ab(X)` is exactly the abelian sheaves
whose support is contained in `Z`. -/
@[stacks 01AX]
theorem closedSubsetAbelianSheafPushforward_essImage_iff_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage ℱ ↔
      abelianSheafSupport ℱ ⊆ Z := by
  rw [closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem hZ ℱ]
  constructor
  · intro h x hx
    by_contra hx'
    exact hx <| by simpa [mem_abelianSheafSupport_iff] using h x hx'
  · intro h x hx
    by_contra hx'
    exact hx <| h <| by simpa [mem_abelianSheafSupport_iff] using hx'

/- Lemma 17.6.1 (4): for the inclusion `i : Z → X`, the inverse-image functor `i⁻¹` is a left
inverse to `i_*`, equivalently the counit `i⁻¹ i_* ℱ ⟶ ℱ` is an isomorphism for every abelian
sheaf `ℱ` on `Z`. This is the `AddCommGrpCat` specialization of the subset-inclusion owner
theorem `subsetSheaf_pullback_pushforward_counit_isIso`. -/
recall subsetSheaf_pullback_pushforward_counit_isIso

end
