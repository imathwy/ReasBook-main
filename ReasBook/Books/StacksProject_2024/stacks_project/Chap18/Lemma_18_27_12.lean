import Mathlib
import StacksProject_2024.Chap07.Lemma_7_17_8
import StacksProject_2024.Chap18.Lemma_18_27_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 18.27.12:
- primary domain: categorical finite presentability in `SheafOfModules 𝒪`, expressed through
  preservation of filtered colimits by the represented functor `Hom_𝒪(ℱ, -)`;
- sampled owner declarations:
  `CategoryTheory.IsFinitelyPresentable`,
  `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `CategoryTheory.GrothendieckTopology.globalSectionsColimitComparison_bijective_of_quasiCompactTestSet`;
- best owner abstraction: the canonical owner is `CategoryTheory.IsFinitelyPresentable ℱ`, with
  the represented functor `coyoneda.obj (op ℱ)` preserving filtered colimits as the standard
  bridge characterization;
- primitive data: a ring-valued sheaf `𝒪`, a finitely presented `\mathcal O`-module `ℱ`, a
  filtered diagram `𝒢`, and the quasi-compact test-set hypothesis on `J`;
- derived API: the fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`, the
  internal-Hom comparison from Lemma `18.27.11`, and the global-sections comparison from
  Lemma `7.17.8 (4)`.

Source/core/bridge triage:
- `source-facing`: finite presentation of `ℱ` together with the Stacks claim that
  `Hom_𝒪(ℱ, -)` preserves filtered colimits under the quasi-compact test-set hypothesis;
- `core/canonical`: `CategoryTheory.IsFinitelyPresentable ℱ`;
- `bridge/view`: `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits` and the
  fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]

/-- Helper for Lemma 18.27.12: a global section of the internal-Hom sheaf is the same thing as a
morphism out of `ℱ`. -/
private noncomputable theorem homEquivInternalHomSections
    (ℱ M : SheafOfModules.{u} 𝒪) :
    ((ihom ℱ).obj M).sections ≃ (ℱ ⟶ M) := by
  -- Proof comment: interpret a global section as a morphism from the tensor unit, then uncurry
  -- through the internal-Hom adjunction and the left unitor.
  have hAdj :
      (SheafOfModules.unit 𝒪 ⟶ (ihom ℱ).obj M) ≃ (ℱ ⟶ M) := by
    -- Proof comment: this is the internal-Hom adjunction, followed by removing the tensor unit.
    simpa using
      ((((ihom.adjunction ℱ).homEquiv (SheafOfModules.unit 𝒪) M).symm).trans
        (((λ_ ℱ).symm.homCongr (Iso.refl M))))
  exact ((((ihom ℱ).obj M).unitHomEquiv).symm).trans hAdj

/-- Helper for Lemma 18.27.12: the sections/Hom equivalence is natural in the target module. -/
private theorem homEquivInternalHomSections_naturality
    (ℱ : SheafOfModules.{u} 𝒪) {M N : SheafOfModules.{u} 𝒪} (f : M ⟶ N)
    (s : ((ihom ℱ).obj M).sections) :
    homEquivInternalHomSections ℱ N (SheafOfModules.sectionsMap ((ihom ℱ).map f) s) =
      homEquivInternalHomSections ℱ M s ≫ f := by
  -- Proof comment: `unitHomEquiv` rewrites section transport as postcomposition in the
  -- internal-Hom object, and then the inverse adjunction equivalence is natural in the target.
  dsimp [homEquivInternalHomSections]
  have hSectionsMap :
      ((((ihom ℱ).obj N).unitHomEquiv).symm
        (SheafOfModules.sectionsMap ((ihom ℱ).map f) s)) =
          ((((ihom ℱ).obj M).unitHomEquiv).symm s) ≫ (ihom ℱ).map f := rfl
  rw [hSectionsMap]
  simpa [Category.assoc] using
    (Adjunction.homEquiv_naturality_right_symm (ihom.adjunction ℱ)
      ((((ihom ℱ).obj M).unitHomEquiv).symm s) f)

/-- Helper for Lemma 18.27.12: the represented functor `Hom_\mathcal O(\mathcal F,-)` is
naturally isomorphic to global sections of the internal-Hom functor with source `ℱ`. -/
private theorem coyonedaIsoGlobalSectionsIhom
    (ℱ : SheafOfModules.{u} 𝒪) :
    coyoneda.obj (op ℱ) ≅
      ihom ℱ ⋙ SheafOfModules.toSheaf 𝒪 ⋙ sheafForget J ⋙ Γ J (Type u) := by
  -- Proof comment: the components are the pointwise sections/Hom equivalences, and naturality is
  -- exactly the compatibility proved in `homEquivInternalHomSections_naturality`.
  refine NatIso.ofComponents ?_ ?_
  · intro M
    exact (Equiv.toIso (homEquivInternalHomSections ℱ M)).symm
  · intro M N f
    ext φ
    apply (homEquivInternalHomSections ℱ N).injective
    simpa using
      (homEquivInternalHomSections_naturality (ℱ := ℱ) (f := f)
        ((homEquivInternalHomSections ℱ M).symm φ)).symm

/-- Companion to Lemma 18.27.12: for a fixed filtered diagram `\mathcal G_\lambda`, the canonical
comparison map
`colim_\lambda Hom_\mathcal O(\mathcal F, \mathcal G_\lambda) →
Hom_\mathcal O(\mathcal F, colim_\lambda \mathcal G_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules.{u} 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ coyoneda.obj (op ℱ))] :
    Function.Bijective (colimit.post 𝒢 (coyoneda.obj (op ℱ))) := by
  let H : Λ ⥤ Sheaf J (Type u) :=
    𝒢 ⋙ ihom ℱ ⋙ SheafOfModules.toSheaf 𝒪 ⋙ sheafForget J
  -- Proof comment: Chapter 7 gives bijectivity for global sections of the internal-Hom diagram.
  have hGlobalSections :
      Function.Bijective (colimit.post H (Γ J (Type u))) := by
    simpa [H] using
      CategoryTheory.GrothendieckTopology
        .globalSectionsColimitComparison_bijective_of_quasiCompactTestSet (J := J) H hJ
  -- Proof comment: finite presentation identifies the internal Hom into the colimit with the
  -- colimit of the internal-Hom diagram.
  have hInternalHom :
      IsIso (colimit.post 𝒢 (ihom ℱ)) :=
    SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation ℱ 𝒢
  let K : SheafOfModules.{u} 𝒪 ⥤ Type u :=
    ihom ℱ ⋙ SheafOfModules.toSheaf 𝒪 ⋙ sheafForget J ⋙ Γ J (Type u)
  let e : coyoneda.obj (op ℱ) ≅ K :=
    coyonedaIsoGlobalSectionsIhom (J := J) (𝒪 := 𝒪) ℱ
  letI : HasColimit (𝒢 ⋙ ihom ℱ) := inferInstance
  letI : PreservesColimit 𝒢 (ihom ℱ) :=
    preservesColimit_of_isIso_post (F := 𝒢) (G := ihom ℱ)
  letI : HasColimit H := inferInstance
  letI : IsIso (colimit.post H (Γ J (Type u))) :=
    (isIso_iff_bijective _).2 hGlobalSections
  letI : PreservesColimit H (Γ J (Type u)) :=
    preservesColimit_of_isIso_post (F := H) (G := Γ J (Type u))
  have hPreservesK : PreservesColimit 𝒢 K := by
    -- Proof comment: `K` is exactly the composite obtained from `H` by appending `Γ`, so the
    -- existing preservation owner for `H` transports directly.
    simpa [H, K] using (inferInstance : PreservesColimit H (Γ J (Type u)))
  letI : PreservesColimit 𝒢 K := hPreservesK
  letI : PreservesColimit 𝒢 (coyoneda.obj (op ℱ)) :=
    preservesColimit_of_natIso e
  -- Proof comment: once the represented functor preserves the chosen filtered colimit, its
  -- canonical comparison map is an isomorphism and therefore bijective.
  exact (isIso_iff_bijective (colimit.post 𝒢 (coyoneda.obj (op ℱ)))).1 inferInstance

-- Proof sketch: apply Lemma `18.27.11` to identify the internal Hom into `colim_λ 𝒢_λ` with the
-- filtered colimit of the internal Homs, then apply Sites, Lemma `7.17.8 (4)` to the resulting
-- filtered diagram of internal Hom sheaves. By the standard owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`, this upgrades finite presentation of `ℱ`
-- to categorical finite presentability.
/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis of Sites, Lemma `7.17.8 (4)`, a
finitely presented `\mathcal O`-module `\mathcal F` is finitely presentable in the category
`SheafOfModules 𝒪`. Equivalently, the represented functor `Hom_\mathcal O(\mathcal F, -)`
preserves filtered colimits. -/
theorem preservesFilteredColimits_coyoneda_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    PreservesFilteredColimits (coyoneda.obj (op ℱ)) := by
  -- Proof comment: it suffices to show that each filtered comparison map of the represented
  -- functor is bijective, then convert that bijection into the canonical `PreservesColimit` data.
  constructor
  intro Λ _ _ _ 𝒢
  letI : HasColimit (𝒢 ⋙ coyoneda.obj (op ℱ)) := inferInstance
  have hbij :
      Function.Bijective (colimit.post 𝒢 (coyoneda.obj (op ℱ))) :=
    homColimitComparison_bijective_of_isFinitePresentation (hJ := hJ) ℱ 𝒢
  letI : IsIso (colimit.post 𝒢 (coyoneda.obj (op ℱ))) :=
    (isIso_iff_bijective _).2 hbij
  -- Proof comment: once the comparison morphism is an isomorphism, the represented functor
  -- preserves this filtered colimit by the generic owner lemma.
  exact preservesColimit_of_isIso_post (F := 𝒢) (G := coyoneda.obj (op ℱ))

/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis, a finitely presented
`\mathcal O`-module is finitely presentable in the categorical sense. -/
theorem isFinitelyPresentable_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    IsFinitelyPresentable.{u} ℱ := by
  exact
    (isFinitelyPresentable_iff_preservesFilteredColimits :
      IsFinitelyPresentable.{u} ℱ ↔ PreservesFilteredColimits (coyoneda.obj (op ℱ))).2
      (preservesFilteredColimits_coyoneda_of_isFinitePresentation hJ ℱ)

end SheafOfModules
