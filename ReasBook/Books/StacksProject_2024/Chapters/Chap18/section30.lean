import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_30_1 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u w

section

variable {C : Type u} [Category.{u} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable {I : Type w} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 18.30.1:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and the Čech sequence attached to a covering family;
- sampled owner declarations:
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `SheafOfModules.evaluation`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the chapter owner
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  `Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)` bridge already owned by
  `localizedStructureModuleExtensionByZero_homEquiv`;
- primitive-vs-derived split:
  the primitive data are only the ringed site `(C, J, 𝒪)`, the covering family `Uᵢ ⟶ U`, and the
  canonical lower-shriek summands `localizedStructureModuleExtensionByZero 𝒪 V`;
  the Čech maps, short complex, and sectionwise restriction/compatibility maps are derived API.

Source/core/bridge triage:
- `source-facing`: the Čech sequence for the covering family and the induced sectionwise sequence;
- `core/canonical`: `localizedStructureModuleExtensionByZero 𝒪 V` together with
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V`;
- `bridge/view`: the explicit Čech maps `ringedSiteCoverCechδ₀`, `ringedSiteCoverCechδ₁`, the
  derived short complex, and the sectionwise functions below.

This file should therefore reuse the chapter owner
`localizedStructureModuleExtensionByZero 𝒪 V` and its canonical Hom/evaluation bridge directly,
instead of exporting types built from private localized extension-by-zero or private
underlying-sheaf abbreviations. -/

section CechModule

/-- Restriction of a section over `U` to a family of sections over a covering family
`Uᵢ ⟶ U`. -/
def ringedSiteCoverSectionRestriction
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : Mod) :
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op U) →
      ∀ i : I, ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (Uᵢ i)) :=
  fun s i ↦ ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map (π i).op s

/-- The Čech compatibility map sending a family of sections on the cover to the pairwise
differences of their restrictions to the fiber products `Uᵢ ×[U] Uⱼ`. -/
def ringedSiteCoverSectionCompatibility
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : Mod) :
    (∀ i : I, ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (Uᵢ i))) →
      ∀ i j : I,
        ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (pullback (π i) (π j))) :=
  fun s i j ↦
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map
        (pullback.fst (π i) (π j)).op (s i) -
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map
        (pullback.snd (π i) (π j)).op (s j)

section CechSequence

variable {I : Type u} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

/-- The canonical augmentation component
`j_{V!}\mathcal O_V \to j_{U!}\mathcal O_U`
attached to a morphism `f : V ⟶ U`. -/
noncomputable def ringedSiteCoverCechArrow
    {V U : C} (f : V ⟶ U) :
    localizedStructureModuleExtensionByZero 𝒪 V ⟶
      localizedStructureModuleExtensionByZero 𝒪 U :=
  (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V
      (localizedStructureModuleExtensionByZero 𝒪 U)).symm
    ((localizedStructureModuleExtensionByZero 𝒪 U).val.map f.op
      ((localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U
          (localizedStructureModuleExtensionByZero 𝒪 U)) (𝟙 _)))

/-- The first canonical Čech map
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i}` attached to a covering family `Uᵢ ⟶ U`. -/
private noncomputable def ringedSiteCoverCechδ₀Component
    (p : I × I) :
    localizedStructureModuleExtensionByZero 𝒪 (pullback (π p.1) (π p.2)) ⟶
      (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) :=
  ringedSiteCoverCechArrow J 𝒪 (pullback.fst (π p.1) (π p.2)) ≫
      Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) p.1 -
    ringedSiteCoverCechArrow J 𝒪 (pullback.snd (π p.1) (π p.2)) ≫
      Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) p.2

noncomputable def ringedSiteCoverCechδ₀ :
    (∐ fun p : I × I ↦ localizedStructureModuleExtensionByZero 𝒪 (pullback (π p.1) (π p.2))) ⟶
        (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) :=
  Sigma.desc (ringedSiteCoverCechδ₀Component J 𝒪 Uᵢ π)

/-- The augmentation
`\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U`
attached to a covering family `Uᵢ ⟶ U`. -/
noncomputable def ringedSiteCoverCechδ₁ :
    (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) ⟶
      localizedStructureModuleExtensionByZero 𝒪 U :=
  Sigma.desc fun i ↦ ringedSiteCoverCechArrow J 𝒪 (π i)

theorem ringedSiteCoverCechCompZero :
    ringedSiteCoverCechδ₀ J 𝒪 Uᵢ π ≫ ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π = 0 := by
  sorry

/-- The canonical Čech short complex attached to a covering family `Uᵢ ⟶ U`. -/
noncomputable def ringedSiteCoverCechShortComplex : ShortComplex Mod :=
  ShortComplex.mk
    (ringedSiteCoverCechδ₀ J 𝒪 Uᵢ π)
    (ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π)
    (ringedSiteCoverCechCompZero J 𝒪 Uᵢ π)

-- Proof sketch: apply the sheaf condition on the localized site `(C/U, J.over U)` to the
-- underlying presheaf of types of the restriction `ℱ|_U`, using the covering family
-- `Over.mk (π i)` of the terminal object of `C/U`. Via `18.19.2.1`, this identifies the induced
-- Hom sequence out of the Čech short complex with the usual sequence of sections. Lemma `12.5.8`
-- then upgrades the section exactness for all `\mathcal O`-modules to exactness and
-- epimorphicity of the canonical module sequence itself.
/-- Lemma 18.30.1: for a ringed site `(\mathcal C, \mathcal O)` and a covering family
`\{ U_i \to U \}` of an object `U`, the canonical Čech sequence
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U \to 0`
is exact in `\mathrm{Mod}(\mathcal O)`. -/
theorem ringedSite_cover_cech_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i))) :
    (ringedSiteCoverCechShortComplex J 𝒪 Uᵢ π).Exact ∧
      Epi (ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π) := by
  sorry

end CechSequence

end CechModule

-- Proof sketch: the main theorem gives the source-facing exact sequence in `Mod(\mathcal O)`.
-- Applying `Hom_{\mathcal O}(-, \mathcal F)` and using `18.19.2.1` identifies the resulting
-- sequence with the usual restriction and compatibility maps on sections.
/-- Companion bridge: for every `\mathcal O`-module `\mathcal F`, the induced sequence of
sections
`0 \to \mathcal F(U) \to \prod_i \mathcal F(U_i) \to \prod_{i,j} \mathcal F(U_i \times_U U_j)`
is injective and exact. -/
theorem ringedSite_cover_section_cech_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : Mod) :
    Function.Injective (ringedSiteCoverSectionRestriction J 𝒪 Uᵢ π ℱ) ∧
      Function.Exact
        (ringedSiteCoverSectionRestriction J 𝒪 Uᵢ π ℱ)
        (ringedSiteCoverSectionCompatibility J 𝒪 Uᵢ π ℱ) := by
  sorry

end

/-! ### Lemma_18_30_2 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable {I : Type v} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

-- Proof sketch: use quasi-compactness of `U` to refine the given covering family by a covering
-- whose image in the original index set is finite. Let `S ⊆ I` be that finite image. By Sites,
-- Lemma `7.8.6`, the sheaf condition descends from the refining cover to the restricted family
-- indexed by `S`, which gives exactness of the corresponding Čech section sequence. Lemma
-- `18.30.1` identifies this with the exactness of the displayed extension-by-zero sequence.
/-- Lemma 18.30.2: if `U` is quasi-compact and `\{U_i \to U\}_{i \in I}` is a covering family of a
ringed site `(\mathcal C, \mathcal O)`, then there is a finite subset `S ⊆ I` such that the
restricted Čech sequence on sections over `S` is exact for every `\mathcal O`-module. By Lemma
18.30.1, this is equivalent to exactness of the finite direct-sum sequence
`\bigoplus_{i,i' \in S} j_{U_i \times_U U_{i'}!}\mathcal O_{U_i \times_U U_{i'}} \to
\bigoplus_{i \in S} j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U \to 0`. -/
theorem quasiCompactObject_exists_finite_subfamily_section_cech_exact
    (hU : J.QuasiCompactObject U)
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i))) :
    ∃ S : Set I, S.Finite ∧
      ∀ ℱ : ringedSiteModuleCategory J 𝒪,
        let restriction :=
          ringedSiteCoverSectionRestriction J 𝒪
            (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ℱ
        let compatibility :=
          ringedSiteCoverSectionCompatibility J 𝒪
            (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ℱ
        Function.Injective restriction ∧ Function.Exact restriction compatibility := sorry

end

/-! ### Lemma_18_30_3 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.30.3:
- primary domain: sections functors on sheaves and sheaves of modules over a Grothendieck site,
  with quasi-compactness controlling preservation of arbitrary coproducts/direct sums;
- sampled owner declarations:
  `sheafSections`,
  `sheafSectionsNatIsoEvaluation`,
  `SheafOfModules.evaluation`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the canonical owner for sections of set-valued sheaves is
  `(sheafSections J (Type (max u v))).obj (op W)`, while the module-valued sections owner is
  `SheafOfModules.evaluation 𝒪 (op W)`, and the source-facing additive-sections functor is its
  abelian-group bridge
  `SheafOfModules.toSheaf 𝒪 ⋙ (sheafSections J AddCommGrpCat.{max u v}).obj (op W)`;
- primitive-vs-derived split:
  primitive data are only the site `(C, J)`, the quasi-compact object `W`, and the index type `ι`;
  the module-valued evaluation functor is the core owner, while the textbook `Ab`-valued sections
  functor is derived by forgetting scalars from that owner through `SheafOfModules.toSheaf 𝒪`;
- source/core/bridge triage:
  `source-facing`: preservation of coproducts/direct sums by sections over a quasi-compact object;
  `core/canonical`: `sheafSections` and `SheafOfModules.evaluation`;
  `bridge/view`: passage from module-valued sections to abelian-group-valued sections by
  `SheafOfModules.toSheaf 𝒪` and the induced sections functor. -/

-- Proof sketch: write an arbitrary coproduct of sheaves as the filtered colimit over its finite
-- subcoproducts; the transition maps are monomorphisms, so Lemma 7.17.7 identifies sections over a
-- quasi-compact object `W` with the corresponding colimit of sections.
/-- Lemma 18.30.3 (1): if `W` is quasi-compact, then taking sections over `W` defines a functor
`Sh(\mathcal{C}) \to \mathrm{Sets}` that preserves coproducts. -/
theorem quasiCompactObject_sheaf_sections_preserves_coproducts
    (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) ((sheafSections J (Type (max u v))).obj (op W)) := sorry

-- Proof sketch: apply part `(1)` to the underlying sheaves of abelian groups via
-- `SheafOfModules.toSheaf 𝒪`; this gives the source-facing additive-sections functor
-- `Mod(𝒪) ⥤ AddCommGrpCat`. The stronger module-valued statement for
-- `SheafOfModules.evaluation 𝒪 (op W)` is a companion owner-level refinement.
/-- Lemma 18.30.3 (2): if `W` is quasi-compact, then for any sheaf of rings `𝒪` the functor
`Mod(\mathcal{O}) \to \mathrm{Ab}` given by sections over `W` preserves direct sums. -/
theorem quasiCompactObject_module_sections_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf 𝒪 ⋙ (sheafSections J AddCommGrpCat.{max u v}).obj (op W)) := sorry

/-- Companion owner-level form of Lemma 18.30.3 (2): for quasi-compact `W`, the stronger
module-valued sections functor `Mod(\mathcal{O}) \to \mathrm{Mod}(\mathcal{O}(W))` also preserves
direct sums. -/
theorem quasiCompactObject_module_evaluation_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (SheafOfModules.evaluation 𝒪 (op W)) := sorry

end

/-! ### Lemma_18_30_4 (from Chap18) -/
open CategoryTheory Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.30.4:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and preservation of direct sums by the represented additive Hom-functor;
- sampled owner declarations:
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `quasiCompactObject_module_evaluation_preserves_direct_sums`,
  `preadditiveCoyoneda.obj`;
- best owner abstraction: the chapter owner
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  sections comparison carried by
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`;
- primitive-vs-derived split: the primitive data are only the ringed site `(C, J, 𝒪)`, the object
  `U`, the quasi-compactness hypothesis on `U`, and the index type `ι`; the represented additive
  Hom-functor and its sections comparison are derived from the owner
  `localizedStructureModuleExtensionByZero 𝒪 U` and the bridge
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` preserves
  direct sums for quasi-compact `U`;
- `core/canonical`: the chapter owner `localizedStructureModuleExtensionByZero 𝒪 U` together with
  the evaluation-preserves-direct-sums theorem
  `quasiCompactObject_module_evaluation_preserves_direct_sums`;
- `bridge/view`: the comparison
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`.

This file should therefore state the lemma directly on
`preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZero 𝒪 U))`, deriving the
sections comparison through `localizedStructureModuleExtensionByZero_homEquiv` instead of exposing
the raw pullback/unit implementation term in the public statement. -/

-- Proof sketch: identify `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` with the sections functor
-- `\mathcal F ↦ \mathcal F(U)` via `localizedStructureModuleExtensionByZero_homEquiv`, then apply
-- the quasi-compact direct-sum preservation statement for sections from Lemma `18.30.3`.
/-- Lemma 18.30.4: if `U` is quasi-compact in a ringed site `(\mathcal C, \mathcal O)`, then the
additive Hom-functor represented by `j_{U!}\mathcal O_U` preserves direct sums. -/
theorem localizedStructureModuleExtensionByZero_hom_preserves_directSums
    (hU : J.QuasiCompactObject U) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZero 𝒪 U))) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_30_6 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: use Situation `18.30.5` to choose, for each local section of `ℱ`, a covering
-- family by basis objects on which that section is represented by maps from the corresponding
-- `h_U^#`. Taking the coproduct over all such chosen basis objects gives a morphism to `ℱ` whose
-- image sieve contains a covering sieve at every section, hence is locally surjective.
/-- Lemma 18.30.6 (1): in Situation `18.30.5`, every sheaf of sets is the target of a locally
surjective map from a coproduct of sheafified representables `h_{U_i}^#` with `U_i ∈ B`. -/
theorem exists_locallySurjective_from_coproduct_basis_sheafifiedRepresentables
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ _hc : HasCoproduct (fun i : I ↦ J.sheafifiedRepresentable (U i)),
          ∃ (φ : (∐ fun i : I ↦ J.sheafifiedRepresentable (U i)) ⟶ ℱ),
            Sheaf.IsLocallySurjective φ := sorry

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: apply Situation `18.30.5` to choose, for every local generator of `ℱ`, a basis
-- object over which that generator is represented. By adjunction this yields maps
-- `j_{U!}\mathcal O_U ⟶ ℱ`; summing over all chosen basis objects produces an epimorphism.
/-- Lemma 18.30.6 (2): in Situation `18.30.5`, every `\mathcal O`-module is a quotient of a
direct sum of `j_{U_i!}\mathcal O_{U_i}` with `U_i ∈ B`. -/
theorem exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ),
          Epi φ := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_30_7 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable [HasFiniteCoproducts (Sheaf J (Type u))]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- A sheaf of sets has a finite basis coequalizer presentation if it is isomorphic to the
coequalizer of two maps between finite coproducts of sheafified representables `h_U^#` built from
objects of `B`. -/
abbrev HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation
    (ℱ : Sheaf J (Type u)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    let _ : HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin m)
    let _ : HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin n)
    let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)) :=
      (Sheaf.instHasColimitsOfShape :
        HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)))
    ∃ (left right :
      (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
        (∐ fun i : Fin n ↦ h[U i]^#[J]))
      (_ : ℱ ≅ coequalizer left right),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

-- Proof sketch: first use Lemma `18.30.6` in Situation `18.30.5` to write `ℱ` as the
-- coequalizer of a pair of maps between possibly infinite coproducts of basis sheafified
-- representables. Then use quasi-compactness of basis objects together with the finite-subcoproduct
-- argument from Lemma `7.17.7` to express that coequalizer as a filtered colimit over finite
-- subdiagrams.
/-- Lemma 18.30.7 (1): in Situation `18.30.5`, every sheaf of sets is a filtered colimit of
sheaves admitting finite coequalizer presentations by sheafified representables `h_U^#` with
`U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_sheafifiedRepresentable_coequalizers
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B (pres.diag.obj i) :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u}) (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- An `\mathcal O`-module has a finite basis cokernel presentation if it is isomorphic to the
cokernel of a map between finite coproducts of the extensions by zero `j_{U!}\mathcal O_U` built
from objects of `B`. -/
abbrev HasFiniteBasisConstructibleModuleCokernelPresentation
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    ∃ (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
      (_ : ℱ ≅ cokernel f),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

-- Proof sketch: start from the epimorphism of Lemma `18.30.6 (2)` available in Situation
-- `18.30.5` from a possibly infinite direct sum of modules `j_{U!}\mathcal O_U` with `U ∈ B`.
-- Apply Lemma `18.30.4` to the quasi-compact basis objects to show that morphisms out of the
-- finite source pieces factor through finite subcoproducts, so the resulting cokernels over
-- finite subdiagrams form a filtered colimit presentation of `ℱ`.
/-- Lemma 18.30.7 (2): in Situation `18.30.5`, every `\mathcal O`-module is a filtered colimit
of modules admitting finite cokernel presentations by sums of the extensions by zero
`j_{U!}\mathcal O_U` with `U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_constructibleModule_cokernels
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (pres.diag.obj i) :=
  sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_30_8 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: write the source module as an iterated cokernel of maps from summands
-- `j_{W!}\mathcal O_W` with `W ∈ B`, reduce to a single such summand mapping into the target
-- presentation, represent the corresponding section locally using the covering families supplied by
-- Situation `18.30.5`, use quasi-compactness of the basis objects to replace the local cover by a
-- finite one, and fold the resulting finite family into a new presentation of the cokernel.
/-- Lemma 18.30.8: in Situation `18.30.5`, the cokernel of any morphism between modules
presented as in `18.30.7.2` by basis objects again admits a finite basis cokernel presentation. -/
theorem ringedSite_constructibleModule_cokernel_of_morphism
    {n₁ m₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B) (hV₁ : ∀ j, V₁ j ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f ⟶ cokernel g) :
    SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation
      𝒪 B (cokernel φ) := sorry

end

/-! ### Lemma_18_30_9 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

/-- A sheaf of commutative rings on a site, viewed as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteCommRingSheafAsRingSheaf :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, J, \mathcal O)`. -/
private abbrev ringedSiteModuleCategory :=
  SheafOfModules (ringedSiteCommRingSheafAsRingSheaf J 𝒪)

/-- Extension by zero from the localized ringed site `(C/U, J.over U, \mathcal O_U)` back to the
ambient ringed site `(C, J, \mathcal O)`. -/
private abbrev ringedSiteLocalizedExtensionByZero (U : C) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 ((ringedSiteCommRingSheafAsRingSheaf J 𝒪).over U))

/-- The localized structure sheaf `\mathcal O_U`, regarded as a module over itself on `(C/U,
J.over U)`. -/
private abbrev ringedSiteLocalizedStructureModule (U : C) :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
  SheafOfModules.unit ((ringedSiteCommRingSheafAsRingSheaf J 𝒪).over U)

/-- The module `j_{U!}\mathcal O_U` on a commutative ringed site. -/
private abbrev extensionByZeroStructureModule (U : C) :
    ringedSiteModuleCategory J 𝒪 :=
  (ringedSiteLocalizedExtensionByZero J 𝒪 U).obj
    (ringedSiteLocalizedStructureModule J 𝒪 U)

/-- The index type obtained by summing the selected finite subfamilies of the covers of the `U_i`.
-/
private abbrev selectedCoverIndex {n : ℕ} (r : Fin n → ℕ) :=
  Σ i : Fin n, Fin (r i)

/-- The object in the selected finite subfamily corresponding to an index in `selectedCoverIndex`.
-/
private abbrev selectedCoverObject {n : ℕ} {K : Fin n → Type w}
    (r : Fin n → ℕ) (κ : ∀ i : Fin n, Fin (r i) → K i)
    (Ucover : ∀ i : Fin n, K i → C) :
    selectedCoverIndex r → C
  | ⟨i, a⟩ => Ucover i (κ i a)

/-- Witness data for a finite basis refinement whose induced map on cokernels is an
isomorphism. -/
structure FiniteBasisRefinementInducingCokernelIsoWitness
    {n m : ℕ} {K : Fin n → Type w}
    (B : Set C) (U : Fin n → C) (V : Fin m → C)
    (Ucover : ∀ i : Fin n, K i → C)
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) where
  /-- The number of chosen cover members retained over each `U i`. -/
  r : Fin n → ℕ
  /-- An injective enumeration of the chosen finite subset of each index set `K i`. -/
  κ : ∀ i : Fin n, Fin (r i) → K i
  /-- The selected enumerations are injective. -/
  κ_injective : ∀ i : Fin n, Function.Injective (κ i)
  /-- The number of basis objects used to refine the overlaps. -/
  ℓ : ℕ
  /-- The refining family of basis objects. -/
  W : Fin ℓ → C
  /-- Each refining object lies in the basis `B`. -/
  hW : ∀ l : Fin ℓ, W l ∈ B
  /-- The top horizontal map from the overlap refinement to the selected cover family. -/
  top :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪
          (selectedCoverObject r κ Ucover a))
  /-- The left vertical map from the overlap refinement to the original source family. -/
  left :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j))
  /-- The right vertical map from the selected finite subcovers to the family `U`. -/
  right :
    (∐ fun a : selectedCoverIndex r ↦
      extensionByZeroStructureModule J 𝒪
        (selectedCoverObject r κ Ucover a)) ⟶
      (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))
  /-- The refinement square commutes with the given morphism `f`. -/
  comm : top ≫ right = left ≫ f
  /-- The induced map on cokernels is an isomorphism. -/
  isIso_cokernel_map : IsIso (cokernel.map top f left right comm)

-- Proof sketch: apply Lemma `18.30.2` to each quasi-compact `U_i` to choose finite subcovers of
-- the given coverings. Use surjectivity of the resulting right vertical map to lift the given
-- morphism from `\bigoplus_j j_{V_j!}\mathcal O_{V_j}` after refining the `V_j` by basis covers,
-- then use the exact sequences from Lemma `18.30.2` for the chosen `U_i`- and `V_j`-covers.
-- Finally refine the quasi-compact overlaps once more by basis objects to obtain the top row with
-- all `W_l` in `B`; the induced map on cokernels is then an isomorphism.
/-- Lemma 18.30.9: in Situation `18.30.5`, a morphism
`\bigoplus_j j_{V_j!}\mathcal O_{V_j} \to \bigoplus_i j_{U_i!}\mathcal O_{U_i}` with `U_i, V_j ∈ B`
and coverings `\{U_{ik} \to U_i\}` by objects of `B` admits finite selected subfamilies of the
given covers and a finite family `W_l ∈ B` fitting into a commutative square whose induced map on
cokernels is an isomorphism. Here `κ i : Fin (r i) → K i` is an injective enumeration of the
selected finite subset of the index set `K i`. -/
theorem exists_finite_basis_refinement_inducing_cokernel_iso
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n m : ℕ}
    (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    (hV : ∀ j : Fin m, V j ∈ B)
    {K : Fin n → Type w}
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    (hcover : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun k : K i ↦ Over.mk (π i k)))
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) :
    Nonempty
      (FiniteBasisRefinementInducingCokernelIsoWitness J 𝒪 B U V Ucover f) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_30_10 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits
open _root_.SheafOfModules.RingedSite (HasFiniteBasisConstructibleModuleCokernelPresentation)

noncomputable section

universe u

namespace CategoryTheory.ShortComplex

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable {S : ShortComplex Mod}

-- Proof sketch: choose explicit `18.30.7.2` presentations for `S.X₁` and `S.X₃`. Lift the
-- generators of the right presentation through the epimorphism `S.g` after a finite basis
-- refinement using Lemma `18.30.9`, then compare kernels via the snake lemma and refine the
-- resulting kernel presentation using Lemma `18.30.2`. This produces a finite basis presentation
-- of the middle term `S.X₂`.
/-- Lemma 18.30.10: in Situation `18.30.5`, extensions of `\mathcal O`-modules admitting finite
basis cokernel presentations as in `18.30.7.2` again admit such a presentation. -/
theorem ringedSite_hasFiniteBasisConstructibleModuleCokernelPresentation_X2_of_shortExact
    (hS : S.ShortExact)
    (hX₁ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₁)
    (hX₃ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₃) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₂ := sorry

end

end CategoryTheory.ShortComplex

/-! ### Lemma_18_30_11 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: apply the weak-LinearRepresentations_Serre_1977 criterion to the object property of modules admitting a
-- finite basis cokernel presentation as in `18.30.7.2`. The basis assumptions are the setup from
-- Situation `18.30.5`, the displayed hypothesis gives the kernel step for maps between the
-- standard finite presentation objects, and the remaining closure properties are exactly the ones
-- established earlier in this subsection.
/-- Lemma 18.30.11: in Situation `18.30.5`, let `\mathcal A \subset \operatorname{Mod}(\mathcal
O)` be the full subcategory of modules isomorphic to a cokernel as in `18.30.7.2`. If the kernel
of every map
`\bigoplus_{j = 1, \ldots, m} j_{V_j!}\mathcal O_{V_j} \to
\bigoplus_{i = 1, \ldots, n} j_{U_i!}\mathcal O_{U_i}`
with `U_i` and `V_j` in `B` again lies in `\mathcal A`, then `\mathcal A` is a weak LinearRepresentations_Serre_1977
subcategory of `\operatorname{Mod}(\mathcal O)`. -/
theorem ringedSite_finiteBasisConstructibleModuleCokernelPresentation_isWeakSerreSubcategory_of_kernel_condition
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (kernel f)) :
    IsWeakSerreClass (HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B) := sorry

end
