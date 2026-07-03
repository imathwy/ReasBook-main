import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_24_1 (from Chap18) -/
open CategoryTheory Limits

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.24.1:
- primary domain: finite type and finite presentation for sheaves of modules over a sheaf of
  rings on a site, with ringed sites as the source-facing specialization;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.Presentation`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`;
- best owner abstraction:
  the generic owner category `SheafOfModules 𝒪`, with finite type / finite presentation as the
  canonical owner predicates and `cokernel` as derived abelian-category data;
- primitive data:
  a morphism `φ : 𝒢 ⟶ ℱ` together with `[𝒢.IsFiniteType]` and `[ℱ.IsFinitePresentation]`;
- derived API:
  the finite-presentation conclusion for `cokernel φ`.

Source/core/bridge triage:
- `source-facing`: the ringed-site statement of Stacks Project Lemma 18.24.1;
- `core/canonical`: the generic owner theorem
  `SheafOfModules.isFinitePresentation_cokernel`;
- `bridge/view`: ringed-space and ringed-site specializations obtained by instantiating the
  ambient sheaf of rings.

No upstream theorem with this exact interface is available in mathlib or earlier project files, so
this file keeps the generic owner theorem instead of introducing a ringed-site-local wrapper.
-/

-- Proof sketch: view `cokernel φ` as the quotient of `ℱ` by the image of `φ`. The image of a
-- finite type sheaf is finite type, and the local definition of finite presentation is stable
-- under quotienting a finitely presented sheaf by a finite type submodule.
/-- Lemma 18.24.1: for a morphism `φ : 𝒢 ⟶ ℱ` of `\mathcal O`-modules on a ringed site, if `𝒢`
is of finite type and `ℱ` is finitely presented, then the cokernel of `φ` is finitely
presented. -/
theorem isFinitePresentation_cokernel
    {𝒢 ℱ : SheafOfModules 𝒪} (φ : 𝒢 ⟶ ℱ) [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (cokernel φ).IsFinitePresentation := sorry

end SheafOfModules

/-! ### Lemma_18_24_2 (from Chap18) -/
/- Lemma 18.24.2: for a surjective morphism `θ : 𝒢 ⟶ ℱ` of `\mathcal O`-modules on a ringed
site, if `ℱ` is finitely presented and `𝒢` is of finite type, then `kernel θ` is of finite type.
This is already the owner-level theorem
`SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`. -/
recall SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation

/-! ### Lemma_18_24_3 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)

/- Domain-style sampling for Lemma 18.24.3:
- primary domain: quasi-coherent sheaves of modules on the chaotic site and the sectionwise
  extension/restriction-of-scalars comparison map;
- sampled owner declarations:
  `ringSheaf`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.RingedSite.IsQuasicoherent`,
  `ModuleCat.extendRestrictScalarsAdj`;
- best owner abstraction:
  the module category `SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)` together with
  the canonical owner predicate `IsQuasicoherent`;
- primitive data:
  the chaotic-topology ring sheaf `ringSheaf (⊥ : GrothendieckTopology C) 𝒪`, a module sheaf `ℱ`,
  and an arrow `f : U ⟶ V`;
- derived API:
  the adjoint transpose `chaoticTensorSectionsMap 𝒪 ℱ f` of the restriction map and the source-
  facing quasi-coherence criterion below.

Source/core/bridge triage:
- `source-facing`: the chaotic-topology criterion for quasi-coherence in Stacks Lemma 18.24.3;
- `core/canonical`: `ringSheaf (⊥ : GrothendieckTopology C) 𝒪` and `ℱ.IsQuasicoherent`;
- `bridge/view`: `chaoticTensorSectionsMap`, obtained by transposing the restriction map
  `ℱ.1.map f.op` along `ModuleCat.extendRestrictScalarsAdj`.

Accordingly, this file deletes the private `chaoticRingSheaf` wrapper and reuses the chapter owner
`ringSheaf`, while keeping only the genuinely source-facing tensor-comparison map as public local
API. -/

/-- The canonical base-change map on sections of an `\mathcal O`-module over the chaotic site,
from `\mathcal F(V) \otimes_{\mathcal O(V)} \mathcal O(U)` to `\mathcal F(U)`. -/
noncomputable abbrev chaoticTensorSectionsMap
    (ℱ : SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) {U V : C} (f : U ⟶ V) :
    (ModuleCat.extendScalars ((𝒪.obj.map f.op).hom)).obj (ℱ.1.obj (op V)) ⟶ ℱ.1.obj (op U) :=
  ((ModuleCat.extendRestrictScalarsAdj ((𝒪.obj.map f.op).hom)).homEquiv _ _).symm (ℱ.1.map f.op)

-- Proof sketch: this is just the definition of `chaoticTensorSectionsMap`; the displayed morphism
-- is obtained by applying the symmetric extension/restriction adjunction to the restriction map
-- `ℱ(U ← V)`.
/-- The canonical sectionwise tensor map is adjoint to the restriction map of `ℱ`. -/
theorem chaoticTensorSectionsMap_def
    (ℱ : SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) {U V : C} (f : U ⟶ V) :
    chaoticTensorSectionsMap 𝒪 ℱ f =
      ((ModuleCat.extendRestrictScalarsAdj ((𝒪.obj.map f.op).hom)).homEquiv _ _).symm
        (ℱ.1.map f.op) := rfl

section Quasicoherence

variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: if `ℱ` is quasi-coherent, then in the chaotic topology every local presentation is
-- already a global presentation on each slice `C/V`, so base change along any arrow `U ⟶ V`
-- identifies `ℱ(U)` with `ℱ(V) ⊗_{\mathcal O(V)} \mathcal O(U)`. Conversely, choosing a module
-- presentation of `ℱ(V)` for each `V`, the assumed isomorphisms show that these presentations pull
-- back exactly to the corresponding restrictions on `C/V`, which is the local presentation
-- criterion for quasi-coherence.
/-- Lemma 18.24.3: for a category `\mathcal C` with the chaotic topology, a sheaf
of `\mathcal O`-modules `\mathcal F` is quasi-coherent if and only if for every morphism
`U \to V` the canonical map
`\mathcal F(V) \otimes_{\mathcal O(V)} \mathcal O(U) \to \mathcal F(U)` is an isomorphism. -/
theorem isQuasicoherent_iff_tensor_sections_map_isIso
    (ℱ : SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :
    ℱ.IsQuasicoherent ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V),
        IsIso (chaoticTensorSectionsMap 𝒪 ℱ f) := sorry

end Quasicoherence

end SheafOfModules

/-! ### Lemma_18_24_4 (from Chap18) -/
open CategoryTheory Opposite CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.24.4:
- primary domain: weak LinearRepresentations_Serre_1977 subcategories of module categories on a ringed site, specialized here
  to the chaotic topology and the quasi-coherent owner predicate;
- sampled owner declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.RingedSite.IsQuasicoherent`;
- best owner abstraction:
  the chapter owner category `ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪` together
  with the ambient object-property owner
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- primitive data:
  the chaotic-site ring sheaf `𝒪` and the flatness hypothesis on each restriction map
  `𝒪(V) ⟶ 𝒪(U)`;
- derived API:
  the instance-valued predicate `ℱ.IsQuasicoherent` and the resulting weak-LinearRepresentations_Serre_1977 closure theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that quasi-coherent `\mathcal O`-modules form a weak
  LinearRepresentations_Serre_1977 subcategory under the flatness hypothesis;
- `core/canonical`: `ringedSiteModuleCategory`, `ObjectProperty.IsWeakSerreClass`, and
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- `bridge/view`: the instance form `ℱ.IsQuasicoherent` attached to that owner predicate.

The theorem below therefore keeps the source-facing weak-LinearRepresentations_Serre_1977 statement, but states it over the
canonical object property `SheafOfModules.isQuasicoherent (ringSheaf (⊥ :
GrothendieckTopology C) 𝒪)` instead of an ad hoc lambda. -/

-- Proof sketch: use the five-term exact-sequence criterion for weak LinearRepresentations_Serre_1977 subcategories. For an
-- exact sequence in `Mod(\mathcal O)`, exactness of sections on the chaotic site and flatness of
-- every restriction map make the tensor-comparison rows exact. Applying the tensor criterion for
-- quasi-coherence and then the five lemma shows the middle term is quasi-coherent whenever the
-- outer four terms are.
/-- Lemma 18.24.4: if every restriction map `\mathcal O(V) \to \mathcal O(U)` on the chaotic site
is flat, then quasi-coherent `\mathcal O`-modules form a weak LinearRepresentations_Serre_1977 subcategory of
`\operatorname{Mod}(\mathcal O)`. -/
theorem quasicoherentModuleProperty_isWeakSerreSubcategory
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom)) :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  sorry

/-- Under flat restriction maps on the chaotic site, quasi-coherent `\mathcal O`-modules carry
the canonical weak-LinearRepresentations_Serre_1977 structure. -/
instance isQuasicoherent_isWeakSerreClass
    [Fact (∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom))] :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  quasicoherentModuleProperty_isWeakSerreSubcategory 𝒪 Fact.out

end SheafOfModules
