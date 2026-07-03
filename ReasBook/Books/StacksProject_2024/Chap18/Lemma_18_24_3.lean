import Mathlib
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

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
