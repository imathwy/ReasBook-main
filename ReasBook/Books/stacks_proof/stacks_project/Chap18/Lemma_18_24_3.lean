import Mathlib
import StacksProject_2024.Chap17.Lemma_17_10_2
import StacksProject_2024.Chap18.Lemma_18_23_3
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

private abbrev Mod𝒪
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
    [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)] :=
  SheafOfModules
    ((sheafCompose (⊥ : GrothendieckTopology C) (forget₂ CommRingCat RingCat)).obj 𝒪)

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
    (ℱ : Mod𝒪 𝒪) {U V : C} (f : U ⟶ V) :
    (ModuleCat.extendScalars ((𝒪.1.map f.op).hom)).obj (ℱ.1.obj (op V)) ⟶
      ℱ.1.obj (op U) :=
  ((ModuleCat.extendRestrictScalarsAdj ((𝒪.1.map f.op).hom)).homEquiv _ _).symm
    (ℱ.1.map f.op)

-- Proof sketch: this is just the definition of `chaoticTensorSectionsMap`; the displayed morphism
-- is obtained by applying the symmetric extension/restriction adjunction to the restriction map
-- `ℱ(U ← V)`.
/-- The canonical sectionwise tensor map is adjoint to the restriction map of `ℱ`. -/
theorem chaoticTensorSectionsMap_def
    (ℱ : Mod𝒪 𝒪) {U V : C} (f : U ⟶ V) :
    chaoticTensorSectionsMap 𝒪 ℱ f =
      ((ModuleCat.extendRestrictScalarsAdj ((𝒪.1.map f.op).hom)).homEquiv _ _).symm
        (ℱ.1.map f.op) := rfl

section Quasicoherence

variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

/-- Helper for Lemma 18.24.3: the identity family of objects covers the chaotic site. -/
private theorem identityFamily_coversTop :
    (⊥ : GrothendieckTopology C).CoversTop (fun X : C ↦ X) := by
  intro W
  -- The identity-family sieve is the maximal sieve on every object, so it is covering.
  have hsieve : Sieve.ofObjects (fun X : C ↦ X) W = ⊤ := by
    simpa using Sieve.pullback_ofObjects_eq_top (Y := fun X : C ↦ X) (X := W) (g := 𝟙 W)
  rw [hsieve]
  exact (⊥ : GrothendieckTopology C).covering_of_eq_top rfl

/-- Helper for Lemma 18.24.3: a cover of the terminal object in the chaotic topology contains an
arrow from any chosen object. -/
private theorem coverArrow_of_coversTop
    {D : Type*} [Category D] {I : Type*} {X : I → D}
    (hX : (⊥ : GrothendieckTopology D).CoversTop X) (V : D) :
    ∃ i : I, Nonempty (V ⟶ X i) := by
  -- Proof comment: in the chaotic topology, covering means generating the maximal sieve.
  have htop : Sieve.ofObjects X V = ⊤ := by
    simpa using hX V
  have hmem : (Sieve.ofObjects X V).arrows (𝟙 V) := by
    simpa [htop] using (show (⊤ : Sieve V).arrows (𝟙 V) from by trivial)
  rw [Sieve.mem_ofObjects_iff] at hmem
  exact hmem

/-- Helper for Lemma 18.24.3: sections on the chaotic slice over `V` are the same as evaluation
at the terminal object `Over.mk (𝟙 V)`. -/
private noncomputable def overSectionsEquivEvaluation
    (V : C)
    (M : SheafOfModules (ringSheaf ((⊥ : GrothendieckTopology C).over V) (𝒪.over V))) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 V))) where
  toFun s := s.1 (op (Over.mk (𝟙 V)))
  invFun m :=
    M.val.sectionsMk
      (fun X ↦ M.val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun X Y f ↦ by
        -- Every object of the slice has a unique morphism to the terminal object.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A slice section is determined by restricting its terminal value along the unique maps.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Evaluating the reconstructed section at the terminal object recovers `m`.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 V))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 V)) = 𝟙 (Over.mk (𝟙 V)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.24.3: evaluating the reconstructed slice section on `Over.mk f` is the
ordinary restriction map along `f`. -/
private theorem overSectionsEquivEvaluation_symm_apply_cover
    {U V : C} (f : U ⟶ V)
    (M : SheafOfModules (ringSheaf ((⊥ : GrothendieckTopology C).over V) (𝒪.over V)))
    (s : M.val.obj (op (Over.mk (𝟙 V)))) :
    ((overSectionsEquivEvaluation (𝒪 := 𝒪) V M).symm s).1 (op (Over.mk f)) =
      M.val.map (Over.homMk f (by simp)).op s := by
  -- Proof comment: the unique map from `Over.mk f` to the terminal object of the slice is
  -- exactly `Over.homMk f`, so the reconstructed section evaluates by ordinary restriction.
  have h : Over.mkIdTerminal.from (Over.mk f) = Over.homMk f (by simp) := by
    exact Over.mkIdTerminal.hom_ext _ _
  change (ConcreteCategory.hom (M.val.map ((Over.mkIdTerminal.from (Over.mk f)).op))) s =
    (ConcreteCategory.hom (M.val.map (Over.homMk f (by simp)).op)) s
  rw [h]
  rfl

/-- Helper for Lemma 18.24.3: the identity family of all objects also covers every chaotic slice
site. -/
private theorem identityOverFamily_coversTop (V : C) :
    ((⊥ : GrothendieckTopology C).over V).CoversTop (fun X : Over V ↦ X) := by
  intro W
  have hsieve : Sieve.ofObjects (fun X : Over V ↦ X) W = ⊤ := by
    simpa using Sieve.pullback_ofObjects_eq_top (Y := fun X : Over V ↦ X) (X := W) (g := 𝟙 W)
  rw [hsieve]
  exact ((⊥ : GrothendieckTopology C).over V).covering_of_eq_top rfl

/-- Helper for Lemma 18.24.3: restricting a quasi-coherent module sheaf to a chaotic slice stays
quasi-coherent. -/
private theorem isQuasicoherent_over_of_isQuasicoherent
    (ℱ : Mod𝒪 𝒪) [ℱ.IsQuasicoherent] (V : C) :
    (ℱ.over V).IsQuasicoherent := by
  -- Proof comment: the ringed-site owner predicate is already packaged as a `Fact` over all
  -- restrictions, so the slice instance is available directly.
  infer_instance

/-- Helper for Lemma 18.24.3: the `ULift`-indexed family of all objects still covers the chaotic
site. -/
private theorem liftedIdentityFamily_coversTop :
    (⊥ : GrothendieckTopology C).CoversTop (fun X : ULift.{max u v} C ↦ X.down) := by
  intro W
  have hsieve : Sieve.ofObjects (fun X : ULift.{max u v} C ↦ X.down) W = ⊤ := by
    ext Y g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.mem_ofObjects_iff]
      exact ⟨ULift.up Y, ⟨𝟙 Y⟩⟩
  rw [hsieve]
  exact (⊥ : GrothendieckTopology C).covering_of_eq_top rfl

/-- Helper for Lemma 18.24.3: on the chaotic slice over `V`, quasi-coherence gives a global
presentation because any cover of the terminal object contains an object isomorphic to the
terminal object itself. -/
private theorem nonemptyPresentation_of_isQuasicoherent_over
    (ℱ : Mod𝒪 𝒪) (V : C) [h : (ℱ.over V).IsQuasicoherent] :
    Nonempty (ℱ.over V).Presentation := by
  -- Route correction: the remaining step is the explicit transport of a chosen chart
  -- presentation along `Over.mk (𝟙 V) ⟶ Xᵢ`, followed by transport across
  -- `Over.iteratedSliceEquiv (Over.mk (𝟙 V))`.
  -- TODO: add the terminal-slice presentation transport bridge described above and apply it to a
  -- chart from `IsQuasicoherent.nonempty_quasicoherentData`.
  sorry

/-- Helper for Lemma 18.24.3: a global presentation on the slice over `V` forces the tensor
comparison map along any arrow into `V` to be an isomorphism. -/
private theorem isIso_chaoticTensorSectionsMap_of_presentation
    (ℱ : Mod𝒪 𝒪) {U V : C} (f : U ⟶ V)
    [Nonempty (ℱ.over V).Presentation] :
    IsIso (chaoticTensorSectionsMap 𝒪 ℱ f) := by
  -- TODO: evaluate a chosen presentation of `ℱ.over V` both at `Over.mk (𝟙 V)` and at
  -- `Over.mk f`, then compare the resulting cokernel map with `chaoticTensorSectionsMap` via the
  -- extension/restriction adjunction and right exactness of extension of scalars.
  sorry

/-- Helper for Lemma 18.24.3: if all sectionwise tensor comparison maps into `V` are isomorphisms,
then the slice over `V` has a global presentation. -/
private theorem nonemptyPresentation_over_of_tensor_sections_map_isIso
    (ℱ : Mod𝒪 𝒪) (V : C)
    (hIso : ∀ ⦃U W : C⦄ (g : U ⟶ W), IsIso (chaoticTensorSectionsMap 𝒪 ℱ g)) :
    Nonempty (ℱ.over V).Presentation := by
  -- TODO: choose a presentation of the module of sections `ℱ(V)` and transport it along each
  -- `chaoticTensorSectionsMap 𝒪 ℱ g` to obtain a slice presentation of `ℱ.over V`.
  sorry

/-- Helper for Lemma 18.24.3: slice presentations on all objects assemble into one ordinary
quasi-coherent datum for `ℱ` on the chaotic site. -/
private theorem nonemptyQuasicoherentData_of_slicePresentations
    (ℱ : Mod𝒪 𝒪) (hpres : ∀ V : C, Nonempty (ℱ.over V).Presentation) :
    Nonempty ℱ.QuasicoherentData := by
  -- Proof comment: the identity family covers the chaotic site, so the slice presentations on all
  -- objects already satisfy the local-on-the-base criterion for ringed-site quasi-coherence.
  have hqc : ℱ.IsQuasicoherent := by
    rw [isQuasicoherent_iff_exists_cover_hasGlobalPresentation_over (J := (⊥ : GrothendieckTopology C))
      (𝒪 := 𝒪) (ℱ := ℱ)]
    refine ⟨ULift.{max u v} C, fun X ↦ X.down, liftedIdentityFamily_coversTop (C := C), ?_⟩
    intro X
    exact hpres X.down
  let _ : ℱ.IsQuasicoherent := hqc
  exact SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := ℱ)

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
@[stacks 0GZN]
theorem isQuasicoherent_iff_tensor_sections_map_isIso
    (ℱ : Mod𝒪 𝒪) :
    ℱ.IsQuasicoherent ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V),
        IsIso (chaoticTensorSectionsMap 𝒪 ℱ f) := by
  constructor
  · intro hℱ
    intro U V f
    -- Restrict quasi-coherence to the slice over `V`, then collapse the chaotic cover to a
    -- single global presentation on that slice.
    let _ : (ℱ.over V).IsQuasicoherent :=
      isQuasicoherent_over_of_isQuasicoherent (𝒪 := 𝒪) ℱ V
    let _ : Nonempty (ℱ.over V).Presentation :=
      nonemptyPresentation_of_isQuasicoherent_over (𝒪 := 𝒪) ℱ V
    -- A global presentation on the chaotic slice identifies sections over `U ⟶ V` with the
    -- expected extension of scalars from sections over `V`.
    exact isIso_chaoticTensorSectionsMap_of_presentation (𝒪 := 𝒪) ℱ f
  · intro h
    -- Route correction: the reverse direction first upgrades the comparison isomorphisms to
    -- global presentations on each slice, then packages those slice presentations as ordinary
    -- quasi-coherent data on `ℱ`.
    exact ⟨nonemptyQuasicoherentData_of_slicePresentations (𝒪 := 𝒪) ℱ
      (fun V ↦ nonemptyPresentation_over_of_tensor_sections_map_isIso (𝒪 := 𝒪) ℱ V h)⟩

end Quasicoherence

end SheafOfModules
