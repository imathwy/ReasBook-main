import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap06.Lemma_6_16_1
import stacks_proof.stacks_project.Chap17.Lemma_17_14_5.FreeSections
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks
import stacks_proof.stacks_project.Chap17.Definition_17_25_1
import stacks_proof.stacks_project.Chap17.Lemma_17_25_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

namespace SectionNonvanishingOpen

/- Lean parses bare `X_[s]` as indexed access, so the reusable owner-level notation is
parenthesized: `(X)_[s]`. In a local context with a fixed ambient variable `X`, one can then add
`local notation "X_[" s "]" => (X)_[s]` to recover the exact textbook surface. -/
set_option quotPrecheck false in
scoped macro:1075 X:term noWs "_[" s:term noWs "]" : term => do
  let sectionNonvanishingOpen :=
    Lean.mkIdent `AlgebraicGeometry.RingedSpace.sectionNonvanishingOpen
  `($sectionNonvanishingOpen $X _ $s)

end SectionNonvanishingOpen

open scoped SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦
    Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

/- Domain-style sampling for Lemma 17.25.10:
- primary domain: nonvanishing loci of global sections of invertible `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `RingedSpace.stalkModuleCat`,
  `SheafOfModules.over`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.pushforwardSections`,
  `Functor.IsEquivalence (tensorRight ℒ)`;
- best owner abstraction: the source-facing owners are the nonvanishing locus/open of a section,
  while the core canonical layer is the invertibility owner
  `SheafOfModules.RingedSite.IsInvertible` together with the bundled stalk owner
  `RingedSpace.stalkModuleCat`; the restricted section map
  `\mathcal O_U \to \mathcal L|_U` is derived bridge/view data built directly from the
  unit/sections adjunction on `ℒ.over U`;
- primitive data: a module `ℒ : ModX` and a global section `s : ℒ.sections`;
- derived API: openness of the nonvanishing locus, the associated open subset `(X)_[s]`, and the
  restricted section morphism on that open.

Source/core/bridge triage:
- `source-facing`: `sectionNonvanishingLocus` and `sectionNonvanishingOpen`;
- `core/canonical`: `IsInvertibleX ℒ`, `RingedSpace.stalkModuleCat`,
  `SheafOfModules.over`, and `SheafOfModules.unitHomEquiv`;
- `bridge/view`: `sectionOverHom`, the restricted section morphism on `ℒ.over U` obtained from
  `SheafOfModules.pushforwardSections`.
-/

/-- The morphism `\mathcal O_U \to \mathcal L|_U` induced by restricting a global section of
`\mathcal L` to an open subset `U`. -/
noncomputable abbrev sectionOverHom (ℒ : ModX) (s : ℒ.sections) (U : Opens X) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ℒ.over U :=
  (ℒ.over U).unitHomEquiv.symm
    (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U)) s)

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The source-defined nonvanishing locus of a section of an `\mathcal O_X`-module. -/
def sectionNonvanishingLocus (ℒ : ModX) (s : ℒ.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤))) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℒ x)))}

-- Proof sketch: for a point where the stalk germ of `s` is not in
-- `\mathfrak m_x \mathcal L_x`, invertibility identifies `\mathcal L_x` with a free rank-one
-- module over the local ring `\mathcal O_{X,x}`; Nakayama then shows that the germ of `s`
-- generates `\mathcal L_x`. Choosing local dual sections with evaluation `1` gives an open
-- neighbourhood basis inside the locus, hence the locus is open.
section Invertible

variable [monoidalModX : MonoidalCategory ModX]

local instance ringedSiteMonoidalCategory :
    MonoidalCategory (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  simpa using monoidalModX

/-- Helper for Lemma 17.25.10: the global module morphism corresponding to a section evaluates to
that section on the top open. -/
private theorem unitHomEquiv_symm_app_top_one
    (ℒ : ModX) (s : ℒ.sections) :
    ((ℒ.unitHomEquiv.symm s).val.app (op ⊤))
        (show ((SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op ⊤))
          from (1 : X.presheaf.obj (op ⊤))) =
      s.1 (op ⊤) := by
  -- Proof comment: `unitHomEquiv` is an equivalence between global module morphisms out of the
  -- unit sheaf and global sections, so evaluating after applying its inverse recovers `s`.
  have hs :
      SheafOfModules.unitHomEquiv ℒ (ℒ.unitHomEquiv.symm s) = s :=
    Equiv.apply_symm_apply ℒ.unitHomEquiv s
  exact congrArg (fun t : ℒ.sections ↦ t.1 (op ⊤)) hs

/-- Helper for Lemma 17.25.10: evaluating `unitHomEquiv` on the top open is evaluation of the
corresponding unit morphism on the distinguished section `1`. -/
private theorem unitHomEquiv_apply_top
    (ℒ : ModX)
    (φ : SheafOfModules.unit (RingedSpace.ringCatSheaf X) ⟶ ℒ) :
    (SheafOfModules.unitHomEquiv ℒ φ).1 (op ⊤) =
      (φ.val.app (op ⊤))
        (show ((SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op ⊤))
          from (1 : X.presheaf.obj (op ⊤))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the underlying unit morphism on the
  -- global unit section.
  rfl

/-- Helper for Lemma 17.25.10: a unit morphism sends the top-open unit germ to the stalk germ of
the associated global section. -/
private theorem unitHomStalkMap_top_eq_germ
    (ℒ : ModX)
    (φ : SheafOfModules.unit (RingedSpace.ringCatSheaf X) ⟶ ℒ)
    (x : X) :
    RingedSpace.moduleStalkMap x φ
      (TopCat.Presheaf.Γgerm
        (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf
        x
        (show ((SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj
            (op (⊤ : Opens X))) from
          (1 : X.presheaf.obj (op (⊤ : Opens X))))) =
      TopCat.Presheaf.Γgerm ℒ.val.presheaf x ((SheafOfModules.unitHomEquiv ℒ φ).1 (op ⊤)) := by
  have hx : x ∈ (⊤ : Opens X) := by
    simp
  -- Proof comment: rewrite the stalk map on the top open and then unfold the terminal evaluation
  -- formula for `unitHomEquiv`.
  simpa [TopCat.Presheaf.Γgerm, unitHomEquiv_apply_top] using
    (RingedSpace.moduleStalkMap_germ x φ ⊤ hx
      (show ((SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj
          (op (⊤ : Opens X))) from
        (1 : X.presheaf.obj (op (⊤ : Opens X)))))

/-- Helper for Lemma 17.25.10: the restricted structure sheaf on any open subset is free of rank
`1`. -/
private theorem unit_over_iso_free_singleton (U : Opens X) :
    Nonempty
      (((SheafOfModules.unit (RingedSpace.ringCatSheaf X) : ModX).over U) ≅
        (SheafOfModules.free.{u} (ULift.{u} (Fin 1)) :
          SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) := by
  let c : Cofan (fun _ : ULift.{u} (Fin 1) ↦
      (SheafOfModules.unit ((RingedSpace.ringCatSheaf X).over U) :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :=
    Cofan.mk
      (P := SheafOfModules.unit ((RingedSpace.ringCatSheaf X).over U))
      (fun _ ↦ 𝟙 _)
  let hc : IsColimit c :=
    mkCofanColimit c
      (fun t ↦ t.inj (default : ULift.{u} (Fin 1)))
      (fun t j ↦ by
        -- Proof comment: the one-point indexing type makes every leg of the cofan identical.
        simpa [c, Subsingleton.elim j (default : ULift.{u} (Fin 1))])
      (fun t m hm ↦ by
        -- Proof comment: the universal morphism is already determined by its unique component.
        simpa [c] using hm (default : ULift.{u} (Fin 1)))
  -- Proof comment: the unit sheaf over `U` is the coproduct of one copy of itself.
  exact ⟨IsColimit.coconePointUniqueUpToIso hc
    (SheafOfModules.isColimitFreeCofan
      (R := (RingedSpace.ringCatSheaf X).over U) (ULift.{u} (Fin 1)))⟩

/-- Helper for Lemma 17.25.10: evaluating `unitHomEquiv` at the terminal object of the slice
site recovers the terminal component of the underlying unit morphism. -/
private theorem unitHomEquiv_apply_terminal
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (φ : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M) :
    (SheafOfModules.unitHomEquiv M φ).1 (op (Over.mk (𝟙 U))) =
      (φ.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj
            (op (Over.mk (𝟙 U)))) from (1 : X.presheaf.obj (op U))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the unit morphism on the terminal
  -- section `1`.
  rfl

/-- Helper for Lemma 17.25.10: the stalkwise-isomorphism criterion for sheaves of modules can be
invoked after forgetting to sheaves of additive groups. -/
private theorem isIso_of_toSheaf_stalkwise_bijective
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Bijective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom))) :
    IsIso φ := by
  let ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj 𝒢 :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hψ : IsIso ψ := by
    -- Proof comment: the generic sheaf criterion upgrades stalkwise bijectivity to a global
    -- isomorphism after forgetting the module structure.
    exact (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (f := ψ)).2
      (fun x ↦ (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2 (hφ x))
  letI : IsIso ψ := hψ
  -- Proof comment: forgetting to additive sheaves reflects isomorphisms.
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf X.ringCatSheaf)

/-- Helper for Lemma 17.25.10: around every point, an invertible module becomes isomorphic to the
unit module on some open neighborhood. -/
private theorem existsUnitChartAround
    (ℒ : ModX) [IsInvertibleX ℒ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty (ℒ.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  let _ : SheafOfModules.IsFiniteLocallyFreeOfRank 1 ℒ :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible_of_stalk_isLocalRing
      (X := X) (fun x ↦ inferInstance) ℒ
  rcases SheafOfModules.IsFiniteLocallyFreeOfRank.exists_open_neighborhood_iso_free
      (ℱ := ℒ) (r := 1) x with ⟨U, hxU, hU⟩
  rcases hU with ⟨eU⟩
  rcases unit_over_iso_free_singleton (X := X) U with ⟨eUnit⟩
  -- Proof comment: compose the local rank-one free chart with the standard identification of the
  -- rank-one free module and the unit module on `U`.
  exact ⟨U, hxU, ⟨eU ≪≫ eUnit.symm⟩⟩

/-- Helper for Lemma 17.25.10: a unit chart on `U` identifies every stalk over `U` with the stalk
ring. -/
private noncomputable def unitChartStalkLinearEquiv
    (ℒ : ModX) {U : Opens X}
    (eU : ℒ.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) :
    RingedSpace.stalkModuleCat ℒ x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let XU : RingedSpace := X.restrict U.isOpenEmbedding
  let j : XU ⟶ X := X.ofRestrict U.isOpenEmbedding
  let xU : XU := ⟨x, hx⟩
  let eOver :
      ((RingedSpace.Hom.pullback j).obj ℒ) ≅
        (SheafOfModules.unit XU.ringCatSheaf : XU.Modules) := by
    -- Proof comment: rewrite the slice restriction `ℒ.over U` as the actual pullback to `X|_U`.
    simpa [SheafOfModules.over, RingedSpace.Hom.pullback] using eU
  -- Proof comment: first transport the chart to the restricted ringed space, then pass to stalks
  -- and finish with the canonical identification of the unit-module stalk and the stalk ring.
  exact
    ((RingedSpace.Hom.pullbackStalkIso j ℒ xU).symm ≪≫
        (RingedSpace.stalkModuleFunctor (X := XU) xU).mapIso eOver).toLinearEquiv.trans
      (RingedSpace.unitStalkLinearEquiv (X := XU) xU)

/-- Helper for Lemma 17.25.10: the global germ of a section agrees with the germ of its
restriction to any open neighborhood of the point. -/
private theorem gammaGerm_eq_restriction_germ
    (ℒ : ModX) (s : ℒ.sections) {U : Opens X} {x : X} (hx : x ∈ U) :
    TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤)) =
      TopCat.Presheaf.germ ℒ.val.presheaf U x hx (s.1 (op U)) := by
  let i : U ⟶ (⊤ : Opens X) := homOfLE le_top
  -- Proof comment: this is the standard germ/restriction compatibility for a global section.
  simpa using
    (TopCat.Presheaf.Γgerm_res_apply
      ℒ.val.presheaf (i := i) (x := x) (hx := hx) (s := s.1 (op ⊤))).symm

/-- Helper for Lemma 17.25.10: evaluating `sectionOverHom` on the terminal slice object recovers
the ordinary restriction of the original global section. -/
private theorem sectionOverHom_apply_terminal
    (ℒ : ModX) (s : ℒ.sections) (U : Opens X) :
    ((sectionOverHom X ℒ s U).val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj
            (op (Over.mk (𝟙 U)))) from (1 : X.presheaf.obj (op U))) =
      s.1 (op U) := by
  -- Proof comment: `sectionOverHom` is defined by inverting `unitHomEquiv`, so applying
  -- `unitHomEquiv` again returns the pushed-forward section, whose terminal component is the
  -- restriction of `s` to `U`.
  rw [← unitHomEquiv_apply_terminal (X := X) (M := ℒ.over U)
    (φ := sectionOverHom X ℒ s U)]
  rw [sectionOverHom, Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 17.25.10: in a local unit chart, the restricted section is represented by its
coefficient section on the ambient open `U`. -/
private noncomputable abbrev chartCoefficient
    (ℒ : ModX) (s : ℒ.sections) {U : Opens X}
    (eU : ℒ.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    X.presheaf.obj (op U) :=
  (SheafOfModules.unitHomEquiv _ (eU.hom ≫ sectionOverHom X ℒ s U)).1 (op (Over.mk (𝟙 U)))

/-- Helper for Lemma 17.25.10: a linear equivalence to the base ring identifies
`𝔪 • ⊤` with the maximal ideal itself. -/
private theorem mem_maximalIdeal_smulTop_iff_apply_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type u} [AddCommMonoid M] [Module A M]
    (e : M ≃ₗ[A] A) (m : M) :
    m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      e m ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro hm
    rw [Submodule.mem_smul_top_iff] at hm
    rcases hm with ⟨y, hy, rfl⟩
    simpa [e.map_smul, smul_eq_mul] using
      Ideal.mul_mem_right (IsLocalRing.maximalIdeal A) (e y) hy
  · intro hm
    rw [Submodule.mem_smul_top_iff]
    refine ⟨e.symm (1 : A), hm, ?_⟩
    calc
      (e m) • e.symm (1 : A) = e.symm ((e m) • (1 : A)) := by
        symm
        exact e.symm.map_smul (e m) (1 : A)
      _ = e.symm (e m) := by simp
      _ = m := by simp

/-- Helper for Lemma 17.25.10: under a unit chart, the stalk germ of the global section becomes
the germ of the coefficient section in the stalk ring. -/
private theorem unitChartStalkLinearEquiv_germ_eq_chartCoefficient
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections)
    {U : Opens X} (eU : ℒ.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) :
    unitChartStalkLinearEquiv (X := X) ℒ eU x hx
        (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤))) =
      X.presheaf.germ U x hx (chartCoefficient (X := X) ℒ s eU) := by
  -- Proof comment: first rewrite the global germ as the germ of the restricted section on `U`,
  -- then transport that germ through the open-immersion stalk comparison and the unit chart.
  -- TODO: specialize `TopCat.Sheaf.stalkPullbackIso_hom_naturality` to
  -- `sectionOverHom X ℒ s U`, rewrite the transported unit germ by
  -- `sectionOverHom_apply_terminal`, and finish with `SheafOfModules.unitStalkLinearMap_germ`.
  sorry

/-- Lemma 17.25.10: for an invertible `\mathcal O_X`-module `\mathcal L` and a global section
`s`, the set of points where the germ of `s` is not contained in
`\mathfrak m_x \mathcal L_x` is open. -/
@[stacks 01CY]
theorem sectionNonvanishingLocus_isOpen (ℒ : ModX)
    [IsInvertibleX ℒ]
    (s : ℒ.sections) :
    IsOpen (sectionNonvanishingLocus X ℒ s) := by
  -- Route correction: the old route drifted into a broader restriction API. The stable route is
  -- to work entirely with `sectionOverHom`, first rewriting the global germ by
  -- `gammaGerm_eq_restriction_germ`, then transporting that restricted germ through
  -- `RingedSpace.Hom.pullbackStalkIso`, and finally normalizing it in a unit chart to a basic-open
  -- coefficient germ.
  refine isOpen_iff_mem_nhds.2 ?_
  intro x hx
  rcases existsUnitChartAround (X := X) ℒ x with ⟨U, hxU, ⟨eU⟩⟩
  let fU : X.presheaf.obj (op U) := chartCoefficient (X := X) ℒ s eU
  have hcoeff_not_mem :
      X.presheaf.germ U x hxU fU ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro hcoeff_mem
    have hs_mem :
        TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℒ x)) := by
      rw [mem_maximalIdeal_smulTop_iff_apply_mem_maximalIdeal
        (e := unitChartStalkLinearEquiv (X := X) ℒ eU x hxU)]
      simpa [fU] using hcoeff_mem
    exact hx hs_mem
  have hcoeff_unit : IsUnit (X.presheaf.germ U x hxU fU) :=
    IsLocalRing.notMem_maximalIdeal.mp hcoeff_not_mem
  refine ⟨X.basicOpen fU, (X.mem_basicOpen fU x hxU).2 hcoeff_unit, ?_⟩
  intro y hy
  have hyU : y ∈ U := (X.basicOpen_le fU) hy
  have hcoeff_unit_y : IsUnit (X.presheaf.germ U y hyU fU) :=
    (X.mem_basicOpen fU y hyU).1 hy
  have hs_not_mem :
      TopCat.Presheaf.Γgerm ℒ.val.presheaf y (s.1 (op ⊤)) ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
          (⊤ : Submodule (X.presheaf.stalk y) (RingedSpace.stalkModuleCat ℒ y)) := by
    intro hs_mem
    have hcoeff_mem :
        X.presheaf.germ U y hyU fU ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
      rw [← mem_maximalIdeal_smulTop_iff_apply_mem_maximalIdeal
        (e := unitChartStalkLinearEquiv (X := X) ℒ eU y hyU)]
      simpa [fU] using hs_mem
    exact (IsLocalRing.notMem_maximalIdeal.mpr hcoeff_unit_y) hcoeff_mem
  exact hs_not_mem

/-- The open subset cut out by the nonvanishing locus of a section of an invertible
`\mathcal O_X`-module. -/
def sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertibleX ℒ]
    (s : ℒ.sections) : Opens X :=
  ⟨sectionNonvanishingLocus X ℒ s, sectionNonvanishingLocus_isOpen X ℒ s⟩

-- Proof sketch: on the open locus from the previous theorem, each stalk germ of `s` is a basis
-- vector of the rank-one free stalk `\mathcal L_x`. A morphism of sheaves of modules is an
-- isomorphism iff it is an isomorphism on all stalks, so the restricted map
-- `\mathcal O_{(X)_[s]} \to \mathcal L|_{(X)_[s]}` induced by `s` is an isomorphism.
/-- On the nonvanishing open `(X)_[s]`, the restricted section induces an isomorphism
`\mathcal O_{(X)_[s]} \cong \mathcal L|_{(X)_[s]}`. -/
instance isIso_restrictedSection_sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertibleX ℒ]
    (s : ℒ.sections) :
    IsIso (sectionOverHom X ℒ s ((X)_[s])) := by
  -- Route correction: after the openness proof is normalized via `sectionOverHom`, the remaining
  -- closing step should stay stalkwise. At each `x : (X)_[s]`, transport the restricted germ
  -- through `RingedSpace.Hom.pullbackStalkIso`, rewrite it to the coefficient germ in a unit
  -- chart, and identify the stalk map with multiplication by that unit.
  -- TODO: package the stalk computation above into a bijectivity statement and conclude with
  -- `isIso_of_toSheaf_stalkwise_bijective`.
  sorry
end Invertible

end Nonvanishing

end AlgebraicGeometry.RingedSpace
