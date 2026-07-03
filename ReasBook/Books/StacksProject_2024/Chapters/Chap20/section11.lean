import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_11_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingAddPresheaf
    {X : RingedSpace.{u}} (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℐ).1

/-- The additive group of sections of an `\mathcal O_X`-module over an open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleSections
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) : AddCommGrpCat.{u} :=
  ((CategoryTheory.sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)).obj
    ((SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℐ)

/-- The Čech cohomology of the underlying additive presheaf of an `\mathcal O_X`-module with
respect to an indexed family of opens. -/
private noncomputable abbrev ringedSpaceModuleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) : AddCommGrpCat.{u} :=
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := inferInstance
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((CategoryTheory.cechComplexFunctor 𝒰).obj (ringedSpaceModuleUnderlyingAddPresheaf ℐ))

-- Proof sketch: the cover condition `iSup 𝒰 = U` identifies the union of the members of the cover
-- with `U`, and degree-zero Čech cohomology of the underlying additive sheaf computes the equalizer
-- of the sheaf gluing diagram. For a sheaf this equalizer is exactly the additive group of sections
-- on `U`.
/-- Lemma 20.11.1 (1): if `\mathcal I` is an injective `\mathcal O_X`-module and `\mathcal U`
is an open covering of `U`, then the degree-zero Čech cohomology of `\mathcal I` with respect to
`\mathcal U` identifies with the section group `\mathcal I(U)`. -/
theorem cech_cohomology_zero_iso_sections_of_injective
    {X : RingedSpace.{u}} {ι : Type u} (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (hℐ : Injective ℐ) :
    Nonempty (ringedSpaceModuleCechCohomology 𝒰 ℐ 0 ≅
      ringedSpaceModuleSections U ℐ) := sorry

-- Proof sketch: an injective `\mathcal O_X`-module is injective in the ambient presheaf-module
-- category, so Lemma `20.10.5` applies to the Čech cohomology `δ`-functor of the covering. The
-- higher right derived functors of degree-zero sections vanish on injective objects, hence every
-- positive Čech cohomology group is zero.
/-- Lemma 20.11.1 (2): if `\mathcal I` is an injective `\mathcal O_X`-module and `\mathcal U`
is an open covering of `U`, then the positive-degree Čech cohomology of `\mathcal I` with respect
to `\mathcal U` vanishes. -/
theorem cech_cohomology_isZero_of_injective_succ
    {X : RingedSpace.{u}} {ι : Type u} (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier)
    (h𝒰 : iSup 𝒰 = U) (ℐ : SheafOfModules (ringedSpaceRingCatSheaf X)) (hℐ : Injective ℐ)
    (p : ℕ) :
    IsZero (ringedSpaceModuleCechCohomology 𝒰 ℐ (p + 1)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_2 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The degree-`p` Čech cohomology functor on `\mathcal O_X`-modules for an indexed family of
opens `\mathcal U`. -/
private noncomputable abbrev ringedSpaceModuleCechCohomologyFunctor
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := inferInstance
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    CategoryTheory.cechComplexFunctor 𝒰 ⋙
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p)

/-- The degree-`p` sheaf cohomology functor on `\mathcal O_X`-modules over a fixed open
subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The degree-`p` Čech cohomology group of an `\mathcal O_X`-module for the indexed family of
opens `\mathcal U`. -/
private noncomputable abbrev ringedSpaceModuleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) : AddCommGrpCat.{u} :=
  (ringedSpaceModuleCechCohomologyFunctor 𝒰 p).obj ℱ

/-- The degree-`p` sheaf cohomology group of an `\mathcal O_X`-module over the open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpen
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) :
    AddCommGrpCat.{u} :=
  (ringedSpaceModuleCohomologyAtOpenFunctor X U p).obj ℱ

-- Proof sketch: choose an injective resolution `ℱ ⟶ ℐ•`, form the double complex
-- `\check{\mathcal C}^•(\mathcal U, \mathcal I^•)`, and compare both `\Gamma(U, \mathcal I^•)`
-- and `\check{\mathcal C}^•(\mathcal U, \mathcal F)` with its total complex. Lemma `20.11.1`
-- identifies each row with a resolution of the corresponding section group, so Lemma `12.25.4`
-- makes the rowwise comparison a quasi-isomorphism. Passing to cohomology yields a natural
-- transformation `\check H^p(\mathcal U, -) → H^p(U, -)`.
/-- Lemma 20.11.2: if `\mathcal U : U = \bigcup_{i \in I} U_i` is an open covering of `U` in a
ringed space `X`, then for every degree `p` there is a natural transformation from the degree-`p`
Čech cohomology functor `\check H^p(\mathcal U, -)` on `\mathcal O_X`-modules to the degree-`p`
sheaf cohomology functor `H^p(U, -)`. -/
theorem cech_cohomology_to_sheaf_cohomology_natTrans
    {X : RingedSpace.{u}} {ι : Type u}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    iSup 𝒰 = U →
      Nonempty (ringedSpaceModuleCechCohomologyFunctor 𝒰 p ⟶
        ringedSpaceModuleCohomologyAtOpenFunctor X U p) := sorry

-- Proof sketch: evaluate the natural transformation of the previous theorem at the fixed
-- `\mathcal O_X`-module `\mathcal F`; the resulting component is the canonical comparison map from
-- the `p`th Čech cohomology group of the cover to the `p`th sheaf cohomology group on `U`.
/-- The comparison map from Čech cohomology to sheaf cohomology for a fixed
`\mathcal O_X`-module. -/
theorem cech_cohomology_to_sheaf_cohomology_map
    {X : RingedSpace.{u}} {ι : Type u}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (p : ℕ)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    iSup 𝒰 = U →
      Nonempty (ringedSpaceModuleCechCohomology 𝒰 ℱ p ⟶
        ringedSpaceModuleCohomologyAtOpen U ℱ p) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_3 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace TopCat
open scoped BigOperators

noncomputable section

universe u uι

section

variable {X : TopCat.{u}} {ι : Type uι}

/-- The intersection of the opens indexed by a finite Čech tuple. -/
def cech_intersection (U : ι → Opens X) {n : ℕ} (I : Fin n → ι) : Opens X :=
  iInf fun j ↦ U (I j)

-- Proof sketch: the full intersection is contained in every partial intersection obtained by
-- omitting one index, since membership in the former gives membership in each constituent open.
/-- Omitting one index from a Čech intersection enlarges the open set. -/
theorem cech_intersection_le_succAboveEmb (U : ι → Opens X) {n : ℕ}
    (I : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    cech_intersection U I ≤ cech_intersection U (I ∘ j.succAboveEmb) := sorry

/-- The degree-`p` Čech cochains of a presheaf on a family of opens. -/
abbrev cech_cochains (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :=
  ∀ I : Fin (p + 1) → ι, F.obj (op (cech_intersection U I))

/-- The restriction map from a partial Čech intersection to the full intersection. -/
def cech_restriction (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) {n : ℕ}
    (I : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    F.obj (op (cech_intersection U (I ∘ j.succAboveEmb))) ⟶
      F.obj (op (cech_intersection U I)) :=
  F.map (homOfLE (cech_intersection_le_succAboveEmb U I j)).op

/-- The underlying function of the Čech coboundary in degree `p`. -/
def cech_differential_fun (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    cech_cochains U F p → cech_cochains U F (p + 1) :=
  fun s I ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) • (cech_restriction U F I j) (s (I ∘ j.succAboveEmb))

-- Proof sketch: evaluate both sides on an index tuple and use additivity of each restriction map
-- together with additivity of the finite sum in the target abelian group.
/-- The Čech coboundary is additive on cochains. -/
theorem cech_differential_fun_map_add (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat)
    (p : ℕ) (s t : cech_cochains U F p) :
    cech_differential_fun U F p (s + t) =
      cech_differential_fun U F p s + cech_differential_fun U F p t := sorry

/-- The Čech coboundary in degree `p` as a morphism of abelian groups. -/
def cech_differential (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    AddCommGrpCat.of (cech_cochains U F p) ⟶ AddCommGrpCat.of (cech_cochains U F (p + 1)) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (cech_differential_fun U F p)
      (cech_differential_fun_map_add U F p)

-- Proof sketch: compare the contribution of a double omission `(a, b)` with the contribution of
-- the transposed omission `(b, a)`; the alternating signs make these terms cancel pairwise.
/-- Two successive Čech coboundaries compose to zero. -/
theorem cech_differential_sq (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (p : ℕ) :
    cech_differential U F p ≫ cech_differential U F (p + 1) = 0 := sorry

/-- The Čech complex of an abelian presheaf on the indexed family of opens `U`. -/
noncomputable def cech_complex (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (fun p ↦ AddCommGrpCat.of (cech_cochains U F p))
    (cech_differential U F) (cech_differential_sq U F)

/-- The degree-`i` Čech cohomology group of the covering `U` with coefficients in `F`. -/
noncomputable abbrev cech_cohomology (U : ι → Opens X) (F : X.Presheaf AddCommGrpCat) (i : ℕ) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
    (cech_complex U F)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u + 1} (X.Sheaf AddCommGrpCat.{u})]

-- Proof sketch: represent a torsor class trivial on the cover by local sections on each `U i`,
-- take their pairwise differences to obtain a Čech `1`-cocycle, and check that changing the local
-- sections alters the cocycle by a coboundary. Conversely, glue the trivial torsors on the cover
-- using a Čech cocycle; the quotient condition defining `IsTrivialOnCover` makes the resulting
-- class independent of choices. This is exactly the subset identified inside `H¹(X, ℋ)` via the
-- torsor classification of Lemma `20.4.3`.
/-- Lemma 20.11.3: via the torsor classification of Lemma 20.4.3, the degree-one Čech cohomology
of the covering `U` is identified with the isomorphism classes of `ℋ`-torsors on `X` whose
restriction to every `U i` is trivial, equivalently whose underlying sheaf admits a section over
every `U i`. -/
theorem cech_H1_equiv_torsorIsoClass_isTrivialOnCover (U : ι → Opens X)
    (ℋ : X.Sheaf AddCommGrpCat.{u}) :
    Nonempty ((cech_cohomology U ℋ.presheaf 1) ≃
      { c : CategoryTheory.AbelianSheafTorsor.IsoClasses ℋ // c.IsTrivialOnCover U }) := sorry

end

/-! ### Lemma_20_11_4 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.11.4:
- primary domain: right derived functors of the canonical inclusion
  `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` and the cohomology presheaf of the underlying abelian
  sheaf;
- sampled owner declarations:
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.forget`,
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`;
- best owner abstraction: the ringed-site theorem
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`, specialized to the structure
  sheaf `(RingedSpace.ringCatSheaf X)`, together with the canonical instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`;
- primitive data: a coefficient sheaf `𝒪 : Sheaf J RingCat`, a sheaf of `𝒪`-modules `ℱ`, and a
  cohomological degree `p`;
- derived API here: the ringed-space specialization `𝒪 := (RingedSpace.ringCatSheaf X)`, together with the
  underlying additive presheaf and sheaf obtained from `PresheafOfModules.toPresheaf` and
  `SheafOfModules.toSheaf`.

Source/core/bridge triage:
- `source-facing`: the ringed-space identification between the underlying additive presheaf of the
  derived inclusion and the cohomology presheaf `U ↦ H^p(U, \mathcal F)`;
- `core/canonical`: `SheafOfModules.forget`, the anonymous instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`, and
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`;
- `bridge/view`: specializing the coefficient sheaf in the canonical ringed-site statement to the
  structure sheaf `(RingedSpace.ringCatSheaf X)`.

This item adds no new owner-level mathematics beyond that canonical ringed-site statement, so the
refined file should recall the owner theorem directly rather than keep a duplicate ringed-space
wrapper.
-/

/- Lemma 20.11.4 is the ringed-space specialization of the canonical ringed-site comparison
between the `p`-th right derived object of `Mod(\mathcal O) ⥤ PMod(\mathcal O)` and the
cohomology presheaf of the underlying additive sheaf. -/
recall ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (F : (RingedSpace.Modules X)) (p : ℕ)

/- Companion recall: the inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` is left exact in the
canonical owner form `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`. -/
#synth PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))

/- Source-facing specialization: for a ringed space `X`, an `\mathcal O_X`-module `\mathcal F`,
and a degree `p`, the canonical owner theorem specializes exactly to the comparison stated in
Lemma 20.11.4. -/
#check (ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf (RingedSpace.ringCatSheaf X) F p :
  IsIsomorphic
    ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj
      (((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).rightDerived p).obj F))
    (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj F).cohomologyPresheaf p))

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The canonical inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` is additive. -/
instance sheafOfModules_forget_additive (X : RingedSpace.{u}) :
    (SheafOfModules.forget (RingedSpace.ringCatSheaf X)).Additive := by
  infer_instance

/-- The sections functor of `\mathcal O_X`-modules over an open subset `U`. -/
abbrev moduleSectionsEvaluation (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

/-- The sections functor on `U` is additive. -/
instance moduleSectionsEvaluation_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsEvaluation X U).Additive where
  map_add := by
    intro M N f g
    change
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
          ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map (f + g)) =
        (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map f) +
          (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map
            ((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map g)
    rw [(SheafOfModules.forget (RingedSpace.ringCatSheaf X)).map_add,
      (PresheafOfModules.evaluation (RingedSpace.ringCatSheaf X).obj (op U)).map_add]

/-- The `E_2^{p,q}` term in the Čech-to-cohomology spectral sequence for an
`\mathcal O_X`-module `ℱ`, computed as Čech cohomology of the `q`-th cohomology presheaf. -/
abbrev moduleCechToCohomologyPageTwoTerm
    (ℱ : (RingedSpace.Modules X)) (p q : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  ((ringedSpaceCechCohomologyDegree U 𝒰 p).obj.obj
    (((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).rightDerived q).obj ℱ))

/-- The degree-`n` cohomology of an `\mathcal O_X`-module on the open subset `U`, viewed as the
`n`-th right derived functor of sections on `U`. -/
abbrev moduleCohomologyAtOpen
    (ℱ : (RingedSpace.Modules X)) (n : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  ((moduleSectionsEvaluation X U).rightDerived n).obj ℱ

/-- A functorial package for the spectral sequence computing the cohomology of an
`\mathcal O_X`-module on `U` from the Čech cohomology of its cohomology presheaves with respect
to the cover `𝒰`. -/
structure CechToModuleCohomologySpectralSequence
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    (U : Opens X.carrier) [HasFiniteProducts (Over U)] {ι : Type u} (𝒰 : ι → Over U)
    [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially
  in the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    (RingedSpace.Modules X) ⥤
      E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} (X.presheaf.obj (op U)))
  /-- The `E₂`-page is the Čech cohomology of the cohomology presheaf
  `\underline{H}^q(\mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p q
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment :
    (RingedSpace.Modules X) → ℕ →
      ModuleCat.{u} (X.presheaf.obj (op U))
  /-- The abutment identifies with the degree-`n` module cohomology of `ℱ` on `U`. -/
  targetIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (n : ℕ),
      abutment ℱ n ≅ moduleCohomologyAtOpen U ℱ n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` with degree-zero Čech cohomology for the
-- cover `𝒰`. Lemma `20.9.2` identifies degree-zero Čech cohomology with sections on `U`, Lemma
-- `20.11.1` shows that injective `\mathcal O_X`-modules are Čech-acyclic for the cover, and
-- Lemmas `20.10.5` and `20.11.4` identify the `E₂`-page with Čech cohomology of the cohomology
-- presheaves `\underline{H}^q(\mathcal F)`. Naturality of the Grothendieck construction gives
-- functoriality in `\mathcal F`.
/-- Lemma 20.11.5: for a ringed space `X`, an open subset `U`, and an open covering `𝒰` of `U`,
there is a cohomological spectral sequence functorial in an `\mathcal O_X`-module `\mathcal F`
whose `E_2^{p,q}`-term is `\check H^p(\mathcal U, \underline{H}^q(\mathcal F))` and whose
abutment is the degree-`p + q` cohomology of `\mathcal F` on `U`. -/
theorem exists_cechToModuleCohomologySpectralSequence :
    Nonempty (CechToModuleCohomologySpectralSequence X U 𝒰) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The degree-`p` Čech cohomology of an `\mathcal O_X`-module for the cover `𝒰`, viewed as the
`q = 0` row of the Čech-to-cohomology spectral sequence. -/
abbrev moduleCechCohomologyAtCover
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0

-- Proof sketch: unfold `moduleCechCohomologyAtCover`; it is defined to be the `q = 0` term
-- `moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0`.
/-- The Čech cohomology abbreviation is the `q = 0` page-two term of the spectral sequence from
Lemma `20.11.5`. -/
theorem moduleCechCohomologyAtCover_def
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    moduleCechCohomologyAtCover U 𝒰 ℱ p =
      moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0 := sorry

-- Proof sketch: apply the spectral sequence of Lemma `20.11.5` to `ℱ`. The hypothesis implies
-- that the higher cohomology presheaves vanish on every finite intersection of the cover, so the
-- `E₂`-page is concentrated on the `q = 0` row. Hence the spectral sequence degenerates at `E₂`,
-- and the edge map identifies the `p`-th Čech cohomology with the degree-`p` cohomology on `U`.
/-- Lemma 20.11.6: if every positive-degree cohomology group of `\mathcal F` vanishes on every
finite intersection of the members of the open covering `𝒰` of `U`, then the degree-`p` Čech
cohomology of `𝒰` with coefficients in `\mathcal F` is canonically isomorphic to the degree-`p`
cohomology of `\mathcal F` on `U` as an `\mathcal O_X(U)`-module. -/
theorem moduleCechCohomologyAtCover_iso_moduleCohomologyAtOpen_of_acyclic_on_intersections
    (h𝒰 : iSup (fun i ↦ (𝒰 i).left) = U)
    (ℱ : (RingedSpace.Modules X))
    (hacyclic : ∀ q : ℕ, 0 < q → ∀ n : ℕ, ∀ σ : Fin (n + 1) → ι,
      IsZero (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' q
        (⨅ a, (𝒰 (σ a)).left)))
    (p : ℕ) :
    IsIsomorphic (moduleCechCohomologyAtCover U 𝒰 ℱ p)
      (moduleCohomologyAtOpen U ℱ p) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_7 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 20.11.7:
- primary domain: Čech cohomology of sheaves of modules on a ringed space, and evaluation of a
  short exact sequence on an open subset;
- inspected owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleCechCohomology`,
  `IsRefinement`,
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.evaluation`;
- best owner abstraction: the degree-one vanishing hypothesis should be expressed directly using
  the chapter owner `moduleCechCohomology`, while the map on sections should be the canonical
  evaluation map of `S.g`; the only refinement data should be the primitive witness
  `IsRefinement 𝒱 cover refine`, not a parallel wrapper structure;
- primitive data: a short complex `S : ShortComplex (RingedSpace.Modules X)`, an open subset `U`, an
  indexed cover `𝒱`, and a refining cover together with a map `refine : κ → ι` witnessing
  `IsRefinement 𝒱 cover refine`;
- derived API: the vanishing of `moduleCechCohomology cover S.X₁ 1` and the surjectivity of
  `((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map S.g)`.

Source/core/bridge triage:
- `source-facing`: the cofinal refinement hypothesis and the surjectivity conclusion of
  Lemma 20.11.7;
- `core/canonical`: `moduleCechCohomology`, `(RingedSpace.Modules X)`, `(RingedSpace.ringCatSheaf X)`, and
  `SheafOfModules.evaluation`;
- `bridge/view`: the refinement witness `IsRefinement`, and the underlying additive presheaf
  functor already absorbed inside `moduleCechCohomology`.

The previous file packaged the refinement witness as a separate public `structure`. That witness is
not a new mathematical owner, only existential source data, so the refined file keeps it directly
inside the source-facing hypothesis and reuses the chapter owners for the actual cohomology and
evaluation constructions.
-/

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Every covering of `U` admits a refinement with vanishing first Čech cohomology in `S.X₁`. -/
abbrev HasCofinalCechH1VanishingRefinement
    (S : ShortComplex (RingedSpace.Modules X)) (U : Opens X.carrier) : Prop :=
  ∀ {ι : Type u} (𝒱 : ι → Opens X.carrier), iSup 𝒱 = U →
    ∃ (κ : Type u) (cover : κ → Opens X.carrier) (refine : κ → ι),
      iSup cover = U ∧
        IsRefinement 𝒱 cover refine ∧
        IsZero (moduleCechCohomology cover S.X₁ 1)

-- Proof sketch: start with a section of `S.X₃(U)` and choose an open cover on which it lifts
-- locally through `S.g`. Refine this cover to one with vanishing first Čech cohomology for
-- `S.X₁`; the differences of the local lifts form a Čech `1`-cocycle in `S.X₁`, hence a
-- coboundary. Correct the local lifts by the corresponding `0`-cochain and glue the adjusted
-- sections to obtain a global lift in `S.X₂(U)`.
/-- Lemma 20.11.7: for a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
every open covering of `U` admits a refinement whose first Čech cohomology with coefficients in
the left term vanishes, then every section of the quotient over `U` lifts to the middle term. -/
theorem module_sections_surjective_of_shortExact_of_cofinal_cechH1_zero
    (S : ShortComplex (RingedSpace.Modules X)) (hS : S.ShortExact) (U : Opens X.carrier)
    (hcech : HasCofinalCechH1VanishingRefinement S U) :
    Function.Surjective ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map S.g) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_8 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits, so Čech complexes of open covers are
available. -/
instance opensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
instance opensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

/-- An `\mathcal O_X`-module has vanishing higher Čech cohomology on every open covering when the
positive-degree Čech cohomology of its underlying additive presheaf vanishes for every cover of
every open subset. -/
def HasVanishingHigherCechOnOpenCoverings
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) : Prop :=
  ∀ {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier), iSup 𝒰 = U →
    ∀ p : ℕ, 0 < p →
      IsZero
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
          ((cechComplexFunctor 𝒰).obj (moduleUnderlyingPresheaf ℱ)))

-- Proof sketch: this is the defining expansion of
-- `HasVanishingHigherCechOnOpenCoverings`; apply the hypothesis to the chosen cover `𝒰`.
/-- Unfolding the higher Čech-vanishing hypothesis on a chosen cover yields vanishing of the
corresponding positive-degree Čech cohomology group. -/
theorem hasVanishingHigherCechOnOpenCoverings_apply
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    {U : Opens X.carrier} {ι : Type u} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
        ((cechComplexFunctor 𝒰).obj (moduleUnderlyingPresheaf ℱ))) := sorry

-- Proof sketch: embed `ℱ` into an injective `\mathcal O_X`-module `ℐ`, let `ℚ := ℐ/ℱ`, and use
-- Lemmas `20.11.1`, `20.11.7`, `20.10.2`, and `13.20.4` to propagate the higher Čech-vanishing
-- hypothesis from `ℱ` to `ℚ`. The long exact cohomology sequence of
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0` then gives the vanishing of `H^p(U, ℱ)` for every `p > 0` by induction.
/-- Lemma 20.11.8: if an `\mathcal O_X`-module has vanishing higher Čech cohomology for every
open covering of every open subset of `X`, then every higher sheaf cohomology group
`H^p(U, \mathcal F)` with `p > 0` is zero. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : (RingedSpace.Modules X)) (hℱ : HasVanishingHigherCechOnOpenCoverings ℱ)
    (U : Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ℱ).H' p U) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_9 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying additive sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits, so Čech complexes of open covers are
available. -/
private instance basisOpensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
private instance basisOpensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

/-- A cover of a basis open by basis opens whose finite intersections remain in the basis. -/
structure BasisStableOpenCover {X : RingedSpace.{u}}
    (B : Set (Opens X.carrier)) (U : Opens X.carrier) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The covering family of opens. -/
  cover : ι → Opens X.carrier
  /-- The covering family covers `U`. -/
  iSup_eq : iSup cover = U
  /-- Each member of the covering family belongs to the basis `B`. -/
  mem_basis : ∀ i, cover i ∈ B
  /-- Every finite intersection of members of the covering family still belongs to the basis. -/
  intersections_mem_basis : ∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (cover ∘ σ) ∈ B

namespace BasisStableOpenCover

/-- A basis-stable open cover refines another indexed open cover if each of its members is
contained in one member of the target cover. -/
def Refines {X : RingedSpace.{u}} {B : Set (Opens X.carrier)} {U : Opens X.carrier}
    (𝒰 : BasisStableOpenCover B U) {κ : Type u} (𝒱 : κ → Opens X.carrier) : Prop :=
  ∃ refine : 𝒰.ι → κ, ∀ i, 𝒰.cover i ≤ 𝒱 (refine i)

end BasisStableOpenCover

/-- An `\mathcal O_X`-module has a cofinal system of basis-stable coverings on which all positive
Čech cohomology groups vanish. -/
def HasCofinalBasisCechAcyclicCoverings
    {X : RingedSpace.{u}} (B : Set (Opens X.carrier))
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B →
    ∀ {κ : Type u} (𝒱 : κ → Opens X.carrier), iSup 𝒱 = U →
      ∃ 𝒰 : BasisStableOpenCover B U,
        BasisStableOpenCover.Refines 𝒰 𝒱 ∧
          ∀ p : ℕ, 0 < p →
            IsZero
              ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
                ((cechComplexFunctor 𝒰.cover).obj (moduleUnderlyingPresheaf ℱ)))

-- Proof sketch: this is exactly the defining content of
-- `HasCofinalBasisCechAcyclicCoverings`, evaluated at the basis open `U` and the cover `𝒱`.
/-- Unfolding the cofinal basis-cover hypothesis produces a refining basis-stable cover with
vanishing positive Čech cohomology. -/
theorem hasCofinalBasisCechAcyclicCoverings_apply
    {X : RingedSpace.{u}} {B : Set (Opens X.carrier)}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X))
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    {U : Opens X.carrier} (hU : U ∈ B)
    {κ : Type u} (𝒱 : κ → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ 𝒰 : BasisStableOpenCover B U,
      BasisStableOpenCover.Refines 𝒰 𝒱 ∧
        ∀ p : ℕ, 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor 𝒰.cover).obj (moduleUnderlyingPresheaf ℱ))) := sorry

-- Proof sketch: embed `ℱ` into an injective `\mathcal O_X`-module, use Lemmas `20.11.1` and
-- `20.11.7` together with the basis-stable cover hypothesis to propagate vanishing to the
-- quotient, and then induct on the cohomological degree via the long exact sequence attached to
-- `0 ⟶ ℱ ⟶ ℐ ⟶ ℚ ⟶ 0`. The basis assumption ensures the Čech complexes for covers in the cofinal
-- system are built from sections on opens still lying in `B`.
/-- Lemma 20.11.9: if `B` is a basis of a ringed space `X` and an `\mathcal O_X`-module
`\mathcal F` has vanishing positive Čech cohomology on a cofinal system of basis-stable coverings
of each basis open, then every higher cohomology group `H^p(U, \mathcal F)` vanishes for
`p > 0` and every basis open `U ∈ B`. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_basisCoverings
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X))
    (hℱ : HasCofinalBasisCechAcyclicCoverings B ℱ)
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ℱ).H' p U) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_10 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
/-- The category of `\mathcal O_X`-modules on a ringed space. -/
/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_*\mathcal O_X` attached to a morphism of
ringed spaces, after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
      ⟨f.hom.c⟩)

/-- The pushforward functor on `\mathcal O`-modules induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The underlying abelian sheaf of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits. -/
instance opensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
instance opensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

-- Proof sketch: pull the cover `𝒱` of `V` back along `f` to a cover of `f⁻¹(V)`. The underlying
-- additive presheaf of `f_* \mathcal I` evaluates on each Čech intersection as
-- `\mathcal I(f^{-1}(V_{j_0 \dots j_p}))`, so its Čech complex identifies with the Čech complex of
-- `\mathcal I` on the pulled-back cover. Then apply injective Čech-acyclicity.
/-- Lemma 20.11.10 (1): if `f : X ⟶ Y` is a morphism of ringed spaces and `\mathcal I` is an
injective `\mathcal O_X`-module, then the positive Čech cohomology of `f_* \mathcal I` vanishes
for every open covering of every open subset `V ⊆ Y`. -/
theorem cech_cohomology_isZero_modulePushforward_of_injective
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ)
    {V : Opens Y.carrier} {ι : Type u} (𝒱 : ι → Opens Y.carrier) (h𝒱 : iSup 𝒱 = V)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
        ((cechComplexFunctor 𝒱).obj
          (moduleUnderlyingPresheaf ((modulePushforward f).obj ℐ)))) := sorry

-- Proof sketch: the first part gives vanishing of higher Čech cohomology for every open covering
-- of every open subset of `Y`. Apply the comparison from Čech cohomology to sheaf cohomology to
-- deduce the vanishing of `H^p(V, f_* \mathcal I)` for all `p > 0`.
/-- Lemma 20.11.10 (2): if `f : X ⟶ Y` is a morphism of ringed spaces and `\mathcal I` is an
injective `\mathcal O_X`-module, then `H^p(V, f_* \mathcal I) = 0` for every open subset
`V ⊆ Y` and every `p > 0`; equivalently, `f_* \mathcal I` is right acyclic for `\Gamma(V, -)`. -/
theorem higherCohomology_isZero_modulePushforward_of_injective
    {X Y : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y) (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ)
    (V : Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ((modulePushforward f).obj ℐ)).H' p V) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_11 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.11:
- primary domain: adjunctions, exactness, and injective-object preservation for module-sheaf
  functors on ringed spaces;
- sampled owner declarations:
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSpace.Hom.IsFlat.pullback_exact`,
  `preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.injective_obj_of_injective`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical pushforward
  functor `f _*`, derived from the adjunction `f^* ⊣ f _*`;
- primitive data: only the morphism `f : X ⟶ Y` and the flatness hypothesis;
- derived API: preservation of injective objects by `f _*`, and the objectwise injectivity
  consequence for `(f _*).obj ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a flat direct image sends injective
  `\mathcal O_X`-modules to injective `\mathcal O_Y`-modules;
- `core/canonical`: `Functor.PreservesInjectiveObjects` together with
  `Functor.injective_obj_of_injective`;
- `bridge/view`: this ringed-space specialization built from
  `SheafOfModules.pullbackPushforwardAdjunction` and `RingedSpace.Hom.IsFlat.pullback_exact`.
-/

-- Proof sketch: Lemma `17.20.2` makes `f^*` exact for a flat morphism, and Lemma `12.29.1`
-- upgrades the adjunction `f^* ⊣ f_*` to preservation of injective objects by `f_*`.
/-- For a flat morphism of ringed spaces, direct image on module sheaves preserves injective
objects. -/
instance modulePushforward_preservesInjectiveObjects_of_isFlat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    (f _*).PreservesInjectiveObjects := by
  sorry

/-- Lemma 20.11.11: for a flat morphism of ringed spaces, the pushforward of an injective
`\mathcal O_X`-module is injective as an `\mathcal O_Y`-module. -/
theorem injective_modulePushforward_of_isFlat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f]
    (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ) :
    Injective ((f _*).obj ℐ) :=
  (f _*).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_11_12 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf of rings. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingSheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℱ

/-- The functor sending a sheaf of `\mathcal O_X`-modules to its degree-`p` cohomology on the
open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The canonical map from the cohomology of a product of `\mathcal O_X`-modules on `U` to the
product of the corresponding cohomology groups. -/
private noncomputable abbrev ringedSpaceModuleProductCohomologyMap
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    (ringedSpaceModuleUnderlyingSheaf (∏ᶜ ℱ)).H' p U ⟶
      ∏ᶜ fun i ↦ (ringedSpaceModuleUnderlyingSheaf (ℱ i)).H' p U :=
  piComparison (ringedSpaceModuleCohomologyAtOpenFunctor X U p) ℱ

-- Proof sketch: degree-zero cohomology is evaluation of the underlying sheaf on `U`, and products
-- of sheaves of modules are computed objectwise on the underlying sheaves, so the relevant
-- `piComparison` map is an isomorphism.
/-- Lemma 20.11.12 (1): for a ringed space `X`, an open subset `U`, and a family of
`\mathcal O_X`-modules `(\mathcal F_i)`, the canonical map
`H^0(U, \prod_i \mathcal F_i) \to \prod_i H^0(U, \mathcal F_i)` is an isomorphism. -/
theorem ringedSpaceModuleProductCohomologyMap_isIso_degree_zero
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    IsIso (ringedSpaceModuleProductCohomologyMap U 0 ℱ) := sorry

-- Proof sketch: choose an open cover on which a class in `H^1(U, \prod_i \mathcal F_i)` vanishes,
-- represent it by a Čech cocycle, use injectivity of the Čech-to-cohomology map in degree `1` for
-- each factor, and identify the Čech complex of the product with the product of the Čech
-- complexes to conclude that the cocycle is zero.
/-- Lemma 20.11.12 (2): for a ringed space `X`, an open subset `U`, and a family of
`\mathcal O_X`-modules `(\mathcal F_i)`, the canonical map
`H^1(U, \prod_i \mathcal F_i) \to \prod_i H^1(U, \mathcal F_i)` is injective. -/
theorem ringedSpaceModuleProductCohomologyMap_injective_degree_one
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Function.Injective (ringedSpaceModuleProductCohomologyMap U 1 ℱ) := sorry

end AlgebraicGeometry
