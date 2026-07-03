import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_41_1 (from Chap20) -/
open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.1:
- primary domain: internal-Hom complexes and tensor-Hom currying for cochain complexes of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `ringedSiteModuleComplexInternalHom`,
  `ringedSiteModuleComplexInternalHom_currying_isomorphic`,
  `ringedSiteModuleComplexTensorInternalHomComparison`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`;
- best owner abstraction:
  `ringedSiteModuleComplexInternalHom`, with the currying theorem
  `ringedSiteModuleComplexInternalHom_currying_isomorphic` as its source-facing derived API;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the internal-Hom complex itself, the tensor-Hom comparison morphisms, and the currying
  isomorphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.1 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner `ringedSiteModuleComplexInternalHom` and its currying
  theorem;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

The target file therefore belongs at the `bridge/view` layer and should directly reuse the
ringed-site owner theorem instead of rebuilding a parallel ringed-space internal-Hom complex,
its differential, and the resulting currying statement locally. -/

/- Lemma 20.41.1: for cochain complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, the nested
internal-Hom complex
`\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))`
is canonically isomorphic to the internal-Hom complex from the total tensor product
`\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet)` to
`\mathcal M^\bullet`. In the project API this is the ringed-site currying theorem, specialized to
the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexInternalHom_currying_isomorphic

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_2 (from Chap20) -/
noncomputable section

namespace AlgebraicGeometry.RingedSpace

open SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 20.41.2:
- primary domain: composition pairing for internal-Hom complexes of module-sheaf cochain
  complexes;
- inspected owner declarations:
  `SheafOfModules.RingedSite.internalHomComplexComposition`,
  `SheafOfModules.RingedSite.internalHomComplexComposition_f`;
- best owner abstraction:
  `SheafOfModules.RingedSite.internalHomComplexComposition`, whose source is already the canonical
  tensor product of the two ringed-site internal-Hom complexes;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the assembled composition morphism and its degreewise formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.2 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.internalHomComplexComposition`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the owner
declaration instead of duplicating its internal-Hom complex, tensor source, and componentwise
construction locally. -/

/- Lemma 20.41.2: for a ringed space `(X, \mathcal O_X)` and complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of
`\mathcal O_X`-modules, there is a canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_{\mathcal O_X}
  \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal L^\bullet))
\to \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal M^\bullet)`.
This item adds no new owner-level data beyond the canonical ringed-site composition morphism, so
the refined bridge file recalls that owner declaration directly. -/
recall internalHomComplexComposition

/- Companion recall: the degree-`n` component formula for the ringed-space specialization is the
specialized form of the ringed-site statement below. -/
recall internalHomComplexComposition_f

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_3 (from Chap20) -/
open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.3:
- primary domain: tensor-internal-Hom comparison for cochain complexes of module sheaves;
- inspected owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparisonF`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparisonComm`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- primitive data:
  the ambient ringed site together with the three complexes;
- derived API:
  the canonical internal-Hom complex and the assembled tensor-internal-Hom comparison morphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.3 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the owner
declaration instead of duplicating the internal-Hom complex or introducing exact-interface
ringed-space aliases. -/

/- Lemma 20.41.3: for a ringed space `(X, \mathcal O_X)` and complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of
`\mathcal O_X`-modules, there is a canonical morphism
`\operatorname{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X}
  \mathcal H\!\mathit{om}^\bullet(\mathcal M^\bullet, \mathcal L^\bullet))
\to \mathcal H\!\mathit{om}^\bullet(\mathcal M^\bullet,
  \operatorname{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet))`.
In the project API this is the ringed-site tensor-internal-Hom comparison morphism, specialized to
the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexTensorInternalHomComparison

/- Companion recall: the degreewise components of the tensor-internal-Hom comparison commute with
the differentials before assembling to the morphism above. -/
recall ringedSiteModuleComplexTensorInternalHomComparisonComm

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_4 (from Chap20) -/
open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.4:
- primary domain: the tensor-internal-Hom unit for cochain complexes of module sheaves on a
  ringed site;
- inspected owner declarations:
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight`;
- best owner abstraction:
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`, with the two naturality theorems as
  its derived functorial API;
- primitive data:
  the ambient ringed site and the two cochain complexes `K` and `L`;
- derived API:
  the assembled canonical morphism
  `K ⟶ ringedSiteModuleComplexInternalHom L (HomologicalComplex.tensorObj K L)` and its left/right
  naturality laws.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.4 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the ringed-site
owner and its companion naturality lemmas, rather than rebuilding a parallel ringed-space
construction. -/

/- Lemma 20.41.4: for complexes `\mathcal K^\bullet` and `\mathcal L^\bullet` of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, there is a canonical morphism
`\mathcal K^\bullet \to \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet))`
of complexes of `\mathcal O_X`-modules. In the project API this is the ringed-site tensor-Hom
unit, specialized to the Grothendieck topology of opens of `X`. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnit

/- Companion recall: functoriality of the canonical tensor-Hom unit in the left complex is the
specialized form of the ringed-site naturality theorem below. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft

/- Companion recall: functoriality of the canonical tensor-Hom unit in the right complex is the
specialized form of the ringed-site naturality theorem below. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_5 (from Chap20) -/
namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.5:
- primary domain: tensor-to-iterated-internal-Hom comparison for cochain complexes of
  `\mathcal O_X`-modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComponent`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_f`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`,
  with the iterated internal-Hom target and its degreewise formula derived from the same
  ringed-site owner layer;
- primitive data:
  the three complexes `K`, `L`, `M` and the ambient monoidal-closed structure on the module
  category;
- derived API:
  the canonical comparison morphism and its degree-`n` component formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.5 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly reuse the owner
declaration instead of introducing a parallel ringed-space wrapper for the same morphism or its
component formula. -/

/- Lemma 20.41.5: given complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, there is a
canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_{\mathcal O_X} \mathcal K^\bullet)
\to \mathcal H\!\mathit{om}^\bullet(\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
  \mathcal L^\bullet), \mathcal M^\bullet)`
of complexes of `\mathcal O_X`-modules. In the project API this is the ringed-site
tensor-to-iterated-internal-Hom comparison, specialized to the canonical site of opens of `X`. -/
recall SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom

/- Companion recall: the degree-`n` component formula for the ringed-space specialization is the
specialized form of the ringed-site statement below. -/
recall SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_f

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.DerivedCategory
open CochainComplex.HomComplex.CohomologyClass
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

/-- The `RingCat`-valued structure sheaf underlying a ringed space. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose (Opens.grothendieckTopology X.carrier) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
private abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The category of `\mathcal O_U`-modules on the open subspace defined by `U`. -/
private abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X))

/-- The restricted open-subspace module category has its standard derived category. -/
private instance openSubspaceModuleCategory_hasDerivedCategory :
    HasDerivedCategory (openSubspaceModuleCategory X U) :=
  HasDerivedCategory.standard (openSubspaceModuleCategory X U)

local notation "ModX" => ambientModuleCategory X
local notation "ModU" => openSubspaceModuleCategory X U
local notation "DModU" => DerivedCategory ModU

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
private abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ambientModuleCategory X ⥤ openSubspaceModuleCategory X U :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- The localization functor from restricted complexes to the derived category on the open
subspace `U`. -/
private abbrev openSubspaceDerivedQ (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
      DerivedCategory (openSubspaceModuleCategory X U) :=
  DerivedCategory.Q

/-- Restriction of a complex of `\mathcal O_X`-modules to the open subspace `U`. -/
private abbrev restrictModuleComplexToOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (ambientModuleCategory X) ℤ) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  ((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj K

-- Proof sketch: restriction to an open subspace is pullback along an open immersion, and the
-- K-injective preservation statement is the module-sheaf version of the standard restriction
-- argument used in Lemma `20.32.1`.
/-- Restriction to an open subspace preserves K-injective complexes of `\mathcal O_X`-modules. -/
private theorem restrictModuleComplexToOpen_isKInjective
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (ambientModuleCategory X) ℤ) [K.IsKInjective] :
    (restrictModuleComplexToOpen X U K).IsKInjective := by
  simpa [restrictModuleComplexToOpen, moduleRestrictionToOpen] using
    (AlgebraicGeometry.RingedSpace.moduleRestrictionToOpen_isKInjective (X := X) U K)

-- Proof sketch: apply `20.41.0.1` with `n = 0` to the restricted complexes
-- `\mathcal L^\bullet|_U` and `\mathcal I^\bullet|_U`, giving morphisms in the homotopy
-- category `K(\mathcal O_U)`. By Lemma `20.32.1`, the restriction of the K-injective complex
-- `\mathcal I^\bullet` is again K-injective, so the localization functor identifies these
-- homotopy classes with morphisms in `D(\mathcal O_U)`. This is the restricted-representative
-- form of the textbook identification
-- `H^0(\Gamma(U, \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal I^\bullet))) =
-- \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`.
/-- Lemma 20.41.6: if `Lc` and `Ic` are complexes of `\mathcal O_X`-modules and `Ic` is
K-injective, then the degree-zero cohomology of the sections of the restricted internal-Hom
complex on an open subset `U` identifies with the morphisms in the derived category of
`\mathcal O_U`-modules between the restricted derived objects represented by `Lc` and `Ic`. -/
noncomputable def openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom
    (Lc Ic : CochainComplex ModX ℤ)
    [Ic.IsKInjective] :
    (CochainComplex.HomComplex (restrictModuleComplexToOpen X U Lc)
      (restrictModuleComplexToOpen X U Ic)).homology (0 : ℤ) ≃
      ((openSubspaceDerivedQ X U).obj (restrictModuleComplexToOpen X U Lc) ⟶
        (openSubspaceDerivedQ X U).obj (restrictModuleComplexToOpen X U Ic)) :=
  let LU := restrictModuleComplexToOpen X U Lc
  let IU := restrictModuleComplexToOpen X U Ic
  let KU := (HomotopyCategory.quotient ModU (up ℤ)).obj LU
  let J0Iso :
      (HomotopyCategory.quotient ModU (up ℤ)).obj (IU⟦(0 : ℤ)⟧) ≅
        (HomotopyCategory.quotient ModU (up ℤ)).obj IU :=
    (HomotopyCategory.quotient ModU (up ℤ)).mapIso
      ((CategoryTheory.shiftFunctorZero (CochainComplex ModU ℤ) ℤ).app IU)
  letI : IU.IsKInjective := restrictModuleComplexToOpen_isKInjective X U Ic
  ((CochainComplex.HomComplex.homologyAddEquiv LU IU (0 : ℤ)).trans homAddEquiv).toEquiv.trans
    ((Iso.homCongr (Iso.refl KU) J0Iso).trans
      ((Equiv.ofBijective
          (DerivedCategory.Qh.map :
            (KU ⟶ (HomotopyCategory.quotient ModU (up ℤ)).obj IU) →
              (DerivedCategory.Qh.obj KU ⟶
                DerivedCategory.Qh.obj ((HomotopyCategory.quotient ModU (up ℤ)).obj IU)))
          (CochainComplex.IsKInjective.Qh_map_bijective KU IU)).trans
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModU).app LU)
          ((DerivedCategory.quotientCompQhIso ModU).app IU))))

-- Proof sketch: unfold the definition. It first identifies
-- `H^0(\operatorname{Hom}^\bullet(L_U^\bullet, I_U^\bullet))` with cohomology classes in the
-- Hom complex, then uses K-injectivity of `I_U^\bullet` to pass from cohomology classes to
-- morphisms in the localized derived category, and finally removes the zero shift.
/-- The canonical equivalence is obtained by composing the standard homology, K-injective, and
zero-shift identifications. -/
theorem openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom_def
    (Lc Ic : CochainComplex ModX ℤ)
    [Ic.IsKInjective] :
    openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom
        Lc Ic =
      let LU := restrictModuleComplexToOpen X U Lc
      let IU := restrictModuleComplexToOpen X U Ic
      let KU := (HomotopyCategory.quotient ModU (up ℤ)).obj LU
      let J0Iso :
          (HomotopyCategory.quotient ModU (up ℤ)).obj (IU⟦(0 : ℤ)⟧) ≅
            (HomotopyCategory.quotient ModU (up ℤ)).obj IU :=
        (HomotopyCategory.quotient ModU (up ℤ)).mapIso
          ((CategoryTheory.shiftFunctorZero (CochainComplex ModU ℤ) ℤ).app IU)
      letI : IU.IsKInjective :=
        restrictModuleComplexToOpen_isKInjective X U Ic
      ((CochainComplex.HomComplex.homologyAddEquiv LU IU (0 : ℤ)).trans homAddEquiv).toEquiv.trans
        ((Iso.homCongr (Iso.refl KU) J0Iso).trans
          ((Equiv.ofBijective
              (DerivedCategory.Qh.map :
                (KU ⟶ (HomotopyCategory.quotient ModU (up ℤ)).obj IU) →
                  (DerivedCategory.Qh.obj KU ⟶
                    DerivedCategory.Qh.obj ((HomotopyCategory.quotient ModU (up ℤ)).obj IU)))
              (CochainComplex.IsKInjective.Qh_map_bijective KU IU)).trans
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModU).app LU)
              ((DerivedCategory.quotientCompQhIso ModU).app IU)))) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The `RingCat`-valued structure sheaf underlying a ringed space. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose (Opens.grothendieckTopology X.carrier) (forget₂ CommRingCat RingCat.{u})).obj
    X.sheaf

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
private abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable {X : RingedSpace.{u}}
variable [Abelian (ambientModuleCategory X)]
variable [CategoryWithHomology (ambientModuleCategory X)]

/-- Use the preadditive structure induced by the ambient abelian category so the standard
Hom-complex API applies to complexes of `\mathcal O_X`-modules. -/
local instance : Preadditive (ambientModuleCategory X) :=
  Abelian.toPreadditive

local notation "CpxOX" => CochainComplex (ambientModuleCategory X) ℤ

/-- The degree-`n` cochains in the Hom complex of two complexes of `\mathcal O_X`-modules. -/
private abbrev homComplexCochain (K L : CpxOX) (n : ℤ) :=
  Cochain K L n

/-- The degreewise comparison on Hom-complex cochains induced by precomposition with `a` and
postcomposition with `b`. -/
private def homComplexPrecompPostcompComponentToFun
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    homComplexCochain L I' n → homComplexCochain L' I n :=
  fun z ↦ (Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)

-- Proof sketch: postcomposition by `b` and precomposition by `a` are additive on cochains, so
-- their composite preserves addition degreewise.
/-- The degreewise Hom-complex comparison map is additive on cochains. -/
private theorem homComplexPrecompPostcompComponentToFun_map_add
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    ∀ z z' : homComplexCochain L I' n,
      homComplexPrecompPostcompComponentToFun a b n (z + z') =
        homComplexPrecompPostcompComponentToFun a b n z +
          homComplexPrecompPostcompComponentToFun a b n z' := sorry

/-- The degree-`n` component of the comparison morphism
`Hom^\bullet(L^\bullet, (I')^\bullet) ⟶ Hom^\bullet((L')^\bullet, I^\bullet)`. -/
private def homComplexPrecompPostcompComponent
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    (CochainComplex.HomComplex L I').X n ⟶ (CochainComplex.HomComplex L' I).X n :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (homComplexPrecompPostcompComponentToFun a b n)
      (homComplexPrecompPostcompComponentToFun_map_add a b n))

-- Proof sketch: the Hom-complex differential is the cochain differential `δ`. Functoriality of
-- `δ` with respect to precomposition and postcomposition is exactly the pair of identities
-- `δ_zero_cocycle_comp` and `δ_comp_zero_cocycle`, specialized to the `0`-cocycles attached to
-- `a` and `b`.
/-- Precomposition and postcomposition assemble into a morphism of Hom complexes. -/
private theorem homComplexPrecompPostcomp_comm
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) :
    ∀ n m : ℤ, (up ℤ).Rel n m →
      homComplexPrecompPostcompComponent a b n ≫ (CochainComplex.HomComplex L' I).d n m =
        (CochainComplex.HomComplex L I').d n m ≫ homComplexPrecompPostcompComponent a b m := sorry

/-- The comparison morphism on Hom complexes induced by precomposition with `a` and
postcomposition with `b`. -/
private def homComplexPrecompPostcomp
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) :
    CochainComplex.HomComplex L I' ⟶ CochainComplex.HomComplex L' I where
  f := homComplexPrecompPostcompComponent a b
  comm' := homComplexPrecompPostcomp_comm a b

-- Proof sketch: by Lemma `20.41.6`, after restricting to any open subset `U`, the degree-zero
-- homology sheaf of each Hom complex identifies with the sheaf associated to the presheaf
-- `U ↦ \mathrm{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. Under these identifications the map induced
-- by `a` and `b` is the identity, so the comparison morphism is a quasi-isomorphism.
/-- Lemma 20.41.7: if `a : (\mathcal L')^\bullet ⟶ \mathcal L^\bullet` and
`b : (\mathcal I')^\bullet ⟶ \mathcal I^\bullet` are quasi-isomorphisms of complexes of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, with both
`\mathcal I^\bullet` and `(\mathcal I')^\bullet` K-injective, then the induced map
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)` is a
quasi-isomorphism. -/
theorem quasiIso_homComplex_precomp_postcomp_of_quasiIso_of_isKInjective
    {L' L I' I : CpxOX}
    (a : L' ⟶ L) (ha : QuasiIso a)
    (b : I' ⟶ I) (hb : QuasiIso b)
    [I'.IsKInjective] [I.IsKInjective] :
    QuasiIso (homComplexPrecompPostcomp a b) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_41_8 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [Abelian (RingedSpace.Modules X)]
variable [HasProducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ,
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSpace.Modules X))]

/-- Use the preadditive structure induced by the ambient abelian category so the standard
cochain-complex APIs use a single local instance. -/
local instance : Preadditive (RingedSpace.Modules X) :=
  Abelian.toPreadditive

local notation "CpxOX" => CochainComplex (RingedSpace.Modules X) ℤ

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O_X`-modules on a ringed space. -/
noncomputable def moduleComplexInternalHomDegree
    (K L : CpxOX) (n : ℤ) : (RingedSpace.Modules X) :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- and both sides reduce to the same degree after reassociating addition on `ℤ`.
/-- Reindexing the target degree in the differential of the internal-Hom complex on a ringed
space. -/
theorem moduleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPostcompose
    (K L : CpxOX) (i j p : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPrecompose
    (K L : CpxOX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (moduleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed space. -/
noncomputable def moduleComplexInternalHomDComponent
    (K L : CpxOX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    moduleComplexInternalHomPostcompose K L i j p -
      moduleComplexInternalHomPrecompose K L i j p hij
  else
    moduleComplexInternalHomPostcompose K L i j p +
      moduleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O_X`-
modules on a ringed space. -/
noncomputable def moduleComplexInternalHomD
    (K L : CpxOX) (i j : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      moduleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦ moduleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the internal-Hom differential is zero unless `j = i + 1`.
/-- The internal-Hom differential on a ringed space vanishes away from adjacent cohomological
degrees. -/
theorem moduleComplexInternalHom_shape
    (K L : CpxOX) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    moduleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms with the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex on a ringed space compose to zero. -/
theorem moduleComplexInternalHom_dCompD
    (K L : CpxOX) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    moduleComplexInternalHomD K L i j ≫ moduleComplexInternalHomD K L j k = 0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O_X`-modules on a ringed
space. -/
noncomputable def moduleComplexInternalHom
    (K L : CpxOX) : CpxOX where
  X := moduleComplexInternalHomDegree K L
  d := moduleComplexInternalHomD K L
  shape := fun i j hij ↦ moduleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦ moduleComplexInternalHom_dCompD K L i j k hij hjk

-- Proof sketch: use the right-orthogonal characterization of K-injective complexes. For an
-- acyclic complex `K`, identify morphisms `K ⟶ \mathcal H\!\mathit{om}^\bullet(L, I)` in the
-- homotopy category with degree-zero cohomology classes in the internal-Hom complex, then use the
-- tensor-Hom currying comparison to rewrite them as morphisms `Tot(K \otimes L) ⟶ I`. Since `L`
-- is K-flat, the total tensor complex is acyclic, and these morphisms vanish because `I` is
-- K-injective.
set_option maxHeartbeats 1000000 in
/-- Lemma 20.41.8: if `\mathcal I^\bullet` is a K-injective complex of `\mathcal O_X`-modules on
a ringed space `(X, \mathcal O_X)` and `\mathcal L^\bullet` is K-flat, then the internal-Hom
complex `\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal I^\bullet)` is
K-injective. -/
theorem moduleComplexInternalHom_isKInjective_of_isKFlat
    (L I : CpxOX) (hL : L.IsKFlat) [I.IsKInjective] :
    ((moduleComplexInternalHom L I : CpxOX)).IsKInjective := sorry

end AlgebraicGeometry.RingedSpace
