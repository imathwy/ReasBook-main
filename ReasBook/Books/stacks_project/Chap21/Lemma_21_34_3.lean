import Mathlib
import stacks_project.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory
open MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]

local notation "RingedSiteModuleComplex" =>
  CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ

/- Domain-style sampling for Lemma 21.34.3:
- primary domain: tensor-internal-Hom comparison for cochain complexes of `\mathcal O`-modules on
  a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `ringedSiteModuleComplexInternalHom`,
  `ringedSiteModuleComplexInternalHom_currying_isomorphic`;
- best owner abstraction: the internal-Hom complex itself is already owned by
  `ringedSiteModuleComplexInternalHom` in `Lemma_21_34_1`;
- primitive data: the ambient monoidal-closed category of `\mathcal O`-modules together with the
  three complexes `K`, `L`, `M`;
- derived API: the tensor-Hom comparison morphism and its degreewise compatibility with the
  differentials.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.3, the canonical tensor-Hom comparison morphism;
- `core/canonical`: `ringedSiteModuleComplexInternalHom`;
- `bridge/view`: none in this file.

This file therefore keeps only the source-facing comparison map and reuses the upstream
internal-Hom owner instead of duplicating its degreewise construction. -/

-- Proof sketch: if `r + s = n`, then adding `q` on the right yields `r + (s + q) = n + q`.
/-- Reindexing identity used in the tensor-Hom comparison map on complexes of modules over a
ringed site. -/
theorem ringedSiteModuleComplexTensorInternalHomTargetIndexEq
    {r s n q : ℤ} (hrs : r + s = n) :
    r + (s + q) = n + q := sorry

/-- The degree-`n` component of the canonical tensor-Hom comparison morphism for complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexTensorInternalHomComparisonF
    (K L M : RingedSiteModuleComplex)
    [HomologicalComplex.HasTensor K L]
    [HomologicalComplex.HasTensor K (ringedSiteModuleComplexInternalHom M L)]
    (n : ℤ) :
    (HomologicalComplex.tensorObj K (ringedSiteModuleComplexInternalHom M L)).X n ⟶
      (ringedSiteModuleComplexInternalHom M
        (HomologicalComplex.tensorObj K L)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (fun r s hrs ↦
      Pi.lift (fun q : ℤ ↦
        MonoidalClosed.curry
          ((α_ (M.X q) (K.X r)
              ((ringedSiteModuleComplexInternalHom M L).X s)).inv ≫
            ((β_ (M.X q) (K.X r)).hom ⊗ₘ
              𝟙 ((ringedSiteModuleComplexInternalHom M L).X s)) ≫
            (α_ (K.X r) (M.X q)
              ((ringedSiteModuleComplexInternalHom M L).X s)).hom ≫
            K.X r ◁ ((𝟙 (M.X q)) ⊗ₘ
              ringedSiteModuleComplexInternalHomEval M L s q) ≫
            K.X r ◁ (ihom.ev (M.X q)).app (L.X (s + q)) ≫
            HomologicalComplex.ιTensorObj K L r (s + q) (n + q)
              (ringedSiteModuleComplexTensorInternalHomTargetIndexEq hrs))))

-- Proof sketch: evaluate both sides on a tensor summand `K^r ⊗ Hom^s(M^•, L^•)` and then on the
-- `q`-th projection of the target product. The source differential splits into the differential on
-- `K^•` and the differential on `Hom^•(M^•, L^•)`, while the target differential splits into the
-- total tensor differential and the internal-Hom differential. After rewriting the associators,
-- braiding, and evaluation maps, the component formulas agree with the standard sign convention.
/-- The degreewise tensor-Hom comparison components commute with the differentials on a ringed
site. -/
theorem ringedSiteModuleComplexTensorInternalHomComparisonComm
    (K L M : RingedSiteModuleComplex)
    [HomologicalComplex.HasTensor K L]
    [HomologicalComplex.HasTensor K (ringedSiteModuleComplexInternalHom M L)]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexTensorInternalHomComparisonF K L M i ≫
      (ringedSiteModuleComplexInternalHom
        M (HomologicalComplex.tensorObj K L)).d i j =
        (HomologicalComplex.tensorObj K
          (ringedSiteModuleComplexInternalHom M L)).d i j ≫
          ringedSiteModuleComplexTensorInternalHomComparisonF K L M j := sorry

/-- Lemma 21.34.3: given complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, there
is a canonical morphism
`\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal H\!om^\bullet(\mathcal M^\bullet,
\mathcal L^\bullet)) \to \mathcal H\!om^\bullet(\mathcal M^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet))`
of complexes of `\mathcal O`-modules, functorial in all three complexes. -/
noncomputable def ringedSiteModuleComplexTensorInternalHomComparison
    (K L M : RingedSiteModuleComplex)
    [HomologicalComplex.HasTensor K L]
    [HomologicalComplex.HasTensor K (ringedSiteModuleComplexInternalHom M L)] :
    HomologicalComplex.tensorObj K (ringedSiteModuleComplexInternalHom M L) ⟶
      ringedSiteModuleComplexInternalHom M
        (HomologicalComplex.tensorObj K L) where
  f := ringedSiteModuleComplexTensorInternalHomComparisonF K L M
  comm' := ringedSiteModuleComplexTensorInternalHomComparisonComm K L M

end

end SheafOfModules.RingedSite
