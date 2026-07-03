import Mathlib
import StacksProject_2024.Chap18.Lemma_18_27_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

local notation "RingedSiteModules" => ringedSiteModuleCategory J 𝒪
local notation "RingedSiteModuleComplex" =>
  CochainComplex RingedSiteModules ℤ

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomDegree
    (K L : RingedSiteModuleComplex) (n : ℤ) : RingedSiteModules :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- so both index expressions simplify to the same integer.
/-- Reindexing the target degree in the differential of the internal-Hom complex. -/
theorem ringedSiteModuleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPostcompose
    (K L : RingedSiteModuleComplex) (i j p : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPrecompose
    (K L : RingedSiteModuleComplex) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (ringedSiteModuleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential. -/
noncomputable def ringedSiteModuleComplexInternalHomDComponent
    (K L : RingedSiteModuleComplex) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    ringedSiteModuleComplexInternalHomPostcompose K L i j p -
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij
  else
    ringedSiteModuleComplexInternalHomPostcompose K L i j p +
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomD
    (K L : RingedSiteModuleComplex) (i j : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      ringedSiteModuleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦
      ringedSiteModuleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the differential is zero unless `j = i + 1`, i.e. unless the
-- cochain-complex shape relation `ComplexShape.up ℤ` holds between `i` and `j`.
/-- The internal-Hom differential vanishes away from adjacent cohomological degrees. -/
theorem ringedSiteModuleComplexInternalHom_shape
    (K L : RingedSiteModuleComplex) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms using the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex compose to zero. -/
theorem ringedSiteModuleComplexInternalHom_dCompD
    (K L : RingedSiteModuleComplex) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    ringedSiteModuleComplexInternalHomD K L i j ≫
        ringedSiteModuleComplexInternalHomD K L j k =
      0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O`-modules on a ringed
site. -/
noncomputable def ringedSiteModuleComplexInternalHom
    (K L : RingedSiteModuleComplex) : RingedSiteModuleComplex where
  X := ringedSiteModuleComplexInternalHomDegree K L
  d := ringedSiteModuleComplexInternalHomD K L
  shape := fun i j hij ↦ ringedSiteModuleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦
    ringedSiteModuleComplexInternalHom_dCompD K L i j k hij hjk

/-- Projection to the `p`-th factor of degree `n` in the internal-Hom complex of two cochain
complexes of `\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomEval
    (K L : RingedSiteModuleComplex) (n p : ℤ) :
    (ringedSiteModuleComplexInternalHom K L).X n ⟶
      (ihom (K.X p)).obj (L.X (n + p)) :=
  show ringedSiteModuleComplexInternalHomDegree K L n ⟶
      (ihom (K.X p)).obj (L.X (n + p)) from
    Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (n + q))) p

variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).PreservesZeroMorphisms]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).PreservesZeroMorphisms]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

-- Proof sketch: repeat the currying argument of More on Algebra, Lemma `15.72.1`, replacing
-- module-valued Homs by internal Homs in the closed symmetric monoidal category
-- `\mathrm{Mod}(\mathcal O)`. Degreewise, one curries each summand
-- `K^p ⊗ \mathcal{H}\!\mathit{om}(L^q, M^{n+p+q})` to
-- `\mathcal{H}\!\mathit{om}(K^p ⊗ L^q, M^{n+p+q})`, assembles over all `p,q`, and compares the
-- differentials using the total-complex sign convention.
/-- Lemma 21.34.1: for cochain complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, the
nested internal-Hom complex
`\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))`
is canonically isomorphic to the internal-Hom complex from the total tensor product
`\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet)` to
`\mathcal M^\bullet`. In Lean, the total tensor product is
`HomologicalComplex.tensorObj K L`. -/
theorem ringedSiteModuleComplexInternalHom_currying_isomorphic
    (K L M : RingedSiteModuleComplex) :
    IsIsomorphic
      (ringedSiteModuleComplexInternalHom K (ringedSiteModuleComplexInternalHom L M))
      (ringedSiteModuleComplexInternalHom (HomologicalComplex.tensorObj K L) M) := sorry

end

end SheafOfModules.RingedSite
