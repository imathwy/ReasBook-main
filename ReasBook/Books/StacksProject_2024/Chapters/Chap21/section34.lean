import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_34_1 (from Chap21) -/
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

/-! ### Lemma_21_34_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModO" => _root_.ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

variable [Preadditive ModO]
variable [HasProducts ModO]
variable [MonoidalCategory ModO]
variable [SymmetricCategory ModO]
variable [MonoidalClosed ModO]
variable [MonoidalPreadditive ModO]
variable [HasColimits ModO]
variable [∀ X : ModO, ((curriedTensor ModO).obj X).Additive]
variable [∀ X Y : CpxO, CochainComplex.HasMapBifunctor X Y (curriedTensor ModO)]

-- Proof sketch: add `r` to the identity `p + q = n` and reassociate the sums.
/-- Reindexing the target degree in the summandwise composition map. -/
private theorem ringedSiteModuleComplexInternalHomCompositionIndexEq
    {p q n r : ℤ} (h : p + q = n) :
    p + (q + r) = n + r := sorry

/-- The degreewise composition map on the `(p,q)`-summand of
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet) \otimes
\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal L^\bullet)`, landing in degree
`n = p + q` of `\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal M^\bullet)`. -/
private noncomputable def ringedSiteModuleComplexInternalHomCompositionComponent
    (K L M : CpxO) (p q n : ℤ) (h : p + q = n) :
    ((ringedSiteModuleComplexInternalHom L M).X p ⊗
        (ringedSiteModuleComplexInternalHom K L).X q) ⟶
      (ringedSiteModuleComplexInternalHom K M).X n :=
  Pi.lift fun r ↦
    ((Pi.π (fun s : ℤ ↦ (ihom (L.X s)).obj (M.X (p + s))) (q + r) ≫
        (ihom (L.X (q + r))).map
          (eqToHom (congrArg (fun t : ℤ ↦ M.X t)
            (ringedSiteModuleComplexInternalHomCompositionIndexEq h)))) ⊗ₘ
      Pi.π (fun s : ℤ ↦ (ihom (K.X s)).obj (L.X (q + s))) r) ≫
    MonoidalClosed.curry
      ((α_ (K.X r) ((ihom (L.X (q + r))).obj (M.X (n + r)))
          ((ihom (K.X r)).obj (L.X (q + r)))).inv ≫
        ((β_ (K.X r) ((ihom (L.X (q + r))).obj (M.X (n + r)))).hom ▷
          (ihom (K.X r)).obj (L.X (q + r))) ≫
        (α_ ((ihom (L.X (q + r))).obj (M.X (n + r))) (K.X r)
          ((ihom (K.X r)).obj (L.X (q + r)))).hom ≫
        ((ihom (L.X (q + r))).obj (M.X (n + r)) ◁
          (ihom.ev (K.X r)).app (L.X (q + r))) ≫
        (β_ ((ihom (L.X (q + r))).obj (M.X (n + r))) (L.X (q + r))).hom ≫
        (ihom.ev (L.X (q + r))).app (M.X (n + r)))

-- Proof sketch: compare both sides after restricting to a summand of total degree `i` and then to
-- the `r`-th factor of the product defining `\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
-- \mathcal M^\bullet)`. The source total-complex differential splits into the two tensor-factor
-- differentials, and the target differential is the standard internal-Hom differential; the
-- resulting identity is the associativity of composition together with the sign convention in the
-- total tensor complex.
/-- The degreewise composition maps are compatible with the differentials, so they assemble to a
morphism of cochain complexes. -/
private theorem ringedSiteModuleComplexInternalHomCompositionComm
    (K L M : CpxO) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    HomologicalComplex.mapBifunctorDesc
        (fun p q h ↦ ringedSiteModuleComplexInternalHomCompositionComponent K L M p q i h) ≫
      (ringedSiteModuleComplexInternalHom K M).d i j =
    (HomologicalComplex.tensorObj
        (ringedSiteModuleComplexInternalHom L M)
        (ringedSiteModuleComplexInternalHom K L)).d i j ≫
      HomologicalComplex.mapBifunctorDesc
        (fun p q h ↦ ringedSiteModuleComplexInternalHomCompositionComponent K L M p q j h) := sorry

/-- Lemma 21.34.2: for a ringed site `(\mathcal C, \mathcal O)` and cochain complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of `\mathcal O`-modules,
there is a canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_\mathcal O
  \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal L^\bullet))
\to \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal M^\bullet)`. -/
noncomputable def internalHomComplexComposition
    (K L M : CpxO) :
    HomologicalComplex.tensorObj
      (ringedSiteModuleComplexInternalHom L M)
      (ringedSiteModuleComplexInternalHom K L) ⟶
      ringedSiteModuleComplexInternalHom K M where
  f n :=
    HomologicalComplex.mapBifunctorDesc
      (fun p q h ↦ ringedSiteModuleComplexInternalHomCompositionComponent K L M p q n h)
  comm' := ringedSiteModuleComplexInternalHomCompositionComm K L M

-- Proof sketch: unfold `internalHomComplexComposition`; its degree-`n` component is the
-- `mapBifunctorDesc` morphism obtained by totalizing the summandwise tensor-lifted composition
-- maps defined in `ringedSiteModuleComplexInternalHomCompositionComponent`.
/-- The degree-`n` component of the canonical composition morphism is given by totalizing the
summandwise composition pairings. -/
theorem internalHomComplexComposition_f
    (K L M : CpxO) (n : ℤ) :
    (internalHomComplexComposition K L M).f n =
      HomologicalComplex.mapBifunctorDesc
        (fun p q h ↦ ringedSiteModuleComplexInternalHomCompositionComponent K L M p q n h) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_34_3 (from Chap21) -/
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

/-! ### Lemma_21_34_4 (from Chap21) -/
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
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ

/-- The degree-`n` component of postcomposition by a cochain map on the internal-Hom complex of
ringed-site module complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPostComponent
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) (n : ℤ) :
    ringedSiteModuleComplexInternalHomDegree L M₁ n ⟶
      ringedSiteModuleComplexInternalHomDegree L M₂ n :=
  Pi.lift (fun p : ℤ ↦
    Pi.π (fun q : ℤ ↦ (ihom (L.X q)).obj (M₁.X (n + q))) p ≫
      (ihom (L.X p)).map (g.f (n + p)))

-- Proof sketch: postcomposition with `g` commutes with both pieces of the internal-Hom
-- differential because `g` is a cochain map, so the defining squares commute after projecting to
-- each factor of the product.
/-- Postcomposition by a cochain map is itself a cochain map on internal-Hom complexes of
`\mathcal O`-modules. -/
theorem ringedSiteModuleComplexInternalHomPostComm
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomPostComponent g i ≫
        ringedSiteModuleComplexInternalHomD L M₂ i j =
      ringedSiteModuleComplexInternalHomD L M₁ i j ≫
        ringedSiteModuleComplexInternalHomPostComponent g j := sorry

/-- Postcomposition by a cochain map on the internal-Hom complex of ringed-site module
complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPost
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) :
    ringedSiteModuleComplexInternalHom L M₁ ⟶
      ringedSiteModuleComplexInternalHom L M₂ where
  f n := ringedSiteModuleComplexInternalHomPostComponent g n
  comm' i j hij := ringedSiteModuleComplexInternalHomPostComm g i j hij

/-- The degree-`n` component of precomposition by a cochain map on the internal-Hom complex of
ringed-site module complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPreComponent
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) (n : ℤ) :
    ringedSiteModuleComplexInternalHomDegree L₂ M n ⟶
      ringedSiteModuleComplexInternalHomDegree L₁ M n :=
  Pi.lift (fun p : ℤ ↦
    Pi.π (fun q : ℤ ↦ (ihom (L₂.X q)).obj (M.X (n + q))) p ≫
      (MonoidalClosed.pre (f.f p)).app (M.X (n + p)))

-- Proof sketch: precomposition with `f` is compatible with the internal-Hom differential by the
-- naturality of `MonoidalClosed.pre` together with the cochain-map identities for `f`.
/-- Precomposition by a cochain map is itself a cochain map on internal-Hom complexes of
`\mathcal O`-modules. -/
theorem ringedSiteModuleComplexInternalHomPreComm
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomPreComponent f i ≫
        ringedSiteModuleComplexInternalHomD L₁ M i j =
      ringedSiteModuleComplexInternalHomD L₂ M i j ≫
        ringedSiteModuleComplexInternalHomPreComponent f j := sorry

/-- Precomposition by a cochain map on the internal-Hom complex of ringed-site module
complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPre
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) :
    ringedSiteModuleComplexInternalHom L₂ M ⟶
      ringedSiteModuleComplexInternalHom L₁ M where
  f n := ringedSiteModuleComplexInternalHomPreComponent f n
  comm' i j hij := ringedSiteModuleComplexInternalHomPreComm f i j hij

/-- The degree-`n` component of the canonical map
`\mathcal K^\bullet ⟶ \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet))`. -/
noncomputable def ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent
    (K L : CpxO) (n : ℤ) :
    K.X n ⟶
      ringedSiteModuleComplexInternalHomDegree L
        (HomologicalComplex.tensorObj K L) n :=
  Pi.lift (fun q : ℤ ↦
    MonoidalClosed.curry
      ((β_ (L.X q) (K.X n)).hom ≫
        HomologicalComplex.ιTensorObj K L n q (n + q) rfl))

-- Proof sketch: evaluate both sides after projecting to the `q`-th factor of the internal-Hom
-- product and uncurry. The resulting maps into the `(i + q)`- and `(j + q)`-summands of the
-- total tensor complex agree by the standard total-complex differential formula and the cochain
-- sign convention.
/-- The degreewise components of the tensor-Hom unit assemble to a morphism of cochain
complexes. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitComm
    (K L : CpxO) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L i ≫
        ringedSiteModuleComplexInternalHomD L (HomologicalComplex.tensorObj K L) i j =
      K.d i j ≫
        ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L j := sorry

/-- Lemma 21.34.4: for complexes `\mathcal K^\bullet` and `\mathcal L^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, there is a canonical morphism
`\mathcal K^\bullet ⟶ \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet))`. In Lean,
`\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet)` is
`HomologicalComplex.tensorObj K L`. -/
noncomputable def ringedSiteModuleComplexTensorTotalizationInternalHomUnit
    (K L : CpxO) :
    K ⟶
      ringedSiteModuleComplexInternalHom L
        (HomologicalComplex.tensorObj K L) where
  f n := ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L n
  comm' i j hij :=
    ringedSiteModuleComplexTensorTotalizationInternalHomUnitComm K L i j hij

-- Proof sketch: compare both sides degreewise. Naturality in `K` is postcomposition by the
-- morphism on total tensor complexes induced from `α`, and the component formulas coincide after
-- projecting to each internal-Hom factor.
/-- The canonical tensor-Hom unit is functorial in the left complex. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft
    {K₁ K₂ L : CpxO} (α : K₁ ⟶ K₂) :
    α ≫ ringedSiteModuleComplexTensorTotalizationInternalHomUnit K₂ L =
      ringedSiteModuleComplexTensorTotalizationInternalHomUnit K₁ L ≫
        ringedSiteModuleComplexInternalHomPost
          (HomologicalComplex.tensorHom α (𝟙 L)) := sorry

-- Proof sketch: compare the two routes from `K` to
-- `Hom^\bullet(L₁^\bullet, Tot(K^\bullet ⊗ L₂^\bullet))`. One route first applies the unit for
-- `L₂` and then precomposes by `β`; the other applies the unit for `L₁` and then postcomposes by
-- the induced morphism on total tensor complexes.
/-- The canonical tensor-Hom unit is functorial in the right complex. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight
    (K : CpxO) {L₁ L₂ : CpxO} (β : L₁ ⟶ L₂) :
    ringedSiteModuleComplexTensorTotalizationInternalHomUnit K L₂ ≫
        ringedSiteModuleComplexInternalHomPre β =
      ringedSiteModuleComplexTensorTotalizationInternalHomUnit K L₁ ≫
        ringedSiteModuleComplexInternalHomPost
          (HomologicalComplex.tensorHom (𝟙 K) β) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_34_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open HomologicalComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (_root_.ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (_root_.ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (_root_.ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (_root_.ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (_root_.ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : _root_.ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (_root_.ringedSiteModuleCategory J 𝒪)).obj X).Additive]

local notation "Mod" => _root_.ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ

/-- Projection to the `p`-th factor of degree `n` in the internal-Hom complex of two cochain
complexes of `\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomEval
    (K L : CpxO) (n p : ℤ) :
    (ringedSiteModuleComplexInternalHom K L).X n ⟶
      (ihom (K.X p)).obj (L.X (n + p)) :=
  show ringedSiteModuleComplexInternalHomDegree K L n ⟶
      (ihom (K.X p)).obj (L.X (n + p)) from
    Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (n + q))) p

-- Proof sketch: rewrite `n` as `t + r` and reassociate the sum on `ℤ`.
/-- Reindexing the target degree in the iterated tensor-Hom comparison map on a ringed site. -/
theorem ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomIndexEq
    {t r n p : ℤ} (h : t + r = n) :
    t + (p + r) = n + p := sorry

/-- The summandwise evaluation-composition map contributing to the degree-`n` component of the
canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_\mathcal O \mathcal K^\bullet)
\to \mathcal H\!\mathit{om}^\bullet(\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
  \mathcal L^\bullet), \mathcal M^\bullet)`. -/
noncomputable def ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComponent
    (K L M : CpxO) (t r n p : ℤ) (h : t + r = n) :
    ((ringedSiteModuleComplexInternalHom L M).X t ⊗ K.X r) ⟶
      (ihom ((ringedSiteModuleComplexInternalHom K L).X p)).obj (M.X (n + p)) :=
  MonoidalClosed.curry
    (((ringedSiteModuleComplexInternalHomEval K L p r) ⊗ₘ
        ((ringedSiteModuleComplexInternalHomEval L M t (p + r)) ⊗ₘ
          𝟙 (K.X r))) ≫
      (α_ ((ihom (K.X r)).obj (L.X (p + r)))
        ((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) (K.X r)).inv ≫
      ((β_ ((ihom (K.X r)).obj (L.X (p + r)))
          ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).hom ⊗ₘ
        𝟙 (K.X r)) ≫
      (β_ (((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) ⊗
          ((ihom (K.X r)).obj (L.X (p + r)))) (K.X r)).hom ≫
      (K.X r ◁
        (β_ ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))
          ((ihom (K.X r)).obj (L.X (p + r)))).hom) ≫
      (α_ (K.X r) ((ihom (K.X r)).obj (L.X (p + r)))
        ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).inv ≫
      ((ihom.ev (K.X r)).app (L.X (p + r)) ⊗ₘ
        𝟙 ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))) ≫
      (ihom.ev (L.X (p + r))).app (M.X (t + (p + r))) ≫
      eqToHom (congrArg (fun z : ℤ ↦ M.X z)
        (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomIndexEq h)))

/-- The degree-`n` component of the canonical tensor-to-iterated-internal-Hom morphism on a
ringed site. -/
noncomputable def ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomF
    (K L M : CpxO)
    [HasTensor (ringedSiteModuleComplexInternalHom L M) K]
    (n : ℤ) :
    (HomologicalComplex.tensorObj (ringedSiteModuleComplexInternalHom L M) K).X n ⟶
      (ringedSiteModuleComplexInternalHom
        (ringedSiteModuleComplexInternalHom K L) M).X n :=
  mapBifunctorDesc
    (fun t r h ↦
      Pi.lift (fun p ↦
        ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComponent
          K L M t r n p h))

-- Proof sketch: project both sides to a tensor summand of total degree `i` and then to a factor
-- of the target product. The source differential splits into the tensor differential on
-- `Hom^\bullet(L^\bullet, M^\bullet) ⊗ K^\bullet`, while the target differential is the
-- internal-Hom differential on `Hom^\bullet(Hom^\bullet(K^\bullet, L^\bullet), M^\bullet)`;
-- after expanding the two evaluation maps, the component identities match the usual sign
-- convention.
/-- The degreewise tensor-to-iterated-internal-Hom maps commute with the differentials. -/
theorem ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComm
    (K L M : CpxO)
    [HasTensor (ringedSiteModuleComplexInternalHom L M) K]
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomF K L M i ≫
      (ringedSiteModuleComplexInternalHom
        (ringedSiteModuleComplexInternalHom K L) M).d i j =
        (HomologicalComplex.tensorObj (ringedSiteModuleComplexInternalHom L M) K).d i j ≫
          ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomF K L M j := sorry

/-- Lemma 21.34.5: for a ringed site `(\mathcal C, \mathcal O)` and cochain complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of `\mathcal O`-modules,
there is a canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_\mathcal O \mathcal K^\bullet)
\to \mathcal H\!\mathit{om}^\bullet(\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
  \mathcal L^\bullet), \mathcal M^\bullet)`
of complexes of `\mathcal O`-modules, functorial in all three complexes. -/
noncomputable def ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom
    (K L M : CpxO)
    [HasTensor (ringedSiteModuleComplexInternalHom L M) K] :
    HomologicalComplex.tensorObj (ringedSiteModuleComplexInternalHom L M) K ⟶
      ringedSiteModuleComplexInternalHom
        (ringedSiteModuleComplexInternalHom K L) M where
  f := ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomF K L M
  comm' := ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComm K L M

-- Proof sketch: unfold the defining structure of
-- `ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`; its degree-`n` component is
-- exactly the totalized family of summandwise evaluation-composition maps.
/-- The degree-`n` component of the canonical tensor-to-iterated-internal-Hom morphism is the
descended summandwise evaluation-composition map in total degree `n`. -/
theorem ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_f
    (K L M : CpxO)
    [HasTensor (ringedSiteModuleComplexInternalHom L M) K]
    (n : ℤ) :
    (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M).f n =
      ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomF K L M n := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_34_6 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u v

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- Restriction of `\mathcal O_X`-modules to the localized ringed site `X.localization U`. -/
private abbrev localizedRestrictionFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ LocalizedRingedSiteModuleCat X U :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- Restriction of a cochain complex of `\mathcal O_X`-modules to the localized ringed site
`X.localization U`. -/
private abbrev localizedRestrictionComplex (X : RingedSite.{u, v}) (U : X)
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex (RingedSiteModuleCat X) ℤ →
      CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ :=
  fun K ↦ ((localizedRestrictionFunctor X U).mapHomologicalComplex (up ℤ)).obj K

section

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X

/-- The derived-category object of `D(\mathcal O_X)` represented by a cochain complex of
`\mathcal O_X`-modules. -/
private abbrev ambientDerivedObject
    [HasDerivedCategory ModX] :
    CochainComplex ModX ℤ → DerivedCategory ModX :=
  fun K ↦ DerivedCategory.Q.obj K

/-- The homotopy-category object represented by a cochain complex of `\mathcal O_X`-modules. -/
private abbrev ambientHomotopyObject :
    CochainComplex ModX ℤ → HomotopyCategory ModX (up ℤ) :=
  fun K ↦ (HomotopyCategory.quotient ModX (up ℤ)).obj K

/-- The derived-category object of `D(\mathcal O_U)` represented by the restriction of a cochain
complex of `\mathcal O_X`-modules to `X.localization U`. -/
private abbrev localizedDerivedObject (U : X)
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex ModX ℤ →
      DerivedCategory (LocalizedRingedSiteModuleCat X U) :=
  fun K ↦ DerivedCategory.Q.obj (localizedRestrictionComplex X U K)

/-- The homotopy-category object represented by the restriction of a cochain complex of
`\mathcal O_X`-modules to `X.localization U`. -/
private abbrev localizedHomotopyObject (U : X)
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms] :
    CochainComplex ModX ℤ →
      HomotopyCategory (LocalizedRingedSiteModuleCat X U) (up ℤ) :=
  fun K ↦
    (HomotopyCategory.quotient (LocalizedRingedSiteModuleCat X U) (up ℤ)).obj
      (localizedRestrictionComplex X U K)

-- Proof sketch: first identify the degree-zero cohomology of the localized Hom complex with
-- morphisms in the localized homotopy category via `21.34.0.1`. Then apply Lemma `21.20.1` to
-- see that the restricted target complex remains K-injective, so the localization functor
-- `K(\mathcal O_U) ⥤ D(\mathcal O_U)` is bijective on morphisms into it.
/-- Lemma 21.34.6 (1): for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`,
a complex `\mathcal L^\bullet` of `\mathcal O`-modules, and a K-injective complex
`\mathcal I^\bullet` of `\mathcal O`-modules, the localization functor
`K(\mathcal O_U) \to D(\mathcal O_U)` is bijective on morphisms from
`\mathcal L^\bullet|_U` to `\mathcal I^\bullet|_U`. Combined with `21.34.0.1`, this is the
textbook equality
`\operatorname{H}^0(\Gamma(U,\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,\mathcal I^\bullet)))
= \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. -/
theorem localized_internalHom_h0_qh_map_bijective
    (U : X)
    [HasDerivedCategory (LocalizedRingedSiteModuleCat X U)]
    [(localizedRestrictionFunctor X U).PreservesZeroMorphisms]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (localizedHomotopyObject X U L ⟶ localizedHomotopyObject X U I) →
          (localizedDerivedObject X U L ⟶ localizedDerivedObject X U I)) := sorry

-- Proof sketch: identify `H^0` of the Hom complex with morphisms in the homotopy category by
-- `21.34.0.2`, and then use the standard fact that a K-injective target computes morphisms in the
-- derived category because `DerivedCategory.Qh.map` is bijective on morphisms into a K-injective
-- complex.
/-- Lemma 21.34.6 (2): for a ringed site `(\mathcal C, \mathcal O)`, a complex
`\mathcal L^\bullet` of `\mathcal O`-modules, and a K-injective complex
`\mathcal I^\bullet` of `\mathcal O`-modules, the localization functor
`K(\mathcal O) \to D(\mathcal O)` is bijective on morphisms from `\mathcal L^\bullet` to
`\mathcal I^\bullet`. Combined with `21.34.0.2`, this is the textbook equality
`\operatorname{H}^0(\Gamma(\mathcal C,\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathcal I^\bullet))) = \operatorname{Hom}_{D(\mathcal O)}(L, M)`. -/
theorem internalHom_h0_qh_map_bijective
    [HasDerivedCategory ModX]
    (L I : CochainComplex ModX ℤ)
    [I.IsKInjective] :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (ambientHomotopyObject X L ⟶ ambientHomotopyObject X I) →
          (ambientDerivedObject X L ⟶ ambientDerivedObject X I)) := sorry

end

/-! ### Lemma_21_34_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).PreservesZeroMorphisms]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).PreservesZeroMorphisms]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]

/-- The canonical morphism
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)`
induced by precomposition with `f` and postcomposition with `g`. -/
noncomputable def ringedSiteModuleComplexInternalHomMap
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : L' ⟶ L) (g : I' ⟶ I) :
    ringedSiteModuleComplexInternalHom L I' ⟶
      ringedSiteModuleComplexInternalHom L' I :=
  ringedSiteModuleComplexInternalHomPost g ≫
    ringedSiteModuleComplexInternalHomPre f

-- Proof sketch: apply Lemma `21.34.6` on every localization `(\mathcal C/U, \mathcal O_U)` to
-- identify the degree-zero cohomology sheaf of each internal-Hom complex with the presheaf
-- `U ↦ Hom_{D(\mathcal O_U)}(L|_U, M|_U)`. The quasi-isomorphisms `f` and `g` identify the source
-- and target representatives of the same derived objects, so this map induces isomorphisms on all
-- cohomology sheaves. Therefore the canonical map of internal-Hom complexes is a quasi-isomorphism.
/-- Lemma 21.34.7: for a ringed site `(\mathcal C, \mathcal O)`, if
`(\mathcal I')^\bullet \to \mathcal I^\bullet` is a quasi-isomorphism of K-injective complexes of
`\mathcal O`-modules and `(\mathcal L')^\bullet \to \mathcal L^\bullet` is a quasi-isomorphism of
complexes of `\mathcal O`-modules, then the induced morphism
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)`
is a quasi-isomorphism. -/
theorem quasiIso_ringedSiteModuleComplexInternalHomMap_of_quasiIso_of_isKInjective
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : L' ⟶ L) (g : I' ⟶ I)
    (hfi : QuasiIso f) (hgi : QuasiIso g)
    (hI' :
      ∀ {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (α : K ⟶ I'),
        K.Acyclic → Nonempty (Homotopy α 0))
    (hI :
      ∀ {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (α : K ⟶ I),
        K.Acyclic → Nonempty (Homotopy α 0))
    [∀ i, (ringedSiteModuleComplexInternalHom L I').HasHomology i]
    [∀ i, (ringedSiteModuleComplexInternalHom L' I).HasHomology i] :
    QuasiIso (ringedSiteModuleComplexInternalHomMap f g) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_34_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The category of cochain complexes of `\mathcal O`-modules on the given ringed site. -/
private abbrev RingedSiteModuleComplex (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  CochainComplex (RingedSiteModules 𝒪) ℤ

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Abelian (RingedSiteModules 𝒪)]

local instance instPreadditiveRingedSiteModules : Preadditive (RingedSiteModules 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules 𝒪)).toPreadditive

local notation "CpxO" => CochainComplex (RingedSiteModules 𝒪) ℤ

variable [HasZeroObject (RingedSiteModules 𝒪)]
variable [HasBinaryBiproducts (RingedSiteModules 𝒪)]
variable [HasProducts (RingedSiteModules 𝒪)]
variable [HasCountableCoproducts (RingedSiteModules 𝒪)]
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [SymmetricCategory (RingedSiteModules 𝒪)]
variable [MonoidalClosed (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ X : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules 𝒪))]

/-- A cochain complex of `\mathcal O`-modules on a ringed site is K-flat when total tensoring
with it preserves acyclic complexes. -/
def IsKFlat (K : CpxO) : Prop :=
  ∀ ⦃F : CpxO⦄
      [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
    (HomologicalComplex.tensorObj F K).Acyclic

-- Proof sketch: this is the defining predicate unfolded.
/-- Unfolding `IsKFlat` gives the preservation of acyclic complexes by total tensoring. -/
theorem isKFlat_iff (K : CpxO) :
    IsKFlat K ↔
      ∀ ⦃F : CpxO⦄
        [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
          (HomologicalComplex.tensorObj F K).Acyclic := sorry

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomDegree
    (K L : CpxO) (n : ℤ) :
    RingedSiteModules 𝒪 :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- and both sides are the same degree after reassociating addition on `ℤ`.
/-- Reindexing the target degree in the internal-Hom differential on a ringed site. -/
theorem ringedSiteModuleComplexInternalHomSuccIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition part of the internal-Hom differential in degree `(i,j,p)` for complexes
of `\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomPostcompose
    (K L : CpxO) (i j p : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition part of the internal-Hom differential in degree `(i,j,p)` for complexes
of `\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomPrecompose
    (K L : CpxO) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (ringedSiteModuleComplexInternalHomSuccIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomDComponent
    (K L : CpxO) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    ringedSiteModuleComplexInternalHomPostcompose K L i j p -
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij
  else
    ringedSiteModuleComplexInternalHomPostcompose K L i j p +
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two complexes of `\mathcal O`-modules on a
ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomD
    (K L : CpxO) (i j : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      ringedSiteModuleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦
      ringedSiteModuleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the internal-Hom differential is zero unless `j = i + 1`.
/-- The internal-Hom differential on a ringed site vanishes away from adjacent degrees. -/
theorem ringedSiteModuleComplexInternalHomShape
    (K L : CpxO) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- complexes, and cancel the mixed terms with the standard sign convention.
/-- The internal-Hom differential for complexes of `\mathcal O`-modules on a ringed site squares
to zero. -/
theorem ringedSiteModuleComplexInternalHomDCompD
    (K L : CpxO) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    ringedSiteModuleComplexInternalHomD K L i j ≫
        ringedSiteModuleComplexInternalHomD K L j k =
      0 := sorry

/-- The internal-Hom complex of two complexes of `\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHom
    (K L : CpxO) : CpxO where
  X := ringedSiteModuleComplexInternalHomDegree K L
  d := ringedSiteModuleComplexInternalHomD K L
  shape := fun i j hij ↦ ringedSiteModuleComplexInternalHomShape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦
    ringedSiteModuleComplexInternalHomDCompD K L i j k hij hjk

-- Proof sketch: use the right-orthogonal characterization of K-injective complexes. For an
-- acyclic complex `K`, identify morphisms `K ⟶ \mathcal H\!\mathit{om}^\bullet(L, I)` in the
-- homotopy category with cohomology classes in the internal-Hom complex, then use the standard
-- tensor-Hom adjunction to rewrite this as morphisms
-- `\operatorname{Tot}(K \otimes L) ⟶ I`. Since `L` is K-flat, the total tensor complex is
-- acyclic, and these morphisms vanish because `I` is K-injective.
/-- Lemma 21.34.8: for a ringed site `(\mathcal C, \mathcal O)`, a K-flat complex
`\mathcal L^\bullet` of `\mathcal O`-modules, and a K-injective complex `\mathcal I^\bullet` of
`\mathcal O`-modules, the internal-Hom complex
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal I^\bullet)` is K-injective. -/
theorem ringedSiteModuleComplexInternalHom_isKInjective_of_isKFlat
    (L I : CpxO) (hL : IsKFlat L) [I.IsKInjective] :
    let K : CochainComplex (RingedSiteModules 𝒪) ℤ := ringedSiteModuleComplexInternalHom L I
    @CochainComplex.IsKInjective (RingedSiteModules 𝒪) _ ‹Abelian (RingedSiteModules 𝒪)› K :=
  sorry

end

end SheafOfModules.RingedSite
