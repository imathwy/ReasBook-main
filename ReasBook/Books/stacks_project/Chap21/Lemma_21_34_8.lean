import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
