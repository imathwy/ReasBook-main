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

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on a ringed
site. -/
abbrev RingedSiteModules
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [HasZeroObject (RingedSiteModules J 𝒪)]
variable [HasProducts (RingedSiteModules J 𝒪)]
variable [HasBinaryBiproducts (RingedSiteModules J 𝒪)]
variable [HasCountableCoproducts (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [SymmetricCategory (RingedSiteModules J 𝒪)]
variable [MonoidalClosed (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).PreservesZeroMorphisms]
variable [∀ X : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj X).PreservesZeroMorphisms]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ X : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules J 𝒪))]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules J 𝒪))]
variable [MonoidalClosed (DerivedCategory (RingedSiteModules J 𝒪))]

local instance instPreadditiveRingedSiteModules : Preadditive (RingedSiteModules J 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules J 𝒪)).toPreadditive

local notation "Mod" => RingedSiteModules J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomDegree
    (K L : CpxO) (n : ℤ) : Mod :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- so both index expressions simplify to the same integer.
/-- Reindexing the target degree in the differential of the internal-Hom complex. -/
theorem ringedSiteModuleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPostcompose
    (K L : CpxO) (i j p : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPrecompose
    (K L : CpxO) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (ringedSiteModuleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential. -/
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

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O`-modules
on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomD
    (K L : CpxO) (i j : ℤ) :
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
theorem ringedSiteModuleComplexInternalHomShape
    (K L : CpxO) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms using the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex compose to zero. -/
theorem ringedSiteModuleComplexInternalHomDCompD
    (K L : CpxO) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    ringedSiteModuleComplexInternalHomD K L i j ≫
        ringedSiteModuleComplexInternalHomD K L j k =
      0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O`-modules on a ringed
site. -/
noncomputable def ringedSiteModuleComplexInternalHom
    (K L : CpxO) : CpxO where
  X := ringedSiteModuleComplexInternalHomDegree K L
  d := ringedSiteModuleComplexInternalHomD K L
  shape := fun i j hij ↦ ringedSiteModuleComplexInternalHomShape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦
    ringedSiteModuleComplexInternalHomDCompD K L i j k hij hjk

/-- A complex is termwise a retract of a finite free `\mathcal O`-module sheaf if every degree
retracts from a finite free sheaf. -/
def CochainComplex.TermwiseFiniteFreeRetract (E : CpxO) : Prop :=
  ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
    Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))

-- Proof sketch: this is just the defining predicate, rewritten without the auxiliary name.
/-- Unfolding `TermwiseFiniteFreeRetract` gives the degreewise finite-free retract condition. -/
theorem cochainComplex_termwiseFiniteFreeRetract_iff (E : CpxO) :
    CochainComplex.TermwiseFiniteFreeRetract E ↔
      ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
        Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod)) := sorry

/-- The object of the derived category `D(\mathcal O)` represented by a complex of
`\mathcal O`-modules on the ringed site. -/
noncomputable abbrev ringedSiteDerivedObject
    (K : CpxO) : DMod :=
  DerivedCategory.Q.obj K

-- Proof sketch: unfold the abbreviation `ringedSiteDerivedObject`.
/-- The abbreviation `ringedSiteDerivedObject` applies the localization functor
`C(\mathcal O) \to D(\mathcal O)` to a complex of `\mathcal O`-modules. -/
theorem ringedSiteDerivedObject_def
    (K : CpxO) :
    ringedSiteDerivedObject K = DerivedCategory.Q.obj K := sorry

/-- The proposition that a complex represents the derived internal Hom of two complexes on the
given ringed site. -/
private noncomputable abbrev ringedSiteDerivedInternalHomObject
    (E F : CpxO) : DMod :=
  (ihom (ringedSiteDerivedObject E)).obj (ringedSiteDerivedObject F)

/-- The proposition that a complex represents the derived internal Hom of two complexes on the
given ringed site. -/
noncomputable def ringedSiteDerivedInternalHomRepresentation
    (E F H : CpxO) : Prop :=
  IsIsomorphic
    (ringedSiteDerivedObject H)
    (ringedSiteDerivedInternalHomObject E F)

-- Proof sketch: unfold `ringedSiteDerivedInternalHomRepresentation` and
-- `ringedSiteDerivedObject`.
/-- Unfolding `ringedSiteDerivedInternalHomRepresentation` says exactly that `Q(H)` is
isomorphic to the derived internal-Hom object `R\mathcal H\!\mathit{om}(Q(E), Q(F))`. -/
theorem ringedSiteDerivedInternalHomRepresentation_def
    (E F H : CpxO) :
    ringedSiteDerivedInternalHomRepresentation E F H ↔
      IsIsomorphic
        (ringedSiteDerivedObject H)
        (ringedSiteDerivedInternalHomObject E F) := sorry

/-- The canonical internal-Hom complex, with the ambient ringed-site parameters fixed. -/
private noncomputable def internalHomCpx
    (E F : CpxO) : CpxO :=
  show CpxO from ringedSiteModuleComplexInternalHom E F

-- Proof sketch: this is the definition of `internalHomCpx`.
/-- The internal helper `internalHomCpx` is definitionally the canonical internal-Hom complex
`ringedSiteModuleComplexInternalHom E F`. -/
theorem internalHomCpx_eq
    (E F : CpxO) :
    internalHomCpx E F = ringedSiteModuleComplexInternalHom E F := rfl

/-- The canonical internal-Hom complex on the fixed ringed site represents the derived internal
Hom of `E` and `F`. -/
def internalHomCpxRepresentsDerivedInternalHom
    (E F : CpxO) : Prop :=
  ringedSiteDerivedInternalHomRepresentation E F (internalHomCpx E F)

-- Proof sketch: unfold `internalHomCpxRepresentsDerivedInternalHom`.
/-- Unfolding `internalHomCpxRepresentsDerivedInternalHom` says that the canonical internal-Hom
complex represents the derived internal Hom of `E` and `F`. -/
theorem internalHomCpxRepresentsDerivedInternalHom_def
    (E F : CpxO) :
    internalHomCpxRepresentsDerivedInternalHom E F ↔
      ringedSiteDerivedInternalHomRepresentation E F (internalHomCpx E F) := by
  rfl

-- Proof sketch: choose a K-injective resolution `F ⟶ I`. By Section `21.35`, the complex
-- `ringedSiteModuleComplexInternalHom E I` represents `R\mathcal H\!\mathit{om}(E, F)`. Since
-- `E` is strictly perfect, only finitely many terms contribute in each degree, so the canonical
-- map `ringedSiteModuleComplexInternalHom E F ⟶ ringedSiteModuleComplexInternalHom E I` is a
-- quasi-isomorphism by the local comparison argument of Lemma `21.44.8`.
/-- Lemma 21.44.9: for complexes `\mathcal E^\bullet` and `\mathcal F^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
`\mathcal E^\bullet` is strictly perfect, then the derived internal Hom
`R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is represented by the
canonical internal-Hom complex `ringedSiteModuleComplexInternalHom E F`. Because `E` is strictly
perfect, the degreewise products in this complex are finite and match the textbook formula
`\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal E^{-q}, \mathcal F^p)`. -/
def ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect
    : CpxO → CpxO → Prop :=
  fun E F ↦
    (∃ a : ℤ, E.IsStrictlyGE a) →
      (∃ b : ℤ, E.IsStrictlyLE b) →
        CochainComplex.TermwiseFiniteFreeRetract E →
          internalHomCpxRepresentsDerivedInternalHom (E := E) (F := F)

end

end SheafOfModules.RingedSite
