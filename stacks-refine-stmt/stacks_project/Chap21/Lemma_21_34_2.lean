import Mathlib
import stacks_project.Chap21.Lemma_21_34_1

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
