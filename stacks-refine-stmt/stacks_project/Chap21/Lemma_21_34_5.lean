import Mathlib
import stacks_project.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

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
