import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

/- Domain-style sampling for Lemma 21.34.5:
- primary domain: tensor/internal-Hom transposition in the closed braided monoidal category of
  cochain complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `MonoidalClosed.braidedHomEquiv`,
  `internalHomComplexComposition`,
  `MonoidalClosed.uncurry`,
  `A ⟶[CpxO] B`;
- best owner abstraction: the repository owner `internalHomComplexComposition` for source-order
  internal-Hom composition on `CpxO`, together with the canonical currying/evaluation operations
  of the closed braided monoidal structure;
- primitive data: the complexes `K`, `L`, `M`;
- derived API: the source-facing tensor-to-iterated-internal-Hom morphism below.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.5;
- `core/canonical`: `internalHomComplexComposition`, `MonoidalClosed.braidedHomEquiv`, and
  `MonoidalClosed.uncurry` on `CpxO` together with the theorem-surface notation
  `A ⟶[CpxO] B`;
- `bridge/view`: the tensor-with-`K` evaluation/currying bridge from the source-order
  composition owner to the iterated internal-Hom target. -/

private noncomputable def ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide
    (K L M : CpxO) :
    ((L ⟶[CpxO] M) ⊗ K) ⊗ (K ⟶[CpxO] L) ⟶ M :=
  (β_ ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L)).hom ≫
    (α_ (K ⟶[CpxO] L) (L ⟶[CpxO] M) K).inv ≫
    ((β_ (K ⟶[CpxO] L) (L ⟶[CpxO] M)).hom ▷ K) ≫
    internalHomComplexComposition K L M ▷ K ≫
    (β_ (K ⟶[CpxO] M) K).hom ≫
    uncurry (𝟙 (K ⟶[CpxO] M))

/-- Lemma 21.34.5: for a ringed site `(𝒞, 𝒪)` and cochain complexes `K^•`, `L^•`, and `M^•`
of `𝒪`-modules, there is a canonical morphism
`Tot(Hom^•(L^•, M^•) ⊗_𝒪 K^•) ⟶ Hom^•(Hom^•(K^•, L^•), M^•)`.
In the repository owner graph, this is the source-order transpose of the tensor-side map obtained
from `internalHomComplexComposition K L M` by tensoring with `K` and then evaluating
`K ⟶[CpxO] M` on `K`. -/
@[stacks 0A92]
noncomputable def ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom
    (K L M : CpxO) :
    ((L ⟶[CpxO] M) ⊗ K) ⟶ ((K ⟶[CpxO] L) ⟶[CpxO] M) :=
  braidedHomEquiv ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L) M <|
    ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide K L M

/-- Uncurrying the canonical tensor-to-iterated-internal-Hom morphism recovers the
composition-and-evaluation map on the tensor side. -/
@[simp] theorem ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_uncurry
    (K L M : CpxO) :
    uncurry (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M) =
      (α_ (K ⟶[CpxO] L) (L ⟶[CpxO] M) K).inv ≫
        ((β_ (K ⟶[CpxO] L) (L ⟶[CpxO] M)).hom ▷ K) ≫
        internalHomComplexComposition K L M ▷ K ≫
        (β_ (K ⟶[CpxO] M) K).hom ≫
        uncurry (𝟙 (K ⟶[CpxO] M)) := by
  have hsymm :
      (braidedHomEquiv ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L) M).symm
          (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M) =
        (β_ ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L)).hom ≫
          uncurry (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M) := by
    simpa [ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom] using
      (braidedHomEquiv_symm_apply
        (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M))
  have htensor :
      (braidedHomEquiv ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L) M).symm
          (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M) =
        ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide K L M := by
    simpa [ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom,
      ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide] using
      (braidedHomEquiv ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L) M).apply_symm_apply
        (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide K L M)
  apply (cancel_epi ((β_ ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L)).hom)).1
  simpa [ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomTensorSide, Category.assoc]
    using hsymm.symm.trans htensor

/-- Applying the source-order tensor/internal-Hom transposition to
`ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M` recovers the explicit
tensor-side composition-and-evaluation map. -/
theorem ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_spec
    (K L M : CpxO) :
    (braidedHomEquiv ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L) M).symm
        (ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom K L M) =
      (β_ ((L ⟶[CpxO] M) ⊗ K) (K ⟶[CpxO] L)).hom ≫
        (α_ (K ⟶[CpxO] L) (L ⟶[CpxO] M) K).inv ≫
        ((β_ (K ⟶[CpxO] L) (L ⟶[CpxO] M)).hom ▷ K) ≫
        internalHomComplexComposition K L M ▷ K ≫
        (β_ (K ⟶[CpxO] M) K).hom ≫
        uncurry (𝟙 (K ⟶[CpxO] M)) := by
  rw [braidedHomEquiv_symm_apply]
  rw [ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_uncurry]

end

end SheafOfModules.RingedSite
