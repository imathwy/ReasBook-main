import StacksProject_2024.Chap18.Lemma_18_27_6
import StacksProject_2024.Chap21.RingedSiteDerivedBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "D" => RingedSiteDerived J 𝒪
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.35.5:
- primary domain: tensor/internal-Hom transposition in a braided monoidal closed derived category
  of sheaves of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.braidedHomEquiv`,
  `CategoryTheory.MonoidalClosed.comp`,
  `CategoryTheory.MonoidalClosed.uncurry`;
- best owner abstraction:
  `source-facing`: the ringed-site tensor-to-iterated-internal-Hom morphism of the Stacks lemma;
  `core/canonical`: `MonoidalClosed.braidedHomEquiv`;
  `bridge/view`: the ambient composition morphism `MonoidalClosed.comp K L M` together with
    the standard `MonoidalClosed.braidedHomEquiv` evaluation formula, which turn the textbook
    composition-evaluation description into the canonical transpose/uncurry formulas;
- primitive data: the chapter owner category `D = RingedSiteDerived J 𝒪`, its braided closed
  monoidal structure, and the objects `K`, `L`, `M`;
- derived API: the source-facing comparison morphism and its two thin specification companions.

Primitive data and derived API separate cleanly here: the internal-Hom composition map already has
its canonical owner in `MonoidalClosed.comp`, so this file keeps only the new source-facing
transpose and derives its companion formulas from that owner. -/

/-- Helper for Lemma 21.35.5: the tensor-side composition-and-evaluation morphism whose transpose
is the canonical map `(L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M)`. -/
private noncomputable def ringedSiteDerivedTensorInternalHomToIteratedInternalHomTensorSide
    (K L M : D) :
    ((L ⟹ M) ⊗ K) ⊗ (K ⟹ L) ⟶ M :=
  (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
    (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
    (comp K L M ▷ K) ≫
    (β_ (K ⟹ M) K).hom ≫
    uncurry (𝟙 (K ⟹ M))

/-- Lemma 21.35.5: for a ringed site `(C, 𝒪)` and objects `K`, `L`, `M` of the derived category
`D`, there is a canonical morphism `(L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M)`. This is the source-order
transpose of the tensor-side map obtained by composing `K ⟹ L` with `L ⟹ M` and then evaluating
`K ⟹ M` on `K`. -/
@[stacks 0A97]
noncomputable def ringedSiteDerivedTensorInternalHomToIteratedInternalHom
    (K L M : D) :
    (L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M) :=
  braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M <|
    ringedSiteDerivedTensorInternalHomToIteratedInternalHomTensorSide K L M

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Applying the source-order tensor/internal-Hom transposition to
`ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M` recovers the explicit tensor-side
composition-and-evaluation map. -/
theorem ringedSiteDerivedTensorInternalHomToIteratedInternalHom_spec
    (K L M : D) :
    (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
        uncurry (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
      (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
        (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        (comp K L M ▷ K) ≫
        (β_ (K ⟹ M) K).hom ≫
        uncurry (𝟙 (K ⟹ M)) := by
  have hsymm :
      (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
          uncurry (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
        (braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M).symm
          (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) := by
    simpa [ringedSiteDerivedTensorInternalHomToIteratedInternalHom] using
      (braidedHomEquiv_symm_apply
        (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M)).symm
  have htensor :
      (braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M).symm
          (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
        ringedSiteDerivedTensorInternalHomToIteratedInternalHomTensorSide K L M := by
    simp [ringedSiteDerivedTensorInternalHomToIteratedInternalHom,
      ringedSiteDerivedTensorInternalHomToIteratedInternalHomTensorSide]
  simpa [ringedSiteDerivedTensorInternalHomToIteratedInternalHomTensorSide, Category.assoc]
    using hsymm.trans htensor

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Uncurrying the canonical tensor-to-iterated-internal-Hom morphism recovers the
composition-and-evaluation map on the tensor side. -/
theorem ringedSiteDerivedTensorInternalHomToIteratedInternalHom_uncurry
    (K L M : D) :
    uncurry (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
        (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        (comp K L M ▷ K) ≫
        (β_ (K ⟹ M) K).hom ≫
        uncurry (𝟙 (K ⟹ M)) := by
  apply (cancel_epi ((β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom)).1
  simpa [Category.assoc] using
    ringedSiteDerivedTensorInternalHomToIteratedInternalHom_spec K L M

attribute [simp] ringedSiteDerivedTensorInternalHomToIteratedInternalHom_uncurry

end

end SheafOfModules.RingedSite
