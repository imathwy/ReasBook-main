import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_27_6

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (Modules X))]
variable [BraidedCategory (DerivedCategory (Modules X))]
variable [MonoidalClosed (DerivedCategory (Modules X))]

local notation "DModX" => DerivedCategory (Modules X)

private noncomputable def tensorInternalHomToIteratedInternalHomTensorSide
    (K L M : DModX) :
    ((L ⟹ M) ⊗ K) ⊗ (K ⟹ L) ⟶ M :=
  (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
    (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
    ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
    (((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K) ≫
    (β_ (K ⟹ M) K).hom ≫
    uncurry (𝟙 (K ⟹ M))

/-- For `K`, `L`, and `M` in `D(𝒪_X)`, there is a canonical morphism
`RHom(L, M) ⊗ K ⟶ RHom(RHom(K, L), M)`, where `⊗` is the derived tensor product on
`D(𝒪_X)`. -/
@[stacks 0A8U]
noncomputable def tensorInternalHomToIteratedInternalHom
    (K L M : DModX) :
    (L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M) :=
  braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M <|
    tensorInternalHomToIteratedInternalHomTensorSide K L M

/-- Applying the canonical source-order tensor/internal-Hom transposition to
`tensorInternalHomToIteratedInternalHom K L M` recovers its explicit tensor-side map. -/
theorem tensorInternalHomToIteratedInternalHom_spec
    (K L M : DModX) :
    (braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M).symm
        (tensorInternalHomToIteratedInternalHom K L M) =
      (β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom ≫
        (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
        (((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K) ≫
        (β_ (K ⟹ M) K).hom ≫
        uncurry (𝟙 (K ⟹ M)) := by
  simpa [tensorInternalHomToIteratedInternalHom,
    tensorInternalHomToIteratedInternalHomTensorSide] using
    (braidedHomEquiv ((L ⟹ M) ⊗ K) (K ⟹ L) M).apply_symm_apply
      (tensorInternalHomToIteratedInternalHomTensorSide K L M)

/-- Uncurrying the canonical tensor-to-iterated-internal-Hom morphism recovers its explicit
transpose. -/
theorem tensorInternalHomToIteratedInternalHom_uncurry
    (K L M : DModX) :
    uncurry (tensorInternalHomToIteratedInternalHom K L M) =
      (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
        (((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K) ≫
        (β_ (K ⟹ M) K).hom ≫
        uncurry (𝟙 (K ⟹ M)) := by
  have h := (braidedHomEquiv_symm_apply (tensorInternalHomToIteratedInternalHom K L M)).symm
  apply (cancel_epi ((β_ ((L ⟹ M) ⊗ K) (K ⟹ L)).hom)).1
  simpa [Category.assoc] using h.trans (tensorInternalHomToIteratedInternalHom_spec K L M)

end

end AlgebraicGeometry.RingedSpace
