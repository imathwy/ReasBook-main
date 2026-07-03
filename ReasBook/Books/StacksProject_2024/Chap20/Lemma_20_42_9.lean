import StacksProject_2024.Chap20.Lemma_20_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.9:
- primary domain: tensor-internal-Hom comparison morphisms in a braided monoidal closed derived
category of `\mathcal O_X`-modules;
- inspected owner declarations:
  `CategoryTheory.MonoidalClosed.comp`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.pre`,
  `MonoidalClosed.uncurry`;
- best owner abstraction: the ambient closed-monoidal composition map `comp K L M`, together with
  currying and precomposition in the internal-Hom variable; Lemma `20.42.9` is its adjoint
  transpose after transporting the tensor factors into the Stacks Project order
  `R\mathcal H\!\mathit{om}(L, M) \otimes^{\mathbf L} K`;
- primitive data: the ambient braided monoidal closed structure on `RingedSpaceDerived X` and
  the objects `K`, `L`, `M`;
- derived API: the canonical comparison morphism together with its uncurrying formula and
  naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the comparison morphism of Lemma 20.42.9;
- `core/canonical`: `comp K L M`, `MonoidalClosed.curry`,
  `MonoidalClosed.pre`, and `MonoidalClosed.uncurry`;
- `bridge/view`: the braiding and associator rearrangement that converts the canonical
  internal-Hom composition/evaluation data into the Stacks Project tensor order.

This file therefore keeps the source-facing comparison map as the public owner and derives it
directly from the canonical internal-Hom composition owner `comp K L M`; downstream files should
reuse that owner directly when they do not need the Stacks-ordered bridge of Lemma `20.42.5`.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.9: for a ringed space `(X, \mathcal O_X)` and objects `K`, `L`, `M` of
`D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)`. -/
noncomputable def tensorInternalHomToIteratedInternalHom
    (K L M : RingedSpaceDerived X) :
    (L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M) :=
  MonoidalClosed.curry
    ((α_ (K ⟹ L) (L ⟹ M) K).inv ≫
      ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
      ((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K ≫
      (β_ (K ⟹ M) K).hom ≫
      MonoidalClosed.uncurry (𝟙 (K ⟹ M)))

-- Proof sketch: the main morphism is defined as the currying of the displayed transpose, so
-- uncurrying it recovers that transpose by `MonoidalClosed.uncurry_curry`.
/-- Uncurrying the canonical tensor-to-iterated-internal-Hom morphism recovers its explicit
transpose. -/
theorem tensorInternalHomToIteratedInternalHom_uncurry
    (K L M : RingedSpaceDerived X) :
    MonoidalClosed.uncurry
        (tensorInternalHomToIteratedInternalHom K L M) =
      (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
        ((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K ≫
        (β_ (K ⟹ M) K).hom ≫
        MonoidalClosed.uncurry (𝟙 (K ⟹ M)) := by
  simp [tensorInternalHomToIteratedInternalHom]

-- Proof sketch: use naturality of currying in the tensor factor `K`, together with the
-- contravariant functoriality of the inner internal Hom in its source variable.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the first variable
`K`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_first_variable
    {K K' L M : RingedSpaceDerived X} (f : K ⟶ K') :
    ((𝟙 ((ihom L).obj M)) ⊗ₘ f) ≫
        tensorInternalHomToIteratedInternalHom K' L M =
      tensorInternalHomToIteratedInternalHom K L M ≫
        (MonoidalClosed.pre ((MonoidalClosed.pre f).app L)).app M := sorry

-- Proof sketch: compare the two transposes obtained from a morphism `L ⟶ L'`; on the source side
-- this acts by precomposition on `R\mathcal H\!\mathit{om}(L', M)`, and on the target side by
-- precomposition on the outer internal Hom along `R\mathcal H\!\mathit{om}(K, L) ⟶
-- R\mathcal H\!\mathit{om}(K, L')`.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the second variable
`L`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_second_variable
    {K L L' M : RingedSpaceDerived X} (g : L ⟶ L') :
    (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 K) ≫
        tensorInternalHomToIteratedInternalHom K L M =
      tensorInternalHomToIteratedInternalHom K L' M ≫
        (MonoidalClosed.pre ((ihom K).map g)).app M := sorry

-- Proof sketch: use functoriality of both internal-Hom factors in the target object `M` and the
-- naturality of currying in the codomain.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the third variable
`M`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_third_variable
    {K L M M' : RingedSpaceDerived X} (h : M ⟶ M') :
    (((ihom L).map h) ⊗ₘ 𝟙 K) ≫
        tensorInternalHomToIteratedInternalHom K L M' =
      tensorInternalHomToIteratedInternalHom K L M ≫
        (ihom ((ihom K).obj L)).map h := sorry

end

end AlgebraicGeometry.RingedSpace
