import Mathlib
import stacks_project.Chap21.Lemma_21_53_1

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]

-- Proof sketch: for each degree `n`, truncate `K` and `L` below `n - 1` so that the relevant
-- cohomology of `K ⊗ L` is unchanged. The bounded truncations satisfy Lemma `21.53.1`, so after a
-- cover they are represented by bounded complexes of locally constant finite-type sheaves. Replace
-- those by bounded above complexes of finite free `\Lambda`-modules and compute the derived tensor
-- product termwise; the resulting cohomology sheaf is again locally constant of finite type.
/-- Lemma 21.53.4: if `K, L ∈ D^-(\mathcal C, \Lambda)` and all cohomology sheaves of `K` and `L`
are locally constant sheaves of finite type `\Lambda`-modules, then every cohomology sheaf of the
derived tensor product `K \otimes_\Lambda^{\mathbf L} L` is locally constant of finite type. -/
theorem derivedTensor_cohomology_isFiniteTypeLocallyConstant
    [MonoidalCategoryStruct (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKboundedAbove : ∃ a : ℤ, K.IsLE a)
    (hLboundedAbove : ∃ b : ℤ, L.IsLE b)
    (hK : ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K))
    (hL : ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj L)) :
    ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj (K ⊗ L)) := sorry

end

end CategoryTheory.Sheaf
