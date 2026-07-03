import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Lemma_15_90_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: base change for ideal-power torsion in module categories, with the source-facing
  torsion submodules written as `M[I^∞]` and
  `(S ⊗[R] M)[(I.map (algebraMap R S))^∞]`, carried by the owner `Ideal.primaryComponent`
  and the ambient owner functor `ModuleCat.extendScalars`;
- inspected same-domain owners:
  `Ideal.primaryComponent`,
  `Ideal.primaryComponent.map`,
  `Module.IsIdealPowerTorsion`,
  `ModuleCat.extendScalars`,
  `TensorProduct.mk`,
  `idealPowerTorsionRestrictedBaseChange`;
- best owner abstraction: the canonical tensor base-change unit together with the source-facing
  primary-component submodules and the induced restricted base-change map on them, viewed as the
  elementwise shadow of the canonical torsion base-change functor obtained by
  `idealPowerTorsionRestrictedBaseChange`;
- primitive data: the ideal `I`, the module `M`, and the canonical tensor base-change unit;
- derived API: the induced restricted linear map on primary components and its bijectivity under
  the flatness and quotient hypotheses.

Source/core/bridge triage:
- `source-facing`: the comparison of the `I^∞`-torsion submodule of `M` with the `(IS)^∞`-torsion
  submodule after base change;
- `core/canonical`: `ModuleCat.extendScalars (algebraMap R S)` and the canonical linear map
  `TensorProduct.mk R S M 1`;
- `bridge/view`: `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I` and the restricted
  map on `Ideal.primaryComponent` cut out by `tensorBaseChangeUnitPrimaryComponent`.
-/

/- The canonical unit map `M → S ⊗[R] M` is `TensorProduct.mk R S M 1`; this is the
mathlib-facing model of the textbook map `M → M \otimes_R S`. -/
-- Proof sketch: if `x` is killed by a power `I^n`, then every pure tensor `1 ⊗ x` is killed by
-- the corresponding power of `IS`; by additivity, the same holds for the image of any element of
-- the `I`-primary component.
private theorem tensorBaseChangeUnitPrimaryComponent_mem
    (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M]
    (x : M[I^∞]) :
    TensorProduct.mk R S M 1 x ∈
      ((S ⊗[R] M)[(I.map (algebraMap R S))^∞] : Submodule S (S ⊗[R] M)) :=
  sorry

/-- The canonical tensor base-change map restricted to the `I^∞`-torsion submodule `M[I^∞]`. -/
def tensorBaseChangeUnitPrimaryComponent
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] :
    (M[I^∞] : Submodule R M) →ₗ[R]
      (((S ⊗[R] M)[(I.map (algebraMap R S))^∞] :
          Submodule S (S ⊗[R] M)).restrictScalars R) :=
  ((TensorProduct.mk R S M 1).domRestrict (M[I^∞] : Submodule R M)).codRestrict
    ((((S ⊗[R] M)[(I.map (algebraMap R S))^∞] :
        Submodule S (S ⊗[R] M)).restrictScalars R))
    (tensorBaseChangeUnitPrimaryComponent_mem I M)

variable (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
variable (hquot :
  Function.Bijective
    (Ideal.quotientMap
      (I.map (algebraMap R S))
      (algebraMap R S)
      Ideal.le_comap_map))

-- Proof sketch: apply the formal glueing hypotheses of Lemmas `15.90.1` and `15.90.2` to reduce
-- to modules with no residual `I`-torsion after quotienting by `I^∞`-torsion. Flatness preserves
-- the injectivity criterion from Lemma `15.89.4`, which shows that no new `(IS)^∞`-torsion
-- appears after tensoring the quotient, so the induced map on primary components is bijective.
/-- Lemma 15.90.3 (1): if `R → S` is flat, `I` is finitely generated, and `R ⧸ I → S ⧸ IS` is
bijective, then for every `R`-module `M` the canonical map `M → S ⊗[R] M` induces a bijection
from `M[I^∞]` onto `((S ⊗[R] M)[(I.map (algebraMap R S))^∞] : Submodule S (S ⊗[R] M))`. -/
theorem tensorBaseChangeUnitPrimaryComponent_bijective
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Bijective (tensorBaseChangeUnitPrimaryComponent S I M) := sorry

-- Proof sketch: if `N` is `I`-power torsion, combine Lemma `15.90.2` with the tensor-Hom
-- adjunction to identify the displayed map with the canonical Hom bijection over `R ⧸ I`. If `M`
-- is `I`-power torsion, any morphism out of `M` factors through the `I^∞`-torsion submodule of
-- the target, and part `(1)` transports that reduction through base change.
/-- Lemma 15.90.3 (2): under the same hypotheses, extension of scalars induces a bijection
`Hom_R(M, N) → Hom_S(S ⊗[R] M, S ⊗[R] N)` whenever either `M` or `N` is `I`-power torsion. -/
theorem extendScalars_hom_bijective_of_idealPowerTorsion_left_or_right
    {M N : ModuleCat R}
    (hMN :
      Module.IsIdealPowerTorsion I M ∨
        Module.IsIdealPowerTorsion I N) :
    Function.Bijective
      (fun f : M ⟶ N ↦ (extendScalars (algebraMap R S)).map f) := sorry

-- Proof sketch: part `(2)` gives full faithfulness of the restricted extension-of-scalars
-- functor on the torsion full subcategories. For essential surjectivity, an `IS`-power torsion
-- `S`-module is unchanged by extension of scalars along `R → S`, so every object of the target
-- lies in the essential image.
/-- Lemma 15.90.3 (3): under the same hypotheses, extension of scalars defines an equivalence
between the full subcategory of `I`-power torsion `R`-modules and the full subcategory of
`IS`-power torsion `S`-modules. -/
theorem idealPowerTorsionRestrictedBaseChange_isEquivalence
    :
    Functor.IsEquivalence
      (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I) := sorry

end
