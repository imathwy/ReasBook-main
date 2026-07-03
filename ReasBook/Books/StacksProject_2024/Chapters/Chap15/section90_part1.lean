import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_90_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: ideal extension and change of rings on module categories, with canonical owner
  abstractions given by `Ideal.map`, `Ideal.quotientMap`, `ModuleCat (R ⧸ I)`, `extendScalars`,
  and the canonical `ObjectProperty` view `fun M ↦ Module.IsIdealPowerTorsion I M`;
- inspected same-domain owners:
  `Ideal.map`,
  `Ideal.quotientMap`,
  `extendScalars`,
  `restrictScalars`,
  `ModuleCat (R ⧸ I)`,
  `ObjectProperty.lift`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the ideal-side construction is the canonical owner `Ideal.map φ I`; for
  modules annihilated by `I`, the owner category is `ModuleCat (R ⧸ I)` and base change is
  `extendScalars` along the quotient map `R ⧸ I →+* S ⧸ Ideal.map φ I`; the `I`-power torsion
  clause remains the source-facing restricted functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`,
  while the bridge to the target torsion full subcategory is the canonical restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` built from `ObjectProperty.lift`.

Source/core/bridge triage:
- `source-facing`: the TFAE for faithful base change on modules cut out by `I`;
- `core/canonical`: `Ideal.map φ I` on ideals and
  `extendScalars (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)` on quotient-module
  categories, together with the direct restricted base-change functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` into the target torsion full subcategory.
-/

/-- Extension of scalars along `φ` carries `I`-power torsion modules to `IS`-power torsion
modules. -/
theorem Module.IsIdealPowerTorsion.extendScalars
    (φ : R →+* S) (I : Ideal R) (M : ModuleCat R)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion (Ideal.map φ I) ((extendScalars φ).obj M) :=
  sorry

/-- Base change along `φ` on the full subcategories of `I`-power torsion and `IS`-power torsion
modules. -/
noncomputable abbrev idealPowerTorsionRestrictedBaseChange
    (φ : R →+* S) (I : Ideal R) :
    ObjectProperty.FullSubcategory (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) :=
  ObjectProperty.lift
    (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)
    (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)
    (fun M ↦ Module.IsIdealPowerTorsion.extendScalars φ I M.obj M.property)

-- Proof sketch: identify the quotient map `R ⧸ I →+* S ⧸ IS` with the base change of `φ`
-- along `R → R ⧸ I`, so Lemmas `10.39.7` and `10.39.16` give the equivalence of the faithfully
-- flat and spectrum-surjective quotient conditions. Clause `(3)` is the canonical quotient-module
-- formulation: for modules annihilated by `I`, work in `ModuleCat (R ⧸ I)` and rewrite base
-- change along `φ` as extension of scalars along `R ⧸ I →+* S ⧸ IS`, then apply Lemma `10.39.14`.
-- Clause `(4)` is the canonical restricted base-change functor
-- `idealPowerTorsionRestrictedBaseChange φ I` on the full subcategory of `I`-power torsion
-- modules. The implication from `I`-power torsion modules to `I`-annihilated
-- modules is immediate, and the converse is obtained by filtering an `I`-power torsion module by
-- its submodules annihilated by powers of `I` and using preservation of colimits by tensor
-- product.
/-- Lemma 15.90.1: for a ring map `φ : R →+* S` and an ideal `I ⊆ R`, the following are
equivalent: `φ` is flat and the induced quotient map `R ⧸ I → S ⧸ IS` is faithfully flat; `φ` is
flat and `Spec (S ⧸ IS) → Spec (R ⧸ I)` is surjective; `φ` is flat and extension of scalars along
`R ⧸ I → S ⧸ IS` is faithful on quotient-ring modules, equivalently on `R`-modules annihilated by
`I`; and `φ` is flat and base change along `φ` is faithful on `I`-power torsion `R`-modules. -/
theorem flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules
    (φ : R →+* S) (I : Ideal R) :
    List.TFAE
      [ φ.Flat ∧ (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).FaithfullyFlat
      , φ.Flat ∧
          Function.Surjective
            (PrimeSpectrum.comap (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
      , φ.Flat ∧
          (extendScalars (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)).Faithful
      , φ.Flat ∧
          (idealPowerTorsionRestrictedBaseChange φ I).Faithful
      ] := sorry

end

/-! ### Lemma_15_90_2 (from Chap15) -/
open ModuleCat
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: change of rings on module categories, especially the base-change unit and
  quotient maps modulo ideals;
- inspected same-domain owners:
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`,
  `idealPowerTorsionRestrictedBaseChange`,
  `Module.IsIdealPowerTorsion`,
  `TensorProduct.mk`,
  `Ideal.quotientMap`;
- best owner abstraction: this file should stay a source-facing bridge theorem, but its ambient
  owner is the chapter theorem
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules` together with the
  module-level tensor base-change map `TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M`; faithfulness
  on `I`-power torsion modules is carried by the chapter owner
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`, and the quotient comparison
  `R ⧸ I → S ⧸ IS` is identified by the canonical tensor/quotient owner
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`; the textbook map `M → M ⊗[R] S` is only
  the tensor-symmetry view.

Source/core/bridge triage:
- `source-facing`: the bijectivity criterion for the canonical map `M → M ⊗[R] S` on ordinary
  `I`-power torsion `R`-modules;
- `core/canonical`: extension of scalars along `algebraMap R S`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted base-change functor
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`.
-/

/-- If the canonical tensor base-change unit is bijective on every `I`-power torsion `R`-module,
then the induced quotient map `R ⧸ I → S ⧸ IS` is bijective. This is the source-facing forward
bridge used in Lemma `15.90.2`. -/
theorem quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion
    (I : Ideal R)
    (hbij : ∀ M : ModuleCat R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) :
    Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  -- Apply the pointwise tensor-unit bijectivity hypothesis to `R ⧸ I`, then identify
  -- `S ⊗[R] (R ⧸ I)` with `S ⧸ IS` via `quotIdealMapEquivTensorQuot`.
  sorry

/-- Lemma 15.90.2: under the flatness and faithful restricted base-change hypothesis supplied by
Lemma `15.90.1`, the following are equivalent: every `I`-power torsion `R`-module `M` is
unchanged by the canonical base-change unit `M → S ⊗[R] M`, and the induced map
`R ⧸ I → S ⧸ IS` is bijective. The forward implication is the atomic quotient-recovery theorem
`quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion`, while the converse
uses the chapter owners `idealPowerTorsionRestrictedBaseChange` and
`tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`. -/
theorem tensorBaseChange_bijective_iff_quotientMap_bijective_of_baseChangeFaithfulOnIdealPowerTorsion
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hfaithful : (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I).Faithful) :
    (∀ M : ModuleCat R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) ↔
    Function.Bijective
        (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  constructor
  · exact quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion I
  · intro hquot M hM
    -- View the torsion statement through the chapter owner
    -- `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules`, then combine
    -- the quotient-map hypothesis with the canonical base-change criterion from Lemma `15.89.9`.
    sorry

end

/-! ### Lemma_15_90_3 (from Chap15) -/
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

/-! ### Lemma_15_90_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped KoszulComplex

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

local notation "ChainCpxR" => ChainComplex (ModuleCat R) ℕ
local notation "CochainCpxR" => CochainComplex (ModuleCat R) ℕ

/- Domain-style sampling:
- primary domain: change of rings on homological complexes of modules, with quasi-isomorphism
  statements about the scalar-extension unit on Koszul and extended alternating Cech complexes;
- sampled owner declarations:
  `ModuleCat.extendRestrictScalarsAdj`,
  `CategoryTheory.Adjunction.mapHomologicalComplex`,
  `Functor.mapHomologicalComplexIdIso`,
  `NatTrans.mapHomologicalComplex`;
- best owner abstraction: the complex-level extension/restriction adjunction
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapHomologicalComplex c`; the
  source-facing quasi-isomorphism statements should use its unit directly instead of keeping
  parallel local wrappers for the same morphism;
- primitive data: the ring map `algebraMap R S`, its flatness, the ideal `I`, and the finite
  family `f`;
- derived API: the chain/cochain base-change unit morphisms obtained by applying
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapHomologicalComplex` to `down ℕ`
  and `up ℕ`.

Source/core/bridge triage:
- `source-facing`: the two quasi-isomorphism statements for the Koszul and extended alternating
  Cech complexes;
- `core/canonical`:
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapHomologicalComplex c` and its unit;
- `bridge/view`: the specific complexes `K^•(f)` and `extendedAlternatingCechComplex f R`.
-/

-- Proof sketch: by Lemma 15.90.2, it is enough to know that every homology module of the
-- Koszul complex on `f` is `I`-power torsion. Lemma 15.28.6 shows that the ideal generated by
-- `f` annihilates the homology, and the equality of zero loci together with finite generation of
-- `I` upgrades this to `I`-power torsion. Flatness then makes the scalar-extension unit a
-- quasi-isomorphism.
/-- Lemma 15.90.4 (1): if `R → S` is flat, `I` is finitely generated, `R ⧸ I → S ⧸ IS` is
bijective, and the finite family `f` cuts out the same closed subset as `I`, then the canonical
base-change map from the Koszul complex on `f` over `R` to its scalar extension along `R → S` is a
quasi-isomorphism. This is the library-facing form of the source statement that
`K(R, f₁, ..., fᵣ) → K(S, f₁, ..., fᵣ)` is a quasi-isomorphism. -/
theorem koszulComplexOn_baseChangeUnit_quasiIso_of_flat_of_quotientMap_bijective
    (I : Ideal R) {r : ℕ} (f : Fin r → R)
    (hI_fg : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (I.map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map))
    (hV : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) =
      PrimeSpectrum.zeroLocus (I : Set R)) :
    QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapHomologicalComplex
          (down ℕ)).unit.app (K^•(f)))) := sorry

-- Proof sketch: apply Lemma 15.90.2 to the extended alternating Čech complex of the `R`-module
-- `R`. Lemma 15.29.5 puts every cohomology module of this complex inside `V(f) = V(I)`, hence
-- finite generation of `I` makes those cohomology modules `I`-power torsion. Flatness then shows
-- that the scalar-extension unit is a quasi-isomorphism.
/-- Lemma 15.90.4 (2): under the same hypotheses, the canonical base-change map from the extended
alternating Čech complex of `R` attached to `f` to its scalar extension along `R → S` is a
quasi-isomorphism. This is the library-facing form of the source statement that the map of
extended alternating Čech complexes from `R` to `S` is a quasi-isomorphism. -/
theorem extendedAlternatingCechComplex_baseChangeUnit_quasiIso_of_flat_of_quotientMap_bijective
    (I : Ideal R) {r : ℕ} (f : Fin r → R)
    (hI_fg : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (I.map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map))
    (hV : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) =
      PrimeSpectrum.zeroLocus (I : Set R)) :
    QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapHomologicalComplex
          (up ℕ)).unit.app (extendedAlternatingCechComplex f R))) := sorry

end

/-! ### Lemma_15_90_5 (from Chap15) -/
noncomputable section

universe u

section

open Module

variable {R : Type u} [CommRing R] {n : ℕ}

/-
Domain-style sampling:
- primary domain: finite presentations of ideals by the canonical linear-combination map from a
  finite free module, together with the short exact kernel sequence of a surjective linear map;
- sampled owner declarations:
  `koszulLinearForm`,
  `Module.range_piEquiv`,
  `LinearMap.rangeRestrict`,
  `LinearMap.shortComplexKer`,
  `LinearMap.shortExact_shortComplexKer`,
- source/core/bridge triage:
  `source-facing`: the relation submodule, its quotient module, the descended map onto
    `Ideal.span (Set.range f)`, and its kernel;
  `core/canonical`: the relation linear map
    `Module.piEquiv (Fin n × Fin n) R (Fin n → R) (idealGeneratorRelationVector f)`, the
    linear-combination owner `koszulLinearForm f`, and the canonical short complex
    `(idealGeneratorRelationModuleToSpan f).shortComplexKer`;
  `bridge/view`: the identifications of these ranges with the source-facing relation submodule and
    with `Ideal.span (Set.range f)` via `Module.range_piEquiv` and `Ideal.submodule_span_eq`.
- primitive data: the relation vectors `idealGeneratorRelationVector f` and the
  linear-combination owner `koszulLinearForm f`;
- derived API: the relation submodule, its quotient module, short exactness of the canonical
  quotient-descended map `idealGeneratorRelationToSpan f`, its kernel short complex, and the
  annihilator containment for
  `idealGeneratorRelationKernel f`.
-/

/-- The basic relation vector `fᵢ eⱼ - fⱼ eᵢ` in the free module on `Fin n`. -/
private def idealGeneratorRelationVector (f : Fin n → R) (ij : Fin n × Fin n) : Fin n → R :=
  f ij.1 • Pi.basisFun R (Fin n) ij.2 - f ij.2 • Pi.basisFun R (Fin n) ij.1

/-- The canonical linear map whose image generates the relation submodule. -/
private abbrev idealGeneratorRelationMap (f : Fin n → R) :
    (Fin n × Fin n → R) →ₗ[R] Fin n → R :=
  piEquiv (Fin n × Fin n) R (Fin n → R) (idealGeneratorRelationVector f)

/-- The submodule of relations generated by the vectors `fᵢ eⱼ - fⱼ eᵢ`, realized through the
owner map `Module.piEquiv`. -/
abbrev idealGeneratorRelationSubmodule (f : Fin n → R) : Submodule R (Fin n → R) :=
  (idealGeneratorRelationMap f).range

/-- The module on generators `eᵢ` subject only to the relations `fᵢ eⱼ = fⱼ eᵢ`. -/
abbrev idealGeneratorRelationModule (f : Fin n → R) :=
  (Fin n → R) ⧸ idealGeneratorRelationSubmodule f

private theorem range_koszulLinearForm_eq_span (f : Fin n → R) :
    LinearMap.range (koszulLinearForm f) = Ideal.span (Set.range f) := by
  simpa [koszulLinearForm] using
    ((range_piEquiv (Fin n) R R f).trans Ideal.submodule_span_eq)

/-- The canonical linear-combination map from the free module on `eᵢ` to the ideal generated by
the tuple `f`, expressed through the chapter owner `koszulLinearForm`. -/
private def idealGeneratorRelationToSpan (f : Fin n → R) :
    (Fin n → R) →ₗ[R] Ideal.span (Set.range f) :=
  (LinearEquiv.ofEq _ _ (range_koszulLinearForm_eq_span f)).toLinearMap ∘ₗ
    (koszulLinearForm f).rangeRestrict

-- Proof sketch: it suffices to check each generator `fᵢ eⱼ - fⱼ eᵢ`; under
-- `idealGeneratorRelationToSpan f` this maps to `fᵢ fⱼ - fⱼ fᵢ`, which is zero.
/-- The canonical map to `Ideal.span (Set.range f)` kills the basic relation map. -/
private theorem idealGeneratorRelationToSpan_comp_relationMap
    (f : Fin n → R) :
    idealGeneratorRelationToSpan f ∘ₗ idealGeneratorRelationMap f = 0 := sorry

/-- The defining relations lie in the kernel of the canonical map to the generated ideal. -/
private theorem idealGeneratorRelationSubmodule_le_ker_toSpan
    (f : Fin n → R) :
    idealGeneratorRelationSubmodule f ≤ (idealGeneratorRelationToSpan f).ker :=
  LinearMap.range_le_ker_iff.mpr (idealGeneratorRelationToSpan_comp_relationMap f)

/-- The canonical map from the presented relation module onto the ideal generated by `f`. -/
def idealGeneratorRelationModuleToSpan (f : Fin n → R) :
    idealGeneratorRelationModule f →ₗ[R] Ideal.span (Set.range f) :=
  (idealGeneratorRelationSubmodule f).liftQ (idealGeneratorRelationToSpan f)
    (idealGeneratorRelationSubmodule_le_ker_toSpan f)

/-- The kernel `K` of the canonical map from the relation module onto the ideal generated by `f`.
-/
abbrev idealGeneratorRelationKernel (f : Fin n → R) :
    Submodule R (idealGeneratorRelationModule f) :=
  (idealGeneratorRelationModuleToSpan f).ker

-- Proof sketch: the descended map is surjective because the classes of the basis vectors map to
-- the generators `fᵢ` of `Ideal.span (Set.range f)`. If `m = ∑ aᵢ eᵢ` maps to zero, then
-- `∑ aᵢ fᵢ = 0`, and multiplying the class of `m` by any generator `fⱼ` rewrites to
-- `(∑ aᵢ fᵢ) eⱼ = 0`; by span induction, the whole ideal annihilates the kernel.
/-- The canonical map from the relation module to `Ideal.span (Set.range f)` is surjective. -/
theorem idealGeneratorRelationModuleToSpan_surjective
    (f : Fin n → R) :
    Function.Surjective (idealGeneratorRelationModuleToSpan f) := sorry

/-- Lemma 15.90.5: the relation-module presentation of the ideal generated by `f` yields the
canonical short exact sequence
`0 ⟶ idealGeneratorRelationKernel f ⟶ idealGeneratorRelationModule f ⟶
  Ideal.span (Set.range f) ⟶ 0`. -/
theorem idealGeneratorRelationShortExact
    (f : Fin n → R) :
    (idealGeneratorRelationModuleToSpan f).shortComplexKer.ShortExact :=
  LinearMap.shortExact_shortComplexKer
    (idealGeneratorRelationModuleToSpan_surjective f)

/-- Lemma 15.90.5 also shows that the ideal `Ideal.span (Set.range f)` annihilates the kernel
`idealGeneratorRelationKernel f`. -/
theorem span_le_annihilator_idealGeneratorRelationKernel
    (f : Fin n → R) :
    Ideal.span (Set.range f) ≤ (idealGeneratorRelationKernel f).annihilator := sorry

end

/-! ### Lemma_15_90_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open ModuleCat
open scoped KoszulComplex
open Ideal.Quotient (eq_zero_iff_mem)

universe u

section

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: first Koszul homology with coefficients, its quotient presentation by cycles and
  boundaries, and the exact sequence obtained from the relation presentation of Lemma `15.90.5`;
- sampled owner declarations:
  `K^•(f)`,
  `HomologicalComplex.tensorObj`,
  `RingTheory.Sequence.IsH1RegularOn`,
  `CategoryTheory.ShortComplex.moduleCatToCycles`,
  `CategoryTheory.ShortComplex.moduleCatHomologyIso`,
  `LinearMap.quotKerEquivOfSurjective`,
  `Ext.precompOfLinear`;
- source/core/bridge triage:
  `source-facing`: the first Koszul homology object `koszulH1 f N`;
  `core/canonical`: degree-`1` homology of the chapter owner `K^•(f)` after tensoring with the
    coefficient module `N`, equivalently the owner predicate `RingTheory.Sequence.IsH1RegularOn`;
  `bridge/view`: the explicit three-term quotient model `koszulH1ModelShortComplex f N`, its
    quotient presentation `koszulH1Presentation f N`, and the vanishing bridge back to the chapter
    owner abstraction;
- primitive data: the owner complex `K^•(f) ⊗ N`, the relation map on tuples, the diagonal linear
  map, the three-term source-facing quotient model, and the linear connecting map
  `Hom_R(I, N) → Ext¹_R(R / I, N)`;
- derived API: the owner-level short exact sequence
  `0 ⟶ Ext¹_R(R / I, N) ⟶ koszulH1 f N ⟶ Hom_R(K, N) ⟶ 0`.
-/

private abbrev moduleSingle₀ (R : Type u) [CommRing R] (N : Type u) [AddCommGroup N] [Module R N] :
    ChainComplex (ModuleCat R) ℕ :=
  (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R N)

private abbrev koszulComplexWithModule (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N] :
    ChainComplex (ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj (K^•(f)) (moduleSingle₀ R N)

/-- The tuple condition `fᵢ xⱼ = fⱼ xᵢ` defining degree-one Koszul cycles. -/
def koszulFirstCycleCondition (x : Fin n → N) : Prop :=
  ∀ i j : Fin n, f i • x j = f j • x i

/-- The linear map whose `(i, j)`-component is `x ↦ fᵢ xⱼ - fⱼ xᵢ`. -/
def koszulFirstCycleMap : (Fin n → N) →ₗ[R] Fin n × Fin n → N :=
  LinearMap.pi fun ij ↦
    (DistribSMul.toLinearMap R N (f ij.1)).comp (LinearMap.proj ij.2) -
      (DistribSMul.toLinearMap R N (f ij.2)).comp (LinearMap.proj ij.1)

/-- The submodule of degree-one Koszul cycles for the finite family `f`. -/
def koszulFirstCycles : Submodule R (Fin n → N) :=
  LinearMap.ker (koszulFirstCycleMap f N)

/-- The tuple condition defining degree-one Koszul cycles is equivalent to membership in the
kernel of the canonical relation map. -/
theorem koszulFirstCycleCondition_iff_mem_ker (x : Fin n → N) :
    koszulFirstCycleCondition f N x ↔ x ∈ LinearMap.ker (koszulFirstCycleMap f N) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    ext ij
    exact sub_eq_zero.mpr (hx ij.1 ij.2)
  · intro hx i j
    exact sub_eq_zero.mp (congrFun hx (i, j))

/-- Membership in the first-cycle submodule is exactly the pairwise Koszul cycle condition. -/
theorem mem_koszulFirstCycles_iff (x : Fin n → N) :
    x ∈ koszulFirstCycles f N ↔ koszulFirstCycleCondition f N x := by
  rw [koszulFirstCycles, koszulFirstCycleCondition_iff_mem_ker]

/-- An element of the first-cycle submodule satisfies the pairwise Koszul cycle condition. -/
theorem koszulFirstCycleCondition_of_mem {x : Fin n → N} (hx : x ∈ koszulFirstCycles f N) :
    koszulFirstCycleCondition f N x :=
  (mem_koszulFirstCycles_iff f N x).1 hx

/-- The diagonal linear map `x ↦ (f₁x, …, fₙx)` landing in the ambient tuple module. -/
def koszulDiagonalLinearMap : N →ₗ[R] Fin n → N :=
  LinearMap.pi fun i ↦ DistribSMul.toLinearMap R N (f i)

/-- The explicit three-term Koszul bridge model with coefficients in `N`,
`N ⟶ N^n ⟶ N^(n × n)`, whose homology presents the owner `H₁(N, f_•)`. -/
def koszulH1ModelShortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (koszulDiagonalLinearMap f N) (koszulFirstCycleMap f N) <| by
    ext x ij
    change f ij.1 • (f ij.2 • x) - f ij.2 • (f ij.1 • x) = 0
    rw [smul_smul, smul_smul, mul_comm (f ij.1) (f ij.2), sub_self]

/-- The source-facing first Koszul homology object `H₁(N, f_•)`, given as the quotient
`ker / im` of the three-term model `N ⟶ N^n ⟶ N^(n × n)`. -/
abbrev koszulH1 : ModuleCat R :=
  (koszulH1ModelShortComplex f N).homology

/-- The source-facing owner `koszulH1 f N` vanishes exactly when the chapter's canonical
degree-`1` Koszul homology with coefficients in `N` vanishes. -/
theorem isZero_koszulH1_iff_isZero_koszulComplexWithModule_homology :
    IsZero (koszulH1 f N) ↔ IsZero ((koszulComplexWithModule f N).homology 1) := by
  sorry

/-- The source-facing owner `koszulH1 f N` is the vanishing predicate used by the chapter owner
`RingTheory.Sequence.IsH1RegularOn`. -/
theorem isH1RegularOn_iff_isZero_koszulH1 :
    RingTheory.Sequence.IsH1RegularOn N f ↔ IsZero (koszulH1 f N) := by
  sorry

/-- The diagonal tuple attached to an element of `N` is a degree-one Koszul cycle. -/
theorem koszulDiagonalTuple_mem_firstCycles (x : N) :
    koszulFirstCycleCondition f N (fun i : Fin n ↦ f i • x) := by
  rw [← mem_koszulFirstCycles_iff]
  rw [koszulFirstCycles, LinearMap.mem_ker]
  ext ij
  change f ij.1 • (f ij.2 • x) - f ij.2 • (f ij.1 • x) = 0
  rw [smul_smul, smul_smul, mul_comm (f ij.1) (f ij.2), sub_self]

/-- The diagonal linear map lands in the first-cycle submodule. -/
theorem koszulDiagonalLinearMap_mem_firstCycles (x : N) :
    koszulDiagonalLinearMap f N x ∈ koszulFirstCycles f N := by
  simpa [koszulDiagonalLinearMap] using
    (mem_koszulFirstCycles_iff f N (koszulDiagonalLinearMap f N x)).2
      (koszulDiagonalTuple_mem_firstCycles f N x)

/-- The diagonal map `x ↦ (f₁x, …, fₙx)` from `N` into the first-cycle module. -/
abbrev koszulDiagonalMap : N →ₗ[R] koszulFirstCycles f N :=
  (koszulH1ModelShortComplex f N).moduleCatToCycles

/-- The explicit quotient presentation of `H₁(N, f_•)`. This remains a bridge/view; the public
owner is `koszulH1 f N`. -/
abbrev koszulH1Presentation :=
  (koszulH1ModelShortComplex f N).moduleCatLeftHomologyData.H

/-- The canonical comparison from the owner `koszulH1 f N` to its quotient presentation. -/
noncomputable abbrev koszulH1IsoPresentation :
    koszulH1 f N ≅ ModuleCat.of R (koszulH1Presentation f N) :=
  (koszulH1ModelShortComplex f N).moduleCatHomologyIso

/-- The free-module map determined by a tuple `(x₁, …, xₙ)` in `N^n`. -/
def koszulTupleLinearMap (x : Fin n → N) : (Fin n → R) →ₗ[R] N :=
  ∑ i : Fin n, (LinearMap.proj i).smulRight (x i)

-- Proof sketch: each generator `fᵢ eⱼ - fⱼ eᵢ` of the relation submodule is sent to
-- `fᵢ • xⱼ - fⱼ • xᵢ`, which vanishes because `x` satisfies the cycle condition.
/-- A first cycle induces a linear map on the relation module of Lemma `15.90.5`. -/
theorem idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap
    {x : Fin n → N}
    (hx : koszulFirstCycleCondition f N x) :
    idealGeneratorRelationSubmodule f ≤
      LinearMap.ker (koszulTupleLinearMap N x) := sorry

/-- A first cycle determines a linear map from the relation module of Lemma `15.90.5` to `N`. -/
def koszulCycleToRelationModuleHom
    (x : koszulFirstCycles f N) :
    idealGeneratorRelationModule f →ₗ[R] N :=
  (idealGeneratorRelationSubmodule f).liftQ
    (koszulTupleLinearMap N x.1)
    (idealGeneratorRelationSubmodule_le_ker_koszulTupleLinearMap f N
      (koszulFirstCycleCondition_of_mem f N x.2))

-- Proof sketch: the assignment `x ↦ (M → N)` is linear because the induced map on the free
-- module depends linearly on the tuple entries, and passage to the quotient preserves linearity.
/-- The construction sending a first cycle to a map from the relation module is additive. -/
theorem koszulCycleToRelationModuleHom_map_add
    (x y : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (x + y) =
      koszulCycleToRelationModuleHom f N x +
        koszulCycleToRelationModuleHom f N y := sorry

-- Proof sketch: the induced map on the relation module scales pointwise with the tuple, so the
-- assignment is linear in the scalar parameter as well.
/-- The construction sending a first cycle to a map from the relation module is `R`-linear. -/
theorem koszulCycleToRelationModuleHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    koszulCycleToRelationModuleHom f N (a • x) =
      a • koszulCycleToRelationModuleHom f N x := sorry

-- Proof sketch: two first cycles induce maps `K → N`, and restricting the sum of their maps from
-- the relation module agrees with the sum of the restrictions.
/-- The canonical map from first cycles to `Hom_R(K, N)` is additive. -/
theorem koszulCyclesToKernelHom_map_add
    (x y : koszulFirstCycles f N) :
    (koszulCycleToRelationModuleHom f N (x + y)).comp
        (idealGeneratorRelationKernel f).subtype =
      (koszulCycleToRelationModuleHom f N x).comp
          (idealGeneratorRelationKernel f).subtype +
        (koszulCycleToRelationModuleHom f N y).comp
          (idealGeneratorRelationKernel f).subtype := sorry

-- Proof sketch: scalar multiplication commutes with restricting the induced map from the relation
-- module to the kernel `K`.
/-- The canonical map from first cycles to `Hom_R(K, N)` is `R`-linear. -/
theorem koszulCyclesToKernelHom_map_smul
    (a : R) (x : koszulFirstCycles f N) :
    (koszulCycleToRelationModuleHom f N (a • x)).comp
        (idealGeneratorRelationKernel f).subtype =
      a •
        (koszulCycleToRelationModuleHom f N x).comp
          (idealGeneratorRelationKernel f).subtype := sorry

/-- The map from first cycles to `Hom_R(K, N)`, where `K` is the kernel from Lemma `15.90.5`. -/
def koszulCyclesToKernelHom :
    koszulFirstCycles f N →ₗ[R]
      (idealGeneratorRelationKernel f →ₗ[R] N) where
  toFun x :=
    (koszulCycleToRelationModuleHom f N x).comp
      (idealGeneratorRelationKernel f).subtype
  map_add' := koszulCyclesToKernelHom_map_add f N
  map_smul' := koszulCyclesToKernelHom_map_smul f N

-- Proof sketch: the tuple `i ↦ fᵢ x` defines a map from the relation module that factors through
-- the canonical surjection to the ideal `(f₁, …, fₙ)`, so its restriction to the kernel `K`
-- vanishes.
/-- Diagonal tuples induce the zero map on the kernel `K` of Lemma `15.90.5`. -/
theorem koszulDiagonalMap_mem_ker_cyclesToKernelHom
    (x : N) :
    koszulCyclesToKernelHom f N (koszulDiagonalMap f N x) = 0 := sorry

-- Proof sketch: every element of the range of the diagonal map is represented by some tuple
-- `i ↦ fᵢ x`, and the previous lemma shows that such tuples are sent to zero on `K`.
/-- The diagonal image is contained in the kernel of the canonical map to `Hom_R(K, N)`. -/
theorem koszulDiagonalMap_le_ker_cyclesToKernelHom :
    LinearMap.range (koszulDiagonalMap f N) ≤ LinearMap.ker (koszulCyclesToKernelHom f N) :=
  sorry

/-- The canonical map from the cycle-quotient presentation in degree one to `Hom_R(K, N)`. -/
def koszulH1PresentationToHomKernel :
    koszulH1Presentation f N →ₗ[R]
      (idealGeneratorRelationKernel f →ₗ[R] N) :=
  (LinearMap.range (koszulDiagonalMap f N)).liftQ
    (koszulCyclesToKernelHom f N)
    (koszulDiagonalMap_le_ker_cyclesToKernelHom f N)

/-- The canonical short complex `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` for
`I = Ideal.span (Set.range f)`. -/
private def idealSpanQuotientShortComplex :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (Ideal.span (Set.range f)).subtype
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      exact eq_zero_iff_mem.mpr x.2)

-- Proof sketch: this is the standard short exact sequence attached to the quotient map
-- `R → R ⧸ Ideal.span (Set.range f)`.
/-- The ideal quotient short complex `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` is short exact. -/
private theorem idealSpanQuotientShortComplex_shortExact :
    (idealSpanQuotientShortComplex f).ShortExact := by
  sorry

/-- Evaluating an `R`-linear map `I → N` on the generators `fᵢ` gives a degree-one Koszul cycle. -/
def idealSpanHomToKoszulFirstCycles :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R] koszulFirstCycles f N where
  toFun φ :=
    ⟨fun i ↦ φ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩, by
      rw [mem_koszulFirstCycles_iff]
      intro i j
      rw [← φ.map_smul, ← φ.map_smul]
      apply congrArg φ
      apply Subtype.ext
      simp [smul_eq_mul, mul_comm]⟩
  map_add' φ ψ := by
    ext i
    simp
  map_smul' a φ := by
    ext i
    simp

/-- The map `N → Hom_R(I, N)` induced by the inclusion `I ↪ R`, sending `x` to
`(a ↦ a • x)`. -/
def spanToIdealSpanHom :
    N →ₗ[R] ((Ideal.span (Set.range f)) →ₗ[R] N) where
  toFun x :=
    { toFun a := (a : R) • x
      map_add' a b := by
        simp [add_smul]
      map_smul' r a := by
        simp [smul_smul] }
  map_add' x y := by
    ext a
    simp [smul_add]
  map_smul' a x := by
    ext b
    simp [smul_smul, mul_comm]

/-- The map `Hom_R(I, N) → koszulH1Presentation f N` induced by evaluation on the generators
`fᵢ`, modulo diagonal boundaries. -/
def idealSpanHomToKoszulH1Presentation :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R] koszulH1Presentation f N :=
  (LinearMap.range (koszulDiagonalMap f N)).mkQ.comp (idealSpanHomToKoszulFirstCycles f N)

/-- The map `N → Hom_R(I, N)` identifies with the diagonal map after passing to the cycle
presentation. -/
theorem idealSpanHomToKoszulH1Presentation_comp_spanToIdealSpanHom :
    idealSpanHomToKoszulH1Presentation f N ∘ₗ spanToIdealSpanHom f N = 0 := by
  sorry

/-- The connecting map `Hom_R(I, N) → Ext¹_R(R / I, N)` for the canonical quotient sequence
`0 ⟶ I ⟶ R ⟶ R / I ⟶ 0`. -/
noncomputable def idealSpanHomToExt :
    ((Ideal.span (Set.range f)) →ₗ[R] N) →ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 :=
  let hS := idealSpanQuotientShortComplex_shortExact f
  (hS.extClass.precompOfLinear R (ModuleCat.of R N) (Nat.add_zero 1)) ∘ₗ
    (((Ext.linearEquiv₀ :
        Ext (ModuleCat.of R (Ideal.span (Set.range f))) (ModuleCat.of R N) 0 ≃ₗ[R]
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N)).symm.toLinearMap) ∘ₗ
      ((ModuleCat.homLinearEquiv :
          (ModuleCat.of R (Ideal.span (Set.range f)) ⟶ ModuleCat.of R N) ≃ₗ[R]
            ((Ideal.span (Set.range f)) →ₗ[R] N)).symm.toLinearMap))

-- Proof sketch: this is the degree-`1` connecting map in the contravariant long exact Ext
-- sequence for `0 → I → R → R / I → 0`; surjectivity follows because `Ext¹_R(R, N) = 0`.
/-- The connecting map `Hom_R(I, N) → Ext¹_R(R / I, N)` for the quotient sequence is surjective. -/
theorem idealSpanHomToExt_surjective :
    Function.Surjective (idealSpanHomToExt f N) := by
  sorry

-- Proof sketch: if two maps `I → N` differ by multiplication with an element of `N`, they define
-- the same class in `koszulH1Presentation f N`, and the only additional relations come from the
-- kernel of the connecting map above.
/-- The source-facing map `Hom_R(I, N) → koszulH1Presentation f N` kills the kernel of the
connecting map to `Ext¹`. -/
theorem ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation :
    LinearMap.ker (idealSpanHomToExt f N) ≤
      LinearMap.ker (idealSpanHomToKoszulH1Presentation f N) := by
  sorry

/-- The quotient of `Hom_R(I, N)` by the kernel of the connecting map maps canonically to the
source-facing degree-one Koszul quotient. -/
noncomputable def idealSpanHomKerToKoszulH1Presentation :
    (((Ideal.span (Set.range f)) →ₗ[R] N) ⧸ LinearMap.ker (idealSpanHomToExt f N)) →ₗ[R]
      koszulH1Presentation f N :=
  (LinearMap.ker (idealSpanHomToExt f N)).liftQ
    (idealSpanHomToKoszulH1Presentation f N)
    (ker_idealSpanHomToExt_le_ker_idealSpanHomToKoszulH1Presentation f N)

/-- The canonical left map
`Ext¹_R(R / Ideal.span (Set.range f), N) ⟶ koszulH1Presentation f N`. -/
noncomputable def koszulExtToH1Presentation :
    Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1 →ₗ[R]
      koszulH1Presentation f N :=
  idealSpanHomKerToKoszulH1Presentation f N ∘ₗ
    ((idealSpanHomToExt f N).quotKerEquivOfSurjective
      (idealSpanHomToExt_surjective f N)).symm.toLinearMap

-- Proof sketch: a map `I → N` induces a tuple map on the relation module that factors through
-- `I`; its restriction to the kernel `K` is therefore zero, and the factorization survives the
-- quotient by boundaries and the identification with `Ext¹`.
/-- The canonical left map to `koszulH1Presentation f N` composes trivially with the map to
`Hom_R(K, N)`. -/
theorem koszulH1PresentationToHomKernel_comp_koszulExtToH1Presentation :
    (koszulH1PresentationToHomKernel f N).comp (koszulExtToH1Presentation f N) = 0 := by
  sorry

/-- The canonical map `H₁(N, f_•) ⟶ Hom_R(K, N)` induced from the quotient presentation. -/
noncomputable def koszulH1ToHomKernel :
    koszulH1 f N ⟶ ModuleCat.of R (idealGeneratorRelationKernel f →ₗ[R] N) :=
  (koszulH1IsoPresentation f N).hom ≫ ModuleCat.ofHom (koszulH1PresentationToHomKernel f N)

/-- The canonical map `Hom_R(I, N) ⟶ H₁(N, f_•)` induced from the quotient presentation. -/
noncomputable def idealSpanHomToKoszulH1 :
    ModuleCat.of R (((Ideal.span (Set.range f)) →ₗ[R] N)) ⟶ koszulH1 f N :=
  ModuleCat.ofHom (idealSpanHomToKoszulH1Presentation f N) ≫ (koszulH1IsoPresentation f N).inv

/-- The canonical left map `Ext¹_R(R / I, N) ⟶ H₁(N, f_•)`. -/
noncomputable def koszulExtToH1 :
    ModuleCat.of R
        (Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R N) 1) ⟶
      koszulH1 f N :=
  ModuleCat.ofHom (koszulExtToH1Presentation f N) ≫ (koszulH1IsoPresentation f N).inv

/-- The owner-level left map `Ext¹_R(R / I, N) ⟶ H₁(N, f_•)` composes trivially with the map to
`Hom_R(K, N)`. -/
theorem koszulH1ToHomKernel_comp_koszulExtToH1 :
    koszulExtToH1 f N ≫ koszulH1ToHomKernel f N = 0 := by
  sorry

/-- The canonical short complex
`0 ⟶ Ext¹_R(R / Ideal.span (Set.range f), N) ⟶ koszulH1 f N ⟶ Hom_R(K, N)`. -/
def koszulH1ShortComplex :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (koszulExtToH1 f N)
    (koszulH1ToHomKernel f N)
    (koszulH1ToHomKernel_comp_koszulExtToH1 f N)

-- Proof sketch: compare the quotient description of `H₁` with the exact sequence
-- `Hom_R(I, N) → Ext¹_R(R / I, N)` from the quotient short exact sequence
-- `0 → I → R → R / I → 0`, and then use Lemma `15.90.5` to identify the cokernel term with
-- `Hom_R(K, N)`.
/-- Lemma 15.90.6: for
`I = Ideal.span (Set.range f)` and `K = idealGeneratorRelationKernel f`, the quotient
presentation short complex
`0 ⟶ Ext¹_R(R / I, N) ⟶ koszulH1 f N ⟶ Hom_R(K, N) ⟶ 0`
is short exact. -/
theorem koszulH1ShortComplex_shortExact :
    (koszulH1ShortComplex f N).ShortExact := by
  sorry

end

/-! ### Lemma_15_90_7 (from Chap15) -/
noncomputable section

universe u

section

variable {R : Type u} [CommRing R] {n : ℕ}
variable (f : Fin n → R) (N : Type u) [AddCommGroup N] [Module R N]

-- Proof sketch: for each generator `f i`, multiplication by `f i` on a cycle tuple
-- `(x₁, …, xₙ)` is represented by the diagonal boundary `x i ↦ (f₁ x i, …, fₙ x i)`, so the
-- resulting class in the owner `koszulH1 f N` is killed by `f i`; passing to the ideal span gives
-- the annihilator containment.
/-- Lemma 15.90.7: if `I = Ideal.span (Set.range f)` is generated by the finite family `f`, then
for every `R`-module `N` the first Koszul homology group `H₁(N, f_•)` is annihilated by `I`. -/
theorem ideal_span_le_annihilator_koszulH1 :
    Ideal.span (Set.range f) ≤ Module.annihilator R (koszulH1 f N) := by
  have hpresentation :
      Ideal.span (Set.range f) ≤ Module.annihilator R (koszulH1Presentation f N) := by
    rw [Ideal.span_le]
    intro a ha
    rcases ha with ⟨i, rfl⟩
    change f i ∈ Module.annihilator R (koszulH1Presentation f N)
    rw [Module.mem_annihilator]
    intro z
    refine Quotient.inductionOn' z ?_
    intro x
    change Submodule.Quotient.mk ((f i) • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨x.1 i, ?_⟩
    apply Subtype.ext
    change koszulDiagonalLinearMap f N (x.1 i) = (f i) • x.1
    ext j
    change f j • x.1 i = f i • x.1 j
    simpa using (koszulFirstCycleCondition_of_mem f N x.2) j i
  rw [Ideal.span_le]
  intro a ha
  change a ∈ Module.annihilator R (koszulH1 f N)
  rw [Module.mem_annihilator]
  intro z
  have ha' : a ∈ Module.annihilator R (koszulH1Presentation f N) :=
    hpresentation (Ideal.subset_span ha)
  rw [Module.mem_annihilator] at ha'
  have hz : a • (koszulH1IsoPresentation f N).hom.hom z = 0 :=
    ha' ((koszulH1IsoPresentation f N).hom.hom z)
  have hsection : (koszulH1IsoPresentation f N).inv.hom ((koszulH1IsoPresentation f N).hom.hom z) = z := by
    exact congrArg (fun g ↦ g z) (congrArg ModuleCat.Hom.hom (koszulH1IsoPresentation f N).hom_inv_id)
  calc
    a • z = a • (koszulH1IsoPresentation f N).inv.hom ((koszulH1IsoPresentation f N).hom.hom z) := by
      rw [hsection]
    _ = (koszulH1IsoPresentation f N).inv.hom (a • (koszulH1IsoPresentation f N).hom.hom z) := by
      rw [LinearMap.map_smul]
    _ = (koszulH1IsoPresentation f N).inv.hom 0 := by
      simpa using congrArg (koszulH1IsoPresentation f N).inv.hom hz
    _ = 0 := by
      rw [LinearMap.map_zero]

end

/-! ### Lemma_15_90_8 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: flat base change for `Ext` in `ModuleCat`, expressed through the canonical
  change-of-rings comparison coming from the `extendScalars`/`restrictScalars` adjunction;
- inspected same-domain owners:
  `Functor.mapExtAddHom`,
  `moduleCatExtFlatBaseChangeComparison`,
  `moduleCatExtFlatBaseChangeAdjointComparison`,
  `moduleCat_ext_flat_baseChange_adjoint_bijective`;
- best owner abstraction: the Chapter 10 owner theorem
  `moduleCat_ext_flat_baseChange_adjoint_bijective`, with degree-`1` surjectivity as a thin
  source-facing specialization;
- primitive data: the ring map `R → S`, an `R`-module `M`, an `S`-module `N`, and flatness;
- derived API: the degree-`1` surjectivity consequence.

Source/core/bridge triage:
- `source-facing`: the degree-`1` surjectivity formulation used in this chapter;
- `core/canonical`: `moduleCatExtFlatBaseChangeAdjointComparison` and its owner theorem
  `moduleCat_ext_flat_baseChange_adjoint_bijective`;
- `bridge/view`: `Functor.mapExtAddHom` for `extendScalars (algebraMap R S)` together with the
  `extendScalars`/`restrictScalars` adjunction.
-/

-- Proof sketch: this is exactly the degree-`1` surjectivity half of the canonical flat
-- base-change bijection for `Ext`, already established in Chapter `10`.
/-- Lemma 15.90.8: for a flat ring map `R → S`, the canonical adjoint flat base-change
comparison
`Ext¹_R(M, N|_R) → Ext¹_S(S ⊗[R] M, N)`
is surjective. -/
theorem moduleCatExtOneFlatBaseChangeAdjointComparison_surjective
    (M : ModuleCat R) (N : ModuleCat S) (hflat : (algebraMap R S).Flat) :
    Function.Surjective (moduleCatExtFlatBaseChangeAdjointComparison M N hflat 1) :=
  (moduleCat_ext_flat_baseChange_adjoint_bijective M N hflat 1).2

end

/-! ### Lemma_15_90_9 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ}
variable (M : ModuleCat R)

-- Proof sketch: identify the displayed sequence with the truncation of the cone of the morphism
-- between the extended alternating Cech complexes for `R` and `S`. Lemma `15.90.4` gives that
-- morphism as a quasi-isomorphism, and flatness lets one tensor it with `M`. Equivalently, the
-- computational proof shows `Mono α` using the `I^∞`-torsion comparison map and proves
-- `ker β = range α` by reducing a compatible family to degree-one Koszul homology, then applying
-- Lemmas `15.90.2`, `15.90.3`, and `15.90.7`, yielding the canonical short-complex owner surface
-- `S.Exact ∧ Mono S.f`.
/-- Lemma 15.90.9: let `f : Fin t → R` generate the ideal `I = (f₁, …, fₜ)`. If `R → S` is flat
and the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the formal glueing complex
`0 → M → (S ⊗[R] M) × ∏ i, M_{f_i} → ∏ i, (S ⊗[R] M)_{f_i} × ∏ i j, M_{f_i f_j}` is exact. In
this library-facing formulation, the overlap term `M_{f_i f_j}` is represented by iterated away
localizations, and the exactness statement is expressed by the owner pair
`(formalGlueingModuleComplex S f M).Exact ∧ Mono (formalGlueingModuleComplex S f M).f`. -/
theorem formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective
    (f : Fin t → R) (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    (formalGlueingModuleComplex S f M).Exact ∧
      Mono (formalGlueingModuleComplex S f M).f :=
  sorry

end
