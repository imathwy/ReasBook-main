import Mathlib
import Mathlib.CategoryTheory.Retract

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_52_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]
variable [IsGrothendieckAbelian.{w} A]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.52.1:
- primary domain: compact objects in Grothendieck abelian categories and their bounded-complex
  representatives in the derived category, with generation data expressed through the canonical
  separator API for object properties;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`,
  `CategoryTheory.ObjectProperty.isSeparating_iff_epi`,
  `CategoryTheory.ObjectProperty.coproductFrom`,
  `CategoryTheory.isCompactObject_iff`,
  `CategoryTheory.additiveClosure`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `CategoryTheory.Retract`;
- best owner abstraction: the compactness owner `IsCompactObject`, applied both to the compact
  derived object `K` and to the generators `E ∈ S`, together with the separating owner
  `ObjectProperty.IsSeparating` for the generating family, the canonical bounded-support owners on
  a chosen cochain representative, and the direct-summand owner `Retract` for the bounded-complex
  conclusion;
- primitive-vs-derived split: the primitive source data are the separating property of the object
  property `fun Y : A ↦ Y ∈ S` and the compactness of each generator in `A`; the concrete
  epimorphic-coproduct presentation is derived from `ObjectProperty.isSeparating_iff_epi`, while
  the boundedness and termwise additive-closure condition are carried by `CochainComplex` support
  owners and the retract data are derived from the canonical owner `Retract`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that every compact object of `D(A)` is a direct summand of
  an object represented by a bounded complex with terms finite direct sums of generators;
- `core/canonical`: `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`, and `CategoryTheory.Retract`;
- `bridge/view`: the Chapter 13 owner `CategoryTheory.additiveClosure`, which records the
  finite-coproduct closure of the generator set up to isomorphism, together with the chosen
  cochain-complex representative `P` of the retract target `DerivedCategory.Q.obj P`.
-/

-- Proof sketch: apply the Stacks argument using compactness of `K` to force bounded-above
-- truncation, resolve `K` by a bounded-above complex of coproducts of elements of `S`, factor the
-- identity through a bounded subcomplex, and then shrink the remaining infinite summands one
-- degree at a time until each term is a finite coproduct of elements of `S`. The resulting
-- bounded complex yields an object of `D(A)` admitting `K` as a retract.
/-- Lemma 21.52.1: if `A` is a Grothendieck abelian category and `S` is a set of objects such
that every object of `A` is a quotient of a direct sum of elements of `S`, while every
`E ∈ S` is compact in `A`, then every compact object of `D(A)` is a direct summand of an object
represented by a bounded complex whose terms are finite direct sums of elements of `S`. -/
theorem compactObject_isRetract_of_finiteCoproductComplex_of_generatingSet
    (S : Set A) {K : DerivedCategory A} (hK : IsCompactObject K)
    (hgen : ObjectProperty.IsSeparating (fun Y : A ↦ Y ∈ S))
    (hsmall : ∀ ⦃E : A⦄, E ∈ S → IsCompactObject E) :
    ∃ (P : CochainComplex A ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧
        P.IsStrictlyLE b ∧
          (∀ i : Set.Icc a b, (additiveClosure fun Y : A ↦ Y ∈ S) (P.X i.1)) ∧
            Nonempty (Retract K (DerivedCategory.Q.obj P)) := sorry

end

end CategoryTheory.IsGrothendieckAbelian

/-! ### Lemma_21_52_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.IsGrothendieckAbelian

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

-- Proof sketch: apply `compactObject_isRetract_of_finiteCoproductComplex_of_generatingSet` to the
-- set of modules `j_{U!}\mathcal O_U` with `U` quasi-compact. Use Lemma `18.28.8` and the
-- quasi-compact covering hypothesis to obtain the generating epimorphism condition, and use the
-- identification `Hom(j_{U!}\mathcal O_U, -) = \Gamma(U, -)` together with Lemma `7.17.7` as
-- packaged in Lemma `18.30.4` to prove that each such generator is compact.
/-- Lemma 21.52.2: if every object of the ringed site admits a covering by quasi-compact objects,
then every compact object of `D(\mathcal O)` is a retract of an object represented by a bounded
complex whose terms are finite direct sums of modules `j_{U!}\mathcal O_U` with `U`
quasi-compact. -/
theorem compactObject_isRetract_of_finite_quasiCompact_extensionByZeroStructureComplex
    [IsGrothendieckAbelian.{w} Mod]
    (hcover : ∀ W : C, ∃ S : J.Cover W, ∀ I : S.Arrow, J.QuasiCompactObject I.Y)
    {K : DMod} (hK : IsCompactObject K) :
    ∃ (P : CochainComplex Mod ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧
        P.IsStrictlyLE b ∧
          (∀ i : Set.Icc a b,
            CategoryTheory.additiveClosure
              (fun ℱ : Mod ↦ ∃ U : C, J.QuasiCompactObject U ∧
                ℱ = localizedStructureModuleExtensionByZero 𝒪 U)
              (P.X i.1)) ∧
            Nonempty (Retract K (DerivedCategory.Q.obj P)) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_52_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

attribute [local instance] HasDerivedCategory.standard

variable [Abelian Mod]

local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Lemma 21.52.3:
- primary domain: bounded-below coproduct preservation in the derived category of sheaves of
  modules, expressed by the represented `Hom` functor from `j_{U!}\mathcal O_U[0]`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_homEquiv`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.preadditiveCoyoneda.obj`;
- best owner abstraction: the source-facing owner is
  `localizedStructureModuleExtensionByZeroDegreeZero`, while the canonical hypothesis layer is
  ordinary sheaf cohomology via `Sheaf.cohomologyPresheafFunctor` on underlying additive sheaves;
- primitive data: the object `U`, the direct-sum compatibility of the ordinary cohomology
  functors `H^p(U, -)`, and the bounded-below coproduct object `∐ M`;
- derived API: the represented `Hom`-functor coproduct comparison for
  `j_{U!}\mathcal O_U[0]`.

Source/core/bridge triage:
- `source-facing`: the bounded-below coproduct comparison for `j_{U!}\mathcal O_U[0]`;
- `core/canonical`: `Sheaf.cohomologyPresheafFunctor` together with the owner
  `localizedStructureModuleExtensionByZero 𝒪 U`;
- `bridge/view`: `preadditiveCoyoneda.obj (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))`.
-/

/-- The degree-zero derived object attached to the standard generator `j_{U!}\mathcal O_U`. -/
abbrev localizedStructureModuleExtensionByZeroDegreeZero
    (U : C) : DMod :=
  (single0).obj (localizedStructureModuleExtensionByZero 𝒪 U)

-- Proof sketch: identify `Hom_D(j_{U!}\mathcal O_U[0], -)` with the degree-zero objectwise
-- cohomology functor at `U` using the adjunction from `18.19.2.1`. Then choose a lower bound for
-- the coproduct object `∐ M_i`, represent the summands by uniformly bounded-below complexes of
-- injectives, take their termwise direct sum, and apply the hypothesis that `H^p(U, -)` commutes
-- with direct sums to compare the resulting cohomology groups.
/- Lemma 21.52.3: if for a ringed site `(\mathcal C, \mathcal O)` and an object `U` the functors
`\mathcal F \mapsto H^p(U, \mathcal F)` commute with direct sums for all `p`, then the degree-zero
derived object attached to `j_{U!}\mathcal O_U` is compact with respect to bounded-below direct
sums: whenever a family `M_i` in `D(\mathcal O)` has a coproduct whose total object is bounded
below, the Hom group from `j_{U!}\mathcal O_U[0]` to that coproduct is canonically the direct sum
of the Hom groups to the summands. In Lean this canonical direct-sum comparison is encoded as
preservation of the coproduct colimit by the represented functor. -/
instance localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow
    (U : C) {ι : Type u} (M : ι → DMod) [HasCoproduct M]
    (hcomm :
      ∀ (p : ℕ) (ι : Type u),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
            Sheaf.cohomologyPresheafFunctor J p ⋙
              (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj
        (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))) := by
  sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_52_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u wI

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasFiniteWidePullbacks C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "D" => DerivedCategory Mod

/-- The index type of the degree-`n` iterated Čech intersections of a chosen covering `cover`. -/
abbrev selectedCoverCechIntersectionIndex
    {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of the `i`-th degree-`n` iterated Čech intersection of `cover`. -/
abbrev selectedCoverCechIntersectionObject
    {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : selectedCoverCechIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

/-- The site-theoretic hypothesis that `B` admits a cofinal system `Cov` of finite coverings whose
members and all iterated Čech intersections remain in `B`. -/
structure CofinalFiniteCoverings
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop where
  cover_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → (J.over U).CoversTop cover.obj
  finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → Finite cover.I
  target_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → U ∈ B
  members_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → ∀ i : cover.I, (cover.obj i).left ∈ B
  intersections_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → ∀ n : ℕ, ∀ i : selectedCoverCechIntersectionIndex cover n,
      selectedCoverCechIntersectionObject cover n i ∈ B
  cofinal : ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type wI⦄ (family : ι → Over U),
    (J.over U).CoversTop family →
      ∃ cover : FormalCoproduct (Over U),
        cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family)

end

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasFiniteWidePullbacks C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "D" => DerivedCategory Mod

-- Proof sketch: first use Lemma `21.16.1` to show that for each `U ∈ B` the functors
-- `\mathcal F \mapsto H^p(U,\mathcal F)` commute with direct sums, by writing a direct sum as the
-- filtered colimit of its finite partial sums. Then apply Lemma `21.52.3`, which upgrades this
-- cohomological direct-sum compatibility to the bounded-below Hom-coproduct comparison for
-- `j_{U!}\mathcal O_U[0]`.
/-- Lemma 21.52.4: under the cofinal finite covering hypotheses on `B` and `Cov`, the degree-zero
derived object attached to `j_{U!} O_U` satisfies the bounded-below coproduct comparison over each
`U ∈ B`. -/
theorem localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov : CofinalFiniteCoverings J B Cov)
    {U : C} (hU : U ∈ B)
    {ι : Type u} (M : ι → D) [HasCoproduct M]
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj
        (op (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U))) := by
  exact
    localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow J 𝒪 U M
      (by
        intro p ι
        sorry)
      hM

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_52_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)

/- Domain-style sampling for Lemma 21.52.5:
- primary domain: compactness of the standard generators `j_{U!}\mathcal O_U[0]` in the derived
  category of sheaves of modules on a ringed site;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroDegreeZero`;
- best owner abstraction: the source-facing owner is
  `localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U`, and the hypothesis layer is best
  expressed through the canonical underlying-abelian cohomology owners
  `F.cohomologyPresheaf p` and `Sheaf.cohomologyPresheafFunctor`;
- primitive data: the vanishing bound and direct-sum preservation for the ordinary site
  cohomology functors on `\mathcal O`-modules over the fixed object `U`;
- derived API: compactness of `j_{U!}\mathcal O_U[0]`.

Source/core/bridge triage:
- `source-facing`: the compactness statement for `j_{U!}\mathcal O_U[0]`;
- `core/canonical`: `CategoryTheory.IsCompactObject`;
- `bridge/view`: the canonical underlying-abelian cohomology presheaf
  `((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).cohomologyPresheaf p` and its objectwise
  evaluation at `U`.
-/

-- Proof sketch: identify
-- `Hom_{D(\mathcal O)}(j_{U!}\mathcal O_U[0], K)` with `R\Gamma(U, K)`. The uniform bound on
-- `H^p(U, \mathcal F)` gives finite cohomological dimension for `\Gamma(U,-)`, and the
-- direct-sum hypothesis makes direct sums of injective resolutions acyclic for this functor. One
-- then computes `R\Gamma(U, \bigoplus_i K_i)` termwise on K-injective representatives and obtains
-- compatibility with arbitrary direct sums, which is exactly compactness of `j_{U!}\mathcal O_U`.
/-- Lemma 21.52.5: if there is an integer `d` such that `H^p(U, \mathcal F) = 0` for all
`p > d` and all sheaves `\mathcal F` of `\mathcal O`-modules, and if each functor
`\mathcal F \mapsto H^p(U, \mathcal F)` commutes with direct sums, then the degree-zero derived
object attached to `j_{U!}\mathcal O_U` is a compact object of `D(\mathcal O)`. -/
theorem localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility
    (U : C)
    (hvanish :
      ∃ d : ℤ, ∀ (p : ℕ), d < p → ∀ ℱ : Mod,
        IsZero ((((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).cohomologyPresheaf p).obj
          (op U)))
    (hcomm :
      ∀ (p : ℕ) (ι : Type u),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
            Sheaf.cohomologyPresheafFunctor J p ⋙
              (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) :
    IsCompactObject (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_52_6 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

-- Proof sketch: apply Lemma `21.52.5` to the degree-zero derived object attached to
-- `j_{U!}\mathcal O_U`. Weak contractibility gives vanishing of higher cohomology over `U` via
-- Lemma `21.51.1`, while quasi-compactness gives direct-sum compatibility of sections over `U`
-- via Modules on Sites, Lemma `18.30.3`.
/-- Lemma 21.52.6: if `U` is quasi-compact and weakly contractible in a ringed site
`(\mathcal C, \mathcal O)`, then the degree-zero derived object attached to
`j_{U!}\mathcal O_U` is a compact object of `D(\mathcal O)`. -/
theorem localizedStructureModuleExtensionByZero_degreeZero_isCompactObject_of_quasiCompact_weaklyContractible
    (U : C) (hUqc : J.QuasiCompactObject U) [J.IsWeaklyContractible U] :
    IsCompactObject (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U) := sorry

end

end SheafOfModules.RingedSite
