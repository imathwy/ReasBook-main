import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_85_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: projective-amplitude criteria in the derived category of modules, specialized to
  two-term cohomology and degree-`1` derived `Ext`;
- sampled owner declarations:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` and `projectiveAmplitudeIn_ext_vanishing_tfae` from
    `Lemma_15_69_2`,
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
    `Lemma_15_78_4`;
- best owner abstraction: the unrestricted degree-`1` vanishing condition is already the canonical
  zero-object statement `IsZero (derivedExtToModuleFunctor K 1)`, while the Noetherian
  specialization should keep the source-facing finite-module `Ext¹` clause explicit and use the
  finitely presented degree-`1` clause from `Lemma_15_78_4` only as the bridge justified by
  Noetherianness. The two-term cohomology-support hypothesis itself should live on the canonical
  t-structure owners `K.IsGE (-1)` and `K.IsLE 0`, with the entrywise vanishing formulation
  demoted to the bridge `DerivedCategory.isGE_iff` / `DerivedCategory.isLE_iff`.

Source/core/bridge triage:
- `source-facing`: the two-term cohomology projectivity criterion of Lemma `15.85.1`;
- `core/canonical`: `K.IsGE (-1)`, `K.IsLE 0`, `HasProjectiveAmplitudeIn`,
  `derivedExtToModuleFunctor`, and
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
  `Lemma_15_78_4`;
- `bridge/view`: the equivalence between the two-term cohomology condition
  `IsZero (H⁻¹ K) ∧ Projective (H⁰ K)` and the projective-amplitude owner specialized to
  `[0, 0]` under the canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`.

Primitive data here are only the canonical two-term support bounds and the two-term cohomology
condition. The unrestricted `Ext¹` test is already canonical upstream as
`IsZero (derivedExtToModuleFunctor K 1)`; the finite-module test in the Noetherian specialization
is source-facing data and should stay visible in the public `TFAE`, with the finitely presented
degree-`1` clause demoted to a companion bridge.
-/

-- Proof sketch: apply Lemma `15.69.2` with `a = b = 0`. Under the hypothesis that the
-- canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`, projective-amplitude in `[0, 0]`
-- means exactly that `H⁻¹(K) = 0` and `H⁰(K)` is projective, while
-- `IsZero (derivedExtToModuleFunctor K 1)` is the same as vanishing of `Ext¹_R(K, M)` for every
-- `R`-module `M`.
/-- Lemma 15.85.1: for a derived `R`-complex whose cohomology is concentrated in degrees `-1`
and `0`, encoded by `K.IsGE (-1)` and `K.IsLE 0`, the condition `H⁻¹(K) = 0` together with
projectivity of `H⁰(K)` is equivalent to the vanishing of `Ext¹_R(K, M)` for every
`R`-module `M`. -/
theorem two_term_cohomology_projective_iff_ext1_vanishes
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)) := sorry

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

-- Proof sketch: the finiteness of `H⁻¹(K)` and `H⁰(K)` together with the canonical two-term
-- bounds `K.IsGE (-1)` and `K.IsLE 0` implies that `K` is pseudo-coherent by Lemma `15.65.17`.
-- Apply Lemma `15.78.4` with `a = b = 0`, and use the canonical bridge
-- `Module.finitePresentation_of_finite` to replace the finitely presented `Ext¹` test by the
-- source-facing finite-module version with finiteness exposed as an explicit hypothesis.
/-- Over a Noetherian ring, a two-term derived complex with finite cohomology in degrees `-1`
and `0` satisfies the same projectivity criterion when `Ext¹_R(K, M)` is tested only on finite
`R`-modules. -/
theorem two_term_cohomology_projective_ext1_tfae_of_noetherian
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hfin_neg_one : Module.Finite R ((H (-1)).obj K))
    (hfin_zero : Module.Finite R ((H 0).obj K)) :
    List.TFAE [
      IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K),
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)),
      ∀ (M : ModuleCat R), Module.Finite R M →
        ∀ e : Ext^(1 : ℤ)(K, (single₀).obj M), e = 0
    ] := sorry

end

end CategoryTheory

/-! ### Remark_15_85_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: the naive cotangent complex `NL_{B/A}` in `D(B)` and its smooth/formally smooth
  Ext-vanishing criteria;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the source-facing Chapter 10 owner for `NL_{B/A}` in `D(B)`;
  - `Generators.self`, the canonical self-presentation `A[B] ↠ B`;
  - `Extension.naiveCotangentChainComplex`, the chapter owner for the two-term naive cotangent
    complex of a presentation;
  - `derivedExtToModuleFunctor`, the Chapter 15 owner for the degree-`1` derived `Ext`
    functorial test;
  - `Algebra.formallySmooth_tfae_presentation_section_conormal_sequence_projective`, the
    presentation-independent formal smoothness criterion.
* best owner abstraction: the primitive data for this remark are only the algebra map `A → B`,
  whose source-facing derived owner is `NL_{B/A} = naiveCotangent A B`. The chosen
  self-presentation and its two-term representative are bridge data internal to that owner. The
  smoothness and formal smoothness criteria are derived API and should be stated for `NL_{B/A}`,
  using the canonical vanishing condition `IsZero (derivedExtToModuleFunctor (naiveCotangentObject
  A B) 1)` rather than a local wrapper predicate, and not for its raw representative.
* layer triage:
  - `source-facing`: the criterion in terms of `Ext^1_B(NL_{B/A}, N)`;
  - `core/canonical`: `naiveCotangent A B`;
  - `bridge/view`: the derived-category realization
    `DerivedCategory.Q.obj
      (((Generators.self A B).toExtension.naiveCotangentChainComplex).extend embeddingDownNat)`.

Primitive data are only the algebra map and the canonical owner `NL_{B/A}`. The derived `Ext`
vanishing condition and the smooth/formally smooth criteria are already owned upstream and are
reused directly here. -/

-- Proof sketch: combine the canonical criterion `Algebra.smooth_iff`, which rewrites smoothness
-- as finite presentation plus formal smoothness, with the degree-`1` derived `Ext`-vanishing
-- criterion `IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1)` applied to the
-- canonical owner `NL_{B/A}`, and with Proposition `10.138.8`, which identifies formal
-- smoothness with
-- vanishing of `H¹(L_{B/A})` together with projectivity of `Ω[B⁄A]`.
/-- Remark 15.85.2 (1): an `A`-algebra `B` is smooth if and only if it is of finite presentation
and `Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem smooth_iff_finitePresentation_and_naiveCotangent_ext1_vanishes :
    Smooth A B ↔
      FinitePresentation A B ∧
        IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := sorry

-- Proof sketch: apply Lemma `15.85.1` to the canonical owner `NL_{B/A}`,
-- whose only nonzero cohomology groups are `H^{-1}(NL_{B/A}) = H1Cotangent A B` and
-- `H^0(NL_{B/A}) = Ω[B⁄A]`, and then rewrite the resulting condition using Proposition
-- `10.138.8`, i.e. `Algebra.formallySmooth_iff`.
/-- Remark 15.85.2 (2): an `A`-algebra `B` is formally smooth if and only if
`Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem formallySmooth_iff_naiveCotangent_ext1_vanishes :
    FormallySmooth A B ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := sorry

end

end Algebra

/-! ### Lemma_15_85_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.85.3:
- primary domain: derived `R`-modules concentrated in `[-1, 0]`, represented by two-term
  cochain complexes;
- sampled owner declarations:
  `IsTwoTermRepresentative`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `Module.Free`,
  `Module.Finite`,
  `IsNoetherianRing`;
- best owner abstraction: the source-facing owner is `IsTwoTermRepresentative K P`, whose
  primitive data are that `P` represents `K` and is supported in degrees `-1` and `0`;
- primitive data: the representative complex together with the two-term owner predicate, while the
  module-theoretic conditions on the degree `0` and degree `-1` terms remain additional inputs;
- derived API: the existence theorems below and downstream predicates built from this owner.

Source/core/bridge triage:
- `source-facing`: the existence of a two-term representative with the stated free / finite
  properties;
- `core/canonical`: `IsTwoTermRepresentative`, together with `K.IsGE (-1)` and `K.IsLE 0`;
- `bridge/view`: the explicit isomorphism witness produced from the t-structure truncation API.

Accordingly, this file exposes direct existential statements over a cochain complex witness rather
than a parallel public wrapper structure carrying the same data. -/

/-- A cochain complex `P` is a two-term representative of `K` if it represents `K` and is
supported in degrees `-1` and `0`. -/
def IsTwoTermRepresentative (K : DMod) (P : Cpx) : Prop :=
  IsIsomorphic (DerivedCategory.Q.obj P) K ∧ P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0

-- Proof sketch: choose a cochain-complex representative of `K`, truncate above degree `0`, then
-- replace it by a quasi-isomorphic bounded-above free complex using Lemma `13.15.4`. Finally
-- truncate below degree `-1`; the homology vanishing outside `{-1, 0}` ensures that this
-- truncation still represents `K`, and the degree-zero term remains free.
/-- Lemma 15.85.3 (1): if an object `K` of `D(R)` has cohomology only in degrees `-1` and `0`,
then `K` is represented by a cochain complex supported in degrees `-1` and `0` whose degree-zero
term is a free `R`-module. -/
theorem exists_twoTermFreeRepresentative
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0) :
    ∃ P : Cpx, IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) := sorry

-- Proof sketch: choose a bounded-above finite-free representative of `K` from Lemma `15.65.5`,
-- using the Noetherian and finite-cohomology hypotheses. Truncating this complex below degree
-- `-1` preserves the represented derived object because the other cohomology groups vanish. The
-- resulting degree-zero term is finite free, and the degree `-1` term is finite because it is a
-- subquotient of finite modules in the original finite-free complex.
/-- Lemma 15.85.3 (2): under the Noetherian and finite-cohomology hypotheses, the two-term
representative can be chosen with finite free degree-zero term and finite degree `-1` term. -/
theorem exists_twoTermFiniteFreeRepresentative
    [IsNoetherianRing R]
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    ∃ P : Cpx,
      IsTwoTermRepresentative K P ∧
        Module.Free R (P.X 0) ∧
          Module.Finite R (P.X 0) ∧ Module.Finite R (P.X (-1)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_85_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open DerivedCategory
open CategoryTheory.Limits
open HomologicalComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)
local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.4:
- primary domain: comparison between homotopy-category and derived-category morphisms from
  bounded-above complexes, together with maps to shifted single complexes encoded by cocycles in
  `HomComplex`;
- inspected owner declarations:
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `DerivedCategory.Qh.map`,
  `CochainComplex.HomComplex.Cocycle.toSingleMk`,
  `CochainComplex.HomComplex.Cocycle.equivHomShift`;
- best owner abstraction: the comparison map of part `(1)` is the canonical localization map
  `DerivedCategory.Qh.map` on homotopy-category morphisms, while the primitive source datum in
  parts `(3)` and `(4)` is a degree `-2` cocycle `a : M.X (-2) ⟶ X` with
  `M.d (-3) (-2) ≫ a = 0`, owned by `Cocycle.toSingleMk`; the derived morphism to `X[2]` is a
  bridge/view obtained by applying `ShiftedHom.map` along `DerivedCategory.Q`;
- primitive data vs. derived API:
  the primitive data is the support/projectivity hypotheses together with the cocycle condition in
  degree `-2`, while the derived morphisms `M^• ⟶ X[2]` and `K^• ⟶ K^{-2}[2]` are bridge
  constructions and should not be stored as independent primitive wrapper data.

Source/core/bridge triage:
- `source-facing`: the four theorem statements below;
- `core/canonical`: `DerivedCategory.Qh.map` and the cocycle owners
  `Cocycle.toSingleMk` / `Cocycle.equivHomShift`;
- `bridge/view`: the derived morphisms obtained from those cocycles via `ShiftedHom.map`. -/

abbrev negTwoCocycleToShift {M K : Cpx}
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0) :=
  Q.map
    (equivHomShift.symm (toSingleMk a (by omega) (-3) (by omega) ha))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

abbrev negTwoProjection (K : Cpx) (hK : K.IsStrictlyGE (-2)) :=
  let _ : K.IsStrictlyGE (-2) := hK
  Q.map
    (equivHomShift.symm
      (toSingleMk
        (𝟙 (K.X (-2)))
        (by omega)
        (-3)
        (by omega)
        (by
          simpa using
            (K.isZero_of_isStrictlyGE (-2) (-3) (by omega)).eq_of_src (K.d (-3) (-2)) 0)))
    ≫
      ((Q.commShiftIso (2 : ℤ)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom
    ≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
          (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

-- Proof sketch: replace `M^•` by a projective resolution `F^• → M^•` whose terms are
-- projective and which is termwise surjective. Since `K^i = 0` for `i ≤ -2`, every morphism
-- `F^• ⟶ K^•` and every homotopy factors uniquely through `M^•`, so the localization map from
-- `K(R)` to `D(R)` is bijective on morphisms out of `M^•`.
/-- Lemma 15.85.4 (1): if `M^•` is zero in positive degrees with `M^0` projective, and `K^•` is
zero in degrees `≤ -2`, then the canonical comparison
`Hom_{K(R)}(M^•, K^•) → Hom_{D(R)}(M^•, K^•)` is bijective. -/
theorem homotopyCategory_to_derived_bijective_of_projective_degree_zero
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-1)) :
    Function.Bijective (Qh.map : ((KQ).obj M ⟶ (KQ).obj K) → _) := sorry

-- Proof sketch: if `a^{-1} + h^0 d_M^{-1} = 0`, modify `a^•` by the homotopy with only
-- degree-zero component `h^0` to kill degree `-1`; then every map `K^• ⟶ N[1]` is homotopic to
-- one vanishing in degree `0`, so the induced `Ext^1` map is zero. Conversely, test against the
-- canonical class in `Ext^1_R(K^•, K^{-1})` and use part `(1)` to recover the required `h^0`.
/-- Lemma 15.85.4 (2): assume `K^•` is zero outside degrees `-1` and `0`, and `K^0` is
projective. For a map of complexes `a^• : M^• ⟶ K^•`, the induced maps
`Ext^1_R(K^•, N) → Ext^1_R(M^•, N)` vanish for all `R`-modules `N` if and only if there exists
`h^0 : M^0 ⟶ K^{-1}` with `a^{-1} + h^0 ∘ d_M^{-1} = 0`. -/
theorem inducesZeroOnModuleExt1_iff_exists_degree_zero_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hKge : K.IsStrictlyGE (-1))
    (hKle : K.IsStrictlyLE 0)
    (hK0 : Projective (K.X 0))
    (a : M ⟶ K) :
    (∀ (N : ModuleCat R) (e : ShiftedHom (Q.obj K) ((single₀).obj N) (1 : ℤ)),
      Q.map a ≫ e = 0) ↔
      ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0 := sorry

-- Proof sketch: choose a projective resolution `F^• → M^•` as in the proof of part `(1)` and a
-- representative `b^• : F^• ⟶ K^•` of `α`. The hypothesis on the composition with the canonical
-- projection to `K^{-2}[2]` lets one modify `b^•` by a homotopy so that its degree `-2`
-- component is exactly `a ∘ p^{-2}`; the support assumptions on `M^•` and `K^•` then force the
-- remaining components to factor through `M^•`, yielding a representative `a^• : M^• ⟶ K^•`
-- with prescribed degree `-2` term.
/-- Lemma 15.85.4 (3): assume `K^•` is zero in degrees `≤ -3`. Let
`α : Hom_{D(R)}(M^•, K^•)`. If the composite of `α` with the canonical projection
`K^• → K^{-2}[2]` comes from a module map `a : M^{-2} ⟶ K^{-2}` satisfying
`a ∘ d_M^{-3} = 0`, then `α` is represented by a map of complexes
`a^• : M^• ⟶ K^•` whose degree `-2` component is `a`. -/
theorem exists_representative_with_prescribed_degree_negTwo
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    (α : Q.obj M ⟶ Q.obj K)
    (a : M.X (-2) ⟶ K.X (-2))
    (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ negTwoProjection K hK = negTwoCocycleToShift a ha) :
    ∃ aMap : M ⟶ K, Q.map aMap = α ∧ aMap.f (-2) = a := sorry

-- Proof sketch: a homotopy between two representatives with the same image in `D(R)` can be
-- chosen on a projective resolution of `M^•`; arguing as in part `(3)`, it factors through
-- `M^•`. If the degree `-2` components already agree, then the support assumptions on `K^•`
-- force the remaining homotopy to have only degree `-1` and degree `0` components, giving
-- exactly the displayed formulas.
/-- Lemma 15.85.4 (4): under the hypotheses of part `(3)`, any two representatives of the same
derived morphism with the same degree `-2` component differ by homotopy components
`h^{-1} : M^{-1} ⟶ K^{-2}` and `h^0 : M^0 ⟶ K^{-1}` satisfying the usual degree `-1` and degree
`0` homotopy formulas. -/
theorem representative_difference_controlled_by_two_step_homotopy
    {M K : Cpx}
    (hM : M.IsStrictlyLE 0)
    (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    {aMap aMap' : M ⟶ K}
    (hQ : Q.map aMap = Q.map aMap')
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) :
    ∃ h : Homotopy aMap' aMap,
      M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
        aMap'.f (-1) =
          aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) + M.d (-1) 0 ≫ h.hom 0 (-1) ∧
        aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := sorry

end

end CategoryTheory

/-! ### Lemma_15_85_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain-style sampling for Lemma 15.85.5:
- primary domain: two-term representatives of derived `R`-modules concentrated in degrees `-1`
  and `0`, together with the annihilator condition they detect on the `R`-modules
  `Ext^1_R(K, N)`;
- sampled owner declarations in this domain:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `derivedExtModuleFunctor`,
  `exists_twoTermFreeRepresentative`,
  `exists_twoTermFiniteFreeRepresentative`,
  `inducesZeroOnModuleExt1_iff_exists_degree_zero_homotopy`,
  `Module.annihilator`;
- best owner abstraction: the primitive source data is a cochain complex `P : Cpx` that is a
  two-term representative of `K`, and the auxiliary scalar condition is the annihilator
  containment on the chapter owner `((derivedExtModuleFunctor K (1 : ℤ)).obj N)`, whose
  source-facing bridge to the textbook group `Ext^1(K, N[0])` and composition formula is derived
  API;
- primitive data vs. derived API: the representative complex, its support bounds, and its degree
  `0` and `-1` module conditions are primitive, while the TFAE comparison with annihilator
  containment and the unpacked `ShiftedHom.mk₀` composition formula are derived API.

Source/core/bridge triage:
- `source-facing`: the numbered TFAE conditions themselves;
- `core/canonical`: the owner predicates `K.IsGE (-1)` / `K.IsLE 0` and the representative
  complex `P : Cpx`, together with the annihilator predicate
  `I ≤ Module.annihilator R (((derivedExtModuleFunctor K (1 : ℤ)).obj N))`;
- `bridge/view`: the comparison `IsIsomorphic (DerivedCategory.Q.obj P) K` and the equivalence
  between annihilator containment and the `Ext^1(K, N[0])` composition formula.

Accordingly, this file reuses the upstream owner `IsTwoTermRepresentative` from
`Lemma_15_85_3` instead of restating the same representative predicate locally.
-/

/-- Scalar multiplication by `a` on the degree `-1` term factors through the differential
`d^{-1} : P^{-1} ⟶ P^0`. -/
def smulFactorsThroughDifferentialAtNegOne
    (P : Cpx) (a : R) : Prop :=
  ∃ h : P.X 0 ⟶ P.X (-1),
    P.d (-1) 0 ≫ h = ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) a)

/-- The ideal `I` is contained in the annihilator of `Ext^1_R(K, N)` for every `R`-module `N`,
viewed through the chapter owner `derivedExtModuleFunctor K 1`. -/
def twoTermExtOneAnnihilatedByIdeal
    (K : DMod) (I : Ideal R) : Prop :=
  ∀ N : ModuleCat R, I ≤ Module.annihilator R ((derivedExtModuleFunctor K (1 : ℤ)).obj N)

/-- Unfolding `twoTermExtOneAnnihilatedByIdeal` recovers the textbook vanishing formula obtained by
postcomposing classes in `Ext^1(K, N[0])` with multiplication by `a` on `N`. -/
theorem twoTermExtOneAnnihilatedByIdeal_iff
    (K : DMod) (I : Ideal R) :
    twoTermExtOneAnnihilatedByIdeal K I ↔
      ∀ (N : ModuleCat R) (a : I) (e : Ext^(1 : ℤ)(K, (single₀).obj N)),
        e.comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((single₀).map (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
          (zero_add (1 : ℤ)) = 0 := sorry

/-- There exists a free two-term representative of `K` on which every scalar from `I` acts on
degree `-1` through the differential. -/
def admits_two_term_free_representative_with_ideal_factorization
    (K : DMod) (I : Ideal R) : Prop :=
  ∃ P : Cpx,
    IsTwoTermRepresentative K P ∧
      Module.Free R (P.X 0) ∧
        ∀ a : I, smulFactorsThroughDifferentialAtNegOne P (a : R)

/-- Every projective two-term representative of `K` has the scalar-factorization property in
degree `-1` for every element of `I`. -/
def all_two_term_projective_representatives_have_ideal_factorization
    (K : DMod) (I : Ideal R) : Prop :=
  ∀ (P : Cpx) (_ : IsTwoTermRepresentative K P) (_ : Projective (P.X 0)) (a : I),
    smulFactorsThroughDifferentialAtNegOne P (a : R)

/-- The ideal `I` is contained in the annihilator of `Ext^1_R(K, N)` for every finite
`R`-module `N`, viewed through the chapter owner `derivedExtModuleFunctor K 1`. -/
def twoTermExtOneAnnihilatedByIdealOnFiniteModules
    (K : DMod) (I : Ideal R) : Prop :=
  ∀ (N : ModuleCat R) (_ : Module.Finite R N),
    I ≤ Module.annihilator R ((derivedExtModuleFunctor K (1 : ℤ)).obj N)

/-- Unfolding `twoTermExtOneAnnihilatedByIdealOnFiniteModules` recovers the textbook vanishing
formula on finite test modules. -/
theorem twoTermExtOneAnnihilatedByIdealOnFiniteModules_iff
    (K : DMod) (I : Ideal R) :
    twoTermExtOneAnnihilatedByIdealOnFiniteModules K I ↔
      ∀ (N : ModuleCat R) (_ : Module.Finite R N)
        (a : I) (e : Ext^(1 : ℤ)(K, (single₀).obj N)),
        e.comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((single₀).map (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
          (zero_add (1 : ℤ)) = 0 := sorry

/-- There exists a finite free two-term representative of `K` with finite degree `-1` term on
which every scalar from `I` acts on degree `-1` through the differential. -/
def admits_two_term_finite_free_representative_with_ideal_factorization
    (K : DMod) (I : Ideal R) : Prop :=
  ∃ P : Cpx,
    IsTwoTermRepresentative K P ∧
      Module.Free R (P.X 0) ∧
        Module.Finite R (P.X 0) ∧
          Module.Finite R (P.X (-1)) ∧
            ∀ a : I, smulFactorsThroughDifferentialAtNegOne P (a : R)

-- Proof sketch: use Lemma `15.85.4` to translate annihilation of `Ext^1_R(K, N)` by `I` into
-- factorization of the scalar endomorphisms on the degree `-1` term through the differential for
-- two-term projective representatives, then compare projective, free, and finite free
-- representatives via Lemma `15.85.3`.
/-- Lemma 15.85.5: for a derived `R`-complex `K` with cohomology concentrated in degrees `-1`
and `0`, the following are equivalent: `I` annihilates `Ext^1_R(K, N)` for every `R`-module `N`;
there exists a two-term representative `K^{-1} ⟶ K^0` with `K^0` free such that every
`a ∈ I` acts on `K^{-1}` through the differential; and every two-term representative with
projective degree-zero term has this factorization property. -/
theorem two_term_ext1_annihilated_tfae
    (K : DMod)
    (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I
    ] := sorry

/-- Lemma 15.85.5, Noetherian finite case: if `R` is Noetherian and `H^{-1}(K)` and `H^0(K)` are
finite, then the three equivalent conditions of `two_term_ext1_annihilated_tfae` are also
equivalent to the finite-module annihilation condition and to the existence of a finite free
two-term representative with the same factorization property. -/
theorem two_term_ext1_annihilated_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DMod)
    (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I,
      twoTermExtOneAnnihilatedByIdealOnFiniteModules K I,
      admits_two_term_finite_free_representative_with_ideal_factorization K I
    ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_85_6 (from Chap15) -/
noncomputable section

open ComplexShape
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
private abbrev extCpx : CpxR ⥤ CpxR' :=
  (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (up ℤ)
local notation "ExtCpx" => (extCpx : CpxR ⥤ CpxR')

/- Domain-style sampling for Lemma 15.85.6:
- primary domain: derived base change for two-term representatives in `D(R)`;
- sampled owner declarations:
  `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`,
  `DerivedCategory.TStructure.t.truncGE`, `Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing datum is the chosen two-term representative `P` of
  `K`, while the core/canonical owners are `IsTwoTermRepresentative`, `K ⊗[R]^L[R']`, and
  `t.truncGE (-1)`;
- primitive vs. derived:
  primitive data are the representative `P` and the flatness of its degree-zero term;
  the scalar-extended complex `ExtCpx.obj P` is only the canonical bridge/view from cochain-level
  base change back to the owner predicate on the truncation target;
- source/core/bridge triage:
  `source-facing`: the statement that two-term representatives stay two-term after flat base
  change and truncation;
  `core/canonical`: `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`, and `t.truncGE`;
  `bridge/view`: the cochain-level scalar extension `ExtCpx.obj P`.

Accordingly, the theorem remains in the owner namespace `IsTwoTermRepresentative` and uses the
imported scalar-extension owner `ExtCpx` directly, rather than introducing a parallel wrapper or
weakening the result to a bare isomorphism statement. -/

-- Proof sketch: write `P` as a two-term complex `P⁻¹ → P⁰` with `P⁰` flat. Tensor the
-- distinguished triangle `P⁰ → P → P⁻¹[1] → P⁰[1]` with `R'`. The flatness of `P⁰` identifies
-- its ordinary tensor product with the derived tensor product, and the degree-support hypothesis
-- on `P` already forces the same cohomological support for `K`, so the scalar-extended complex is
-- concentrated in degrees `-1` and `0`. The induced comparison to `K ⊗[R]^L[R']` is therefore
-- an isomorphism on homology in degrees `≥ -1`, so the scalar-extended complex computes the
-- upper truncation `τ_{\ge -1}` and remains a two-term representative there.
namespace IsTwoTermRepresentative

/-- Lemma 15.85.6: if `P` is a two-term representative of `K` whose degree-zero term is flat,
then the scalar extension of `P` along `R → R'` is a two-term representative of
`τ_{\ge -1}(K ⊗_R^{\mathbf L} R')`. -/
theorem truncGE_derivedTensorWithAlgebra
    {K : DModR} {P : CpxR}
    (hP : IsTwoTermRepresentative K P)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsTwoTermRepresentative ((t.truncGE (-1)).obj (K ⊗[R]^L[R'])) ((ExtCpx).obj P) :=
  sorry

end IsTwoTermRepresentative

end

end CategoryTheory

/-! ### Lemma_15_85_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure
open scoped ChangeOfRings
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
  { __ := AddEquiv.refl R'
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R R' ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/- Domain-style sampling for Lemma 15.85.7:
- primary domain: two-term representatives in `D(R)` and their behavior under derived base
  change, together with the Ext-annihilation TFAE from Lemma `15.85.5`;
- sampled owner declarations in this domain:
  `IsTwoTermRepresentative`,
  `IsTwoTermRepresentative.truncGE_derivedTensorWithAlgebra`,
  `two_term_ext1_annihilated_tfae`,
  `Ideal.map`;
- best owner abstraction: the primitive source datum is still the source-facing condition
  `admits_two_term_free_representative_with_ideal_factorization K I`, but the supporting
  representative/base-change mechanism should run through the chapter owner
  `IsTwoTermRepresentative` and its scalar-extension theorem, while the three-way comparison is
  already owned by `two_term_ext1_annihilated_tfae`;
- primitive data vs. derived API: the primitive witness is a free two-term representative of `K`
  with the scalar-factorization property for `I`; the truncation target
  `(t.truncGE (-1)).obj (K ⊗[R]^L[R'])`, the mapped ideal `Ideal.map (algebraMap R R') I`, and the
  TFAE package are derived API built from those owners.

Source/core/bridge triage:
- `source-facing`: the base-changed equivalence of the three conditions from Lemma `15.85.5`,
  together with the assertion that condition `(2)` holds after base change;
- `core/canonical`: `IsTwoTermRepresentative`, its theorem
  `truncGE_derivedTensorWithAlgebra`, and the owner TFAE theorem
  `two_term_ext1_annihilated_tfae`;
- `bridge/view`: the specific free representative extracted from `hcond` and its scalar-extended
  cochain complex.

Accordingly, this file keeps the source-facing theorem but rewrites its proof entirely through the
existing owner abstractions rather than introducing a parallel local wrapper for the base-changed
representative package.
-/

-- Proof sketch: choose a two-term free representative `P` for `K` from `hcond`. Apply
-- Lemma `15.85.6` to identify the scalar-extended complex `P ⊗_R R'` with
-- `τ_{\ge -1}(K ⊗_R^L R')`. The extended complex is still supported in degrees `-1` and `0`, its
-- degree-zero term stays free after base change, and the factorization identities for elements of
-- `I` extend `R'`-linearly to every element of `Ideal.map (algebraMap R R') I`, giving condition
-- `(2)` of Lemma `15.85.5` for the base-changed object. Applying Lemma `15.85.5` to that target
-- then recovers the full three-condition package.
variable (R') in
/-- Lemma 15.85.7: if `K` satisfies condition `(2)` of Lemma `15.85.5` with respect to `(R, I)`,
then for `τ_{\ge -1}(K ⊗_R^{\mathbf L} R')` the three conditions of Lemma `15.85.5` with respect
to `(R', Ideal.map (algebraMap R R') I)` are equivalent, and condition `(2)` holds. -/
theorem truncGE_derivedTensorWithAlgebra_two_term_ext1_annihilated_tfae
    (K : DModR) (I : Ideal R)
    (hcond : admits_two_term_free_representative_with_ideal_factorization K I) :
    let K' := (t.truncGE (-1)).obj (K ⊗[R]^L[R'])
    let I' := Ideal.map (algebraMap R R') I
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K' I',
      admits_two_term_free_representative_with_ideal_factorization K' I',
      all_two_term_projective_representatives_have_ideal_factorization K' I'
    ] ∧
      admits_two_term_free_representative_with_ideal_factorization K' I' := by
  classical
  dsimp
  rcases hcond with ⟨P, hP, hfree0, hfactor⟩
  let K' := (t.truncGE (-1)).obj (K ⊗[R]^L[R'])
  let I' := Ideal.map (algebraMap R R') I
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let Pbase : CpxR' := (F.mapHomologicalComplex (up ℤ)).obj P
  have hflat0 : Module.Flat R (P.X 0) := Module.Flat.of_free
  have hPbase : IsTwoTermRepresentative K' Pbase := by
    simpa [K', Pbase, F] using
      IsTwoTermRepresentative.truncGE_derivedTensorWithAlgebra hP hflat0
  have hfree0' : Module.Free R' (Pbase.X 0) := by
    let e : (Pbase.X 0 : ModuleCat R') ≃ₗ[R'] TensorProduct R R' (P.X 0) := by
      simpa [Pbase, F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.AlgebraTensorModule.congr
          restrictScalarsSelfEquiv
          (LinearEquiv.refl R (P.X 0)))
    exact Module.Free.of_equiv' (inferInstance : Module.Free R' (TensorProduct R R' (P.X 0)))
      e.symm
  have hfactor_gen :
      ∀ a : I,
        smulFactorsThroughDifferentialAtNegOne Pbase (algebraMap R R' (a : R)) := by
    intro a
    rcases hfactor a with ⟨g, hg⟩
    refine ⟨F.map g, ?_⟩
    change F.map (P.d (-1) 0) ≫ F.map g =
      ModuleCat.ofHom
        (LinearMap.lsmul R' ((F.obj (P.X (-1)) : ModuleCat R')) (algebraMap R R' (a : R)))
    rw [← F.map_comp, hg]
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change
      (F.map
          (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))))
        ((1 : R') ⊗ₜ[R] m) =
        (algebraMap R R' (a : R)) •
          (((1 : R') ⊗ₜ[R] m : F.obj (P.X (-1))))
    have hmap :
        (F.map
            (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))))
          ((1 : R') ⊗ₜ[R] m) =
          (((1 : R') ⊗ₜ[R] ((a : R) • m) :
            F.obj (P.X (-1)))) := by
      convert
        ModuleCat.ExtendScalars.map_tmul (algebraMap R R')
          (ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) (a : R))) (1 : R') m using 1
    rw [hmap]
    simpa [LinearMap.lsmul_apply] using
      (TensorProduct.tmul_smul (algebraMap R R' (a : R))
        (1 : ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')))
        m)
  have hfactor_zero :
      smulFactorsThroughDifferentialAtNegOne Pbase (0 : R') := by
    refine ⟨0, ?_⟩
    ext m
    simp
  have hfactor_add {a b : R'} :
      smulFactorsThroughDifferentialAtNegOne Pbase a →
      smulFactorsThroughDifferentialAtNegOne Pbase b →
      smulFactorsThroughDifferentialAtNegOne Pbase (a + b) := by
    rintro ⟨ga, hga⟩ ⟨gb, hgb⟩
    refine ⟨ga + gb, ?_⟩
    ext m
    simp [hga, hgb, LinearMap.lsmul_apply]
  have hfactor_smul (c : R') {a : R'} :
      smulFactorsThroughDifferentialAtNegOne Pbase a →
      smulFactorsThroughDifferentialAtNegOne Pbase (c * a) := by
    rintro ⟨g, hg⟩
    refine ⟨c • g, ?_⟩
    ext m
    have hgm :
        ModuleCat.Hom.hom g (ModuleCat.Hom.hom (Pbase.d (-1) 0) m) = a • m := by
      simpa [LinearMap.lsmul_apply] using congrArg (fun f ↦ ModuleCat.Hom.hom f m) hg
    simp [hgm, LinearMap.lsmul_apply, mul_smul]
  have hmap_generators :
      Set.range (fun a : I ↦ algebraMap R R' (a : R)) = (algebraMap R R') '' (I : Set R) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hI' :
      Ideal.span (Set.range (fun a : I ↦ algebraMap R R' (a : R))) = I' := by
    calc
      Ideal.span (Set.range (fun a : I ↦ algebraMap R R' (a : R)))
          = Ideal.span ((algebraMap R R') '' (I : Set R)) := by
            rw [hmap_generators]
      _ = Ideal.map (algebraMap R R') (Ideal.span (I : Set R)) := by
            rw [Ideal.map_span]
      _ = I' := by
            simpa [I', Ideal.span_eq]
  have hfactor' :
      ∀ a : I',
        smulFactorsThroughDifferentialAtNegOne Pbase (a : R') := by
    intro a
    have ha :
        (a : R') ∈ Ideal.span (Set.range (fun b : I ↦ algebraMap R R' (b : R))) := by
      simpa [hI'] using a.2
    refine Submodule.span_induction
      (fun x hx ↦ by
        rcases hx with ⟨b, rfl⟩
        exact hfactor_gen b)
      hfactor_zero
      (fun x y _ _ hx hy ↦ hfactor_add hx hy)
      (fun c x _ hx ↦ hfactor_smul c hx)
      ha
  have hcond' : admits_two_term_free_representative_with_ideal_factorization K' I' := by
    refine ⟨Pbase, hPbase, hfree0', hfactor'⟩
  rcases hPbase.1 with ⟨e⟩
  have hK'GE : K'.IsGE (-1) := by
    have : (DerivedCategory.Q.obj Pbase).IsGE (-1) := by
      let _ : Pbase.IsStrictlyGE (-1) := hPbase.2.1
      rw [DerivedCategory.isGE_Q_obj_iff]
      infer_instance
    exact t.isGE_of_iso e (-1)
  have hK'LE : K'.IsLE 0 := by
    have : (DerivedCategory.Q.obj Pbase).IsLE 0 := by
      let _ : Pbase.IsStrictlyLE 0 := hPbase.2.2
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    exact t.isLE_of_iso e 0
  refine ⟨?_, hcond'⟩
  simpa [K', I'] using two_term_ext1_annihilated_tfae K' I' hK'GE hK'LE

end

end CategoryTheory

/-! ### Lemma_15_85_8 (from Chap15) -/
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open DerivedCategory.TStructure

section

variable {𝒜 : Type u} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-
Domain-style sampling for Lemma 15.85.8:
- primary domain: the canonical `t`-structure on derived categories of abelian categories, and
  its specialization to scalar endomorphisms of two-term derived `R`-modules;
- sampled owner declarations in this domain:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.Epi`;
- best owner abstraction: the cohomological amplitude hypotheses belong to the canonical
  `t`-structure owners `K.IsGE (-1)`, `K.IsLE 0`, `K'.IsGE (-1)`, and `K'.IsLE 0`, while the map
  hypotheses are the canonical categorical conditions `IsIso ((H^0).map α)` and
  `Epi ((H^(-1)).map α)`, whose intrinsic categorical conclusion is `Epi α`;
- primitive data vs. derived API: for the owner theorem below, the primitive inputs are `K`, `K'`,
  `α`, and the cohomological hypotheses. In the module specialization, the canonical bridge is the
  purely categorical `cancel_epi` argument after obtaining `Epi α`; the hypotheses on `H^0(α)`
  and `H^{-1}(α)` are source-facing bridge data used only to supply `Epi α`. The proof-route data
  involving a kernel object `M`, a distinguished triangle, and the vanishing
  `Hom(M⟦2⟧, K') = 0` are internal bridge data and should not become public wrapper data.

Source/core/bridge triage:
- `source-facing`: the scalar-annihilation transfer theorem in `D(R)` below;
- `core/canonical`: the owner predicates `IsGE` / `IsLE`, the homology-map hypotheses on `α`,
  and the resulting categorical conclusion `Epi α` in `D(𝒜)`;
- `bridge/view`: the distinguished-triangle argument and the Chapter 13 vanishing/factorization
  lemmas used in the proof sketch.
-/

-- Proof sketch: let `M` be the kernel of `H⁻¹(α)`. The hypotheses on the two-term cohomology of
-- `K` and `K'`, together with `H⁰(α)` being an isomorphism and `H⁻¹(α)` being surjective, place
-- `α` in a distinguished triangle `M⟦1⟧ ⟶ K ⟶ K' ⟶ M⟦2⟧`. If `f • 𝟙 K = 0`, then
-- `α ≫ (f • 𝟙 K') = 0`, so `f • 𝟙 K'` factors through a morphism `M⟦2⟧ ⟶ K'`. Lemma `13.27.3`
-- gives `Hom(M⟦2⟧, K') = 0` because `M⟦2⟧` is concentrated in degree `-2` and `K'` has
-- cohomology only in degrees `-1` and `0`.
/-- Owner form of Lemma 15.85.8: in the derived category of an abelian category, a morphism
between two-term objects inducing an isomorphism on `H^0` and an epimorphism on `H^{-1}` is
itself an epimorphism.
-/
theorem epi_of_h0_iso_of_hneg1_epi
    {K K' : D(𝒜)} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α)) :
    Epi α := sorry

end

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR

/-- Lemma 15.85.8: let `α : K ⟶ K'` be a morphism in `D(R)` between objects with cohomology only
in degrees `-1` and `0`. If `H⁰(α)` is an isomorphism and `H⁻¹(α)` is an epimorphism, then any
scalar `f : R` acting by zero on `K` also acts by zero on `K'`. -/
theorem smul_id_eq_zero_of_h0_iso_of_hneg1_epi
    {K K' : DModR} (α : K ⟶ K') (f : R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := by
  letI : Epi α := epi_of_h0_iso_of_hneg1_epi α hKGE hKLE hK'GE hK'LE hα0 hαneg1
  refine (cancel_epi α).1 ?_
  calc
    α ≫ (f • 𝟙 K') = f • α := by simp
    _ = (f • 𝟙 K) ≫ α := by simp
    _ = 0 := by simpa [hf]
    _ = α ≫ 0 := by simp

end

end CategoryTheory

/-! ### Lemma_15_85_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.85.9:
- primary domain: two-term objects in the derived category of `R`-modules and the owner predicate
  `twoTermExtOneAnnihilatedByIdeal`;
- sampled owner declarations:
  `twoTermExtOneAnnihilatedByIdeal`,
  `smul_id_eq_zero_of_h0_iso_of_hneg1_epi`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: this source-facing transfer lemma should stay phrased on the owner
  predicate `twoTermExtOneAnnihilatedByIdeal`, while the `H⁻¹` surjectivity assumption is best
  expressed by the canonical categorical hypothesis `Epi ((H^(-1)).map α)` rather than by the
  underlying-function view;
- primitive data vs. derived API: the primitive inputs are `K`, `K'`, `α`, the cohomological
  bounds, and the owner annihilation predicate. Surjectivity of `((H^(-1)).map α).hom` is a
  derived concrete view of the canonical `Epi` owner hypothesis. -/

-- Proof sketch: let `M = ker(H^{-1}(α))`. The hypotheses give a distinguished triangle
-- `M[1] ⟶ K ⟶ K' ⟶ M[2]`. Applying `Hom_{D(R)}(-, N[1])` yields an exact sequence in which the
-- term coming from `M[1]` vanishes because `Ext^{-1}_R(M, N) = 0`, so
-- `Ext^1_R(K', N) ↪ Ext^1_R(K, N)`. Hence any element of `I` annihilating `Ext^1_R(K, N)` also
-- annihilates `Ext^1_R(K', N)`.
/-- Lemma 15.85.9: let `I` be an ideal of `R`, and let `α : K ⟶ K'` in `D(R)` induce an
isomorphism on `H^0` and a surjection on `H^{-1}`. If `K` has cohomology only in degrees `-1`
and `0`, and if `K'` does as well, then the Ext-annihilation condition from Lemma `15.85.5 (1)`
for `K` implies the same condition for `K'`. -/
theorem twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi
    (I : Ideal R)
    {K K' : DMod}
    (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hI : twoTermExtOneAnnihilatedByIdeal K I) :
    twoTermExtOneAnnihilatedByIdeal K' I := sorry

end

end CategoryTheory

/-! ### Lemma_15_85_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open PrimeSpectrum
open scoped PrimeSpectrum

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/- Domain-style sampling for Lemma 15.85.10:
- primary domain: two-term derived `R`-complexes, `I`-projective cohomology, and finite
  basic-open localization criteria for projectivity on the open complement `Spec R \ V(I)`;
- sampled owner declarations in this domain:
  `Module.IsIdealProjective`,
  `Module.IsIdealPowerTorsion`,
  `Module.LocallyFree`,
  `twoTermExtOneAnnihilatedByIdeal`,
  `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- best owner abstraction: the primitive source data is the pair of cohomology modules
  `H^(-1)(K)` and `H^0(K)` together with the chapter owners `Module.IsIdealProjective` and
  `Module.IsIdealPowerTorsion`; the localization-cover clauses are source-facing finite-set
  projectivity criteria for `H⁰(K)` on finite basic-open neighborhoods of `Spec R \ V(I)`, so
  they stay inline in the theorem statement rather than being promoted to separate public owners;
- primitive data vs. derived API: annihilator containment, ideal-projectivity, and localized
  projectivity of `H⁰(K)` are primitive clause data, while the `Ext¹` reformulations are derived
  API supplied upstream by Lemma `15.85.5`.

Source/core/bridge triage:
- `source-facing`: the TFAE statements below and their finite-localization clauses;
- `core/canonical`: `Module.IsIdealProjective`, `Module.IsIdealPowerTorsion`,
  `twoTermExtOneAnnihilatedByIdeal`, and `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- `bridge/view`: the comparison between the cohomology-side conditions and the `Ext¹` conditions.
-/

-- Proof sketch: use the distinguished triangle
-- `H^{-1}(K)[1] ⟶ K ⟶ H^0(K)[0] ⟶ H^{-1}(K)[2]` to compare annihilation of `Ext^1_R(K, N)` by
-- powers of `I` with annihilation of `H^{-1}(K)` and `I^c`-projectivity of `H^0(K)`. In the
-- Noetherian finite case, combine Lemma `15.85.5` with the local criterion for `I`-projective
-- modules and the standard algebraic equivalences between `V(f_1, ..., f_s)` and powers of `I`.
/-- Lemma 15.85.10: for a derived `R`-complex `K` with cohomology concentrated in degrees `-1`
and `0`, the existence of a power `I^c` satisfying the equivalent conditions `(1)`, `(2)`, `(3)`
of Lemma `15.85.5` is equivalent to the existence of a power `I^c` that annihilates `H^{-1}(K)`
and makes `H^0(K)` `I^c`-projective. -/
theorem two_term_ideal_power_projectivity_tfae
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K)
    ] := sorry

/-- Lemma 15.85.10, Noetherian finite case: if `R` is Noetherian and `H^{-1}(K)` and `H^0(K)` are
finite, then the two equivalent conditions of `two_term_ideal_power_projectivity_tfae` are also
equivalent to the finite-module version of Lemma `15.85.5` and to the local projectivity criteria
obtained from finite families cutting out `V(I)`, viewed as finite basic-open covers of
`Spec R \ V(I)`. -/
theorem two_term_ideal_power_projectivity_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K)) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K),
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s, Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          (↑s : Set R) ⊆ I ∧
            V((↑s : Set R)) = V((I : Set R)) ∧
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∀ s : Finset R,
          (↑s : Set R) ⊆ I →
            V((↑s : Set R)) = V((I : Set R)) →
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K))
    ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_85_11 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 15.85.11:
- primary domain: the canonical `t`-structure on `D(𝒜)` for an abelian category `𝒜`, and
  objects concentrated in degrees `≤ 0` and `≥ -1`;
- sampled owner declarations:
  `exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero`,
  `Triangulated.TStructure.isZero_truncLE_obj_of_isGE`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`;
- best owner abstraction: the endpoint cohomology bounds belong to the canonical owner predicates
  `K1.IsLE 0` and `K3.IsGE (-1)`, the intervening factorization belongs to
  `exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero`, and the final vanishing should
  be expressed by the canonical `t`-structure fact that `τ_{\le -2} K3 = 0` under the owner
  hypothesis `K3.IsGE (-1)`, rather than through a parallel degree-gap wrapper;
- primitive data: the objects `K1`, `K2`, `K3`, the morphisms `φ`, `ψ`, and the vanishing
  conditions on `H^0(φ)` and `H^{-1}(ψ)`;
- derived API: the composite-vanishing conclusion.

Source/core/bridge triage:
- `source-facing`: the textbook composite-vanishing statement below;
- `core/canonical`: the `t`-structure predicates `IsGE` / `IsLE`;
- `bridge/view`: the equivalent cohomology-vanishing formulations `isGE_iff` / `isLE_iff`.

Accordingly, this file keeps the source-facing theorem and replaces the repeated interval-vanishing
binders by the canonical `t`-structure owner predicates. Since the proof is purely formal in the
derived-category `t`-structure, the owner ambient category is the general `DerivedCategory 𝒜`,
not the special case `D(R)`. -/

-- Proof sketch: apply Lemma `13.12.5` to the length-two chain `K1 ⟶ K2 ⟶ K3`. The hypotheses
-- `H^0(φ) = 0` and `H^{-1}(ψ) = 0` force the composite to factor through the truncation
-- `τ_{\le -2} K3`, and `K3.IsGE (-1)` implies that truncation object is zero, so the factorized
-- morphism vanishes.
/-- Lemma 15.85.11: in the derived category of an abelian category, if `K1` has no cohomology in
degrees `> 0`, if `K3` has no cohomology in degrees `< -1`, if `φ : K1 ⟶ K2` induces the zero
map on `H^0`, and if `ψ : K2 ⟶ K3` induces the zero map on `H^{-1}`, then the composite
`K1 ⟶ K3` is zero. -/
theorem comp_zero_of_h0_map_eq_zero_of_hneg1_map_eq_zero
    {K1 K2 K3 : D(𝒜)} (φ : K1 ⟶ K2) (ψ : K2 ⟶ K3)
    (hK1 : K1.IsLE 0) (hK3 : K3.IsGE (-1))
    (hφ : (H^0).map φ = 0)
    (hψ : (H^(-1)).map ψ = 0) :
    φ ≫ ψ = 0 := by
  obtain ⟨τφ, hfactor⟩ :=
    exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero (mk₂ φ ψ) hK1
      (fun j hj ↦ by
        cases j with
        | zero =>
            simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one] using hφ
        | succ j =>
            cases j with
            | zero =>
                simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_one_succ] using hψ
            | succ j =>
                exact False.elim (by simpa using hj))
  letI := hK3
  have hτK3 : Limits.IsZero ((t.truncLE (-2)).obj K3) := by
    simpa using t.isZero_truncLE_obj_of_isGE (-2) (-1) rfl K3
  have hτφ : τφ = 0 := hτK3.eq_of_tgt τφ 0
  calc
    φ ≫ ψ = τφ ≫ (t.truncLEι (-2)).app K3 := by
      simpa [ComposableArrows.mk₂, ComposableArrows.Precomp.map_zero_one,
        ComposableArrows.Precomp.map_one_succ] using hfactor.symm
    _ = 0 := by rw [hτφ, Limits.zero_comp]

end

end CategoryTheory

/-! ### Lemma_15_85_12 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR
local notation "singleComplex₀" => CochainComplex.singleFunctor ModR (0 : ℤ)

/- Domain-style sampling for Lemma 15.85.12:
- primary domain: two-term cochain complexes in `ModuleCat R`, presented as mapping cones of
  matrices and, more canonically, of endomorphisms of finite free modules, and their derived
  images;
- sampled owner declarations of the same kind:
  `Matrix.toLin'`,
  `LinearMap.det_toLin'`,
  `CochainComplex.mappingCone`,
  `CochainComplex.singleFunctor`,
  `LinearMap.det`;
- best owner abstraction: the canonical owner for the two-term complex attached to an
  endomorphism `f` of a finite free module is
  `CochainComplex.mappingCone ((CochainComplex.singleFunctor ModR 0).map (ModuleCat.ofHom f))`,
  while the source-facing statement remains the matrix presentation `R^n \xrightarrow{A} R^n`;
- primitive data: for the source-facing lemma, a matrix `A : Matrix (Fin n) (Fin n) R` and a
  chosen representation isomorphism from the derived image of the corresponding two-term complex
  to `K`;
- derived API: the supporting finite-free endomorphism bridge theorem over the canonical
  mapping-cone owner.

Source/core/bridge triage:
- `source-facing`: the textbook matrix statement that an arbitrary `K` represented by
  `R^n \xrightarrow{A} R^n` is annihilated by `det A`;
- `core/canonical`: `CochainComplex.mappingCone` of the map induced by `f` on the degree-zero
  single complex;
- `bridge/view`: the finite-free endomorphism version together with the matrix comparison
  `A.toLin'` and `LinearMap.det_toLin'`.

Accordingly, this file keeps the matrix formulation as the main numbered source-facing theorem,
and exposes the finite-free endomorphism statement only as a supporting bridge over the canonical
mapping-cone owner. -/

/-- Matrix specialization of Lemma 15.85.12: if `K` is represented by the two-term complex
`R^n \xrightarrow{A} R^n`, then multiplication by `det A` acts by zero on `K` in `D(R)`. -/
theorem matrixTwoTermDerived_det_endomorphism_eq_zero {n : ℕ}
    (K : DModR) (A : Matrix (Fin n) (Fin n) R)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom A.toLin')))) K) :
    Matrix.det A • 𝟙 K = 0 := sorry

-- Proof sketch: choose a basis of the finite free module `M`, represent `f` by a matrix `A`, and
-- apply the source-facing matrix lemma above to that presentation. The determinant comparison
-- `LinearMap.det_toLin'` identifies the resulting scalar action with multiplication by
-- `LinearMap.det f`.
/-- Supporting bridge: if `K` is represented by the two-term complex `M \xrightarrow{f} M` in
degrees `-1` and `0`, where `M` is finite free over `R`, then multiplication by `det(f)` acts by
zero on `K` in `D(R)`. -/
theorem endomorphismTwoTermDerived_det_endomorphism_eq_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (K : DModR) (f : M →ₗ[R] M)
    (hK : IsIsomorphic
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleComplex₀).map (ModuleCat.ofHom f)))) K) :
    LinearMap.det f • 𝟙 K = 0 := sorry

end

end CategoryTheory
