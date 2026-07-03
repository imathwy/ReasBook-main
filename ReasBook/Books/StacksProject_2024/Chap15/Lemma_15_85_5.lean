import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Lemma_15_66_1
import StacksProject_2024.Chap15.Lemma_15_85_3

-- Declarations for this item will be appended below by the statement pipeline.

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
