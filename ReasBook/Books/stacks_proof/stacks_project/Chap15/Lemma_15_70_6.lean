import Mathlib
import StacksProject_2024.Chap10.Example_10_28_7
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_62_1
import StacksProject_2024.Chap10.Lemma_10_71_9
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap13.Lemma_13_27_3
import StacksProject_2024.Chap15.Definition_15_70_1
import StacksProject_2024.Chap15.Lemma_15_70_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "Mod" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: finite injective dimension for bounded-below derived `R`-complexes, tested by
  vanishing of derived `Ext` groups from ideal quotients;
- sampled owner declarations:
  `D⁺(Mod)`,
  `HasFiniteInjectiveDimension`,
  `injectiveAmplitudeIn_ext_vanishing_tfae`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`;
- best owner abstraction: the source-facing owner here remains
  `HasFiniteInjectiveDimension K.obj`, while the bounded-below hypothesis should be carried by the
  Chapter `13` owner `K : D⁺(Mod)` rather than by the surrogate datum
  `∃ n : ℤ, K.IsGE n`;
- primitive vs. derived:
  primitive data are the ideal `I`, the bounded-below derived object `K : D⁺(Mod)`, and
  finite cohomology modules;
  derived API is the eventual vanishing of `Ext^i((single₀).obj (R ⧸ J), K)` for ideals
  `J ⊇ I`, with `ShiftedHom` kept only as the core owner behind the Chapter `13` notation;
- source/core/bridge triage:
  `source-facing`: `finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge`;
  `core/canonical`: `HasFiniteInjectiveDimension`, `DerivedCategory.IsGE`, and `ShiftedHom`;
  `bridge/view`: the cohomology-vanishing description of `D⁺(R)`, which is demoted in favor of
    the owner-level bounded-below hypothesis.
-/

-- Proof sketch: the forward implication is obtained by computing `Ext` against a bounded
-- injective representative of `K`. For the reverse implication, use Lemma `15.70.2` to reduce
-- finite injective dimension to vanishing of `Ext^i_R(M, K)` for all finite modules `M`; then
-- filter `M` by cyclic quotients, reduce to prime quotients `R/𝔭`, and use Noetherian induction.
-- When `I ⊈ 𝔭`, choose `f ∈ I \ 𝔭`, compare `R/𝔭` with `R/(𝔭, f)`, and apply finite generation of
-- the relevant `Ext` modules plus Nakayama's lemma. The bounded-below hypothesis is carried by
-- the Chapter `13` owner `K : D⁺(R)`.

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.70.6: if `p` is prime and `f ∉ p`, then colon by `(f)` does not enlarge
`p`. -/
lemma prime_colon_span_singleton_eq_of_not_mem
    (p : Ideal R) (hp : p.IsPrime) {f : R} (hf : f ∉ p) :
    p.colon (Ideal.span ({f} : Set R)) = p := by
  apply le_antisymm
  · intro x hx
    -- Rewrite colon membership as the single multiplication test `x * f ∈ p`.
    rw [Ideal.mem_colon_span_singleton] at hx
    exact (hp.mem_or_mem (by simpa [mul_comm] using hx)).resolve_right hf
  · -- Every element of `p` still lies in the colon ideal because `p` is an ideal.
    intro x hx
    rw [Ideal.mem_colon_span_singleton]
    exact Ideal.mul_mem_right _ _ hx

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.70.6: a bounded-below target has no ideal-quotient extensions in degrees
strictly below the lower bound. -/
lemma ideal_quotient_ext_vanish_below_lower_bound
    (K : D⁺(Mod)) {a i : ℤ}
    (hKGE : K.obj.IsGE a) (J : Ideal R) (hi : i < a)
    (e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj)) :
    e = 0 := by
  -- The source lies in degree `0`, so the Chapter 13 vanishing range kills all degrees `< a`.
  have hsub :
      Subsingleton
        (Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj)) := by
    simpa using
      shiftedHom_subsingleton_of_lt_sub
        ((single₀).obj (ModuleCat.of R (R ⧸ J)))
        K.obj
        0
        a
        i
        (inferInstance :
          ((single₀).obj (ModuleCat.of R (R ⧸ J))).IsLE 0)
        hKGE
        (by simpa using hi)
  exact Subsingleton.elim e 0

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.70.6: if a module is identified with `R ⧸ q`, then every ideal
annihilating it is contained in `q`. -/
lemma le_of_le_annihilator_of_equiv_quotient
    {N : Type u} [AddCommGroup N] [Module R N]
    (q : Ideal R) (e : N ≃ₗ[R] (R ⧸ q)) {J : Ideal R}
    (hJann : J ≤ Module.annihilator R N) :
    J ≤ q := by
  intro a ha
  have haAnn : a ∈ Module.annihilator R N := hJann ha
  -- Evaluate the annihilator condition on the class of `1` in the quotient model.
  have hkill : a • e.symm (Ideal.Quotient.mk q 1) = 0 :=
    Module.mem_annihilator.mp haAnn _
  -- Transport the equality back to `R ⧸ q`, where it reads `a = 0`.
  have hzero_smul : a • (1 : R ⧸ q) = 0 := by
    simpa using congrArg e hkill
  have hzero_mul : ((Ideal.Quotient.mk q) a) * 1 = 0 := by
    change a • (1 : R ⧸ q) = 0
    exact hzero_smul
  have hzero : (Ideal.Quotient.mk q) a = 0 := by
    simpa using hzero_mul
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- Helper for Lemma 15.70.6: eventual vanishing on quotient modules by ideals containing `I`
propagates to all ideal quotients in the same high-degree range. -/
lemma finite_ext_of_finite_module_and_finite_homology
    (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj))
    (M : Mod) [Module.Finite R M] (i : ℤ) :
    Module.Finite R (Ext^i((single₀).obj M, K.obj)) := by
  -- Route correction: the source proof needs finite generation of the target `Ext` module before
  -- the Nakayama step on prime quotients can even be stated.
  -- TODO: use the Ext cohomology spectral sequence for `(M[0], K)` and the finiteness of the
  -- `E₂` page terms `Ext^p_R(M, H^q(K))`, which follows from `ModuleCat.finite_ext`.
  sorry

/-- Helper for Lemma 15.70.6: in a short exact sequence of source modules, vanishing of
`Ext^i(-, K)` on the left term and of `Ext^i(-, K)` and `Ext^(i + 1)(-, K)` on the right term
forces vanishing on the middle term. -/
lemma ext_vanish_middle_of_shortExact_outer
    (K : D⁺(Mod))
    {N₁ N₂ N₃ : Type u}
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (i : ℤ)
    (h₁ : ∀ e : Ext^i((single₀).obj (ModuleCat.of R N₁), K.obj), e = 0)
    (h₃ : ∀ e : Ext^i((single₀).obj (ModuleCat.of R N₃), K.obj), e = 0)
    (h₃succ : ∀ e : Ext^(i + 1)((single₀).obj (ModuleCat.of R N₃), K.obj), e = 0)
    (e : Ext^i((single₀).obj (ModuleCat.of R N₂), K.obj)) :
    e = 0 := by
  let S : ShortComplex Mod :=
    ShortComplex.moduleCatMk f g <| by
      ext x
      exact (hfg (f x)).2 ⟨x, rfl⟩
  let hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  have hprecomp_zero : hS.singleTriangle.mor₁ ≫ e = 0 := by
    -- The left-hand vanishing hypothesis kills the precomposition of `e` with the first map.
    have hzero : ((single₀).map (ModuleCat.ofHom f)) ≫ e = 0 := by
      simpa using h₁ (((single₀).map (ModuleCat.ofHom f)) ≫ e)
    simpa [S, hS] using hzero
  obtain ⟨e₃, he₃⟩ :=
    Pretriangulated.Triangle.yoneda_exact₂ hS.singleTriangle hS.singleTriangle_distinguished e
      hprecomp_zero
  have he₃zero : e₃ = 0 := by
    -- The right-hand vanishing hypothesis kills the factor supplied by exactness.
    simpa using h₃ e₃
  -- Substitute the vanishing right-hand factor back into the exactness factorization.
  have hzero_factor : hS.singleTriangle.mor₂ ≫ e₃ = 0 := by
    rw [he₃zero]
    change ((single₀).map (ModuleCat.ofHom g)) ≫
        (0 : hS.singleTriangle.obj₃ ⟶ (shiftFunctor D(Mod) i).obj K.obj) = 0
    have hcomp :
        ((single₀).map (ModuleCat.ofHom g)) ≫
          (0 : hS.singleTriangle.obj₃ ⟶ (shiftFunctor D(Mod) i).obj K.obj) = 0 := by
      aesop_cat
    exact hcomp
  exact he₃.trans hzero_factor

/-- Helper for Lemma 15.70.6: vanishing on strictly larger prime quotients propagates, by prime
cyclic devissage, to every finite module annihilated by an ideal strictly larger than `p`. -/
lemma finite_module_ext_vanish_above_bound_of_strictly_larger_prime_quotients
    (K : D⁺(Mod))
    (p : Ideal R) (hp : p.IsPrime) {b : ℤ}
    (hprime :
      ∀ (q : Ideal R), q.IsPrime → p < q →
        ∀ i : ℤ, b < i →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ q)), K.obj), e = 0)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hann : ∃ J : Ideal R, p < J ∧ J ≤ Module.annihilator R M)
    (i : ℤ) (hi : b < i)
    (e : Ext^i((single₀).obj (ModuleCat.of R M), K.obj)) :
    e = 0 := by
  classical
  let _ := hp
  -- Run the prime-cyclic induction with the annihilator witness threaded through the motive.
  revert hann i hi e
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      intro hannN i hi e
      -- A subsingleton source module gives the zero source object, so every class is zero.
      have hzero : IsZero ((single₀).obj (ModuleCat.of R N)) := by
        exact
          (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).map_isZero
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N))
      exact hzero.eq_of_src _ _
  | quotient N q eNQ =>
      intro hannN i hi e
      rcases hannN with ⟨J, hpJ, hJann⟩
      -- The annihilator witness on `N` transports to the quotient `R ⧸ q`, forcing `J ≤ q`.
      have hJq : J ≤ q.asIdeal :=
        le_of_le_annihilator_of_equiv_quotient q.asIdeal eNQ hJann
      have hpq : p < q.asIdeal := lt_of_lt_of_le hpJ hJq
      -- Transport the class across the module isomorphism before applying the prime hypothesis.
      let β :
          (single₀).obj (ModuleCat.of R N) ≅
            (single₀).obj (ModuleCat.of R (R ⧸ q.asIdeal)) :=
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).mapIso eNQ.toModuleIso
      obtain ⟨eQ, heQ⟩ := (β.symm.homCongr (Iso.refl _)).surjective e
      have hQ : eQ = 0 := hprime q.asIdeal q.isPrime hpq i hi eQ
      have htransport :
          (β.symm.homCongr (Iso.refl _)) eQ =
            (β.symm.homCongr (Iso.refl _)) 0 := by
        exact congrArg (β.symm.homCongr (Iso.refl _)) hQ
      simpa [heQ] using htransport
  | exact N₁ N₂ N₃ f g hf hg hfg hN₁ hN₃ =>
      intro hannN₂ i hi e
      rcases hannN₂ with ⟨J, hpJ, hJann₂⟩
      -- Any ideal annihilating the middle term also annihilates the submodule and the quotient.
      have hann₁ : ∃ J : Ideal R, p < J ∧ J ≤ Module.annihilator R N₁ := by
        refine ⟨J, hpJ, ?_⟩
        intro a ha
        rw [Module.mem_annihilator]
        intro x
        apply hf
        have haAnn : a ∈ Module.annihilator R N₂ := hJann₂ ha
        simpa [map_smul] using Module.mem_annihilator.mp haAnn (f x)
      have hann₃ : ∃ J : Ideal R, p < J ∧ J ≤ Module.annihilator R N₃ := by
        refine ⟨J, hpJ, ?_⟩
        intro a ha
        rw [Module.mem_annihilator]
        intro z
        obtain ⟨y, rfl⟩ := hg z
        have haAnn : a ∈ Module.annihilator R N₂ := hJann₂ ha
        simpa [map_smul] using congrArg g (Module.mem_annihilator.mp haAnn y)
      -- The remaining bridge is the long exact sequence in `Ext` for this short exact row.
      exact
        ext_vanish_middle_of_shortExact_outer K f g hf hg hfg i
          (hN₁ hann₁ i hi)
          (hN₃ hann₃ i hi)
          (hN₃ hann₃ (i + 1) (by omega))
          e

/-- Helper for Lemma 15.70.6: once the quotient term `R / (p, f)` vanishes in degree `i + 1`,
scalar multiplication by `f` is surjective on `Ext^i_R(R / p, K)`. -/
lemma prime_quotient_ext_precomp_surjective_of_quotient_vanishing
    (K : D⁺(Mod))
    (p : Ideal R) (hp : p.IsPrime) {f : R} (hf : f ∉ p) (i : ℤ)
    (hquotsucc :
      ∀ e :
        Ext^(i + 1)(
          (single₀).obj (ModuleCat.of R (R ⧸ (p ⊔ Ideal.span ({f} : Set R)))),
          K.obj),
          e = 0) :
    Function.Surjective
      (fun e' : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ p)), K.obj) ↦ f • e') := by
  -- Route correction: the source proof only needs the quotient row
  -- `0 → R / p --f→ R / p → R / (p, f) → 0` to make multiplication by `f` surjective on
  -- `Ext^i(R / p, K)`. The remaining blocker is the exact comparison between the degree-zero
  -- `Ext` map for the short exact row and scalar multiplication on the integer-shifted `Ext`.
  -- TODO: rewrite `quotient_colon_span_singleton_shortExact p f` using
  -- `prime_colon_span_singleton_eq_of_not_mem p hp hf`, apply the degree-`0/1`
  -- contravariant long exact sequence to the shifted target `K.obj⟦i⟧`, use `hquotsucc` to kill
  -- the connecting map, and identify the resulting surjective precomposition map with
  -- `e' ↦ f • e'`.
  sorry

/-- Helper for Lemma 15.70.6: the test-family hypothesis already forces vanishing on all prime
quotients in high degrees. -/
lemma prime_quotient_ext_vanish_above_bound_of_test_family
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj))
    {b : ℤ}
    (hb :
      ∀ (J : Ideal R), I ≤ J →
        ∀ i : ℤ, b < i →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0) :
    ∀ (p : Ideal R), p.IsPrime →
      ∀ i : ℤ, b < i →
        ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ p)), K.obj), e = 0 := by
  -- TODO: keep the source-proof route. Choose a maximal bad prime via the well-founded relation
  -- `>` on ideals of a Noetherian ring, use `hb` directly in the branch `I ≤ p`, and otherwise
  -- choose `f ∈ I \ p`, kill the quotient `R / (p, f)` by
  -- `finite_module_ext_vanish_above_bound_of_strictly_larger_prime_quotients`, apply
  -- `prime_quotient_ext_precomp_surjective_of_quotient_vanishing`, and finish with Nakayama using
  -- `finite_ext_of_finite_module_and_finite_homology`.
  sorry

/-- Helper for Lemma 15.70.6: vanishing on all prime quotients propagates, by prime cyclic
devissage, to vanishing on every finite module in the same range. -/
lemma finite_module_ext_vanish_above_bound_of_prime_quotients
    (K : D⁺(Mod)) {b : ℤ}
    (hprime :
      ∀ (p : Ideal R), p.IsPrime →
        ∀ i : ℤ, b < i →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ p)), K.obj), e = 0) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (i : ℤ), b < i →
      ∀ e : Ext^i((single₀).obj (ModuleCat.of R M), K.obj), e = 0 := by
  intro M _ _ _ i hi e
  classical
  -- Use the prime-cyclic induction principle directly, with the target degree kept in the motive.
  revert i hi e
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      intro i hi e
      -- A subsingleton source module gives the zero source object, so every class is zero.
      have hzero : IsZero ((single₀).obj (ModuleCat.of R N)) := by
        exact
          (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).map_isZero
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N))
      exact hzero.eq_of_src _ _
  | quotient N q eNQ =>
      intro i hi e
      -- Transport the class to the prime quotient supplied by the induction principle.
      let β :
          (single₀).obj (ModuleCat.of R N) ≅
            (single₀).obj (ModuleCat.of R (R ⧸ q.asIdeal)) :=
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).mapIso eNQ.toModuleIso
      obtain ⟨eQ, heQ⟩ := (β.symm.homCongr (Iso.refl _)).surjective e
      have hQ : eQ = 0 := hprime q.asIdeal q.isPrime i hi eQ
      have htransport :
          (β.symm.homCongr (Iso.refl _)) eQ =
            (β.symm.homCongr (Iso.refl _)) 0 := by
        exact congrArg (β.symm.homCongr (Iso.refl _)) hQ
      simpa [heQ] using htransport
  | exact N₁ N₂ N₃ f g hf hg hfg hN₁ hN₃ =>
      intro i hi e
      -- The source-row exactness reduces the middle term to the two outer induction hypotheses.
      exact
        ext_vanish_middle_of_shortExact_outer K f g hf hg hfg i
          (hN₁ i hi)
          (hN₃ i hi)
          (hN₃ (i + 1) (by omega))
          e

/-- Helper for Lemma 15.70.6: eventual vanishing on quotient modules by ideals containing `I`
propagates to all ideal quotients in the same high-degree range. -/
lemma ideal_quotient_ext_vanish_above_bound_of_test_family
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj))
    {b : ℤ}
    (hb :
      ∀ (J : Ideal R), I ≤ J →
        ∀ i : ℤ, b < i →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0) :
    ∀ (J : Ideal R) (i : ℤ), b < i →
      ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 := by
  -- Route correction: expose the source-proof skeleton explicitly. First pass from the test
  -- family to all prime quotients, then devissage from prime quotients to arbitrary finite
  -- modules, and finally specialize back to the quotient `R ⧸ J`.
  intro J i hi e
  -- The prime step is the Noetherian-induction plus Nakayama core of the source argument.
  let hprime :=
    prime_quotient_ext_vanish_above_bound_of_test_family I hI K hKfinite hb
  -- The final devissage step extends prime-quotient vanishing to every finite module.
  let hfinite :=
    finite_module_ext_vanish_above_bound_of_prime_quotients K (b := b) hprime
  -- Specialize the finite-module statement to the quotient module `R ⧸ J`.
  simpa using hfinite (R ⧸ J) i hi e

/-- Lemma 15.70.6: let `R` be a Noetherian ring, let `I ⊆ R` be an ideal contained in the
Jacobson radical, and let `K ∈ D^+(R)` have finite cohomology modules. Then `K` has finite
injective dimension if and only if there exists an integer `b` such that
`Ext^i_R(R/J, K) = 0` for every `i > b` and every ideal `J ⊇ I`. -/
@[stacks 0DW2]
theorem finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ,
        ∀ (J : Ideal R), I ≤ J →
          ∀ i : ℤ, b < i →
            ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 := by
  constructor
  · intro hK
    rcases (hasFiniteInjectiveDimension_iff K.obj).1 hK with ⟨a, b, hAmp⟩
    have hExt :
        ∀ (J : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 :=
      ((injectiveAmplitudeIn_ext_vanishing_tfae K.obj a b).out 0 2).mp hAmp
    refine ⟨b, ?_⟩
    intro J hIJ i hi e
    -- Finite injective amplitude already gives vanishing outside `[a, b]`.
    exact hExt J i (by
      intro hmem
      exact not_lt_of_ge hmem.2 hi) e
  · rintro ⟨b, hb⟩
    rcases (derivedCategory_t_plus_iff K.obj).1 K.property with ⟨a, ha⟩
    have hKGE : K.obj.IsGE a := by
      -- Repackage the `D⁺` witness as the canonical `IsGE` owner needed by Chapter 13.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact ha i hi
    have hExt :
        ∀ (J : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 := by
      intro J i hi e
      by_cases hlow : i < a
      · -- Degrees below `a` vanish because `K` is bounded below.
        exact ideal_quotient_ext_vanish_below_lower_bound K hKGE J hlow e
      · -- Degrees outside `[a, b]` and not below `a` must lie above `b`.
        have hhigh : b < i := by
          by_contra hbi
          apply hi
          exact ⟨le_of_not_gt hlow, le_of_not_gt hbi⟩
        exact ideal_quotient_ext_vanish_above_bound_of_test_family I hI K hKfinite hb J i hhigh e
    have hAmp : HasInjectiveAmplitudeIn K.obj a b :=
      ((injectiveAmplitudeIn_ext_vanishing_tfae K.obj a b).out 2 0).mp hExt
    -- Once vanishing holds outside `[a, b]`, Lemma `15.70.2` returns finite injective amplitude.
    exact (hasFiniteInjectiveDimension_iff K.obj).2 ⟨a, b, hAmp⟩

end

end CategoryTheory
