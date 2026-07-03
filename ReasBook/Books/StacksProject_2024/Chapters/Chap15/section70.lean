import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_70_1 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: derived-category amplitude conditions for `DerivedCategory (ModuleCat R)`,
  together with the canonical injective-dimension invariant on `ModuleCat R`;
- inspected owner declarations:
  `CategoryTheory.injectiveDimension`,
  `CategoryTheory.injectiveDimension_ne_top_iff`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.HasFiniteProjectiveDimension`;
- best owner abstraction:
  `source-facing`: `HasInjectiveAmplitudeIn` and `HasFiniteInjectiveDimension` for objects of
    `D(R)`;
  `core/canonical`: `injectiveDimension` for module-level finite injective dimension;
  `bridge/view`: the representative-complex unpacking lemmas for the derived-category owners;
- primitive vs. derived:
  the primitive data for the source-facing definition are the representative cochain complex,
  support bounds, injective terms, and the isomorphism in `D(R)`;
  the module-level predicate is not primitive data here, since mathlib already owns that notion
  through `injectiveDimension`. -/

/-- Definition 15.70.1 (2): an object `K` of `D(R)` has injective-amplitude in `[a, b]` if it is
isomorphic in the derived category to a cochain complex of injective `R`-modules supported in
degrees `a` through `b`. -/
def HasInjectiveAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∃ I : CochainComplex (ModuleCat R) ℤ,
    I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I)

/-- Definition 15.70.1 (1): an object `K` of `D(R)` has finite injective dimension if it has
injective-amplitude in some finite interval `[a, b]`. -/
def HasFiniteInjectiveDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b

-- Proof sketch: unfold `HasInjectiveAmplitudeIn`; the right-hand side is exactly the existence of
-- a representing cochain complex of injective modules supported in degrees `[a, b]`.
/-- An object of `D(R)` has injective-amplitude in `[a, b]` exactly when it admits a
representative complex of injective `R`-modules supported in those degrees. -/
theorem hasInjectiveAmplitudeIn_iff_exists_representative
    (K : DMod) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∃ I : CochainComplex (ModuleCat R) ℤ,
        I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
          (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) :=
  Iff.rfl

-- Proof sketch: unfold `HasFiniteInjectiveDimension`; this is definitionally the existence of
-- some finite interval in which `K` has injective-amplitude.
/-- An object of `D(R)` has finite injective dimension exactly when it has injective-amplitude in
some finite interval. -/
theorem hasFiniteInjectiveDimension_iff
    (K : DMod) :
    HasFiniteInjectiveDimension K ↔
      ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b :=
  Iff.rfl

/- Module-level finite injective dimension is already expressed by the canonical invariant
`CategoryTheory.injectiveDimension`. -/
#check (injectiveDimension : ModuleCat R → WithBot ℕ∞)

/- Companion recall: `injectiveDimension M ≠ ⊤` is the canonical finite-injective-dimension
criterion, and with `injectiveDimension_le_iff` it is equivalent to the existence of a natural
number bound. -/
recall injectiveDimension_ne_top_iff
recall injectiveDimension_le_iff

end

end CategoryTheory

/-! ### Lemma_15_70_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: injective-amplitude criteria in `DerivedCategory (ModuleCat R)`, expressed by
  vanishing of derived `Ext` groups;
- inspected owner declarations:
  `CategoryTheory.HasInjectiveAmplitudeIn`,
  `CategoryTheory.Ext^i(_, _)`,
  `CategoryTheory.projectiveAmplitudeIn_ext_vanishing_tfae`,
  `CategoryTheory.injective_iff_ext_one_eq_zero`,
  `CategoryTheory.injective_tfae_extOneFromIdealQuotient_eq_zero_baer`;
- best owner abstraction: the source-facing owner is `HasInjectiveAmplitudeIn K a b`; the
  shifted-Hom vanishing clauses are derived API describing that owner, not a separate local owner;
- layer: `source-facing`, since this lemma gives the textbook criterion for the existing owner
  `HasInjectiveAmplitudeIn`;
- primitive data: `K : DMod` and the bounds `a b : ℤ`;
- derived API: testing `Ext^i((single₀).obj N, K)` and its ideal-quotient specialization by
  direct vanishing `∀ e, e = 0`, in the same chapter style as the projective-amplitude and
  Baer-criterion files;
- bridge/view: the core owner remains `ShiftedHom`, but `Ext^i(_, _)` is the canonical
  source-facing notation already introduced in Chapter `13`, so the public theorem surface should
  use that notation rather than restating the raw owner. -/

-- Proof sketch: prove `(1) → (2)` by computing morphisms from degree-zero modules against an
-- injective representative supported in `[a, b]`; `(2) → (3)` is immediate by specializing to
-- quotient modules `R/I`; for `(3) → (1)`, first recover cohomological boundedness of `K` from
-- the case `I = ⊥`, then truncate an injective resolution and apply Lemma `15.55.4` to the final
-- kernel using the vanishing for all quotients `R/I`.
/-- Lemma 15.70.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` is represented by a cochain complex of injective `R`-modules supported in
degrees `[a, b]`; for every `R`-module `N`, the groups `Ext^i_R(N, K)` vanish for
`i ∉ [a, b]`; and it is enough to test this vanishing on quotient modules `R/I` for ideals
`I ⊆ R`. -/
theorem injectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasInjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj N, K), e = 0
      , ∀ (I : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ I)), K), e = 0
      ] := sorry

end

end CategoryTheory

/-! ### Example_15_70_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory
open Abelian.Ext
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)

/- Domain-style sampling for Example 15.70.3:
- primary domain: injective-dimension bounds in `ModuleCat R` and bounded-derived splitting in
  `Dᵇ(ModuleCat R)`;
- sampled owner declarations:
  `injectiveDimension`,
  `injectiveDimension_le_iff`,
  `HasInjectiveDimensionLT.subsingleton`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
- best owner abstraction: the source-facing statement is the Dedekind-domain specialization of the
  Chapter 13 bounded-derived splitting theorem. The primitive new input is the owner-level module
  bound `injectiveDimension _ ≤ 1`, while the needed `HasInjectiveDimensionLE _ 1` instance and
  resulting degree-two `Ext`-vanishing are derived through `injectiveDimension_le_iff` and
  `HasInjectiveDimensionLT.subsingleton`;
- primitive vs. derived API: primitive data are the Dedekind-domain injective-dimension bound in
  the canonical owner `injectiveDimension` and the bounded derived object `K : Dᵇ(Mod)`; the
  `HasInjectiveDimensionLE` witness and `Ext`-vanishing input for the splitting theorem are derived
  pointwise from that owner-level bound.
- source/core/bridge triage:
  `source-facing`: the Dedekind-domain specialization of the bounded-derived splitting statement;
  `core/canonical`: `injectiveDimension`, `injectiveDimension_le_iff`,
    `HasInjectiveDimensionLT.subsingleton`, and
    `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
  `bridge/view`: the pointwise passage from the Dedekind-domain injective-dimension bound to the
  degree-two `Ext`-vanishing hypothesis required by the Chapter 13 owner theorem.
-/

/-- Every `R`-module over a Dedekind domain has injective dimension at most `1`. -/
-- Proof sketch: apply Lemma `15.70.2` to the degree-zero derived object of `M`; the hypothesis
-- needed there is that every quotient `R/I` has projective dimension at most `1`, which follows
-- from the fact that every nonzero ideal of a Dedekind domain is finite projective.
theorem injectiveDimension_le_one_of_isDedekindDomain
    (M : Mod) :
    injectiveDimension M ≤ 1 := by
  exact (injectiveDimension_le_iff M 1).2 (by
    sorry)

/-- Bridge/view: over a Dedekind domain, every degree-two `Ext` group of modules is trivial. -/
theorem subsingleton_ext_two_of_isDedekindDomain
    (M N : Mod) :
    Subsingleton (Ext N M 2) := by
  letI : HasInjectiveDimensionLE M 1 :=
    (injectiveDimension_le_iff M 1).mp (injectiveDimension_le_one_of_isDedekindDomain M)
  simpa using HasInjectiveDimensionLT.subsingleton M 2 2 le_rfl N

/-- Example 15.70.3: over a Dedekind domain, every bounded derived object of `R`-modules is
isomorphic to the finite biproduct of its shifted cohomology modules over some interval
containing its cohomological support. -/
-- Proof sketch: apply the Chapter 13 splitting theorem
-- `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`; its degree-two `Ext`-vanishing
-- hypothesis is supplied by the module-level owner bound above through
-- `injectiveDimension_le_iff` and the canonical owner lemma
-- `HasInjectiveDimensionLT.subsingleton`.
theorem isomorphic_to_biproduct_shiftedCohomology_of_isDedekindDomain
    (K : DbMod) :
    ∃ a b : ℤ,
      Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn Mod K.obj a b) := by
  sorry

end

end CategoryTheory

/-! ### Example_15_70_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CochainComplex.HomComplex.Cocycle
open TrivSqZeroExt
open scoped DualNumber

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε

/-- The bi-infinite `ε`-periodic cochain complex `⋯ ⟶ R ⟶ R ⟶ R ⟶ ⋯` over the dual numbers,
with every differential given by multiplication by `ε`. -/
def dualNumbersBiInfinitePeriodicComplex : CochainComplex ModRε ℤ :=
  CochainComplex.of
    (fun _ : ℤ ↦ ModuleCat.of Rε Rε)
    (fun _ : ℤ ↦ dualNumbersPeriodicDifferential k)
    (fun _ : ℤ ↦ dualNumbersPeriodicDifferential_sq k)

-- Proof sketch: `dualNumbersBiInfinitePeriodicComplex` is defined using `CochainComplex.of` with
-- the same differential in every degree, so the degree-`n` differential is definitionally left
-- multiplication by `ε`.
/-- Every differential in the bi-infinite dual-numbers complex is multiplication by `ε`. -/
theorem dualNumbersBiInfinitePeriodicComplex_d (n : ℤ) :
    (dualNumbersBiInfinitePeriodicComplex k).d n (n + 1) =
      dualNumbersPeriodicDifferential k := sorry

end

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε
local notation "single0" => DerivedCategory.singleFunctor ModRε (0 : ℤ)

/- Domain-style sampling:
- primary domain: explicit cochain-complex representatives of degree-zero modules in
  `DerivedCategory (ModuleCat Rε)`;
- inspected owner declarations: `Ideal.Quotient.mkₐ`,
  `CochainComplex.HomComplex.Cocycle.toSingleMk`, `DerivedCategory.Q`,
  `DerivedCategory.singleFunctor`, and `DerivedCategory.singleFunctorIsoCompQ`;
- best owner abstraction: the source-facing owner here is the concrete complex
  `dualNumbersBiInfinitePeriodicComplex k`, not an existential wrapper around it;
- source/core/bridge triage: `dualNumbersBiInfinitePeriodicAugmentation` is the
  `source-facing` map, `DerivedCategory.Q` together with `single0` is the
  `core/canonical` owner layer, and termwise injectivity is a separate `bridge/view` property;
- primitive data: the explicit augmentation
  `dualNumbersBiInfinitePeriodicAugmentation k :
    dualNumbersBiInfinitePeriodicComplex k ⟶
      (CochainComplex.singleFunctor ModRε (0 : ℤ)).obj (dualNumbersResidueModule k)`;
- derived API: the induced isomorphism
  `DerivedCategory.Q.obj (dualNumbersBiInfinitePeriodicComplex k) ≅
    (single0).obj (dualNumbersResidueModule k)`;
  the extra field hypothesis belongs only to the separate termwise-injectivity theorem below. -/

-- Proof sketch: as for the one-sided periodic complex, a cochain map to the degree-zero complex
-- is determined by its degree-zero component, here the quotient map `Rε → Rε/(ε)`.
/-- The canonical augmentation from the bi-infinite dual-numbers periodic complex to the residue
module in degree `0`. -/
def dualNumbersBiInfinitePeriodicAugmentation :
    dualNumbersBiInfinitePeriodicComplex k ⟶
      (CochainComplex.singleFunctor ModRε (0 : ℤ)).obj (dualNumbersResidueModule k) :=
  let π : (dualNumbersBiInfinitePeriodicComplex k).X 0 ⟶ dualNumbersResidueModule k :=
    ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap
  (toSingleMk π (by simp) (-1) (by simp) (by
      have hd :
          (dualNumbersBiInfinitePeriodicComplex k).d (-1) 0 =
            dualNumbersPeriodicDifferential k := by
        simpa using dualNumbersBiInfinitePeriodicComplex_d k (-1)
      rw [hd]
      apply ModuleCat.hom_ext
      ext
      change (Ideal.Quotient.mk (kerIdeal k k))
          ((LinearMap.mulLeft Rε (ε : Rε)) 1) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [mem_kerIdeal_iff_inr]
      ext <;> simp [LinearMap.mulLeft_apply])).homOf

-- Proof sketch: compute cohomology exactly as for the one-sided periodic resolution; the
-- bi-infinite complex is exact away from degree `0`, and its degree-zero cohomology is
-- `Rε / (ε)`.
/-- The canonical augmentation from the bi-infinite periodic dual-numbers complex to the residue
module in degree `0` is a quasi-isomorphism. -/
theorem dualNumbersBiInfinitePeriodicAugmentation_quasiIso :
    QuasiIso (dualNumbersBiInfinitePeriodicAugmentation k) := sorry

-- Proof sketch: use the standard two-sided periodic injective resolution of `R / (ε)` over the
-- dual numbers. The complex is exact away from degree `0`, and its degree-`0` cohomology is the
-- quotient by `(ε)`.
/-- Example 15.70.4: for the dual numbers `R = k[ε]/(ε^2)` over a commutative ring `k` and
`M = R / (ε)`, the explicit bi-infinite periodic complex `⋯ ⟶ R ⟶ R ⟶ R ⟶ ⋯` with differential
given by multiplication by `ε` represents `M[0]` in `D(R)`. Over a field, the separate theorem
`dualNumbersBiInfinitePeriodicComplex_term_injective` upgrades this representative to an injective
one. Lean reuses the canonical chapter owner `DualNumber k`, definitionally `TrivSqZeroExt k k`.
-/
noncomputable def dualNumbersBiInfinitePeriodicComplex_iso_single0ResidueModule :
    DerivedCategory.Q.obj (dualNumbersBiInfinitePeriodicComplex k) ≅
      (single0).obj (dualNumbersResidueModule k) :=
  letI : QuasiIso (dualNumbersBiInfinitePeriodicAugmentation k) :=
    dualNumbersBiInfinitePeriodicAugmentation_quasiIso k
  asIso (DerivedCategory.Q.map (dualNumbersBiInfinitePeriodicAugmentation k)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ ModRε (0 : ℤ)).app
      (dualNumbersResidueModule k)).symm

end

section

variable (k : Type u) [Field k]

local notation "Rε" => DualNumber k

-- Proof sketch: the dual numbers `k[ε]/(ε^2)` form a self-injective Frobenius algebra over the
-- field `k`, so the regular module is injective.
/-- The dual numbers over a field are injective as a module over themselves. -/
theorem dualNumbers_self_injective :
    Module.Injective Rε Rε := sorry

-- Proof sketch: every term of `dualNumbersBiInfinitePeriodicComplex` is the regular module `R`,
-- and `dualNumbers_self_injective` identifies that regular module as injective; translate to
-- `ModuleCat` using `Module.injective_iff_injective_object`.
/-- Every term of the bi-infinite dual-numbers periodic complex is injective. -/
theorem dualNumbersBiInfinitePeriodicComplex_term_injective (n : ℤ) :
    Injective ((dualNumbersBiInfinitePeriodicComplex k).X n) := sorry

end

/-! ### Lemma_15_70_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "Hb" => boundedDerivedHomologyFunctor Mod

/-
Domain-style sampling for Lemma 15.70.5:
- primary domain: finite injective dimension in `D(R)`, together with bounded derived objects and
  bounded cochain-complex presentations;
- sampled owner declarations:
  `HasFiniteInjectiveDimension`,
  `injectiveDimension`,
  `DbMod`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.homologyFunctor`,
  `t.bounded`,
  `Compᵇ(Mod)`;
- best owner abstraction: the source-facing statements stay about finite injective dimension,
  while boundedness in `D(R)` should be stated directly on the chapter owner
  `DbMod`, and the representative-level bounded-complex hypothesis should reuse the
  chapter owner `Compᵇ(Mod)` rather than a raw cochain complex together with separate
  support-bound witnesses;
  finite injective dimension for modules is already canonically owned by `injectiveDimension`,
  and the bounded-derived cohomology objects should be read through the chapter owner
  `boundedDerivedHomologyFunctor`, so the hypotheses below should use
  `injectiveDimension _ ≠ ⊤` directly on `((Hb i).obj K)`;
- primitive vs. derived:
  primitive data are the bounded derived object `K : DbMod` in part `(1)`, read through the
  chapter owner `Hb i`,
  the bounded representative complex `K' : Compᵇ(Mod)` in part `(2)`, and the module-level
  finite-injective-dimension hypotheses on cohomology objects or terms;
  derived API is the resulting `HasFiniteInjectiveDimension` conclusion, stated in part `(2)`
  directly for the represented object `Q.obj K'.obj`;
- source/core/bridge triage:
  `source-facing`: the two finite-injective-dimension theorems below;
  `core/canonical`: `HasFiniteInjectiveDimension`, `injectiveDimension`,
    `DbMod`, `Hb`,
    `DerivedCategory.homologyFunctor`, `t.bounded`, and
    `Compᵇ(Mod)`;
  `bridge/view`: passage from a chosen representative `K'` to an arbitrary isomorphic derived
  object, which is not kept in the main public theorem statement.
-/

-- Proof sketch: apply the Ext spectral sequence of Lemma `13.21.3` to the functor
-- `Hom_R(N, -)` and use the boundedness of `K` together with the finite injective-dimension
-- bounds on the cohomology objects `H^i(K)` to deduce eventual vanishing of
-- `Ext^n_R(N, K)` for every module `N`; then conclude from the criterion of Lemma `15.70.2`.
/-- Lemma 15.70.5 (1): if `K` lies in the bounded derived category `D^b(R)` and each cohomology
module `H^i(K)` has finite injective dimension, then `K` has finite injective dimension. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_homology_finiteInjectiveDimension
    (K : DbMod)
    (hH : ∀ i : ℤ,
      injectiveDimension ((Hb i).obj K) ≠ ⊤) :
    HasFiniteInjectiveDimension K.obj := sorry

-- Proof sketch: for each term `K'ⁱ`, choose a finite injective resolution and splice these
-- resolutions into a bounded double complex representing `DerivedCategory.Q.obj K'`. The total
-- complex is again bounded with injective terms, so it gives a finite injective-amplitude
-- representative of `DerivedCategory.Q.obj K'`.
/-- Lemma 15.70.5 (2): if a bounded cochain complex `K'` has termwise finite injective dimension,
then the represented derived object `Q.obj K'.obj` has finite injective
dimension. The boundedness datum is carried by the chapter owner `Compᵇ(Mod)`. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_termwise_finiteInjectiveDimension
    (K' : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, injectiveDimension (K'.obj.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension (Q.obj K'.obj) := sorry

end

end CategoryTheory

/-! ### Lemma_15_70_6 (from Chap15) -/
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
/-- Lemma 15.70.6: let `R` be a Noetherian ring, let `I ⊆ R` be an ideal contained in the
Jacobson radical, and let `K ∈ D^+(R)` have finite cohomology modules. Then `K` has finite
injective dimension if and only if there exists an integer `b` such that
`Ext^i_R(R/J, K) = 0` for every `i > b` and every ideal `J ⊇ I`. -/
theorem finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ,
        ∀ (J : Ideal R), I ≤ J →
          ∀ i : ℤ, b < i →
            ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 := sorry

end

end CategoryTheory

/-! ### Lemma_15_70_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open IsLocalRing
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "Mod" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "κ" => ResidueField R
local notation "κ₀" => Functor.obj single₀ (ModuleCat.of R κ)

/- Domain-style sampling:
- primary domain: finite injective dimension in `DerivedCategory (ModuleCat R)` for local
  Noetherian rings, tested by eventual vanishing of `Ext` from the residue field;
- sampled owner declarations:
  `D⁺(Mod)`,
  `HasFiniteInjectiveDimension`,
  `finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge`,
  `ringJacobson_eq_maximalIdeal`,
  `ResidueField`,
  `DerivedCategory.t.plus`;
- best owner abstraction: the owner remains `HasFiniteInjectiveDimension`; this item is a
  `bridge/view` specialization of Lemma `15.70.6` along the canonical local-ring data
  `maximalIdeal R` and `ResidueField R`, with the bounded-below input carried by the Chapter `13`
  owner `K : D⁺(Mod)`, not by a second explicit witness;
- primitive data: `K : D⁺(Mod)` and finite cohomology modules;
- derived API: eventual vanishing of `Ext^i(κ₀, K)`, with the raw `ShiftedHom` owner kept
  implicit behind the Chapter `13` notation;
- abstraction check: `ResidueField R` is already the canonical quotient `R ⧸ maximalIdeal R`, so
  no local wrapper around the residue-field test object should be introduced. -/

-- Proof sketch: specialize Lemma `15.70.6` to the ideal `maximalIdeal R`. In a local ring,
-- `Ring.jacobson R = maximalIdeal R`, so the ideal-quotient test family collapses to the single
-- quotient `R / maximalIdeal R = ResidueField R`.
/-- Lemma 15.70.7: for a local Noetherian ring `R` and an object `K ∈ D⁺(R)` with finite
cohomology modules, `K` has finite injective dimension if and only if the groups
`Ext^i_R(ResidueField R, K)` vanish for all sufficiently large `i`. -/
lemma finiteInjectiveDimension_iff_eventually_residueField_ext_vanishes
    (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ,
        ∀ i : ℤ, b < i → ∀ e : Ext^i(κ₀, K.obj), e = 0 := by
  have hcriterion :=
    finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge
      (maximalIdeal R) (by simpa [ringJacobson_eq_maximalIdeal R]) K hKfinite
  constructor
  · intro hK
    rcases hcriterion.mp hK with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro i hi e
    simpa [ResidueField] using hb (maximalIdeal R) le_rfl i hi e
  · rintro ⟨b, hb⟩
    refine hcriterion.mpr ⟨b, ?_⟩
    intro J hJ i hi e
    by_cases htop : J = ⊤
    · subst htop
      let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := inferInstance
      have hzero : IsZero ((single₀).obj (ModuleCat.of R (R ⧸ (⊤ : Ideal R)))) :=
        (single₀).map_isZero
          (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (R ⧸ (⊤ : Ideal R))))
      exact hzero.eq_of_src e 0
    · have hJ_eq : maximalIdeal R = J :=
        Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) htop hJ
      subst hJ_eq
      simpa [ResidueField] using hb i hi e

end

end CategoryTheory
