import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_69_1 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: projective-amplitude conditions for objects of `DerivedCategory (ModuleCat R)`,
  together with the canonical module-level projective-dimension invariant;
- inspected owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `CategoryTheory.projectiveDimension_le_iff`,
  `CategoryTheory.DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: `HasProjectiveAmplitudeIn` and `HasFiniteProjectiveDimension` for objects of
    `D(R)`;
  `core/canonical`: `projectiveDimension` for module-level finite projective dimension;
  `bridge/view`: the representative-complex unpacking theorem for `HasProjectiveAmplitudeIn`;
- primitive vs. derived:
  the primitive data for projective amplitude are a representative complex `P`, an isomorphism
  `K ≅ DerivedCategory.Q.obj P`, support bounds, and termwise projectivity;
  finite projective dimension in `D(R)` is derived from the amplitude owner by existentially
  forgetting the interval, while module-level finite projective dimension is already owned by
  `projectiveDimension`. -/

/-- Definition 15.69.1 (2): an object `K` of `D(R)` has projective-amplitude in `[a, b]` if it is
isomorphic in the derived category to a cochain complex of projective `R`-modules concentrated in
degrees `a` through `b`. -/
def HasProjectiveAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∃ (P : Cpx) (_ : K ≅ DerivedCategory.Q.obj P),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i)

-- Proof sketch: this is just the direct expansion of the definition of projective-amplitude in
-- terms of a bounded representative with projective terms and a chosen isomorphism in `D(R)`.
/-- An object of `D(R)` has projective-amplitude in `[a, b]` exactly when it admits a
representative by a cochain complex of projective `R`-modules concentrated in degrees `a`
through `b`. -/
theorem hasProjectiveAmplitudeIn_iff_exists_representative (K : DMod) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : Cpx) (_ : K ≅ DerivedCategory.Q.obj P),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) :=
  Iff.rfl

/-- Definition 15.69.1 (1): an object `K` of `D(R)` has finite projective dimension if it has
projective-amplitude in some finite interval `[a, b]`. -/
def HasFiniteProjectiveDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b

-- Proof sketch: one direction forgets the specified amplitude interval from a projective
-- representative, while the other direction records the interval furnished by
-- `HasProjectiveAmplitudeIn`.
/-- An object of `D(R)` has finite projective dimension exactly when it has projective-amplitude in
some finite interval `[a, b]`. -/
theorem hasFiniteProjectiveDimension_iff (K : DMod) :
    HasFiniteProjectiveDimension K ↔ ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b :=
  Iff.rfl

end

end CategoryTheory

/-! ### Lemma_15_69_2 (from Chap15) -/
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
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain-style sampling:
- primary domain: projective-amplitude criteria in `D(R)` detected by derived `Ext` against
  degree-zero modules;
- sampled owner declarations:
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` from `Lemma_15_66_1`,
  `ShiftedHom`,
  `Ext^i(X, Y)` from `Definition_13_27_1`,
  `existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing` from
    `Lemma_15_77_6`;
- best owner abstraction:
  `source-facing`: the interval and half-line vanishing clauses in the TFAE, written as
    vanishing of the derived extension groups `Ext^i(K, N[0])`;
  `core/canonical`: the chapter owner `derivedExtToModuleFunctor K i` for the unrestricted
    degree-`i` vanishing test on modules;
  `bridge/view`: its value at `N`, namely `ShiftedHom K ((singleFunctor _ 0).obj N) i`, written in
    the chapter notation as `Ext^i(K, N[0])`.

Primitive data here are only the degree-wise vanishing statements with their module argument
visible. The “outside an interval”, “for all degrees above a bound”, and mixed cohomology-plus-Ext
clauses are derived API over the existing Ext owner, so the public theorem surface should keep the
source-facing pointwise `Ext^i(K, N[0])` clauses rather than hide `N` inside
`IsZero (derivedExtToModuleFunctor K i)`.
-/

/-
Proof sketch: follow the Stacks proof. `(1) → (2)` computes `Ext` from a bounded projective
representative. `(2) → (3)` and `(3) → (4)` test cohomology against injective modules. For
`(4) → (1)`, first deduce cohomology vanishing below `a`, choose a bounded-above projective
representative, truncate in degree `a`, and use the degree `1 - a` `Ext`-vanishing plus
Lemma `10.77.2` to show the leftmost cokernel is projective.
-/
/-- Lemma 15.69.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` has projective-amplitude in `[a, b]`; the derived `Ext` groups
`Ext^i_R(K, N)` vanish for every `R`-module `N` and every
`i ∉ [-b, -a]`; `H^n(K)` vanishes for `n > b` and these groups vanish for all `i > -a`; and
`H^n(K)` vanishes for `n ∉ [a - 1, b]` and `Ext^{-a + 1}_R(K, N)` vanishes for every
`R`-module `N`. -/
theorem projectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R) (i : ℤ), -a < i → ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R), ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0
      ] := sorry

end

end CategoryTheory

/-! ### Example_15_69_3 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open TrivSqZeroExt
open scoped DualNumber

section

variable (k : Type u) [CommRing k]

local notation "Rε" => DualNumber k
local notation "ModRε" => ModuleCat Rε

/- Domain-style sampling:
- primary domain: dual numbers as a trivial square-zero extension, together with the explicit
  `ε`-periodic cochain complex in `ModuleCat Rε`;
- inspected owner declarations:
  `TrivSqZeroExt.kerIdeal`,
  `Ideal.Quotient.mkₐ`,
  `Ideal.Quotient.mkₐ_eq_mk`,
  `DualNumber.eps_mul_eps`,
  `CochainComplex.of`;
- best owner abstraction:
  `source-facing`: the residue module `R / (ε)` and the explicit periodic complex
    `R --ε→ R --ε→ ⋯`;
  `core/canonical`: `TrivSqZeroExt.kerIdeal` for the ideal `(ε)` and `CochainComplex.of` for the
    complex, with `Ideal.Quotient.mkₐ` for the quotient algebra map;
  `bridge/view`: the quotient presentation of `R / (ε)` by the kernel ideal of
    `TrivSqZeroExt.fstHom`;
- primitive data: the dual-number ring `Rε` and multiplication by `ε`;
- derived API: the residue module, quotient map, periodic complex, augmentation, and the
  projective-dimension statements below. -/

/-- The residue module `R / (ε)` for the dual numbers `R`, realized via the canonical kernel ideal
of `TrivSqZeroExt.fstHom`. -/
abbrev dualNumbersResidueModule : ModRε :=
  ModuleCat.of Rε (Rε ⧸ kerIdeal k k)

/-- Multiplication by `ε` on the dual numbers, viewed as an endomorphism of the free rank-one
module `R`. -/
def dualNumbersPeriodicDifferential : ModuleCat.of Rε Rε ⟶ ModuleCat.of Rε Rε :=
  ModuleCat.ofHom (LinearMap.mulLeft Rε (ε : Rε))

-- Proof sketch: `ε` is square-zero in the trivial square-zero extension, so composing left
-- multiplication by `ε` with itself is left multiplication by `ε^2 = 0`.
/-- Left multiplication by `ε` squares to zero on the dual numbers. -/
theorem dualNumbersPeriodicDifferential_sq :
    dualNumbersPeriodicDifferential k ≫ dualNumbersPeriodicDifferential k = 0 := sorry

/-- The infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` over the dual numbers. -/
def dualNumbersPeriodicComplex : CochainComplex ModRε ℕ :=
  CochainComplex.of
    (fun _ ↦ ModuleCat.of Rε Rε)
    (fun _ ↦ dualNumbersPeriodicDifferential k)
    (fun _ ↦ dualNumbersPeriodicDifferential_sq k)

/-- The canonical augmentation from the periodic `ε`-complex to the module `R / (ε)` concentrated
in degree `0`. -/
def dualNumbersPeriodicAugmentation :
    dualNumbersPeriodicComplex k ⟶
      (CochainComplex.single₀ ModRε).obj (dualNumbersResidueModule k) :=
  (CochainComplex.toSingle₀Equiv
      (dualNumbersPeriodicComplex k)
      (dualNumbersResidueModule k)).symm
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Rε (kerIdeal k k)).toLinearMap)

-- Proof sketch: every term of `dualNumbersPeriodicComplex` is the free rank-one module `R`, hence
-- projective in `ModuleCat R`.
/-- Each term of the periodic dual-numbers complex is projective. -/
theorem dualNumbersPeriodicComplex_projective (n : ℕ) :
    Projective ((dualNumbersPeriodicComplex k).X n) := sorry

-- Proof sketch: identify the degree-zero homology of the periodic `ε`-complex with `R / (ε)` and
-- check that the higher homology vanishes because consecutive differentials are both multiplication
-- by the square-zero element `ε`.
/-- Example 15.69.3: for the dual numbers `R = k[ε]/(ε^2)` over a commutative ring `k` and
`M = R / (ε)`, the canonical
augmentation from the infinite `ε`-periodic cochain complex `R --ε→ R --ε→ R --ε→ ⋯` to the
degree-zero complex `M[0]` is a quasi-isomorphism. Lean uses the canonical owner
`DualNumber k` for `R`, definitionally `TrivSqZeroExt k k`. -/
theorem dualNumbersResidueModule_quasiIso_periodicComplex :
    QuasiIso (dualNumbersPeriodicAugmentation k) := sorry

end

section

variable (k : Type u) [CommRing k] [Nontrivial k]

-- Proof sketch: if `R / (ε)` had finite projective dimension, some finite truncation of the
-- periodic projective resolution would force a projective syzygy. For the dual numbers this never
-- happens, because every syzygy is again isomorphic to `R / (ε)`.
/-- Over a nontrivial commutative ring, the residue module over the dual numbers does not have
finite projective dimension. -/
theorem dualNumbersResidueModule_projectiveDimension_eq_top :
    projectiveDimension (dualNumbersResidueModule k) = ⊤ := sorry

end
