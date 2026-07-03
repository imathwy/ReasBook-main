import Mathlib
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Topology.Inseparable

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_107_1 (from Chap15) -/
open Ideal IsLocalRing

universe u

section

variable (A : Type u) [CommRing A]

/-- The reduction `A_red` of a commutative ring `A`. -/
abbrev unibranchReduction :=
  A ⧸ nilradical A

/-- The normalization of the reduction of a commutative ring inside its fraction field. -/
abbrev unibranchNormalization :=
  integralClosure (unibranchReduction A) (FractionRing (unibranchReduction A))

namespace Unibranch

/- The textbook notation is `A_red`. Lean parses bare `A_red` as a single identifier, so the
owner-level term notation is parenthesized as `(A)_red`. -/
/-- Scoped notation for the reduction `A_red` of a commutative ring `A`. -/
scoped notation:max "(" R ")" "_red" => unibranchReduction R

/-- Scoped notation for the unibranch normalization `A'`. -/
scoped postfix:max "′" => unibranchNormalization

end Unibranch

open scoped Unibranch

/-- The unibranch normalization inherits an `A`-algebra structure through the quotient map
`A → (A)_red`. -/
instance : Algebra A A′ :=
  ((algebraMap (A)_red A′).comp (algebraMap A (A)_red)).toAlgebra

/-- The unibranch normalization lies over the reduction `(A)_red` as an `A`-algebra tower. -/
instance : IsScalarTower A (A)_red A′ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The unibranch normalization is integral over `A`. -/
instance : Algebra.IsIntegral A A′ :=
  Algebra.IsIntegral.trans (A)_red

variable [IsLocalRing A]

/-- The reduction of a local ring is again local. -/
instance :
    IsLocalRing (A)_red := by
  let _ : Nontrivial (A ⧸ nilradical A) := Ideal.Quotient.nontrivial_iff.2 <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      (nilradical_le_prime (maximalIdeal A))
  simpa [unibranchReduction, Ideal.Quotient.algebraMap_eq] using
    (IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective :
      IsLocalRing (A ⧸ nilradical A))

/-- The canonical quotient map from a local ring to its reduction is local. -/
instance : IsLocalHom (algebraMap A (A)_red) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The residue field `κ(m)` at a maximal point `m`. -/
abbrev MaximalSpectrum.ResidueField {R : Type u} [CommRing R] (m : MaximalSpectrum R) :=
  m.asIdeal.ResidueField

/-- Any maximal ideal of the unibranch normalization `A'` contracts to the maximal ideal of the
local base ring `A`. -/
theorem unibranchNormalization_comap_maximalIdeal
    {m : Ideal A′} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap A A′) m = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

private noncomputable abbrev maximalIdealResidueFieldEquiv :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- The canonical residue-field map `κ(A) → κ(m')` induced by the local base map
`A → A' = unibranchNormalization A`. -/
noncomputable def unibranchNormalizationResidueFieldMap
    (m : MaximalSpectrum A′) :
    ResidueField A →+* m.ResidueField :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A A′)
      (unibranchNormalization_comap_maximalIdeal A m.isMaximal).symm).comp
    (maximalIdealResidueFieldEquiv A).symm.toRingHom

/-- The residue field at a maximal point of the unibranch normalization is canonically a
`ResidueField A`-algebra. -/
noncomputable instance (m : MaximalSpectrum A′) :
    Algebra (ResidueField A) m.ResidueField :=
  (unibranchNormalizationResidueFieldMap A m).toAlgebra

/-- Definition 15.107.1 (1): a local ring is unibranch if its reduction is a domain and the
normalization of that reduction in its fraction field is local. -/
class IsUnibranch : Prop where
  toIsDomain : IsDomain (A)_red
  isLocalRing_unibranchNormalization :
    letI : IsDomain (A)_red := toIsDomain
    IsLocalRing A′

instance [h : IsUnibranch A] : IsDomain (A)_red :=
  h.toIsDomain

instance [h : IsUnibranch A] : IsLocalRing A′ := by
  letI : IsDomain (A)_red := h.toIsDomain
  exact h.isLocalRing_unibranchNormalization

/-- The canonical map `A → A'` to the unibranch normalization is local. -/
instance [IsUnibranch A] : IsLocalHom (algebraMap A A′) :=
  algebraMap_isLocalHom_of_isLocalRing_of_integral

/-- Definition 15.107.1 (2): a local ring is geometrically unibranch if it is unibranch and the
canonical residue-field extension induced by `A → A'` is purely inseparable. -/
class IsGeometricallyUnibranch : Prop where
  toIsUnibranch : IsUnibranch A
  residueField_isPurelyInseparable :
    letI : IsUnibranch A := toIsUnibranch
    IsPurelyInseparable (ResidueField A) (ResidueField A′)

instance [h : IsGeometricallyUnibranch A] : IsUnibranch A :=
  h.toIsUnibranch

instance [h : IsGeometricallyUnibranch A] :
    IsPurelyInseparable (ResidueField A) (ResidueField A′) := by
  letI : IsUnibranch A := h.toIsUnibranch
  exact h.residueField_isPurelyInseparable

/-- A field is unibranch. -/
instance (K : Type u) [Field K] : IsUnibranch K := sorry

/-- A field is geometrically unibranch. -/
instance (K : Type u) [Field K] :
    IsGeometricallyUnibranch K := sorry

end

/-! ### Lemma_15_107_2 (from Chap15) -/
open scoped TensorProduct
open scoped Unibranch
open Algebra.TensorProduct
open IsLocalRing

universe u

noncomputable section

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "A′h" => A′ ⊗[A] Ah

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch normalization, henselization, and prime
  spectra under tensor-product base change;
- sampled owner declarations of the same kind:
  `unibranchNormalization`,
  `IsHenselizationOf`,
  `minimalPrimes`,
  `Algebra.TensorProduct.includeRight`;
- best owner abstraction: the source-facing object is the chapter owner `A′ =
  unibranchNormalization A`, while the ideal-theoretic comparison statements are derived API on the
  canonical tensor-product base change `A′ ⊗[A] Ah`;
- primitive data: the local ring `A`, its chosen henselization `Ah`, and the owner `A′`;
- derived API: contraction along `A′ → A′h` and `Ah → A′h`, together with the canonical sets of
  maximal and minimal primes.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 15.107.2;
- `core/canonical`: `unibranchNormalization`, `IsHenselizationOf`, `Ideal.comap`,
  `minimalPrimes`, `Algebra.TensorProduct.includeRight`;
- `bridge/view`: the base-changed ring `A′h = A′ ⊗[A] Ah`.
-/

-- Proof sketch: reduce to the reduced case, identify the closed fiber of
-- `Anorm → Anormh = Anorm ⊗[A] Ah` with `Anorm ⊗[A] ResidueField A`, and use the trivial residue
-- field extension of a henselization together with integrality over the local base to show that
-- comap along `A' → (A')^h` gives a bijection on maximal ideals.
/-- Lemma 15.107.2 (1): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A')` is bijective on maximal ideals. -/
theorem unibranchNormalizationTensorHenselization_bijOn_maximalIdeals
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (includeLeftRingHom : A′ →+* A′h))
      {m : Ideal A′h | m.IsMaximal}
      {m : Ideal A′ | m.IsMaximal} := sorry

-- Proof sketch: compare minimal primes on both sides with the fibers over the minimal primes of
-- `A`, use that `A'` becomes the total ring of fractions after inverting non-zero-divisors, and
-- identify `(A')^h ⊗[A] Q(Ared)` with `A^h ⊗[A] Q(Ared)` to match the minimal-prime sets.
/-- Lemma 15.107.2 (2): for `A' = unibranchNormalization A` and `(A')^h = A' ⊗[A] A^h`, the map
`Spec((A')^h) → Spec(A^h)` is bijective on minimal primes. -/
theorem unibranchNormalizationTensorHenselization_bijOn_minimalPrimes
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn
      (Ideal.comap ((includeRight : Ah →ₐ[A] A′h).toRingHom))
      (minimalPrimes A′h)
      (minimalPrimes Ah) := sorry

-- Proof sketch: `Anormh` is normal after base change to the henselization, so localizations at
-- maximal ideals are domains; combine this with henselian-pair connectivity of the closed fiber
-- to see that the connected closed subset cut out by a minimal prime meets the closed fiber in a
-- unique point, hence lies in a unique maximal ideal.
/-- Lemma 15.107.2 (3): every minimal prime of `(A')^h = A' ⊗[A] A^h` is contained in a unique
maximal ideal. -/
theorem unibranchNormalizationTensorHenselization_minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal A′h} (hp : p ∈ minimalPrimes A′h) :
    ∃! m : Ideal A′h, m.IsMaximal ∧ p ≤ m := sorry

-- Proof sketch: after the previous clause, each minimal prime determines a unique maximal ideal;
-- normality of the local rings of `Anormh` implies each maximal localization is a domain, so a
-- maximal ideal can contain only one minimal prime.
/-- Lemma 15.107.2 (4): every maximal ideal of `(A')^h = A' ⊗[A] A^h` contains exactly one
minimal prime. -/
theorem unibranchNormalizationTensorHenselization_maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal A′h} (hm : m.IsMaximal) :
    ∃! p : Ideal A′h, p ∈ minimalPrimes A′h ∧ p ≤ m := sorry

end

/-! ### Lemma_15_107_3 (from Chap15) -/
universe u

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch local rings, henselizations, and minimal
  prime ideals;
- sampled owner declarations of the same kind:
  `IsUnibranch`,
  `IsHenselizationOf`,
  `henselizationMap_faithfullyFlat`,
  `unibranchNormalizationTensorHenselization_bijOn_minimalPrimes`;
- best owner abstraction: `IsUnibranch` is the core owner, while the chosen henselization `Ah` and
  its minimal-prime set form the bridge/view used to restate the source criterion;
- primitive data: the local ring `A` and the chosen henselization `Ah`;
- derived API: the unique-minimal-prime characterization on `Ah`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `IsUnibranch`, `IsHenselizationOf`, `minimalPrimes`;
- `bridge/view`: the chosen henselization `Ah`.
-/

-- Proof sketch: for `(2) → (1)`, contract the unique minimal prime of `Ah` along the faithfully
-- flat henselization map to get the unique minimal prime of `A`, then use the reduced henselized
-- quotient to force the normalization of `Ared` to be local. For `(1) → (2)`, use the local
-- normalization of `Ared`, the comparison with its base change to `Ah` from Lemma `15.107.2`, and
-- the filtered-colimit description of henselization to show that every two minimal primes of `Ah`
-- coincide.
/-- Lemma 15.107.3: for a local ring `A` and a chosen henselization `Ah` of `A`, the ring `A` is
unibranch if and only if `Ah` has a unique minimal prime ideal. -/
theorem isUnibranch_iff_existsUnique_minimalPrime_henselization :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := sorry

end

/-! ### Lemma_15_107_4 (from Chap15) -/
open scoped TensorProduct
open scoped Unibranch
open Algebra.TensorProduct
open IsLocalRing

universe u v w

noncomputable section

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

section StrictHenselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ash : Type u} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "A′sh" => A′ ⊗[A] Ash
local notation "κ" => ResidueField A

local instance unibranchNormalizationTensorLeftAlgebra : Algebra A′ A′sh :=
  Algebra.TensorProduct.leftAlgebra

private noncomputable abbrev maximalSpectrumToResidueField
    (m : MaximalSpectrum A′) :
    A′ →+* m.asIdeal.ResidueField :=
  (algebraMap (A′ ⧸ m.asIdeal) m.asIdeal.ResidueField).comp (Ideal.Quotient.mk m.asIdeal)

private noncomputable abbrev maximalSpectrumBaseAlgebra
    (m : MaximalSpectrum A′) :
    Algebra A′ m.asIdeal.ResidueField :=
  RingHom.toAlgebra (maximalSpectrumToResidueField m)

private theorem existsUnique_bijective_fiberPrimeOfAlgHom
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (ι : ResidueField Ash ≃+* Kbar)
    (hι : ι.toRingHom.comp (ResidueField.map (algebraMap A Ash)) = algebraMap κ Kbar)
    (m : MaximalSpectrum A′) :
    ∃! F : (m.asIdeal.ResidueField →ₐ[κ] Kbar) → PrimeSpectrum (m.asIdeal.Fiber A′sh),
      Function.Bijective F := by
  sorry

/-- The canonical fiber point attached to a `κ`-algebra embedding
`κ(m') = Ideal.ResidueField m.asIdeal → Kbar`. -/
noncomputable def fiberPrimeOfAlgHom
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (ι : ResidueField Ash ≃+* Kbar)
    (hι : ι.toRingHom.comp (ResidueField.map (algebraMap A Ash)) = algebraMap κ Kbar)
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField →ₐ[κ] Kbar) → PrimeSpectrum (m.asIdeal.Fiber A′sh) :=
  Classical.choose (existsUnique_bijective_fiberPrimeOfAlgHom ι hι m)

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch normalization, strict henselization, and
  fibers of the spectral map after tensor-product base change;
- sampled owner declarations of the same kind:
  `unibranchNormalization`,
  `IsStrictHenselizationOf`,
  `fiberPrimeAt`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `Ideal.Fiber`;
- best owner abstraction: the source-facing ring is `A′ = unibranchNormalization A`, and the
  canonical bridge from the spectral fiber over a prime to a ring object is the fiber ring
  `m.Fiber A′sh`, whose spectrum is identified upstream by `PrimeSpectrum.preimageHomeomorphFiber`
  and whose distinguished points over primes of `A′sh` are owned by `fiberPrimeAt`;
- primitive data: the local ring `A`, its chosen strict henselization `Ash`, the normalization
  owner `A′`, and a maximal point `m : MaximalSpectrum A′`;
- derived API: the residue-field algebraicity statement, the fiber-point counting statement over
  `m`, and the minimal/maximal-prime comparison statements on `A′sh`.

Source/core/bridge triage:
- `source-facing`: the five clauses of Lemma 15.107.4;
- `core/canonical`: `unibranchNormalization`, `IsStrictHenselizationOf`, `Ideal.Fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`, `minimalPrimes`, `Ideal.comap`;
- `bridge/view`: the tensor-product base change `A′sh = A′ ⊗[A] Ash`.
-/

-- Proof sketch: the map `A → A'` is integral, so the induced extension of residue fields at a
-- maximal ideal `m' ⊂ A'` is algebraic over the residue field of the contracted maximal ideal of
-- `A`; locality of `A → A'` identifies this contracted maximal ideal with `maximalIdeal A`.
/-- Lemma 15.107.4 (1): for a maximal ideal `m' ⊂ A'`, the residue field
`κ(m') = Ideal.ResidueField m'.asIdeal` is algebraic over `κ = A / maximalIdeal A`. -/
theorem unibranchNormalization_residueField_isAlgebraic
    (m : MaximalSpectrum A′) :
    Algebra.IsAlgebraic κ m.asIdeal.ResidueField := sorry

-- Proof sketch: `PrimeSpectrum.preimageHomeomorphFiber` identifies primes of the fiber ring
-- `m'.Fiber A′sh` with primes of `A′sh` lying over `m'`. Choosing a residue-field identification
-- `ResidueField Ash ≃ Kbar` compatible with the base residue-field map turns a
-- `κ`-algebra embedding `κ(m') → Kbar` into a unique fiber point, and every fiber point arises
-- uniquely in this way.
/-- Lemma 15.107.4 (2): let `m' ⊂ A'` be maximal, let `Kbar` be an algebraic closure of `κ`, and
choose a compatible identification `ResidueField Ash ≃ Kbar`. Then fiber points of
`m'.Fiber A′sh = κ(m') ⊗[A'] (A' ⊗[A] Ash)` are canonically in bijection with `κ`-algebra
embeddings `κ(m') → Kbar`. -/
theorem fiberPrimeOfAlgHom_bijective
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (ι : ResidueField Ash ≃+* Kbar)
    (hι : ι.toRingHom.comp (ResidueField.map (algebraMap A Ash)) = algebraMap κ Kbar)
    (m : MaximalSpectrum A′) :
    Function.Bijective (fiberPrimeOfAlgHom ι hι m) := by
  exact (Classical.choose_spec (existsUnique_bijective_fiberPrimeOfAlgHom ι hι m)).1

/-- Equivalence form of Lemma 15.107.4 (2). -/
noncomputable def fiberPrimeOfAlgHomEquiv
    {Kbar : Type w} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (ι : ResidueField Ash ≃+* Kbar)
    (hι : ι.toRingHom.comp (ResidueField.map (algebraMap A Ash)) = algebraMap κ Kbar)
    (m : MaximalSpectrum A′) :
    (m.asIdeal.ResidueField →ₐ[κ] Kbar) ≃ PrimeSpectrum (m.asIdeal.Fiber A′sh) :=
  Equiv.ofBijective (fiberPrimeOfAlgHom ι hι m) (fiberPrimeOfAlgHom_bijective ι hι m)

-- Proof sketch: compare minimal primes of `A′sh` and `Ash` by tensoring with the total ring
-- of fractions of `Ared`; as in the henselization case, both spectra identify with the minimal
-- primes lying over the minimal primes of `A`, and the tensor-factor `A′` does not change the
-- generic fiber.
/-- Lemma 15.107.4 (3): the map `Spec(A′sh) → Spec(Ash)` induced by the right tensor-factor map
`Ash → A′sh` is bijective on minimal primes. -/
theorem unibranchNormalizationTensorStrictHenselization_bijOn_minimalPrimes
    (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn
      (Ideal.comap ((includeRight : Ash →ₐ[A] A′sh).toRingHom))
      (minimalPrimes A′sh)
      (minimalPrimes Ash) := sorry

-- Proof sketch: normality of `A′sh` gives that each localization at a maximal ideal is a
-- domain, while the henselian-pair connectivity argument for the closed fiber shows that the
-- closed subset defined by a minimal prime meets the closed fiber in exactly one point.
/-- Lemma 15.107.4 (4): every minimal prime of `(A')^sh = A' ⊗[A] A^sh` is contained in a unique
maximal ideal. -/
theorem unibranchNormalizationTensorStrictHenselization_minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal A′sh} (hp : p ∈ minimalPrimes A′sh) :
    ∃! m : Ideal A′sh, m.IsMaximal ∧ p ≤ m := sorry

-- Proof sketch: after clause `(4)`, each minimal prime determines a unique maximal ideal. Since
-- the localizations of `A′sh` at maximal ideals are normal domains, a maximal ideal cannot
-- contain two distinct minimal primes.
/-- Lemma 15.107.4 (5): every maximal ideal of `(A')^sh = A' ⊗[A] A^sh` contains a unique minimal
prime. -/
theorem unibranchNormalizationTensorStrictHenselization_maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal A′sh} (hm : m.IsMaximal) :
    ∃! p : Ideal A′sh, p ∈ minimalPrimes A′sh ∧ p ≤ m := sorry

end StrictHenselization

/-! ### Lemma_15_107_5 (from Chap15) -/
universe u

section

variable (A Ash : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-
Domain-style sampling:
- primary domain: local commutative algebra of geometrically unibranch local rings, strict
  henselizations, and minimal prime ideals;
- sampled owner declarations of the same kind:
  `IsGeometricallyUnibranch`,
  `IsStrictHenselizationOf`,
  `isUnibranch_iff_existsUnique_minimalPrime_henselization`,
  `unibranchNormalizationTensorStrictHenselization_bijOn_minimalPrimes`;
- best owner abstraction: `IsGeometricallyUnibranch` is the core owner, while the chosen strict
  henselization `Ash` and its minimal-prime set are the bridge/view used to restate the source
  criterion;
- primitive data: the local ring `A` and the chosen strict henselization `Ash`;
- derived API: the unique-minimal-prime characterization on `Ash`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `IsGeometricallyUnibranch`, `IsUnibranch`, `minimalPrimes`,
  `IsStrictHenselizationOf`;
- `bridge/view`: the chosen strict henselization `Ash` together with the comparison of minimal
  primes from Lemma `15.107.4`.
-/

-- Proof sketch: combine the henselization criterion from Lemma `15.107.3` with the strict
-- henselization comparison results from Lemma `15.107.4`. The unibranch part is already owned by
-- the henselization theorem, while the geometric refinement is detected by the strict
-- henselization fibers and their minimal primes.
/-- Lemma 15.107.5: for a local ring `A` and a chosen strict henselization `Ash` of `A`, the ring
`A` is geometrically unibranch if and only if `Ash` has a unique minimal prime ideal. -/
theorem isGeometricallyUnibranch_iff_existsUnique_minimalPrime_strictHenselization :
    IsGeometricallyUnibranch A ↔ ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := sorry

end

/-! ### Definition_15_107_6 (from Chap15) -/
universe u

noncomputable section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and minimal
  primes;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `minimalPrimes`;
- best owner abstraction: the source-facing branch-count owners should take the base local ring
  and the chosen henselization/strict henselization explicitly, while the counted minimal-prime
  set remains the canonical derived object on the chosen target ring;
- primitive data: the base local ring together with the chosen henselization/strict-henselization
  owner instance;
- derived API: the minimal-prime count `(minimalPrimes _).encard` on the chosen target ring.

Source/core/bridge triage:
- `source-facing`: `branchNumber`, `geometricBranchNumber`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `minimalPrimes`;
- `bridge/view`: direct unfolding of the source-facing definitions to `(minimalPrimes _).encard`.
-/

variable (A : Type u)
variable [CommRing A] [IsLocalRing A]

/-- Definition 15.107.6: for a chosen henselization `Ah` of the local ring `A`, the number of
branches of `A` is the extended natural number counting the minimal primes of `Ah`. -/
abbrev branchNumber (Ah : Type u) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] : ℕ∞ :=
  (minimalPrimes Ah).encard

/-- Definition 15.107.6: for a chosen strict henselization `Ash` of the local ring `A`, the
number of geometric branches of `A` is the extended natural number counting the minimal primes of
`Ash`. -/
abbrev geometricBranchNumber
    (Ash : Type u) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash] : ℕ∞ :=
  (minimalPrimes Ash).encard

/-! ### Lemma_15_107_7 (from Chap15) -/
open scoped Unibranch
open IsLocalRing

universe u

noncomputable section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and the unibranch normalization;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `IsUnibranch`,
  `MaximalSpectrum`;
- best owner abstraction: `branchNumber` and `geometricBranchNumber` remain the source-facing
  owners, while the maximal-ideal side of the finite formulas should be expressed through the
  canonical owner `MaximalSpectrum A′` instead of a parallel subtype of maximal ideals;
- primitive data: the local ring `A` together with a chosen henselization or strict
  henselization;
- derived API: cardinality comparisons for minimal primes and for the maximal spectrum of the
  unibranch normalization.

Source/core/bridge triage:
- `source-facing`: the six clauses of Lemma 15.107.7;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsUnibranch`,
  `IsGeometricallyUnibranch`, `minimalPrimes`, and `MaximalSpectrum`;
- `bridge/view`: the finite-count formulas over `MaximalSpectrum A′`.
-/

section Henselization

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Proof sketch: use the comparison of minimal primes from the henselization count with the reduced
-- integral closure and the fact that an infinite set of minimal primes forces the counted set in
-- the definition of `branchNumber` to have infinite cardinality.
/-- Lemma 15.107.7 (1): if a local ring `A` has infinitely many minimal prime ideals, then the
number of branches of `A`, computed from a chosen henselization `Ah`, is `∞`. -/
theorem branchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    branchNumber A Ah = ⊤ := sorry

-- Proof sketch: unfold `branchNumber` and combine Lemma `15.107.3`, turning the statement
-- `branchNumber A Ah = 1` into the existence of a unique minimal prime of `Ah`.
/-- Lemma 15.107.7 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is `1` if and only if `A` is unibranch. -/
theorem branchNumber_eq_one_iff_isUnibranch :
    branchNumber A Ah = 1 ↔ IsUnibranch A := sorry

-- Proof sketch: apply Lemma `15.107.2` to identify minimal primes of the henselization-side
-- normalization base change with minimal primes of `Ah`, then use Lemma `15.107.2 (4)` to replace
-- those minimal primes by points of the maximal spectrum of the reduced integral closure `A'`.
/-- Lemma 15.107.7 (3): if `A` has finitely many minimal primes, then the number of branches of
`A`, computed from a chosen henselization `Ah`, is the number of points of the maximal spectrum of
the unibranch normalization `A'` of `A`. -/
theorem branchNumber_eq_encard_maximalIdeals_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    branchNumber A Ah = (Set.univ : Set (MaximalSpectrum A′)).encard := sorry

end Henselization

section StrictHenselization

variable (A Ash : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "κ" => ResidueField A

-- Proof sketch: use the strict henselization analogue of the branch count and compare minimal
-- primes through Lemma `15.107.4`; an infinite set of minimal primes forces the strict
-- henselization count to be infinite as well.
/-- Lemma 15.107.7 (4): if a local ring `A` has infinitely many minimal prime ideals, then the
number of geometric branches of `A`, computed from a chosen strict henselization `Ash`, is `∞`. -/
theorem geometricBranchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    geometricBranchNumber A Ash = ⊤ := sorry

-- Proof sketch: unfold `geometricBranchNumber` and combine Lemma `15.107.5`, turning the
-- statement
-- `geometricBranchNumber A Ash = 1` into the existence of a unique minimal prime of `Ash`.
/-- Lemma 15.107.7 (5): the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, is `1` if and only if `A` is geometrically unibranch. -/
theorem geometricBranchNumber_eq_one_iff_isGeometricallyUnibranch :
    geometricBranchNumber A Ash = 1 ↔ IsGeometricallyUnibranch A := sorry

-- Proof sketch: use Lemma `15.107.4 (3)` to replace minimal primes of `Ash` by minimal primes of
-- `A' ⊗[A] A^sh`, use Lemma `15.107.4 (5)` to group them by maximal ideals of `A'`, and then
-- identify each fiber with the separable-degree multiplicity from the residue field extension over
-- `κ` by the actual embedding type `Field.Emb κ m.ResidueField`, equivalently `[κ(m') : κ]_s`,
-- using Lemma `15.107.4 (2)` together with Fields, Lemma `9.14.8`.
/-- Lemma 15.107.7 (6): if `A` has finitely many minimal primes, then the number of geometric
branches of `A`, computed from a chosen strict henselization `Ash`, is obtained by counting each
point `m'` of the maximal spectrum of the unibranch normalization `A'` of `A` with multiplicity
`[κ(m') : κ]_s`. -/
theorem geometricBranchNumber_eq_encard_weighted_maximalSpectrum_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    geometricBranchNumber A Ash =
      (Set.univ :
        Set (Σ m : MaximalSpectrum A′, Field.Emb κ m.ResidueField)).encard :=
    sorry

end StrictHenselization

/-! ### Lemma_15_107_8 (from Chap15) -/
open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and smoothness at the closed point;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`;
- best owner abstraction: the source-facing branch-count equalities should stay expressed in terms
  of the chapter owners `branchNumber` / `geometricBranchNumber` with the source-facing smoothness
  hypothesis `Algebra.SmoothAtPrime A B (closedPoint B)`, while henselization and strict
  henselization remain primitive ambient data through `IsHenselizationOf` and
  `IsStrictHenselizationOf`;
- primitive data: a local homomorphism `A → B` of local rings, a chosen henselization or strict
  henselization on each side, the source-facing closed-point smoothness hypothesis, and in clause
  `(2)` the purely inseparable residue-field extension;
- derived API: the equalities comparing the branch and geometric-branch counts.

Source/core/bridge triage:
- `source-facing`: the two branch-count invariance statements below;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, and the canonical local smoothness owner `IsSmoothAt`;
- `bridge/view`: `Algebra.smoothAtPrime_iff_isSmoothAt`, which justifies keeping
  `Algebra.SmoothAtPrime` as the source-facing hypothesis rather than introducing a parallel local
  reformulation.
-/

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

section StrictHenselization

variable {Ash : Type u} {Bsh : Type v}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]

-- Proof sketch: pass to chosen strict henselizations of `A` and `B`, use that the smooth local
-- map remains flat after strict henselization, and compare minimal primes by going down and the
-- domain criterion after quotienting by a minimal prime of `A`.
/-- Lemma 15.107.8 (1): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A`, then the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, equals the number of geometric branches of `B`, computed from a chosen strict
henselization `Bsh`. -/
theorem geometricBranchNumber_eq_of_smoothAtPrime_closedPoint
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B)) :
    geometricBranchNumber A Ash = geometricBranchNumber B Bsh := sorry

end StrictHenselization

section Henselization

variable {Ah : Type u} {Bh : Type v}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]

-- Proof sketch: repeat the strict-henselization argument with ordinary henselizations. The purely
-- inseparable residue-field extension is used after normalizing the reduced domain quotient of `A`
-- to force the relevant tensor product with the henselization of `B` to stay local.
/-- Lemma 15.107.8 (2): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A` and whose induced residue-field extension is purely inseparable, then the number
of branches of `A`, computed from a chosen henselization `Ah`, equals the number of branches of
`B`, computed from a chosen henselization `Bh`. -/
theorem branchNumber_eq_of_smoothAtPrime_closedPoint_of_purelyInseparable
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B))
    (hκ : IsPurelyInseparable (ResidueField A) (ResidueField B)) :
    branchNumber A Ah = branchNumber B Bh := sorry

end Henselization

end
