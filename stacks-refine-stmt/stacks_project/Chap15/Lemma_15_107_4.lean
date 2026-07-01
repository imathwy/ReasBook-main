import Mathlib
import stacks_project.Chap10.Lemma_10_155_2
import stacks_project.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

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
