import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_116_6
import stacks_proof.stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

/-- Helper for Chap10 Lemma 10 116 7: tensoring a field extension on the right is faithfully
flat over the original algebra. -/
private lemma tensorProductRightFaithfullyFlat
    {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]
    {S : Type w} [CommRing S] [Algebra k S] :
    Module.FaithfullyFlat S (K ⊗[k] S) := by
  -- Faithful flatness is standard for `S ⊗[k] K`; the tensor-product commutativity equivalence
  -- transports it to the right-inclusion spelling `K ⊗[k] S`.
  exact Module.FaithfullyFlat.of_linearEquiv S (S ⊗[k] K)
    (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 116 7: finite local Krull dimensions in Noetherian rings can be
cancelled from the left in `WithBot ℕ∞`. -/
private lemma ringKrullDimLocalizationAtPrime_add_left_cancel
    {A : Type u} [CommRing A] [IsNoetherianRing A] (x : PrimeSpectrum A) {a b : WithBot ℕ∞}
    (h : ringKrullDim (Localization.AtPrime x.asIdeal) + a =
      ringKrullDim (Localization.AtPrime x.asIdeal) + b) : a = b := by
  -- Rewrite the local-ring dimension as the finite height of the prime, then use ordered
  -- cancellation for addition by a non-bottom, non-top element of `WithBot ℕ∞`.
  have hdim_bot : ringKrullDim (Localization.AtPrime x.asIdeal) ≠ (⊥ : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
      (Localization.AtPrime x.asIdeal)]
    exact WithBot.coe_ne_bot
  have hdim_top : ringKrullDim (Localization.AtPrime x.asIdeal) ≠ (⊤ : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
      (Localization.AtPrime x.asIdeal)]
    intro htop
    exact (ne_of_lt (Ideal.height_lt_top Ideal.IsPrime.ne_top')) (WithBot.coe_eq_top.mp htop)
  have h' : a + ringKrullDim (Localization.AtPrime x.asIdeal) =
      b + ringKrullDim (Localization.AtPrime x.asIdeal) := by
    simpa [add_comm] using h
  apply le_antisymm
  · exact ((WithBot.add_le_add_iff_right' hdim_bot hdim_top).mp (le_of_eq h'))
  · exact ((WithBot.add_le_add_iff_right' hdim_bot hdim_top).mp (ge_of_eq h'))

/-- Helper for Chap10 Lemma 10 116 7: a height-zero statement transported through
`preimageEquivFiber` rewrites to the canonical `fiberPrimeAt`. -/
private lemma fiberPrimeAt_primeHeight_zero_of_comap_eq
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    {p : PrimeSpectrum R} {q : PrimeSpectrum T}
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p)
    (hzero : (PrimeSpectrum.preimageEquivFiber R T p ⟨q, hq⟩).asIdeal.primeHeight = 0) :
    (fiberPrimeAt R T q).asIdeal.primeHeight = 0 := by
  -- Once the contraction equality is reduced to reflexivity, `fiberPrimeAt` is exactly this
  -- `preimageEquivFiber` image.
  cases hq
  simpa [fiberPrimeAt] using hzero

/-- Helper for Chap10 Lemma 10 116 7: under a faithfully flat map, every prime has a prime above
it whose fiber prime has height zero. -/
private lemma exists_prime_over_with_fiberPrimeAt_primeHeight_zero
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum T,
      PrimeSpectrum.comap (algebraMap R T) q = p ∧
        (fiberPrimeAt R T q).asIdeal.primeHeight = 0 := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R T)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q0, hq0⟩ := hsurj p
  have hnontrivial : Nontrivial (p.asIdeal.Fiber T) := by
    -- A single prime above `p` witnesses nontriviality of the fiber ring over `p`.
    exact
      (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := R) (S := T) p).2
        ⟨q0, hq0⟩
  letI : Nontrivial (p.asIdeal.Fiber T) := hnontrivial
  obtain ⟨rIdeal, hrIdeal⟩ :=
    Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal (p.asIdeal.Fiber T))) bot_ne_top
  letI : rIdeal.IsPrime := Ideal.minimalPrimes_isPrime hrIdeal
  let r : PrimeSpectrum (p.asIdeal.Fiber T) := ⟨rIdeal, inferInstance⟩
  let qover := (PrimeSpectrum.preimageEquivFiber R T p).symm r
  have hr_min : rIdeal ∈ minimalPrimes (p.asIdeal.Fiber T) := by
    simpa using hrIdeal
  have hr_zero : rIdeal.primeHeight = 0 := by
    -- Minimal primes are exactly the height-zero primes.
    simpa using (Ideal.primeHeight_eq_zero_iff (I := rIdeal)).2 hr_min
  have hEqAsIdeal :
      (PrimeSpectrum.preimageEquivFiber R T p qover).asIdeal = r.asIdeal := by
    exact congrArg PrimeSpectrum.asIdeal
      ((PrimeSpectrum.preimageEquivFiber R T p).apply_symm_apply r)
  have hEqIdeal :
      (PrimeSpectrum.preimageEquivFiber R T p qover).asIdeal = rIdeal := by
    simpa [r] using hEqAsIdeal
  have hchosen :
      (PrimeSpectrum.preimageEquivFiber R T p qover).asIdeal.primeHeight = 0 := by
    simpa [hEqIdeal] using hr_zero
  refine ⟨qover.1, qover.2, ?_⟩
  -- Move the minimal-prime height computation back to the public `fiberPrimeAt` spelling.
  exact fiberPrimeAt_primeHeight_zero_of_comap_eq (R := R) (T := T) qover.2 hchosen

/-- Helper for Chap10 Lemma 10 116 7: a height-zero fiber prime has zero relative dimension. -/
private lemma relativeDimensionAt_eq_zero_of_fiberPrimeAt_primeHeight_zero
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T] {q : PrimeSpectrum T}
    (hqf : (fiberPrimeAt R T q).asIdeal.primeHeight = 0) :
    relativeDimensionAt R T q = 0 := by
  -- The relative dimension is the Krull dimension of the localization of the fiber at this prime;
  -- the AtPrime height formula evaluates that dimension as the prime height.
  calc
    relativeDimensionAt R T q = ringKrullDim (fiberLocalRingAt R T q) := rfl
    _ = ((((fiberPrimeAt R T q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
      calc
        ringKrullDim (fiberLocalRingAt R T q) =
            ↑((fiberPrimeAt R T q).asIdeal.height) := by
              simpa [fiberLocalRingAt] using
                (IsLocalization.AtPrime.ringKrullDim_eq_height
                  (fiberPrimeAt R T q).asIdeal (fiberLocalRingAt R T q))
        _ = ((((fiberPrimeAt R T q).asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞)) := by
              rw [Ideal.height_eq_primeHeight]
    _ = 0 := by simpa [hqf]

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-
Domain-style sampling:
- primary domain: relative fiber dimension for finite type algebras over a field, under tensor base
  change along a field extension;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `fiberLocalRingAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`;
- best owner abstraction: the source-facing fiber-dimension quantity is already owned in this
  chapter by `relativeDimensionAt`; the ring `fiberLocalRingAt` is primitive supporting data, not
  the public dimension owner;
- primitive data: the points `x : PrimeSpectrum S`, `xK : PrimeSpectrum S_K`, and the contraction
  witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: the additive identities comparing `relativeDimensionAt S S_K xK` with local-ring
  dimensions and residue-field transcendence degrees.

Source/core/bridge triage:
* `source-facing`: the fiber-dimension formulas and zero-dimensional fiber point over `x`;
* `core/canonical`: `relativeDimensionAt`, together with the supporting owners
  `Localization.AtPrime`, `fiberLocalRingAt`, and the Chapter 10 local-dimension formulas;
* `bridge/view`: the tensor base-change map `iSK` and the lies-over equation
  `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: localize the flat base-change map `S → S_K` at `x` and `xK`, then apply the
-- flat-local dimension formula from Lemma `10.112.7` to identify the dimension of the localized
-- special fiber with the difference between the dimensions of `(S_K)_{xK}` and `S_x`. Since the
-- project records Krull dimensions in `WithBot ℕ∞`, this is stated in the equivalent additive
-- form.
/-
Chap10 Lemma 10 116 7: the three public declarations below record the fiber-dimension formula,
the equivalent transcendence-degree formula, and the zero-dimensional point in the base-change
fiber.
-/
-- recall relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension / relativeDimensionAt_add_trdeg_residueField_eq_of_tensorProduct_fieldExtension / exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero

/-
/-- Validator bridge for Chap10 Lemma 10 116 7: records the three public declarations that
together form the planned main result for this item. -/
theorem relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension / relativeDimensionAt_add_trdeg_residueField_eq_of_tensorProduct_fieldExtension / exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero
-/

/-- First part of Chap10 Lemma 10 116 7: for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the dimension of `S_x`, equals the dimension of `(K ⊗[k] S)_{xK}`. -/
@[stacks 0CWE]
lemma relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + ringKrullDim (Localization.AtPrime x.asIdeal) =
      ringKrullDim (Localization.AtPrime xK.asIdeal) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : Algebra.FiniteType K S_K := inferInstance
  letI : IsNoetherianRing S_K := Algebra.FiniteType.isNoetherianRing K S_K
  letI : Module.FaithfullyFlat S S_K :=
    tensorProductRightFaithfullyFlat (k := k) (K := K) (S := S)
  letI : Algebra.HasGoingDown S S_K := inferInstance
  have hdim :=
    ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
      (R := S) (S := S_K) xK
  -- After replacing `x` by the contraction of `xK`, Lemma 10.112.7 gives the same equality
  -- with the summands in the opposite order.
  cases hxK
  simpa [relativeDimensionAt, Ideal.under_def, PrimeSpectrum.comap_asIdeal, add_comm] using
    hdim.symm

-- Proof sketch: combine Lemma `10.116.6`, which identifies the local dimensions of `Spec(S)` and
-- `Spec(S_K)` at corresponding points, with Lemma `10.116.3`, which expresses those local
-- dimensions as `dim S_x + trdeg_k κ(x)` and `dim (S_K)_{xK} + trdeg_K κ(xK)`. Cancelling the
-- local-dimension terms gives the transcendence-degree formula for the fiber dimension, again
-- written in additive form because the dimension values lie in `WithBot ℕ∞`.
/-- Second part of Chap10 Lemma 10 116 7: for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the transcendence degree of `κ(xK)` over `K`, equals the
transcendence degree of `κ(x)` over `k`. -/
@[stacks 0CWE]
lemma relativeDimensionAt_add_trdeg_residueField_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : Algebra.FiniteType K S_K := inferInstance
  have hrel :=
    relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension
      (k := k) (K := K) (S := S) x xK hxK
  have htop := primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    (k := k) (K := K) (S := S) x xK hxK
  have hdown := topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (k := k) (S := S) x
  have hup := topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (k := K) (S := S_K) xK
  have hsum :
      ringKrullDim (Localization.AtPrime x.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) =
        ringKrullDim (Localization.AtPrime xK.asIdeal) +
          Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) := by
    -- The local topological dimensions agree after tensoring, and each side decomposes into
    -- local-ring dimension plus residue-field transcendence degree.
    calc
      ringKrullDim (Localization.AtPrime x.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) =
          topologicalKrullDimAt x := hdown.symm
      _ = topologicalKrullDimAt xK := htop
      _ = ringKrullDim (Localization.AtPrime xK.asIdeal) +
          Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) := hup
  have hcancelInput :
      ringKrullDim (Localization.AtPrime x.asIdeal) +
          (relativeDimensionAt S S_K xK +
            Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField)) =
        ringKrullDim (Localization.AtPrime x.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
    -- Substitute the relative-dimension/local-ring formula into the topological-dimension
    -- comparison, then put both sides in a common cancellable normal form.
    calc
      ringKrullDim (Localization.AtPrime x.asIdeal) +
          (relativeDimensionAt S S_K xK +
            Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField)) =
          (relativeDimensionAt S S_K xK + ringKrullDim (Localization.AtPrime x.asIdeal)) +
            Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) := by
            ac_rfl
      _ = ringKrullDim (Localization.AtPrime xK.asIdeal) +
            Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) := by
            rw [hrel]
      _ = ringKrullDim (Localization.AtPrime x.asIdeal) +
            Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := hsum.symm
  exact ringKrullDimLocalizationAtPrime_add_left_cancel (A := S) x hcancelInput

-- Proof sketch: choose a prime of `S_K` minimal over the extended prime `x.asIdeal • ⊤`; such a
-- point lies over `x`, and the corresponding fiber local ring is zero-dimensional because a
-- minimal prime of the fiber has Krull dimension `0`.
/-- Third part of Chap10 Lemma 10 116 7: for every point `x : Spec(S)`, one can choose a point of
`Spec(K ⊗[k] S)` lying over `x` whose relative dimension is `0`. -/
@[stacks 0CWE]
lemma exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero
    (x : PrimeSpectrum S) :
    ∃ xK : PrimeSpectrum S_K,
      PrimeSpectrum.comap iSK xK = x ∧ relativeDimensionAt S S_K xK = 0 := by
  -- The source statement keeps `S` finite type over `k`, although this existence step only uses
  -- faithful flatness of the tensor base-change map.
  have _ : Algebra.FiniteType k S := inferInstance
  letI : Module.FaithfullyFlat S S_K :=
    tensorProductRightFaithfullyFlat (k := k) (K := K) (S := S)
  obtain ⟨xK, hxK, hheight⟩ :=
    exists_prime_over_with_fiberPrimeAt_primeHeight_zero (R := S) (T := S_K) x
  refine ⟨xK, ?_, ?_⟩
  · -- The algebra map for the right tensor-product algebra is the map denoted `iSK`.
    simpa using hxK
  · -- The chosen fiber prime is minimal, so its fiber-local Krull dimension is zero.
    exact relativeDimensionAt_eq_zero_of_fiberPrimeAt_primeHeight_zero
      (R := S) (T := S_K) hheight

end
