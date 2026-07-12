import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import StacksProject_2024.Chap10.Lemma_10_25_2
import StacksProject_2024.Chap15.Lemma_15_105_16
import StacksProject_2024.Chap15.Lemma_15_105_5
import StacksProject_2024.Chap15.Lemma_15_105_6
import StacksProject_2024.Chap15.Lemma_15_105_7
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped TensorProduct

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.105.8: every minimal prime carries its canonical prime-ideal instance. -/
local instance minimalPrimes_isPrime_instance (p : minimalPrimes A) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/- Domain-style sampling:
- primary domain: commutative algebra of weakly étale ring maps, absolute flatness, and
  reducedness ascent along flat maps with reduced fibers;
- sampled owner declarations:
  `IsAbsolutelyFlatRing`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isReduced_of_flat_of_fiber`,
  `Ideal.Fiber`,
  `isReduced_of_isAbsolutelyFlatRing`;
- best owner abstraction: the ambient map property is the chapter owner
  `Algebra.IsWeaklyEtale`, while absolute flatness and reducedness remain owner predicates on the
  source and target rings;
- primitive vs. derived: the primitive data are the owner classes `IsAbsolutelyFlatRing A`,
  `IsReduced A`, and `Algebra.IsWeaklyEtale A B`; the two transfer theorems below are derived API;
- source/core/bridge triage:
  `source-facing`: the two Stacks transfer lemmas below;
  `core/canonical`: `IsAbsolutelyFlatRing`, `IsReduced`, `Algebra.IsWeaklyEtale`,
    `hasWeakDimensionLE_of_isWeaklyEtale`, `Ideal.Fiber`, `isReduced_of_flat_of_fiber`, and
    `isReduced_of_isAbsolutelyFlatRing`;
  `bridge/view`: the zero-weak-dimension TFAE and weakly étale base change to residue-field
    fibers, with part `(1)` upgrading those field fibers to absolutely flat rings and hence
    reduced rings.

This file should therefore expose the source-facing consequences directly in terms of the explicit
owner input `hAB : Algebra.IsWeaklyEtale A B`, reusing the chapter ascent owners instead of
introducing parallel local reducedness or absolute-flatness wrappers. For reducedness, the
source-facing weakly étale fiber theorem below is the bridge into the general ascent owner
`isReduced_of_flat_of_fiber`.
-/

/-- Helper for Lemma 15.105.8: a weakly étale algebra over a field is absolutely flat because
every singleton-generated subalgebra is étale, hence a finite product of fields. -/
lemma isAbsolutelyFlatRing_of_isWeaklyEtale_over_field_local
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.IsWeaklyEtale K S] :
    IsAbsolutelyFlatRing S := by
  refine ⟨fun x ↦ ?_⟩
  let A : Subalgebra K S := Algebra.adjoin K ({x} : Set S)
  have hAfg : A.FG := by
    -- The singleton-generated subalgebra is finite type, hence finitely generated.
    rw [Subalgebra.fg_iff_finiteType A]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  have hAet : Algebra.Etale K A := etale_of_fg_subalgebra_of_isWeaklyEtale A hAfg
  obtain ⟨ι, _hι, T, hField, hAlg, e, _hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp hAet
  let y : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  letI : ∀ i, Field (T i) := hField
  letI : ∀ i, Algebra K (T i) := hAlg
  letI : ∀ i, IsAbsolutelyFlatRing (T i) := fun i ↦ inferInstance
  letI : IsAbsolutelyFlatRing (∀ i, T i) := inferInstance
  obtain ⟨z, hz⟩ := IsAbsolutelyFlatRing.exists_factor (A := ∀ i, T i) (e y)
  refine ⟨((e.symm z : A) : S), ?_⟩
  -- Transport the product-side factorization back through the algebra equivalence.
  have hy : y = y ^ 2 * e.symm z := by
    simpa using congrArg e.symm hz
  exact congrArg (fun t : A ↦ (t : S)) hy

/-- Helper for Lemma 15.105.8: every prime localization of a weakly étale algebra over an
absolutely flat base ring is a field. -/
lemma isField_atPrime_of_isAbsolutelyFlatRing_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsAbsolutelyFlatRing A] (q : PrimeSpectrum B) :
    IsField (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum A := ⟨q.asIdeal.under A, Ideal.IsPrime.under A q.asIdeal⟩
  let Ap := Localization.AtPrime p.asIdeal
  let S := Ap ⊗[A] B
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : Field Ap := (isField_atPrime_of_isAbsolutelyFlatRing (R := A) p).toField
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsWeaklyEtale Ap S := hAB.baseChange
  letI : IsAbsolutelyFlatRing S :=
    isAbsolutelyFlatRing_of_isWeaklyEtale_over_field_local (K := Ap) (S := S)
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl
  letI : IsLocalization M S := by
    dsimp [S, M, Ap]
    infer_instance
  have hdisj : Disjoint (M : Set B) (q.asIdeal : Set B) := by
    rw [Set.disjoint_left]
    intro x hxM hxq
    rcases (show ∃ a : p.asIdeal.primeCompl, algebraMap A B a = x by
        simpa [M, Algebra.algebraMapSubmonoid] using hxM) with ⟨a, rfl⟩
    exact a.2 (show a.1 ∈ p.asIdeal from hxq)
  let qS : Ideal S := q.asIdeal.map (algebraMap B S)
  have hqS_prime : qS.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint M S q.asIdeal q.isPrime hdisj
  let q' : PrimeSpectrum S := ⟨qS, hqS_prime⟩
  have hcomap : Ideal.comap (algebraMap B S) q'.asIdeal = q.asIdeal := by
    simpa [q', qS] using
      (IsLocalization.comap_map_of_isPrime_disjoint M S q.isPrime hdisj)
  let eS : Localization M ≃ₐ[B] S := IsLocalization.algEquiv M (Localization M) S
  let qLoc : PrimeSpectrum (Localization M) := PrimeSpectrum.comap eS.toRingHom q'
  have hcomapLoc : Ideal.comap (algebraMap B (Localization M)) qLoc.asIdeal = q.asIdeal := by
    have hcomp :
        eS.toRingHom.comp (algebraMap B (Localization M)) = algebraMap B S := by
      ext x
      simp [eS.commutes]
    rw [show qLoc.asIdeal = Ideal.comap eS.toRingHom q'.asIdeal by rfl]
    change Ideal.comap ((eS.toRingHom.comp (algebraMap B (Localization M)))) q'.asIdeal = q.asIdeal
    simpa [hcomp] using hcomap
  let e0 :
      Localization.AtPrime q.asIdeal ≃ₐ[B] Localization.AtPrime qLoc.asIdeal := by
    let e0' := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M qLoc.asIdeal
    rw [hcomapLoc] at e0'
    exact e0'
  have hPrimeCompl :
      (Ideal.comap eS.toRingHom q'.asIdeal).primeCompl.map eS.toRingHom =
        q'.asIdeal.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx hy
    · intro hy
      refine ⟨eS.symm y, ?_, by simp⟩
      intro hx
      exact hy (by simpa using hx)
  letI :
      IsLocalization (Ideal.comap eS.toRingHom q'.asIdeal).primeCompl
        (Localization.AtPrime qLoc.asIdeal) := by
    simpa [qLoc] using
      (inferInstance : IsLocalization qLoc.asIdeal.primeCompl (Localization.AtPrime qLoc.asIdeal))
  let e1 :
      Localization.AtPrime qLoc.asIdeal ≃+* Localization.AtPrime q'.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime qLoc.asIdeal)
      (Localization.AtPrime q'.asIdeal)
      eS.toRingEquiv hPrimeCompl
  have hfield' : IsField (Localization.AtPrime q'.asIdeal) :=
    isField_atPrime_of_isAbsolutelyFlatRing (R := S) q'
  letI : Field (Localization.AtPrime q'.asIdeal) := IsField.toField hfield'
  exact (e0.toRingEquiv.trans e1).toMulEquiv.isField (Field.toIsField _)

-- Proof sketch: localize at an arbitrary prime `q` of `B`, base change the weakly étale map to
-- the field `A_(q ∩ A)`, and use the field case to see that the localized base change is
-- absolutely flat. The resulting localization of `B` is therefore a field, and Lemma `15.105.5`
-- turns the field-localization criterion into absolute flatness of `B`.
/-- Lemma 15.105.8 (1): if `A` is absolutely flat and `A → B` is weakly étale, then `B` is
absolutely flat. -/
@[stacks 092I]
theorem isAbsolutelyFlatRing_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsAbsolutelyFlatRing A] :
    IsAbsolutelyFlatRing B := by
  -- Lemma `15.105.5` reduces absolute flatness to the field-localization criterion.
  exact
    ((weakDimensionLEZero_tfae (A := B)).out 3 1).mp fun q ↦
      isField_atPrime_of_isAbsolutelyFlatRing_of_isWeaklyEtale hAB q

-- After base change to a residue field, a weakly étale map stays weakly étale. Over a field, part
-- `(1)` makes the fiber absolutely flat, and reducedness is the thin companion from
-- Lemma `15.105.5`.
/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
absolutely flat. -/
theorem isAbsolutelyFlatRing_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsAbsolutelyFlatRing (p.asIdeal.Fiber B) := by
  let hfiber : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) := hAB.baseChange
  exact isAbsolutelyFlatRing_of_isWeaklyEtale hfiber

/-- Every fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` of a weakly étale map `A → B` is
reduced. -/
theorem isReduced_fiber_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber B) := by
  letI : IsAbsolutelyFlatRing (p.asIdeal.Fiber B) :=
    isAbsolutelyFlatRing_fiber_of_isWeaklyEtale hAB p
  exact isReduced_of_isAbsolutelyFlatRing (p.asIdeal.Fiber B)

-- The source proof replaces a reduced ring by the product of the localizations at its minimal
-- primes, and Lemma `15.105.6` packages the resulting product of fields as absolutely flat.
/-- Helper for Lemma 15.105.8: the product of the localizations at the minimal primes of a
reduced ring is absolutely flat. -/
lemma product_minimalPrimeLocalizations_isAbsolutelyFlat [IsReduced A] :
    IsAbsolutelyFlatRing (∀ p : minimalPrimes A, Localization.AtPrime p.1) := by
  -- Each minimal-prime localization is a field by Lemma `10.25.2`.
  letI (p : minimalPrimes A) : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
  letI (p : minimalPrimes A) : Field (Localization.AtPrime p.1) :=
    IsField.toField ((algebraMap_embedding_into_product_of_fields (R := A)).2 p)
  -- Lemma `15.105.6` then upgrades the product ring to an absolutely flat ring.
  simpa using
    isAbsolutelyFlatRing_pi (K := fun p : minimalPrimes A ↦ Localization.AtPrime p.1)

-- After base change to an absolutely flat ring, part `(1)` makes the tensor product absolutely
-- flat, and Lemma `15.105.5` turns that into reducedness.
/-- Helper for Lemma 15.105.8: base changing a weakly étale map along an absolutely flat ring
produces a reduced tensor product. -/
lemma isReduced_baseChange_of_isWeaklyEtale_of_isAbsolutelyFlatRing
    {A' : Type w} [CommRing A'] [Algebra A A']
    (hAB : Algebra.IsWeaklyEtale A B) [IsAbsolutelyFlatRing A'] :
    IsReduced (A' ⊗[A] B) := by
  -- Base change preserves weakly étale morphisms by Lemma `15.105.7`.
  let hbase : Algebra.IsWeaklyEtale A' (A' ⊗[A] B) := hAB.baseChange
  -- Part `(1)` upgrades the absolutely flat source to an absolutely flat target.
  letI : IsAbsolutelyFlatRing (A' ⊗[A] B) := isAbsolutelyFlatRing_of_isWeaklyEtale hbase
  -- Lemma `15.105.5` identifies absolutely flat rings as reduced rings.
  exact isReduced_of_isAbsolutelyFlatRing (A' ⊗[A] B)

/-- Lemma 15.105.8 (2): if `A` is reduced and `A → B` is weakly étale, then `B` is reduced. -/
@[stacks 092I]
theorem isReduced_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) [IsReduced A] :
    IsReduced B := by
  -- Route correction: follow the source proof through the minimal-prime embedding of `A`,
  -- rather than the unrelated Noetherian fiber-ascent route.
  let Aprime := ∀ p : minimalPrimes A, Localization.AtPrime p.1
  -- Lemma `10.25.2` provides the injective map from `A` into the product of its minimal-prime
  -- localizations.
  have hAprime_injective : Function.Injective (algebraMap A Aprime) := by
    simpa [Aprime] using (algebraMap_embedding_into_product_of_fields (R := A)).1
  -- The product of these localizations is absolutely flat because it is a product of fields.
  have hAprime_absFlat : IsAbsolutelyFlatRing Aprime := by
    simpa [Aprime] using product_minimalPrimeLocalizations_isAbsolutelyFlat (A := A)
  letI : IsAbsolutelyFlatRing Aprime := hAprime_absFlat
  -- Base change of the weakly étale map to `Aprime` is therefore reduced by part `(1)`.
  have hbaseReduced : IsReduced (Aprime ⊗[A] B) := by
    exact
      isReduced_baseChange_of_isWeaklyEtale_of_isAbsolutelyFlatRing
        (A := A) (A' := Aprime) (B := B) hAB
  letI : IsReduced (Aprime ⊗[A] B) := hbaseReduced
  letI : Module.Flat A B := hAB.moduleFlat
  -- Flatness of `B` over `A` keeps the base-change map `B → Aprime ⊗[A] B` injective.
  have hbase_injective :
      Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[A] Aprime ⊗[A] B) := by
    exact
      Algebra.TensorProduct.includeRight_injective
        (R := A) (A := Aprime) (B := B) hAprime_injective
  -- Reducedness descends along injective ring maps.
  exact
    isReduced_of_injective
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Aprime ⊗[A] B).toRingHom hbase_injective

end
