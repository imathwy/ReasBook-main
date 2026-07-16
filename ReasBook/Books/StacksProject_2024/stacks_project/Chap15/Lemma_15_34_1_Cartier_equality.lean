import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.RingTheory.Extension.Cotangent.Basic
import StacksProject_2024.stacks_project.Chap10.Definition_10_135_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_114_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_135_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_116_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_149_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_134_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_12
import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_11
import StacksProject_2024.stacks_project.Chap15.Lemma_15_33_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v}
variable [hk : Field k] [hK : Field K] [hAlg : Algebra k K]
variable [hfg : Algebra.FiniteType k K]

/- Domain triage:
* primary domain: Kähler differentials and the first homology of the naive cotangent complex for
  finitely generated field extensions;
* sampled owner declarations:
  - `KaehlerDifferential.finite`,
  - `Algebra.H1Cotangent`,
  - the canonical instance `Module.Finite K (H1Cotangent k K)`,
  - `Algebra.trdeg`;
* best owner abstraction: the primitive data are the canonical modules `Ω[K⁄k]` and
  `H1Cotangent k K`; their finite-dimensionality over the field `K` is derived API obtained from
  the upstream `Module.Finite` owners, not separate public owner data for this item. The finite
  presentation bridge belongs only inside a later proof and not in the file-level public context;
* layer triage:
  - `source-facing`: Cartier's equality itself;
  - `core/canonical`: `Ω[K⁄k]` and `H1Cotangent k K`;
  - `bridge/view`: the explicit finite-dimensional and `finrank` consequences over `K`.

This file therefore keeps the source-facing equality directly on the canonical owners and deletes
the redundant helper wrappers that only repackage their finite-dimensional consequences. -/

/-
The finite-type hypothesis is only needed for the global-complete-intersection owner and the final
Cartier equality. Keep the generic helper API free of that extra section variable.
-/
omit hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): a directed family of subalgebras whose supremum
is `⊤` contains every finite subset of the ambient field in one stage. -/
private lemma exists_stage_subalgebra_contains_finset
    {ι : Type*} [Nonempty ι] (S : ι → Subalgebra k K) (hdir : Directed (· ≤ ·) S)
    (hSup : iSup S = ⊤)
    (s : Finset K) :
    ∃ i, (↑s : Set K) ⊆ S i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.choice ‹Nonempty ι›, ?_⟩
      simp
  | @insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      have ha_mem : a ∈ iSup S := by
        simpa [hSup] using (show a ∈ (⊤ : Subalgebra k K) from trivial)
      have ha_mem' : ∃ j, a ∈ S j := by
        change a ∈ ((iSup S : Subalgebra k K) : Set K) at ha_mem
        rw [Subalgebra.coe_iSup_of_directed hdir] at ha_mem
        simpa [Set.mem_iUnion] using ha_mem
      rcases ha_mem' with ⟨j, hj⟩
      rcases hdir i j with ⟨m, him, hjm⟩
      refine ⟨m, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, SetLike.mem_coe] at hx ⊢
      rcases hx with rfl | hx
      · exact hjm hj
      · exact him (hi hx)

include hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): a finite-type field algebra is itself a global
complete intersection, not just a directed colimit of such subalgebras. -/

private lemma global_complete_intersection_of_finiteType_field :
    IsGlobalCompleteIntersection k K := by
  classical
  obtain ⟨ι, S, hdir, hGCI, hSup⟩ :=
    exists_directed_globalCompleteIntersection_subalgebra_family (k := k) (K := K)
  by_cases hne : Nonempty ι
  · let _ : Nonempty ι := hne
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := K)
    rcases exists_stage_subalgebra_contains_finset (k := k) (K := K) S hdir hSup s with
      ⟨i, hi⟩
    -- Once one stage contains a finite algebra generating set of `K`, that stage must already be
    -- the whole field.
    have hle : Algebra.adjoin k (↑s : Set K) ≤ S i := by
      refine Algebra.adjoin_le ?_
      intro x hx
      exact hi hx
    have htop_le : (⊤ : Subalgebra k K) ≤ S i := by
      simpa [hs] using hle
    have htop : S i = ⊤ := top_le_iff.mp htop_le
    exact IsGlobalCompleteIntersection.of_algEquiv (hGCI i) <|
      (Subalgebra.equivOfEq (S i) ⊤ htop).trans (Subalgebra.topEquiv (R := k) (A := K))
  · let _ : IsEmpty ι := not_nonempty_iff.mp hne
    have hbot : iSup S = (⊥ : Subalgebra k K) := by
      simp
    -- In the empty-family corner case, `⊤ = ⊥`, so the algebra map `k → K` is surjective and
    -- `K` already has the empty presentation over `k`.
    have hsurj : Function.Surjective (algebraMap k K) := by
      intro x
      have htopbot : (⊤ : Subalgebra k K) = ⊥ := hSup.symm.trans hbot
      have hx : x ∈ (⊥ : Subalgebra k K) := by
        rw [← htopbot]
        trivial
      change ∃ y : k, algebraMap k K y = x at hx
      exact hx
    let e0 : Fin 0 ≃ PEmpty.{1} :=
      { toFun := Fin.elim0
        invFun := PEmpty.elim
        left_inv := fun i ↦ Fin.elim0 i
        right_inv := fun x : PEmpty.{1} ↦ PEmpty.elim x }
    let P : Algebra.Presentation k K (Fin 0) (Fin 0) :=
      (Algebra.Presentation.ofBijectiveAlgebraMap (R := k) (S := K)
          ⟨(algebraMap k K).injective, hsurj⟩).reindex e0 e0
    refine
      { presentation_or_subsingleton := Or.inr ⟨0, 0, P, ?_⟩ }
    have hPdim : P.dimension = 0 := by
      simp [P, Algebra.Presentation.ofBijectiveAlgebraMap_dimension]
    rw [hPdim]
    exact ringKrullDim_eq_zero_of_field K

omit hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): the conormal module of a finite presentation of a
field is finite-dimensional over that field. -/
private lemma presentationCotangent_finiteDimensional
    {n c : ℕ} (P : Algebra.Presentation k K (Fin n) (Fin c)) :
    FiniteDimensional K P.toExtension.Cotangent := by
  let _ : Module.Finite K P.toExtension.Cotangent := Extension.Cotangent.finite P.fg_ker
  exact (Module.Free.chooseBasis K P.toExtension.Cotangent).finiteDimensional_of_finite

/-- Helper for Lemma 15.34.1 (Cartier equality): the exact cotangent-complex sequences rewrite the
Cartier expression for a presentation `P` as the number of generators minus the conormal
dimension. -/
private lemma presentation_euler_eq_generator_sub_cotangent_finrank
    {n c : ℕ} (P : Algebra.Presentation k K (Fin n) (Fin c))
    [FiniteDimensional K P.toExtension.Cotangent] :
    Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) =
      Int.ofNat n - Int.ofNat (Module.finrank K P.toExtension.Cotangent) := by
  let d := P.toExtension.cotangentComplex
  let _ : FiniteDimensional K P.toExtension.CotangentSpace :=
    P.cotangentSpaceBasis.finiteDimensional_of_finite
  let _ : FiniteDimensional K P.toExtension.H1Cotangent :=
    FiniteDimensional.of_injective P.toExtension.h1Cotangentι
      P.toExtension.h1Cotangentι_injective
  let _ : FiniteDimensional K (H1Cotangent k K) :=
    FiniteDimensional.of_injective P.equivH1Cotangent.symm.toLinearMap
      P.equivH1Cotangent.symm.injective
  have hCotangentSpace : Module.finrank K P.toExtension.CotangentSpace = n := by
    simpa using Module.finrank_eq_card_basis P.cotangentSpaceBasis
  have hH1 :
      Module.finrank K (LinearMap.ker d) = Module.finrank K (H1Cotangent k K) := by
    simpa [d] using LinearEquiv.finrank_eq P.equivH1Cotangent
  -- First compute the Kähler-differential term from the exact sequence
  -- `P.Cotangent → P.CotangentSpace → Ω[K⁄k]`.
  have hOmega :
      Module.finrank K Ω[K⁄k] + Module.finrank K (LinearMap.range d) = n := by
    have hExact :
        LinearMap.ker P.toExtension.toKaehler = LinearMap.range d :=
      LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler
    have hRange :
        LinearMap.range P.toExtension.toKaehler = ⊤ :=
      LinearMap.range_eq_top.2 P.toExtension.toKaehler_surjective
    have hRank := LinearMap.finrank_range_add_finrank_ker P.toExtension.toKaehler
    rw [hRange, finrank_top, hExact, hCotangentSpace] at hRank
    simpa [d] using hRank
  -- Then compute the `H¹` term from the exact sequence
  -- `H¹(L_{K/k}) → P.Cotangent → P.CotangentSpace`.
  have hCotangent :
      Module.finrank K (LinearMap.range d) + Module.finrank K (H1Cotangent k K) =
        Module.finrank K P.toExtension.Cotangent := by
    have hRank := LinearMap.finrank_range_add_finrank_ker d
    rw [hH1] at hRank
    simpa using hRank
  have hOmegaNat :
      Module.finrank K Ω[K⁄k] = n - Module.finrank K (LinearMap.range d) := by
    omega
  have hH1Nat :
      Module.finrank K (H1Cotangent k K) =
        Module.finrank K P.toExtension.Cotangent - Module.finrank K (LinearMap.range d) := by
    omega
  have hrange_le_n : Module.finrank K (LinearMap.range d) ≤ n := by
    omega
  have hrange_le_cot :
      Module.finrank K (LinearMap.range d) ≤ Module.finrank K P.toExtension.Cotangent := by
    omega
  rw [hOmegaNat, hH1Nat]
  rw [Int.ofNat_sub hrange_le_n, Int.ofNat_sub hrange_le_cot]
  ring_nf
  rfl

/-- Helper for Lemma 15.34.1 (Cartier equality): the generic point of the spectrum of a field is
the prime corresponding to the zero ideal. -/
private def primeSpectrum_bot_of_field (R : Type*) [CommRing R] [Field R] : PrimeSpectrum R :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- Helper for Lemma 15.34.1 (Cartier equality): the residue field at a prime of the base field is
canonically the base field itself. -/
private noncomputable def field_prime_residueField_algEquiv_self (p : PrimeSpectrum k) :
    p.asIdeal.ResidueField ≃ₐ[k] k := by
  let φ : k →ₐ[k] p.asIdeal.ResidueField := IsScalarTower.toAlgHom k k p.asIdeal.ResidueField
  have hκ : Function.Bijective φ := by
    constructor
    · exact RingHom.injective _
    · simpa using (Ideal.algebraMap_residueField_surjective p.asIdeal)
  exact (AlgEquiv.ofBijective φ hκ).symm

/-- Helper for Lemma 15.34.1 (Cartier equality): every fiber of `K / k` over a prime of the base
field is canonically identified with `K`. -/
private noncomputable def field_prime_fiber_algEquiv_self (p : PrimeSpectrum k) :
    p.asIdeal.Fiber K ≃ₐ[k] K :=
  (Algebra.TensorProduct.congr
      (field_prime_residueField_algEquiv_self (k := k) p)
      (AlgEquiv.refl : K ≃ₐ[k] K)).trans
    (Algebra.TensorProduct.lid k K)

/-- Helper for Lemma 15.34.1 (Cartier equality): the fibers of `K / k` over primes of the base
field have the same Krull dimension as `K` itself. -/
private lemma ringKrullDim_field_fiber_eq (p : PrimeSpectrum k) :
    ringKrullDim (p.asIdeal.Fiber K) = ringKrullDim K := by
  -- The field-fiber identification keeps the source route explicit before passing to any
  -- complete-intersection owner.
  simpa using
    ringKrullDim_eq_of_ringEquiv
      (field_prime_fiber_algEquiv_self (k := k) (K := K) p).toRingEquiv

/-- Helper for Lemma 15.34.1 (Cartier equality): a presentation of the field target whose
dimension agrees with `ringKrullDim K` is automatically a relative global complete intersection
presentation over the base field. -/
private lemma presentation_isRelativeGlobalCompleteIntersection_of_field
    {n c : ℕ} (P : Algebra.Presentation k K (Fin n) (Fin c))
    (hP : ringKrullDim K = P.dimension) :
    P.IsRelativeGlobalCompleteIntersection := by
  intro p hp
  -- Over a field base, every nonempty fiber is canonically another copy of `K`.
  calc
    ringKrullDim (p.asIdeal.Fiber K) = ringKrullDim K :=
      ringKrullDim_field_fiber_eq (k := k) (K := K) p
    _ = P.dimension := hP

include hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): the global complete-intersection owner can be
unpacked to an explicit quotient presentation of `K`. -/

private lemma exists_explicit_quotient_presentation_of_field :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
      (_e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] K),
      ringKrullDim K = n - c := by
  let _ : IsGlobalCompleteIntersection k K :=
    global_complete_intersection_of_finiteType_field (k := k) (K := K)
  rcases (show IsGlobalCompleteIntersection k K from inferInstance).quotientPresentation_or_subsingleton with
    hsub | ⟨n, c, f, ⟨e⟩, hdim⟩
  · exfalso
    exact one_ne_zero (Subsingleton.elim (1 : K) 0)
  · exact ⟨n, c, f, e, hdim⟩

omit hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): transport the naive quotient presentation along
the chosen algebra equivalence to obtain a relative global complete-intersection presentation of
`K`. -/
private lemma quotient_field_presentation_isRelativeGlobalCompleteIntersection
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] K)
    (hdim : ringKrullDim K = n - c) :
    let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
    let P : Algebra.Presentation k K (Fin n) (Fin c) :=
      (Algebra.Presentation.naive : Algebra.Presentation k T (Fin n) (Fin c)).ofAlgEquiv e
    P.IsRelativeGlobalCompleteIntersection := by
  let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  let P : Algebra.Presentation k K (Fin n) (Fin c) :=
    (Algebra.Presentation.naive : Algebra.Presentation k T (Fin n) (Fin c)).ofAlgEquiv e
  -- The transported presentation still computes `ringKrullDim K`, so the field-base criterion
  -- upgrades it to the relative complete-intersection owner.
  have hP : ringKrullDim K = P.dimension := by
    let P0 : Algebra.Presentation k T (Fin n) (Fin c) := Algebra.Presentation.naive
    have hP0 : ringKrullDim K = P0.dimension := by
      simpa [P0, Algebra.Presentation.dimension] using hdim
    calc
      ringKrullDim K = P0.dimension := hP0
      _ = P.dimension := by
        simpa [P0, P] using (P0.dimension_ofAlgEquiv e)
  exact presentation_isRelativeGlobalCompleteIntersection_of_field (k := k) (K := K) P hP

/-- Helper for Lemma 15.34.1 (Cartier equality): the naive quotient presentation itself is a
relative global complete intersection once the transported presentation over `K` is known to be
one. -/
private lemma quotient_field_naive_presentation_isRelativeGlobalCompleteIntersection
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] K)
    (hdim : ringKrullDim K = n - c) :
    let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
    let P0 : Algebra.Presentation k T (Fin n) (Fin c) := Algebra.Presentation.naive
    P0.IsRelativeGlobalCompleteIntersection := by
  let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  let P0 : Algebra.Presentation k T (Fin n) (Fin c) := Algebra.Presentation.naive
  let P : Algebra.Presentation k K (Fin n) (Fin c) := P0.ofAlgEquiv e
  have hrel :
      P.IsRelativeGlobalCompleteIntersection :=
    quotient_field_presentation_isRelativeGlobalCompleteIntersection
      (k := k) (K := K) f e hdim
  -- Proof comment: reuse the already proved owner on `P0.ofAlgEquiv e` and transport it back
  -- along `e.symm`; this keeps the source route on the same explicit quotient presentation.
  simpa [P] using
    (RingHom.Syntomic.presentation_relativeGlobalCompleteIntersection_ofAlgEquiv
      (R := k) (P := P) hrel e.symm)

/-- Helper for Lemma 15.34.1 (Cartier equality): in the explicit quotient model, the conormal term
has rank exactly equal to the number of displayed relations. -/
private lemma quotient_field_presentation_cotangent_finrank
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] K)
    (hdim : ringKrullDim K = n - c) :
    let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
    let P : Algebra.Presentation k K (Fin n) (Fin c) :=
      (Algebra.Presentation.naive : Algebra.Presentation k T (Fin n) (Fin c)).ofAlgEquiv e
    Module.finrank K P.toExtension.Cotangent = c := by
  sorry

omit k K hk hK hAlg hfg

/-- Helper for Lemma 15.34.1 (Cartier equality): in a Noetherian local ring, the length of a
regular sequence is bounded by the ring's Krull dimension. -/
private lemma regularSequence_length_le_ringKrullDim_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {rs : List A} (hreg : RingTheory.Sequence.IsRegular A rs) :
    (((rs.length : ℕ∞) : WithBot ℕ∞)) ≤ ringKrullDim A := by
  have hdim :
      ringKrullDim (A ⧸ Ideal.ofList rs) + (((rs.length : ℕ∞) : WithBot ℕ∞)) =
        ringKrullDim A := by
    simpa using ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
      (R := A) (rs := rs) hreg
  have hquot_ne_top : Ideal.ofList rs ≠ ⊤ := by
    simpa [ne_comm] using hreg.top_ne_smul
  let _ : Nontrivial (A ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.2 hquot_ne_top
  have hle :
      (((rs.length : ℕ∞) : WithBot ℕ∞)) ≤
        ringKrullDim (A ⧸ Ideal.ofList rs) + (((rs.length : ℕ∞) : WithBot ℕ∞)) := by
    -- Proof comment: the quotient term contributes a nonnegative summand, so discarding it can
    -- only decrease the Krull-dimension side.
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  exact hdim ▸ hle

include k hk

/-- Helper for Lemma 15.34.1 (Cartier equality): localizing a polynomial ring over a field at any
prime has Krull dimension at most the number of variables. -/
private lemma ringKrullDim_localizationAtPrime_mvPolynomial_le_num_vars
    {n : ℕ} (q : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤ n := by
  have hmv :
      ringKrullDim (MvPolynomial (Fin n) k) =
        ringKrullDim k + Nat.card (Fin n) :=
    MvPolynomial.ringKrullDim_of_isNoetherianRing
  -- Proof comment: identify the local dimension with the height of the contracted prime and then
  -- compare that height to the ambient polynomial-ring dimension.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
    (Localization.AtPrime q.asIdeal)]
  refine le_trans (Ideal.height_le_ringKrullDim_of_ne_top q.isPrime.ne_top) ?_
  simpa [hmv]

include K hK hAlg

/-- Helper for Lemma 15.34.1 (Cartier equality): the explicit quotient model should satisfy
`c ≤ n`, so the displayed dimension `n - c` matches the corresponding integer difference. -/
private lemma quotient_field_presentation_relations_le_generators
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] K)
    (hdim : ringKrullDim K = n - c) :
    c ≤ n := by
  let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  have hprime : (⊥ : Ideal T).IsPrime := by
    simpa [RingHom.injective_iff_ker_eq_bot e.toRingHom |>.mp e.injective] using
      (RingHom.ker_isPrime e.toRingHom)
  let P0 : Algebra.Presentation k T (Fin n) (Fin c) := Algebra.Presentation.naive
  let q : PrimeSpectrum T := ⟨⊥, hprime⟩
  let q' := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q
  let A := Localization.AtPrime q'.asIdeal
  have hrel0 :
      P0.IsRelativeGlobalCompleteIntersection :=
    quotient_field_naive_presentation_isRelativeGlobalCompleteIntersection
      (k := k) (K := K) f e hdim
  have hreg :
      RingTheory.Sequence.IsRegular A
        ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) k) A)) := by
    -- Route correction: stay on the explicit quotient model and localize at its generic prime,
    -- rather than transporting to a separate field-point presentation.
    simpa [P0, q, q', A] using
      (Algebra.relativeGCI_localized_relations_isRegular (f := f) hrel0 q)
  have hlen :
      (((c : ℕ∞) : WithBot ℕ∞)) ≤ ringKrullDim A := by
    -- Route correction: work entirely on the explicit quotient model at the generic prime.
    -- The localized relations are regular, so their length is bounded by the local dimension.
    simpa [A, List.length_ofFn, List.length_map] using
      regularSequence_length_le_ringKrullDim_local
        (A := A) (rs := (List.ofFn f).map (algebraMap (MvPolynomial (Fin n) k) A)) hreg
  have hdimA : ringKrullDim A ≤ n := by
    -- Proof comment: the generic-point localization sits over a prime of the polynomial ring, so
    -- its Krull dimension is bounded by the number of variables.
    exact ringKrullDim_localizationAtPrime_mvPolynomial_le_num_vars (k := k) q'
  have hcn :
      (((c : ℕ∞) : WithBot ℕ∞)) ≤ n := by
    exact le_trans hlen hdimA
  exact ENat.coe_le_coe.mp (WithBot.coe_le_coe.mp hcn)

-- Proof sketch: pick a global complete intersection presentation
-- `k[x₁, ..., xₙ] / (f₁, ..., f_c)` of `K`, identify `Ω[K⁄k]` and `H¹(L_{K/k})` with the cokernel
-- and kernel of the resulting two-term complex `K^c → K^n`, and compute the Euler
-- characteristic `n - c` as the transcendence degree of `K / k`.
include hfg

/-- Lemma 15.34.1 (Cartier equality): for a finitely generated field extension `K / k`, the
transcendence degree of `K` over `k` equals, in `ℤ`, the difference between the dimensions of
`Ω[K⁄k]` and `H¹(L_{K/k})`. -/
theorem cartier_equality :
    Int.ofNat (Cardinal.toNat (trdeg k K)) =
      Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) := by
  obtain ⟨n, c, f, e, hdim⟩ :=
    exists_explicit_quotient_presentation_of_field (k := k) (K := K)
  let T := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)
  let _ : Field T := e.toRingEquiv.field
  let P : Algebra.Presentation k K (Fin n) (Fin c) :=
    (Algebra.Presentation.naive : Algebra.Presentation k T (Fin n) (Fin c)).ofAlgEquiv e
  let _ : FiniteDimensional K P.toExtension.Cotangent :=
    presentationCotangent_finiteDimensional (k := k) (K := K) P
  have hCotangent :
      Module.finrank K P.toExtension.Cotangent = c :=
    quotient_field_presentation_cotangent_finrank (k := k) (K := K) f e hdim
  have hEuler :
      Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) =
        Int.ofNat n - Int.ofNat c := by
    -- The quotient presentation computes the cotangent Euler characteristic by `n - c`.
    calc
      Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) =
          Int.ofNat n - Int.ofNat (Module.finrank K P.toExtension.Cotangent) :=
        presentation_euler_eq_generator_sub_cotangent_finrank (k := k) (K := K) P
      _ = Int.ofNat n - Int.ofNat c := by rw [hCotangent]
  have htrdegNat : Cardinal.toNat (trdeg k K) = n - c := by
    -- The fraction field of `K` is again `K`, so the transcendence-degree owner specializes to
    -- the same integer computed by the quotient-model dimension `n - c`.
    let e : FractionRing K ≃ₐ[k] K := (FractionRing.algEquiv K K).restrictScalars k
    have hfrac :
        ringKrullDim K = Cardinal.toNat (trdeg k (FractionRing K)) :=
      ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field (k := k) (S := K)
    have htrdegFrac :
        Cardinal.toNat (trdeg k (FractionRing K)) = Cardinal.toNat (trdeg k K) := by
      exact congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e)
    have hwith :
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) = Cardinal.toNat (trdeg k K) := by
      calc
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) = ringKrullDim K := hdim.symm
        _ = Cardinal.toNat (trdeg k (FractionRing K)) := hfrac
        _ = Cardinal.toNat (trdeg k K) := by
          simpa using congrArg (fun m : ℕ ↦ ((m : ℕ∞) : WithBot ℕ∞)) htrdegFrac
    exact WithTop.coe_injective (WithBot.coe_injective hwith.symm)
  have hcn : c ≤ n :=
    quotient_field_presentation_relations_le_generators (k := k) (K := K) f e hdim
  have htrdeg :
      Int.ofNat (Cardinal.toNat (trdeg k K)) = Int.ofNat n - Int.ofNat c := by
    rw [htrdegNat]
    exact Int.ofNat_sub hcn
  calc
    Int.ofNat (Cardinal.toNat (trdeg k K)) = Int.ofNat n - Int.ofNat c := htrdeg
    _ = Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) := hEuler.symm

end

end Algebra
