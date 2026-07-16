import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_125_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_6
import stacks_proof.stacks_project.Chap10.Lemma_10_125_2
import stacks_proof.stacks_project.Chap10.Lemma_10_125_5

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- 
Domain-style sampling:
- primary domain: local relative fiber dimension on `Spec(S)` and the corresponding bounded
  locus;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `Module.flatOverBaseLocus`,
  `Module.mem_flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the bounded-dimension locus
  `{ q : PrimeSpectrum S | relativeDimensionAt R S q ≤ n }` should be a named owner on
  `PrimeSpectrum S`, while the source-facing theorem remains the equality-at-the-point
  neighborhood statement from the Stacks lemma and the locus-membership version is only companion
  API.

Source/core/bridge triage:
- `source-facing`: the equality-at-the-point neighborhood statement of Lemma `10.125.6`;
- `core/canonical`: `relativeDimensionAt` and the induced bounded-dimension locus owner;
- `bridge/view`: the membership lemma for the named locus and the strengthened
  locus-membership-neighborhood formulation.

Primitive data are only `n` and the prime `q`; the repeated inequality
`relativeDimensionAt R S q ≤ n` is derived API from the locus owner.
-/

/-- The locus in `Spec(S)` where the relative dimension of `S/R` is at most `n`. -/
def relativeDimensionAtLELocus (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (n : ℕ) : Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) }

-- Proof sketch: unfold `relativeDimensionAtLELocus`.
/-- Membership in `relativeDimensionAtLELocus` means that the local fiber dimension is at most
`n`. -/
theorem mem_relativeDimensionAtLELocus (n : ℕ) (q : PrimeSpectrum S) :
    q ∈ relativeDimensionAtLELocus R S n ↔ relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) := by
  -- Unfolding the owner set leaves exactly the displayed inequality.
  rfl

/-- Helper for Chap10 Lemma 10 125 6: a finite upper bound on the relative dimension gives its
value as a natural number below that bound. -/
private lemma exists_nat_eq_relativeDimensionAt_of_le {n : ℕ} {q : PrimeSpectrum S}
    (hq : relativeDimensionAt R S q ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m ≤ n ∧ relativeDimensionAt R S q = (m : WithBot ℕ∞) := by
  -- First rule out the bottom value using nonnegativity of Krull dimension for the fiber local ring.
  have hnonbot : relativeDimensionAt R S q ≠ ⊥ := by
    have h0 : (0 : WithBot ℕ∞) ≤ relativeDimensionAt R S q := by
      simpa [relativeDimensionAt] using
        (ringKrullDim_nonneg_of_nontrivial (R := fiberLocalRingAt R S q))
    intro hbot
    simpa [hbot] using h0
  -- The `WithBot` value is therefore an `ENat`; the finite upper bound rules out `⊤`.
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hnonbot
  have ha_le : a ≤ (n : ℕ∞) := by
    rw [← ha] at hq
    exact WithBot.coe_le_coe.mp hq
  have ha_ne_top : a ≠ ⊤ := by
    intro htop
    have htop_le : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by
      simpa [htop] using ha_le
    exact (ENat.coe_lt_top n).not_ge htop_le
  -- Convert the finite `ENat` witness back to a natural number.
  refine ⟨a.toNat, ENat.toNat_le_of_le_coe ha_le, ?_⟩
  have hcoe : (a.toNat : ℕ∞) = a := ENat.coe_toNat ha_ne_top
  exact ha.symm.trans (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hcoe.symm)

/-- Helper for Chap10 Lemma 10 125 6: the Krull dimension of a prime localization is bounded by
the Krull dimension of the original ring. -/
private lemma ringKrullDim_localizationAtPrime_le_ringKrullDim
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] :
    ringKrullDim (Localization.AtPrime I) ≤ ringKrullDim A := by
  -- Rewrite the localized dimension as the height of the prime and compare with global dimension.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height I (Localization.AtPrime I)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- Helper for Chap10 Lemma 10 125 6: a quasi-finite algebra over the tensor-polynomial
base `K ⊗[R] R[X₁, ..., X_m]` has Krull dimension at most `m`. -/
private lemma ringKrullDim_le_of_quasiFinite_tensorMvPolynomial_algebra
    {K : Type*} [Field K] [Algebra R K] {m : ℕ}
    {A : Type*} [CommRing A] [Algebra K A]
    [Algebra (K ⊗[R] MvPolynomial (Fin m) R) A]
    [IsScalarTower K (K ⊗[R] MvPolynomial (Fin m) R) A]
    [Algebra.FiniteType K A]
    [Algebra.QuasiFinite (K ⊗[R] MvPolynomial (Fin m) R) A] :
    ringKrullDim A ≤ (m : WithBot ℕ∞) := by
  -- Transport the tensor-polynomial base to the ordinary polynomial ring over `K`.
  let B := MvPolynomial (Fin m) R
  let P := MvPolynomial (Fin m) K
  let T := K ⊗[R] B
  let e : T ≃ₐ[K] P := MvPolynomial.algebraTensorAlgEquiv R K
  letI : Algebra T P := e.toRingHom.toAlgebra
  letI : Algebra P A := ((algebraMap T A).comp e.symm.toRingHom).toAlgebra
  have hKP : IsScalarTower K P A := by
    refine IsScalarTower.of_algebraMap_eq fun k ↦ ?_
    change algebraMap K A k = algebraMap T A (e.symm (algebraMap K P k))
    rw [e.symm.commutes]
    exact IsScalarTower.algebraMap_apply K T A k
  letI : IsScalarTower K P A := hKP
  have hTP : IsScalarTower T P A := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap T A x = algebraMap T A (e.symm (e x))
    rw [e.symm_apply_apply]
  letI : IsScalarTower T P A := hTP
  letI : Algebra.QuasiFinite P A := Algebra.QuasiFinite.of_restrictScalars T P A
  -- With the base normalized to `K[X₁, ..., X_m]`, apply the previous dimension bound.
  exact ringKrullDim_le_of_quasiFinite_mvPolynomial_algebra (k := K) (n := m) (S := A)

/-- Helper for Chap10 Lemma 10 125 6: the fiber of a quasi-finite algebra over an
`m`-variable polynomial algebra has Krull dimension at most `m`. -/
private lemma ringKrullDim_fiber_le_of_quasiFinite_mvPolynomial
    {A : Type*} [CommRing A] [Algebra R A] {m : ℕ}
    [Algebra (MvPolynomial (Fin m) R) A]
    [IsScalarTower R (MvPolynomial (Fin m) R) A]
    [Algebra.FiniteType R A] [Algebra.QuasiFinite (MvPolynomial (Fin m) R) A]
    (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber A) ≤ (m : WithBot ℕ∞) := by
  -- Base-change the polynomial presentation to the residue field of `p`.
  let K := p.asIdeal.ResidueField
  letI : Field K := inferInstance
  letI : Algebra R K := inferInstance
  let B := MvPolynomial (Fin m) R
  let T := K ⊗[R] B
  letI : CommRing T := inferInstance
  letI : Algebra K T := inferInstance
  letI : Algebra B T := Algebra.TensorProduct.rightAlgebra
  letI : Module B T := Algebra.toModule
  letI : Algebra T (T ⊗[B] A) := Algebra.TensorProduct.leftAlgebra
  have hKT : IsScalarTower K T (T ⊗[B] A) := by
    constructor
    intro k t x
    simp
  letI : IsScalarTower K T (T ⊗[B] A) := hKT
  have hBA : Algebra.FiniteType B A := by
    exact Algebra.FiniteType.of_restrictScalars_finiteType R B A
  letI : Algebra.FiniteType B A := hBA
  have hQF_BA : Algebra.QuasiFinite B A := by
    infer_instance
  letI : Algebra.QuasiFinite B A := hQF_BA
  have hQF : Algebra.QuasiFinite T (T ⊗[B] A) := by
    exact Algebra.QuasiFinite.baseChange (R := B) (S := A) (A := T)
  letI : Algebra.QuasiFinite T (T ⊗[B] A) := hQF
  have hFT_T : Algebra.FiniteType T (T ⊗[B] A) := by
    exact Algebra.FiniteType.baseChange (R := B) (A := A) T
  have hFT_K_T : Algebra.FiniteType K T := by
    infer_instance
  have hFT_K : Algebra.FiniteType K (T ⊗[B] A) := by
    exact Algebra.FiniteType.trans hFT_K_T hFT_T
  letI : Algebra.FiniteType K (T ⊗[B] A) := hFT_K
  have hdim_tensor : ringKrullDim (T ⊗[B] A) ≤ (m : WithBot ℕ∞) :=
    ringKrullDim_le_of_quasiFinite_tensorMvPolynomial_algebra
      (R := R) (K := K) (A := T ⊗[B] A) (m := m)
  -- Identify the base-changed algebra with the usual fiber and transport the dimension bound.
  let e : T ⊗[B] A ≃ₐ[K] p.asIdeal.Fiber A :=
    Algebra.IsPushout.cancelBaseChangeAlg R K B T A
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact hdim_tensor

/-- Helper for Chap10 Lemma 10 125 6: the quotient presentation of the local fiber ring is
unchanged after localizing the target away from an element. -/
private lemma ringKrullDim_quotient_localizationAway_comap
    (g : S) (qg : PrimeSpectrum (Localization.Away g)) :
    let q := PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg
    ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) =
      ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) := by
  intro q
  -- First align the prime of `S` with its ideal-theoretic contraction from `S_g`.
  let qI : Ideal S := Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal
  have hqI : q.asIdeal = Ideal.comap (AlgEquiv.refl : S ≃ₐ[S] S) qI := by
    have hq : q.asIdeal = qI := by
      simpa [qI, q] using
        (PrimeSpectrum.comap_asIdeal (f := algebraMap S (Localization.Away g)) qg)
    rw [hq]
    exact (Ideal.comap_id qI).symm
  let eSource : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qI :=
    Localization.localAlgEquiv q.asIdeal qI (AlgEquiv.refl : S ≃ₐ[S] S) hqI
  let eTower : Localization.AtPrime qI ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g) qg.asIdeal)
  let e : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    eSource.trans eTower
  let Iq : Ideal (Localization.AtPrime q.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
      (Ideal.comap (algebraMap R S) q.asIdeal)
  let Ig : Ideal (Localization.AtPrime qg.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
      (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)
  -- The base prime contracted through `R → S → S_g` is independent of the chosen spelling.
  have hbase :
      Ideal.comap (algebraMap R S) q.asIdeal =
        Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    simpa [q, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap,
      IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  -- The local-ring comparison is an `S`-algebra equivalence, hence also respects the `R`-maps.
  have heR : e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)) =
      algebraMap R (Localization.AtPrime qg.asIdeal) := by
    ext r
    change e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
      algebraMap R (Localization.AtPrime qg.asIdeal) r
    calc
      e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
          e (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S r)) := by
            rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
      _ = algebraMap S (Localization.AtPrime qg.asIdeal) (algebraMap R S r) := by
            exact e.commutes (algebraMap R S r)
      _ = algebraMap R (Localization.AtPrime qg.asIdeal) r := by
            rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime qg.asIdeal)]
  -- Transport the extended base ideal across the local-ring equivalence.
  have hmap : Ig = Ideal.map e.toRingHom Iq := by
    calc
      Ig = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal) := rfl
      _ = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R S) q.asIdeal) := by
            rw [← hbase]
      _ = Ideal.map (e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)))
          (Ideal.comap (algebraMap R S) q.asIdeal) := by
            rw [heR]
      _ = Ideal.map e.toRingHom Iq := by
            rw [Ideal.map_map]
  let eQuot :
      ((Localization.AtPrime q.asIdeal) ⧸ Iq) ≃+*
        ((Localization.AtPrime qg.asIdeal) ⧸ Ig) :=
    Ideal.quotientEquiv Iq Ig e.toRingEquiv hmap
  -- Krull dimension is invariant under the induced quotient ring equivalence.
  exact (ringKrullDim_eq_of_ringEquiv eQuot).symm

/-- Helper for Chap10 Lemma 10 125 6: relative dimension is unchanged when computed after a
localization away from an element and then pulled back by the localization comap. -/
private lemma relativeDimensionAt_localizationAway_comap
    (g : S) (qg : PrimeSpectrum (Localization.Away g)) :
    relativeDimensionAt R (Localization.Away g) qg =
      relativeDimensionAt R S (PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg) := by
  -- Route correction: compare quotient presentations of the two local fiber rings instead of
  -- constructing a direct equivalence between the transported fiber-local-ring definitions.
  let q := PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg
  calc
    relativeDimensionAt R (Localization.Away g) qg =
        ringKrullDim (fiberLocalRingAt R (Localization.Away g) qg) := rfl
    _ = ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) := by
          rw [← ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := Localization.Away g) qg]
    _ = ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) := by
          exact ringKrullDim_quotient_localizationAway_comap (R := R) (S := S) g qg
    _ = ringKrullDim (fiberLocalRingAt R S q) := by
          rw [ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := S) q]
    _ = relativeDimensionAt R S q := rfl

/-- Helper for Chap10 Lemma 10 125 6: a quasi-finite algebra over an `m`-variable polynomial
algebra has relative dimension at most `m` at every prime. -/
private lemma relativeDimensionAt_le_of_quasiFinite_mvPolynomial
    {A : Type v} [CommRing A] [Algebra R A] {m : ℕ}
    [Algebra (MvPolynomial (Fin m) R) A]
    [IsScalarTower R (MvPolynomial (Fin m) R) A]
    [Algebra.FiniteType R A] [Algebra.QuasiFinite (MvPolynomial (Fin m) R) A]
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q ≤ (m : WithBot ℕ∞) := by
  -- First compare the local fiber ring with the whole fiber ring at the contracted base prime.
  rw [relativeDimensionAt]
  exact
    (ringKrullDim_localizationAtPrime_le_ringKrullDim
      (I := (fiberPrimeAt R A q).asIdeal)).trans
      (ringKrullDim_fiber_le_of_quasiFinite_mvPolynomial
        (R := R) (A := A) (m := m) (PrimeSpectrum.comap (algebraMap R A) q))

variable [Algebra.FiniteType R S]

/-- Chap10 Lemma 10 125 6: let `R → S` be a finite type ring map, let `q : Spec(S)` be a prime, and
assume the relative dimension of `S/R` at `q` is exactly `n`. Then there exists an open
neighbourhood of `q` in `Spec(S)` contained in `relativeDimensionAtLELocus R S n`, i.e. on which
the relative fiber dimension is everywhere at most `n`. -/
@[stacks 00QH]
theorem exists_openNhdsOf_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S) (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := by
  -- Shrink around `q` to a localization admitting a quasi-finite polynomial presentation.
  obtain ⟨g, hg, φ, hφ⟩ :=
    exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq n q hq
  have hq_basic : q ∈ PrimeSpectrum.basicOpen g :=
    (PrimeSpectrum.mem_basicOpen g q).2 hg
  let U : OpenNhdsOf q := ⟨PrimeSpectrum.basicOpen g, hq_basic⟩
  refine ⟨U, ?_⟩
  intro q' hq'
  rw [mem_relativeDimensionAtLELocus]
  -- Every point of the basic open comes from a prime of the localization away from `g`.
  have hq'_range :
      q' ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hq'
  obtain ⟨qg, hqg⟩ := hq'_range
  subst q'
  -- Use the polynomial presentation as the non-inferable algebra structure on `S_g`.
  letI : Algebra (MvPolynomial (Fin n) R) (Localization.Away g) := φ.toRingHom.toAlgebra
  have hscalar : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  letI : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g) := hscalar
  letI : Algebra.QuasiFinite (MvPolynomial (Fin n) R) (Localization.Away g) := hφ
  have hle :
      relativeDimensionAt R (Localization.Away g) qg ≤ (n : WithBot ℕ∞) :=
    relativeDimensionAt_le_of_quasiFinite_mvPolynomial (R := R) qg
  simpa [relativeDimensionAt_localizationAway_comap] using hle

-- Proof sketch: if `q ∈ relativeDimensionAtLELocus R S n`, let `m := relativeDimensionAt R S q`.
-- The equality-case argument at the actual local dimension `m` gives an open neighborhood of `q`
-- contained in the `≤ m` locus; since `m ≤ n`, that neighborhood is also contained in the
-- `≤ n` locus.
/-- Companion strengthening: if `q` already lies in the bounded-dimension locus
`relativeDimensionAtLELocus R S n`, then there is an open neighbourhood of `q` contained in that
locus. -/
theorem exists_openNhdsOf_mem_relativeDimensionAtLELocus
    (n : ℕ) (q : PrimeSpectrum S) (hq : q ∈ relativeDimensionAtLELocus R S n) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := by
  -- Convert membership in the bounded locus into an exact finite relative-dimension value.
  have hq_le : relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) :=
    (mem_relativeDimensionAtLELocus n q).mp hq
  obtain ⟨m, hmn, hm⟩ := exists_nat_eq_relativeDimensionAt_of_le (R := R) (S := S) hq_le
  -- Apply the equality case at that exact value, then enlarge the bound from `m` to `n`.
  obtain ⟨U, hU⟩ := exists_openNhdsOf_relativeDimensionAt_eq m q hm
  refine ⟨U, ?_⟩
  intro q' hq'
  rw [mem_relativeDimensionAtLELocus]
  have hle_m : relativeDimensionAt R S q' ≤ (m : WithBot ℕ∞) :=
    (mem_relativeDimensionAtLELocus m q').mp (hU q' hq')
  have hmn' : (m : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    exact_mod_cast hmn
  exact hle_m.trans hmn'

end
