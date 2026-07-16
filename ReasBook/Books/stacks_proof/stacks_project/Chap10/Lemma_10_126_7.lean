import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.StacksAttribute
import stacks_proof.stacks_project.Chap10.Lemma_10_122_10
import stacks_proof.stacks_project.Chap10.Lemma_10_6_2
import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.Index

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']
variable [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R S']

attribute [local instance] MvPolynomial.algebraMvPolynomial

-- Semantic recall: `Algebra.FinitePresentation` is the canonical owner for finitely presented
-- `R`-algebras, while `PrimeSpectrum`, `Localization.AtPrime`, and `Localization.Away` provide
-- the source-faithful local-ring and principal-open localization interfaces.

/-- Helper for Chap10 Lemma 10 126 7: a prime avoiding an away denominator lifts to the away
localization. -/
private lemma exists_primeSpectrum_away_comap_eq_of_notMem
    {A : Type*} [CommRing A] (p : PrimeSpectrum A) {f : A} (hf : f ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q = p := by
  -- Proof comment: the image of `Spec(A_f)` is exactly the basic open `D(f)`.
  have hp_range : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa [PrimeSpectrum.mem_basicOpen] using hf
  exact Set.mem_range.mp hp_range

/-- Helper for Chap10 Lemma 10 126 7: a prime of an away localization is determined by its
contraction to the source ring. -/
private lemma eq_of_away_comap_eq
    {A : Type*} [CommRing A] {f : A}
    {p : PrimeSpectrum A}
    {q₁ q₂ : PrimeSpectrum (Localization.Away f)}
    (hq₁ : PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q₁ = p)
    (hq₂ : PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q₂ = p) :
    q₁ = q₂ := by
  -- Proof comment: localization does not identify distinct primes lying over the same source
  -- prime, so equality of the two contractions forces equality upstairs.
  let comap_injective :
      Function.Injective (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) :=
    PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  exact comap_injective (hq₁.trans hq₂.symm)

omit [Algebra.FinitePresentation R S'] in
/-- Helper for Chap10 Lemma 10 126 7: an iterated away localization of `S'_g'` is a single away
localization of `S'` after clearing the second denominator. -/
private lemma singleOriginalAwayAlgEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    (g : A) (u : Localization.Away g) :
    let h : A := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[R] Localization.Away h) := by
  -- Proof comment: replace the iterated denominator by a numerator representative in `S'`, then
  -- compare the two away localizations through the standard associated-element equivalence.
  let a : A := (IsLocalization.Away.sec g u).1
  let h : A := g * a
  let hassoc :
      Associated (algebraMap A (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap A (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[R] Localization.Away (algebraMap A (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap A (Localization.Away g) a))).restrictScalars R
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap A (Localization.Away g) a)) := by
    simpa [h] using
      (inferInstance :
        IsLocalization.Away h (Localization.Away (algebraMap A (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap A (Localization.Away g) a) ≃ₐ[R] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap A (Localization.Away g) a))).symm.restrictScalars R
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 126 7: if an element of `S'_g'` avoids a lifted prime over `q'`,
then the cleared original denominator still avoids `q'`. -/
private lemma notMem_original_away_of_iterated_away
    {A : Type*} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A) {g : A} (hg : g ∉ q.asIdeal)
    {u : Localization.Away g} (qAway : PrimeSpectrum (Localization.Away g))
    (hqAway : PrimeSpectrum.comap (algebraMap A (Localization.Away g)) qAway = q)
    (hu : u ∉ qAway.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  -- Proof comment: the numerator chosen by `sec` is associated to `u`, so if that numerator
  -- entered the lifted prime then `u` would enter as well; primality then finishes the argument.
  have hsec_not_mem_away :
      algebraMap A (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qAway.asIdeal := by
    intro hsec_mem
    have hu_mem : u ∈ qAway.asIdeal := by
      exact
        (Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    intro hsec_mem
    have hqAwayIdeal :
        Ideal.comap (algebraMap A (Localization.Away g)) qAway.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
    have hmem_away :
        algebraMap A (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈ qAway.asIdeal := by
      change
        (IsLocalization.Away.sec g u).1 ∈
          Ideal.comap (algebraMap A (Localization.Away g)) qAway.asIdeal
      rw [hqAwayIdeal]
      exact hsec_mem
    exact hsec_not_mem_away hmem_away
  exact (show q.asIdeal.IsPrime from inferInstance).mul_notMem hg hsec_not_mem

/-- Helper for Chap10 Lemma 10 126 7: localizing at a prime after passing to one away chart is
canonically the same as localizing the original ring at the contracted prime. -/
private noncomputable def atPrimeAwayLocalizationAlgEquiv_of_comap_eq
    {A : Type*} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A) {g : A} (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap A (Localization.Away g)) qg = q) :
    Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qg.asIdeal :=
  let eDomain : Localization.AtPrime q.asIdeal ≃ₐ[A]
      Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away g)) qg.asIdeal) :=
    Localization.localAlgEquiv
      q.asIdeal
      (Ideal.comap (algebraMap A (Localization.Away g)) qg.asIdeal)
      (show A ≃ₐ[A] A from AlgEquiv.refl)
      (by simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg.symm)
  let eDouble :
      Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away g)) qg.asIdeal) ≃ₐ[A]
        Localization.AtPrime qg.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers g) qg.asIdeal
  -- Proof comment: first rewrite the contracted prime to the displayed away-chart prime, then use
  -- the standard iterated-localization equivalence for `A → A_g → (A_g)_(qg)`.
  (eDomain.trans eDouble).restrictScalars R

/-- Helper for Chap10 Lemma 10 126 7: a polynomial presentation descends through its quotient as
soon as the chosen tuple kills a finite family spanning the presentation kernel. -/
private lemma presentationKernel_descends_to_awayChart
    {A : Type*} [CommRing A] [Algebra R A]
    {n m : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] S)
    (hπsurj : Function.Surjective π)
    (rels : Fin m → MvPolynomial (Fin n) R)
    (hrels : Ideal.span (Set.range rels) = RingHom.ker π.toRingHom)
    (u : Fin n → A)
    (hzero : ∀ j, MvPolynomial.aeval u (rels j) = 0) :
    ∃ φ : S →ₐ[R] A,
      φ.comp π = MvPolynomial.aeval u := by
  have hkerle :
      RingHom.ker π.toRingHom ≤ RingHom.ker (MvPolynomial.aeval u).toRingHom := by
    -- Proof comment: it is enough to check the chosen spanning family of kernel relations, since
    -- each displayed relation already evaluates to zero on the tuple `u`.
    rw [← hrels]
    refine Ideal.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with ⟨j, rfl⟩
    simpa [RingHom.mem_ker] using hzero j
  refine ⟨AlgHom.liftOfSurjective π hπsurj (MvPolynomial.aeval u) hkerle, ?_⟩
  -- Proof comment: after identifying `S` with the quotient by the presentation kernel, the
  -- descended map agrees with the original polynomial evaluation on the presentation generators.
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  -- Proof comment: both sides are `R`-algebra maps out of the same polynomial ring, so it
  -- suffices to compare their values on the variables.
  simpa using
    (AlgHom.liftOfSurjective_apply
      π
      hπsurj
      (MvPolynomial.aeval u)
      hkerle
      (MvPolynomial.X i))

/-- Helper for Chap10 Lemma 10 126 7: if one multiplier kills an element before localizing away
from that multiplier, the localized image is zero. -/
private lemma awayMap_eq_zero_of_mul_eq_zero
    {A : Type*} [CommRing A] {g r : A} (hgr : g * r = 0) :
    algebraMap A (Localization.Away g) r = 0 := by
  -- Proof comment: `IsLocalization.map_eq_zero_iff` records exactly the denominator-clearing
  -- criterion for the away map `A → A_g`.
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g) (Localization.Away g) r]
  refine ⟨⟨g, ⟨1, by simp⟩⟩, ?_⟩
  simpa using hgr

/-- Helper for Chap10 Lemma 10 126 7: on the `Spec(A)` branch of
`Spec(A × C) ≃ Spec(A) ⊕ Spec(C)`, the first-factor idempotent `(1, 0)` stays outside the
corresponding product prime. -/
private lemma firstFactorIdempotent_not_mem_of_productPrime
    {A : Type*} {C : Type*} [CommRing A] [CommRing C]
    (p : PrimeSpectrum A) :
    ((1 : A), (0 : C)) ∉ ((PrimeSpectrum.primeSpectrumProd A C).symm (Sum.inl p)).asIdeal := by
  -- Proof comment: on the `Sum.inl` branch the product prime is `p × ⊤`, so membership of
  -- `(1, 0)` would force `1 ∈ p`, contradicting that a prime ideal is proper.
  intro hmem
  have h1 : (1 : A) ∈ p.asIdeal := by
    simpa [PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal] using hmem
  have hp1 : (1 : A) ∉ p.asIdeal := by
    simpa [Ideal.eq_top_iff_one] using p.2.ne_top
  exact hp1 h1

/-- Helper for Chap10 Lemma 10 126 7: after transporting a raw product decomposition back across
an algebra equivalence, the pulled-back first-factor idempotent still avoids every tracked prime.
-/
private lemma firstFactorIdempotent_not_mem_of_refinedProduct
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (e : B ≃ₐ[A] (A × C))
    (p : PrimeSpectrum A)
    (q : PrimeSpectrum B)
    (hq :
      PrimeSpectrum.comap e.symm.toRingHom q =
        (PrimeSpectrum.primeSpectrumProd A C).symm (Sum.inl p)) :
    e.symm ((1 : A), (0 : C)) ∉ q.asIdeal := by
  -- Proof comment: move the membership question across `e`, reduce to the left-branch product
  -- prime supplied by `hq`, and apply the explicit product-prime computation above.
  intro hmem
  have hmemProd :
      ((1 : A), (0 : C)) ∈ (PrimeSpectrum.comap e.symm.toRingHom q).asIdeal := by
    change e.symm ((1 : A), (0 : C)) ∈ q.asIdeal
    simpa using hmem
  have hqIdeal :
      (PrimeSpectrum.comap e.symm.toRingHom q).asIdeal =
        ((PrimeSpectrum.primeSpectrumProd A C).symm (Sum.inl p)).asIdeal := by
    simpa using congrArg PrimeSpectrum.asIdeal hq
  rw [hqIdeal] at hmemProd
  exact firstFactorIdempotent_not_mem_of_productPrime (A := A) (C := C) p hmemProd

/-- Helper for Chap10 Lemma 10 126 7: on the `Spec(C)` branch of
`Spec(A × C) ≃ Spec(A) ⊕ Spec(C)`, the first-factor idempotent `(1, 0)` lies in the
corresponding product prime. -/
private lemma firstFactorIdempotent_mem_of_productPrimeRight
    {A : Type*} {C : Type*} [CommRing A] [CommRing C]
    (p : PrimeSpectrum C) :
    ((1 : A), (0 : C)) ∈ ((PrimeSpectrum.primeSpectrumProd A C).symm (Sum.inr p)).asIdeal := by
  -- Proof comment: on the right branch the product prime is `⊤ × p`, so `(1, 0)` belongs to it
  -- through the first factor alone.
  simpa [PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal]

/-- Helper for Chap10 Lemma 10 126 7: localizing `B × C` away from the first-factor idempotent
`(1, 0)` recovers the first factor `B`. -/
private lemma prodFst_isLocalizationAwayOneZero
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] :
    letI := (RingHom.fst B C).toAlgebra
    IsLocalization.Away (((1 : B), (0 : C)) : B × C) B := by
  -- Proof comment: this is the canonical product-localization instance already provided by
  -- mathlib for the idempotent `(1, 0)`.
  infer_instance

/-- Helper for Chap10 Lemma 10 126 7: the stalk equivalence should first descend to a principal
open target chart carrying a bijective local ring map from `S_q`. -/
private lemma exists_descendedAwayAlgHom_of_localizationAtPrime_algEquiv
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    (h :
      Localization.AtPrime q.asIdeal ≃ₐ[R]
        Localization.AtPrime q'.asIdeal) :
    ∃ g' : { x : S' // x ∉ q'.asIdeal },
      ∃ φ : S →ₐ[R] Localization.Away g'.1,
      ∃ qg' : PrimeSpectrum (Localization.Away g'.1),
      ∃ hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal,
        PrimeSpectrum.comap (algebraMap S' (Localization.Away g'.1)) qg' = q' ∧
        Function.Bijective
          (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap) :=
    by
  -- Route correction: the source-faithful first stage is explicit denominator clearing, not a
  -- search for a generic presentation wrapper. One first fixes a polynomial presentation of `S`,
  -- clears the images of its generators inside `S'_{q'}`, and then prepares the second shrink on
  -- the finite relation family before descending through the quotient.
  obtain ⟨n, π, hπsurj, hπkerfg⟩ := @Algebra.FinitePresentation.out R S _ _ _ inferInstance
  obtain ⟨m, rels, hrels⟩ :
      ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) R,
        Ideal.span (Set.range rels) = RingHom.ker π.toRingHom := by
    -- Proof comment: the finite-presentation datum is normalized to one explicit finite relation
    -- family so the later denominator-clearing step can target those concrete relations.
    simpa using Submodule.fg_iff_exists_fin_generating_family.mp hπkerfg
  let x : Fin n → Localization.AtPrime q'.asIdeal := fun i ↦
    h (algebraMap S (Localization.AtPrime q.asIdeal) (π (MvPolynomial.X i)))
  obtain ⟨g₁, hg₁, a, ha⟩ :=
    exists_notMem_and_common_denominator_atPrime q'.asIdeal x
  let A := Localization.Away g₁
  let denom : Submonoid.powers g₁ := ⟨g₁, ⟨1, by simp⟩⟩
  let u : Fin n → A := fun i ↦ IsLocalization.mk' A (a i) denom
  let ρ₁ : A →+* Localization.AtPrime q'.asIdeal :=
    Localization.awayLift (algebraMap S' (Localization.AtPrime q'.asIdeal)) g₁
      (IsLocalization.map_units (Localization.AtPrime q'.asIdeal) (⟨g₁, hg₁⟩ : q'.asIdeal.primeCompl))
  have hu : ∀ i, ρ₁ (u i) = x i := by
    intro i
    -- Proof comment: the first common denominator turns the chosen stalk images of the
    -- presentation generators into actual elements of the away chart `S'[(g₁)⁻¹]`.
    let hgUnits : ∀ y : Submonoid.powers g₁,
        IsUnit (algebraMap S' (Localization.AtPrime q'.asIdeal) y.1) := by
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨k, rfl⟩
      simpa using
        (IsLocalization.map_units (Localization.AtPrime q'.asIdeal)
          (⟨g₁, hg₁⟩ : q'.asIdeal.primeCompl)).pow k
    apply
      (IsLocalization.lift_mk'_spec
        hgUnits
        (a i)
        (x i)
        denom).2
    simpa [ρ₁, u, x, denom, mul_comm] using (ha i).symm
  have hqg₁_exists :
      ∃ qg₁ : PrimeSpectrum (Localization.Away g₁),
        PrimeSpectrum.comap (algebraMap S' (Localization.Away g₁)) qg₁ = q' :=
    exists_primeSpectrum_away_comap_eq_of_notMem q' hg₁
  obtain ⟨qg₁, hqg₁⟩ := hqg₁_exists
  let eAtPrime :
      Localization.AtPrime q'.asIdeal ≃ₐ[S'] Localization.AtPrime qg₁.asIdeal :=
    atPrimeAwayLocalizationAlgEquiv_of_comap_eq q' qg₁ hqg₁
  have hρ₁ :
      eAtPrime.toRingHom.comp ρ₁ =
        algebraMap A (Localization.AtPrime qg₁.asIdeal) := by
    -- Proof comment: after transporting the `q'`-stalk along the lifted away-chart prime `qg₁`,
    -- the original away lift becomes the canonical algebra map from `A` to `A_(qg₁)`.
    apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
    ext s
    simpa [RingHom.comp_apply, ρ₁] using
      DFunLike.congr_fun
        (IsScalarTower.algebraMap_eq S' A (Localization.AtPrime qg₁.asIdeal))
        s
  let _ := m
  let _ := rels
  let _ := hrels
  let _ := hu
  let _ := qg₁
  let _ := hqg₁
  let _ := eAtPrime
  let _ := hρ₁
  let ρ₁a : A →ₐ[R] Localization.AtPrime q'.asIdeal :=
    { toRingHom := ρ₁
      commutes' := by
        intro r
        simpa [ρ₁, IsScalarTower.algebraMap_apply R S' A,
          IsScalarTower.algebraMap_apply R S' (Localization.AtPrime q'.asIdeal)] }
  let z : Fin m → A := fun j ↦ MvPolynomial.aeval u (rels j)
  have hz : ∀ j, ρ₁ (z j) = 0 := by
    intro j
    have hrel_mem : rels j ∈ RingHom.ker π.toRingHom := by
      rw [← hrels]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hrel_zero : π (rels j) = 0 := by
      simpa [RingHom.mem_ker] using hrel_mem
    -- Proof comment: after evaluating the relation through the cleared tuple `u`, the away-to-stalk
    -- map rewrites the result to `h (π (rels j))`, which vanishes because `rels j` lies in the
    -- presentation kernel.
    calc
      ρ₁ (z j) = MvPolynomial.aeval x (rels j) := by
        simpa [ρ₁a, z, hu] using
          (MvPolynomial.comp_aeval_apply u ρ₁a (rels j))
      _ = h (algebraMap S (Localization.AtPrime q.asIdeal) (π (rels j))) := by
            let ψ : MvPolynomial (Fin n) R →ₐ[R] Localization.AtPrime q'.asIdeal :=
              h.toAlgHom.comp
                (((Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R).comp π)
            have hψ :
                MvPolynomial.aeval x = ψ := by
              refine MvPolynomial.algHom_ext fun i ↦ ?_
              simp [ψ, x]
            rw [hψ]
            rfl
      _ = 0 := by simp [hrel_zero]
  obtain ⟨g₂, hg₂, hz₂⟩ :=
    exists_notMem_zero_family_after_second_shrink_atPrime q'.asIdeal hg₁ z
      (by simpa [ρ₁] using hz)
  let A₂ := Localization.Away (g₁ * g₂)
  let ρ₂ : A →+* A₂ :=
    IsLocalization.Away.awayToAwayRight g₁ g₂
  let ρ₂a : A →ₐ[R] A₂ :=
    { toRingHom := ρ₂
      commutes' := by
        intro r
        simp [ρ₂, IsLocalization.Away.awayToAwayRight_eq,
          IsScalarTower.algebraMap_apply R S' A, IsScalarTower.algebraMap_apply R S' A₂] }
  have hz₂' : ∀ j, ρ₂ (z j) = 0 := by
    simpa [A₂, ρ₂] using hz₂
  let u₂ : Fin n → A₂ := fun i ↦ ρ₂ (u i)
  have hzero₂ : ∀ j, MvPolynomial.aeval u₂ (rels j) = 0 := by
    intro j
    -- Proof comment: the second shrink kills the entire finite relation family literally in the
    -- smaller away chart, so the quotient descent can now be applied directly.
    calc
      MvPolynomial.aeval u₂ (rels j) = ρ₂ (z j) := by
        simpa [u₂, z, ρ₂a] using
          (MvPolynomial.comp_aeval_apply u ρ₂a (rels j)).symm
      _ = 0 := hz₂' j
  obtain ⟨φ, hφ⟩ :=
    presentationKernel_descends_to_awayChart π hπsurj rels hrels u₂ hzero₂
  have hg' : g₁ * g₂ ∉ q'.asIdeal := q'.2.mul_notMem hg₁ hg₂
  have hqg'_exists :
      ∃ qg' : PrimeSpectrum (Localization.Away (g₁ * g₂)),
        PrimeSpectrum.comap (algebraMap S' (Localization.Away (g₁ * g₂))) qg' = q' :=
    exists_primeSpectrum_away_comap_eq_of_notMem q' hg'
  obtain ⟨qg', hqg'⟩ := hqg'_exists
  let ρ₂' : A₂ →+* Localization.AtPrime q'.asIdeal :=
    Localization.awayLift (algebraMap S' (Localization.AtPrime q'.asIdeal)) (g₁ * g₂)
      (IsLocalization.map_units (Localization.AtPrime q'.asIdeal)
        (⟨g₁ * g₂, hg'⟩ : q'.asIdeal.primeCompl))
  have hρ₂'comp : ρ₂'.comp ρ₂ = ρ₁ := by
    -- Proof comment: both ways of sending the first away chart to the stalk `S'_{q'}` are the
    -- canonical localization map on the image of `S'`, so they agree globally.
    apply IsLocalization.ringHom_ext (Submonoid.powers g₁)
    ext s
    calc
      (ρ₂'.comp ρ₂) (algebraMap S' A s) = ρ₂' (algebraMap S' A₂ s) := by
        simp [RingHom.comp_apply, ρ₂, IsLocalization.Away.awayToAwayRight_eq]
      _ = algebraMap S' (Localization.AtPrime q'.asIdeal) s := by
            simp [ρ₂', Localization.awayLift]
      _ = ρ₁ (algebraMap S' A s) := by
            simp [ρ₁, Localization.awayLift]
  have hu₂ : ∀ i, ρ₂' (u₂ i) = x i := by
    intro i
    have hcomp_i :=
      congrArg (fun F : A →+* Localization.AtPrime q'.asIdeal ↦ F (u i)) hρ₂'comp
    calc
      ρ₂' (u₂ i) = ρ₁ (u i) := by simpa [u₂, RingHom.comp_apply] using hcomp_i
      _ = x i := hu i
  let eAtPrime₂S :
      Localization.AtPrime q'.asIdeal ≃ₐ[S'] Localization.AtPrime qg'.asIdeal :=
    atPrimeAwayLocalizationAlgEquiv_of_comap_eq q' qg' hqg'
  have hρ₂ :
      eAtPrime₂S.toRingHom.comp ρ₂' =
        algebraMap A₂ (Localization.AtPrime qg'.asIdeal) := by
    -- Proof comment: after transporting the `q'`-stalk along the lifted prime `qg'`, the second
    -- away-to-stalk map becomes the canonical algebra map from the descended chart.
    apply IsLocalization.ringHom_ext (Submonoid.powers (g₁ * g₂))
    ext s
    simpa [RingHom.comp_apply, ρ₂'] using
      DFunLike.congr_fun
        (IsScalarTower.algebraMap_eq S' A₂ (Localization.AtPrime qg'.asIdeal))
        s
  let eAtPrime₂ :
      Localization.AtPrime q'.asIdeal ≃ₐ[R] Localization.AtPrime qg'.asIdeal :=
    eAtPrime₂S.restrictScalars R
  let E :
      Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qg'.asIdeal :=
    h.trans eAtPrime₂
  let ιq : S →ₐ[R] Localization.AtPrime q.asIdeal :=
    (Algebra.ofId S (Localization.AtPrime q.asIdeal)).restrictScalars R
  let ιqg : A₂ →ₐ[R] Localization.AtPrime qg'.asIdeal :=
    (Algebra.ofId A₂ (Localization.AtPrime qg'.asIdeal)).restrictScalars R
  have hEcompAlg : E.toAlgHom.comp ιq = ιqg.comp φ := by
    have hcompπ :
        (E.toAlgHom.comp ιq).comp π = (ιqg.comp φ).comp π := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      have hφXi :
          φ (π (MvPolynomial.X i)) = u₂ i := by
        simpa [AlgHom.comp_apply] using
          congrArg (fun F : MvPolynomial (Fin n) R →ₐ[R] A₂ ↦ F (MvPolynomial.X i)) hφ
      have hρ₂Xi :
          eAtPrime₂ (ρ₂' (u₂ i)) =
            algebraMap A₂ (Localization.AtPrime qg'.asIdeal) (u₂ i) := by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun F : A₂ →+* Localization.AtPrime qg'.asIdeal ↦ F (u₂ i))
            hρ₂
      -- Proof comment: both descended maps agree on the chosen presentation generators, hence on
      -- the entire source algebra after quotienting by the presentation kernel.
      calc
        (E.toAlgHom.comp ιq).comp π (MvPolynomial.X i)
            = eAtPrime₂ (x i) := by simp [E, ιq, x]
        _ = eAtPrime₂ (ρ₂' (u₂ i)) := by rw [hu₂ i]
        _ = algebraMap A₂ (Localization.AtPrime qg'.asIdeal) (u₂ i) := hρ₂Xi
        _ = (ιqg.comp φ).comp π (MvPolynomial.X i) := by simpa [ιqg, hφXi]
    ext s
    rcases hπsurj s with ⟨p, rfl⟩
    exact congrArg (fun F : MvPolynomial (Fin n) R →ₐ[R] Localization.AtPrime qg'.asIdeal ↦ F p)
      hcompπ
  have hEcomp :
      E.toRingHom.comp (algebraMap S (Localization.AtPrime q.asIdeal)) =
        (algebraMap A₂ (Localization.AtPrime qg'.asIdeal)).comp φ.toRingHom := by
    ext s
    simpa [ιq, ιqg, AlgHom.comp_apply, RingHom.comp_apply] using
      congrArg (fun F : S →ₐ[R] Localization.AtPrime qg'.asIdeal ↦ F s) hEcompAlg
  have hmax :
      Ideal.comap E.toRingHom
          (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    let _ : IsLocalHom E.toRingHom := IsLocalHom.of_surjective E.toRingHom E.surjective
    simpa using
      (IsLocalRing.maximalIdeal_comap E.toRingHom)
  have hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal := by
    -- Proof comment: the transported equivalence identifies the maximal ideals of the two local
    -- rings, and contracting those maximal ideals back to the source rings recovers the prime
    -- contraction statement needed for the local ring map.
    have hqMax :
        Ideal.comap (algebraMap S (Localization.AtPrime q.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) =
        q.asIdeal :=
      Localization.AtPrime.comap_maximalIdeal
    have hqgMax :
        Ideal.comap (algebraMap A₂ (Localization.AtPrime qg'.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal)) =
        qg'.asIdeal :=
      Localization.AtPrime.comap_maximalIdeal
    calc
      q.asIdeal =
          Ideal.comap (algebraMap S (Localization.AtPrime q.asIdeal))
            (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) := by
              simpa using hqMax.symm
      _ =
          Ideal.comap (algebraMap S (Localization.AtPrime q.asIdeal))
            (Ideal.comap E.toRingHom
              (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal))) := by
                rw [hmax]
      _ =
          Ideal.comap (E.toRingHom.comp (algebraMap S (Localization.AtPrime q.asIdeal)))
            (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal)) := by
              rw [Ideal.comap_comap]
      _ =
          Ideal.comap
            (((algebraMap A₂ (Localization.AtPrime qg'.asIdeal)).comp φ.toRingHom))
            (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal)) := by
              rw [hEcomp]
      _ =
          Ideal.comap φ.toRingHom
            (Ideal.comap (algebraMap A₂ (Localization.AtPrime qg'.asIdeal))
              (IsLocalRing.maximalIdeal (Localization.AtPrime qg'.asIdeal))) := by
                rw [Ideal.comap_comap]
      _ = Ideal.comap φ.toRingHom qg'.asIdeal := by
            rw [hqgMax]
  have hlocalEq :
      Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap = E.toRingHom := by
    -- Proof comment: both local maps out of `S_q` agree on the image of `S`, so the localization
    -- universal property identifies them.
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext s
    calc
      Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap
          (algebraMap S (Localization.AtPrime q.asIdeal) s) =
        algebraMap A₂ (Localization.AtPrime qg'.asIdeal) (φ s) := by
          exact
            Localization.localRingHom_to_map
              q.asIdeal qg'.asIdeal φ.toRingHom hcomap s
      _ = E (algebraMap S (Localization.AtPrime q.asIdeal) s) := by
            symm
            simpa [RingHom.comp_apply] using
              congrArg
                (fun F : S →+* Localization.AtPrime qg'.asIdeal ↦ F s)
                hEcomp
  have hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap) := by
    rw [hlocalEq]
    exact E.bijective
  exact ⟨⟨g₁ * g₂, hg'⟩, φ, qg', hcomap, hqg', hlocal⟩

/-- Helper for Chap10 Lemma 10 126 7: the kernel of `S → T` is the same as the kernel of the
ambient descended-chart map `S → A` when `T` is viewed as an `S`-subalgebra of `A`. -/
private lemma refinementSubalgebra_kernelFg
    {A : Type*} [CommRing A] [Algebra S A]
    (T : Subalgebra S A)
    (hkerA : (RingHom.ker (algebraMap S A)).FG) :
    (RingHom.ker (algebraMap S T)).FG := by
  have hkerEq : RingHom.ker (algebraMap S T) = RingHom.ker (algebraMap S A) := by
    ext x
    change (algebraMap S T x = 0) ↔ (algebraMap S A x = 0)
    constructor
    · intro hx
      exact congrArg (fun y : T ↦ (y : A)) hx
    · intro hx
      exact Subtype.ext <| by simpa using hx
  -- Proof comment: `T` is just the range-restricted codomain of `S → A`, so the two kernels
  -- coincide and finite generation transports across that equality.
  simpa [hkerEq] using hkerA

/-- Helper for Chap10 Lemma 10 126 7: if an `R`-algebra `A` is already finitely presented over
`R`, then any compatible `S`-algebra structure on `A` is finitely presented over `S`. -/
private lemma finitePresentation_of_baseChangeTarget
    {A : Type*} [CommRing A]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Algebra.FinitePresentation R A] :
    (algebraMap S A).FinitePresentation := by
  -- Proof comment: finite presentation descends along restriction of scalars once `S` is finite
  -- type over `R`, and the target statement is the ring-hom reformulation of that fact.
  letI : Algebra.FinitePresentation S A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S A
  simpa [RingHom.finitePresentation_algebraMap]

/-- Helper for Chap10 Lemma 10 126 7: quotienting an away chart by the kernel of a zero-section
retraction recovers the base away ring. -/
private noncomputable abbrev kernelQuotientAlgEquivOfZeroSectionRetraction
    {A : Type*} [CommRing A] [Algebra R A]
    {f : R}
    [Algebra (Localization.Away f) (Localization.Away (algebraMap R A f))]
    (σf : Localization.Away (algebraMap R A f) →ₐ[Localization.Away f] Localization.Away f)
    (hσf :
      Function.LeftInverse σf
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))) :
    (Localization.Away (algebraMap R A f) ⧸ RingHom.ker σf.toRingHom) ≃ₐ[Localization.Away f]
      Localization.Away f := by
  -- Proof comment: the retraction identity identifies the quotient by `ker σf` with the base away
  -- ring by the first-isomorphism theorem for ring retractions.
  exact Ideal.quotientKerAlgEquivOfRightInverse hσf

/-- Helper for Chap10 Lemma 10 126 7: the quotient by the current away-chart zero-section kernel
is already projective over the base away ring. -/
private lemma kernelQuotientProjectiveOverBase_ofZeroSectionRetraction
    {A : Type*} [CommRing A] [Algebra R A]
    {f : R}
    [Algebra (Localization.Away f) (Localization.Away (algebraMap R A f))]
    (σf : Localization.Away (algebraMap R A f) →ₐ[Localization.Away f] Localization.Away f)
    (hσf :
      Function.LeftInverse σf
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))) :
    Module.Projective (Localization.Away f)
      (Localization.Away (algebraMap R A f) ⧸ RingHom.ker σf.toRingHom) := by
  let e :=
    kernelQuotientAlgEquivOfZeroSectionRetraction σf hσf
  -- Proof comment: transport the canonical projective module structure on the base ring across
  -- the quotient equivalence supplied by the zero-section retraction.
  exact Module.Projective.of_equiv' e.symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 126 7: a projective quotient module is pure as an ideal. -/
private lemma idealPure_of_projectiveQuotient
    {A : Type*} [CommRing A] (I : Ideal A)
    (hproj : Module.Projective A (A ⧸ I)) :
    I.Pure := by
  letI : Module.Projective A (A ⧸ I) := hproj
  -- Proof comment: purity is flatness of the quotient module, and projective modules are flat.
  exact Module.Flat.of_projective

/-- Helper for Chap10 Lemma 10 126 7: the kernel of an algebra retraction is pure because the
quotient is a retract of the free module over the source ring. -/
private lemma idealPure_of_kernelQuotientRetraction
    {A : Type*} [CommRing A] [Algebra R A]
    {f : R}
    [Algebra (Localization.Away f) (Localization.Away (algebraMap R A f))]
    (σf : Localization.Away (algebraMap R A f) →ₐ[Localization.Away f] Localization.Away f)
    (hσf :
      Function.LeftInverse σf
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R A f)))) :
    (RingHom.ker σf.toRingHom).Pure := by
  let B := Localization.Away (algebraMap R A f)
  let I : Ideal B := RingHom.ker σf.toRingHom
  let Q := Ideal.Quotient I
  letI : Algebra B Q := Ideal.Quotient.algebra _
  letI : Module B Q := Algebra.toModule
  letI : Module (Localization.Away f) Q := RestrictScalars.module (Localization.Away f) B Q
  letI : IsScalarTower (Localization.Away f) B Q := RestrictScalars.isScalarTower _ _ _
  have hprojBase : Module.Projective (Localization.Away f) Q :=
    kernelQuotientProjectiveOverBase_ofZeroSectionRetraction
      (R := R)
      (A := A)
      (f := f)
      σf
      hσf
  letI : Algebra.FormallyUnramified (Localization.Away f) B := by infer_instance
  letI : Algebra.EssFiniteType (Localization.Away f) B := by infer_instance
  have hproj : Module.Projective B Q :=
    Algebra.FormallyUnramified.projective_of_restrictScalars
      (R := Localization.Away f)
      (S := B)
      (M := Q)
  exact idealPure_of_projectiveQuotient I hproj

/-- Helper for Chap10 Lemma 10 126 7: after shrinking away from `f`, the tracked prime lifts to a
prime of the current away chart, and the localized target remains quasi-finite over the localized
base. -/
private lemma currentAwayPrime_and_quasiFiniteAt_of_bijectiveLocalRingHom
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R A) hq.over))
    {f : R}
    (hf : f ∉ p) :
    let B := Localization.Away (algebraMap R A f)
    letI : Algebra (Localization.Away f) B :=
      (Localization.awayMap (algebraMap R A) f).toAlgebra
    ∃ qf : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap A B) qf = ⟨q, inferInstance⟩ ∧
      Algebra.QuasiFiniteAt (Localization.Away f) qf.asIdeal := by
  let B := Localization.Away (algebraMap R A f)
  letI : Algebra (Localization.Away f) B :=
    (Localization.awayMap (algebraMap R A) f).toAlgebra
  have hfq : algebraMap R A f ∉ q := by
    intro hmem
    exact hf <| by
      rw [hq.over]
      simpa [Ideal.mem_comap] using hmem
  have hdisj :
      Disjoint (Submonoid.powers (algebraMap R A f) : Set A) q := by
    -- Proof comment: every power of the inverted element still avoids `q`, so the localized prime
    -- is the standard image prime of `q`.
    rw [Set.disjoint_left]
    intro x hxPow hxq
    rcases (Submonoid.mem_powers_iff _ _).mp hxPow with ⟨n, rfl⟩
    exact hfq <| ‹q.IsPrime›.mem_of_pow_mem n hxq
  have hqfPrime : (Ideal.map (algebraMap A B) q).IsPrime := by
    -- Proof comment: primality survives localization because the denominator submonoid is
    -- disjoint from the tracked prime.
    exact
      IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers (algebraMap R A f))
        B
        q
        inferInstance
        hdisj
  let qf : PrimeSpectrum B := ⟨Ideal.map (algebraMap A B) q, hqfPrime⟩
  have hqfComap : PrimeSpectrum.comap (algebraMap A B) qf = ⟨q, inferInstance⟩ := by
    ext1
    -- Proof comment: contraction of the localized prime returns the original prime by the same
    -- disjointness calculation.
    simpa [qf, PrimeSpectrum.comap_asIdeal] using
      (IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers (algebraMap R A f))
        B
        (show q.IsPrime from inferInstance)
        hdisj)
  have hquasi : Algebra.QuasiFiniteAt R q :=
    quasiFiniteAt_of_bijective_localRingHom p q hq hlocal
  have hquasiAway : Algebra.QuasiFiniteAt (Localization.Away f) qf.asIdeal := by
    have hqfOver : qf.asIdeal.LiesOver q := by
      refine ⟨?_⟩
      simpa [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hqfComap).symm
    have hquasiTarget : Algebra.QuasiFiniteAt R qf.asIdeal := by
      -- Proof comment: the localization map `A → A_f` is surjective on stalks, so quasi-finiteness
      -- at `q` transports to the localized prime `qf`.
      letI : qf.asIdeal.LiesOver q := hqfOver
      exact
        Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver
          q
          (RingHom.surjectiveOnStalks_of_isLocalization
            (Submonoid.powers (algebraMap R A f))
            B)
          qf.asIdeal
    letI : IsScalarTower R (Localization.Away f) B :=
      away_localization_isScalarTower f
    -- Proof comment: restrict scalars from `R` to `R_f` once the current-away target is already
    -- known to be quasi-finite over `R`.
    exact toQuasiFiniteAt_of_restrictScalars qf hquasiTarget
  exact ⟨qf, hqfComap, hquasiAway⟩

/-- Helper for Chap10 Lemma 10 126 7: the source prime below the current away-chart prime is the
original base prime. -/
private lemma currentAway_under_comap_eq_basePrime
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hq : q.LiesOver p)
    {f : R} :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R A f)) :=
      (Localization.awayMap (algebraMap R A) f).toAlgebra
    ∀ qf : PrimeSpectrum (Localization.Away (algebraMap R A f)),
      PrimeSpectrum.comap (algebraMap A (Localization.Away (algebraMap R A f))) qf =
        ⟨q, inferInstance⟩ →
      (qf.asIdeal.under (Localization.Away f)).under R = p := by
  let B := Localization.Away (algebraMap R A f)
  letI : Algebra (Localization.Away f) B :=
    (Localization.awayMap (algebraMap R A) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) B :=
    away_localization_isScalarTower f
  intro qf hqf
  have hqfIdeal : Ideal.comap (algebraMap A B) qf.asIdeal = q := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqf
  ext x
  -- Proof comment: unfold the two contractions and compare the current-away prime directly with
  -- the original prime through the away-localization scalar tower.
  calc
    x ∈ (qf.asIdeal.under (Localization.Away f)).under R
        ↔ algebraMap R B x ∈ qf.asIdeal := by
          change
            algebraMap (Localization.Away f) B (algebraMap R (Localization.Away f) x) ∈
                qf.asIdeal ↔
              algebraMap R B x ∈ qf.asIdeal
          rw [← IsScalarTower.algebraMap_apply R (Localization.Away f) B x]
    _ ↔ algebraMap R A x ∈ q := by
          rw [← hqfIdeal]
          rfl
    _ ↔ x ∈ p := by
          rw [hq.over]
          rfl

/-- Helper for Chap10 Lemma 10 126 7: Zariski's main theorem gives a finite `A`-subalgebra
neighborhood of a quasi-finite target prime whose basic open agrees with the target basic open
around that prime. -/
private lemma currentAwayExistsFiniteSubalgebraAwayMapBijective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (qB : PrimeSpectrum B)
    (hquasi : Algebra.QuasiFiniteAt A qB.asIdeal) :
    ∃ (B' : Subalgebra A B) (r : B'),
      Module.Finite A B' ∧ (r : B) ∉ qB.asIdeal ∧
        Function.Bijective (Localization.awayMap B'.val.toRingHom r) := by
  letI : Algebra.QuasiFiniteAt A qB.asIdeal := hquasi
  have hfgExists :
      ∃ B' : Subalgebra A B, B'.toSubmodule.FG ∧ ∃ r : B',
        r.1 ∉ qB.asIdeal ∧ Function.Bijective (Localization.awayMap B'.val.toRingHom r) :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective qB.asIdeal
  obtain ⟨B', hB'fg, r, hr, hbij⟩ := hfgExists
  have hfinite : Module.Finite A B' :=
    ⟨(Subalgebra.toSubmodule B').fg_top.mpr hB'fg⟩
  -- Proof comment: the owner quasi-finite theorem already returns the right basic-open
  -- neighborhood; repackage its finite-generation output as the `Module.Finite` structure needed
  -- by the later subalgebra-refinement route.
  exact ⟨B', r, hfinite, hr, hbij⟩

/-- Helper for Chap10 Lemma 10 126 7: after the second shrink, the final target away chart is the
localization of the first-away quotient at the transported class of `C g`. -/
private theorem final_away_target_isLocalization_mapped_powers
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    IsLocalization
      (Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ))
      (Localization.Away (algebraMap S A fg)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρprodA : Localization.Away (algebraMap S A f) →+*
      Localization.Away ((algebraMap S A f) * algebraMap S A g) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((algebraMap S A f) * algebraMap S A g))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away ((algebraMap S A f) * algebraMap S A g)) := ρprodA.toAlgebra
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  let coeff : Localization.Away (algebraMap S A f) :=
    algebraMap A (Localization.Away (algebraMap S A f)) (algebraMap S A g)
  have hpow :
      Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ) =
        Submonoid.powers coeff := by
    simpa [Qf, uQ, eQuot, coeff] using
      (final_away_target_quotient_map_powers
        (R := S)
        (S := A)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj)
  have hprod : IsLocalization.Away coeff
      (Localization.Away ((algebraMap S A f) * algebraMap S A g)) := by
    -- Proof comment: the target-side iterated away chart is first normalized to the product
    -- denominator chart before comparing it with the pipeline's final chart.
    simpa [coeff] using
      (final_away_target_chart_isLocalization_product
        (R := S)
        (S := A)
        (f := f)
        (g := g))
  letI : IsLocalization.Away coeff
      (Localization.Away ((algebraMap S A f) * algebraMap S A g)) := hprod
  let eProd : Localization.Away coeff ≃ₐ[Localization.Away (algebraMap S A f)]
      Localization.Away ((algebraMap S A f) * algebraMap S A g) :=
    Localization.algEquiv (Submonoid.powers coeff)
      (Localization.Away ((algebraMap S A f) * algebraMap S A g))
  let eMul : Localization.Away ((algebraMap S A f) * algebraMap S A g) ≃ₐ[
      Localization.Away (algebraMap S A f)] Localization.Away (algebraMap S A fg) :=
    final_away_target_product_to_mul_transport
      (R := S)
      (S := A)
      (f := f)
      (g := g)
  have hloc : IsLocalization (Submonoid.powers coeff)
      (Localization.Away (algebraMap S A fg)) := by
    -- Proof comment: transport the owner localization from the product denominator chart to the
    -- actual final-away target chart.
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers coeff) (eProd.trans eMul)
  -- Proof comment: after identifying the mapped powers with powers of the target coefficient,
  -- the target final chart is the desired localization of the first-away quotient.
  dsimp only
  rw [hpow]
  exact hloc

/-- Helper for Chap10 Lemma 10 126 7: the final target chart is the canonical localization of the
first-away quotient over the quotient ring itself. -/
private noncomputable abbrev final_away_target_localization_algEquiv_over_quotient
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    letI : Algebra Qf (Localization.Away (algebraMap S A f)) := eQuot.toAlgHom.toAlgebra
    letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
      (ρfgA.comp eQuot.toRingHom).toAlgebra
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    Localization.Away uQ ≃ₐ[Qf]
      Localization.Away (algebraMap S A fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  have hmapped :
      IsLocalization
        (Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, Qf, uQ, eQuot, ρfgA] using
      (final_away_target_isLocalization_mapped_powers
        (S := S)
        (A := A)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj)
  letI :
      IsLocalization
        (Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (Localization.Away (algebraMap S A fg)) := hmapped
  have haway : IsLocalization.Away uQ (Localization.Away (algebraMap S A fg)) := by
    -- Proof comment: move the localization structure back across the quotient equivalence so the
    -- owner `Localization.algEquiv` can be used directly over the quotient chart.
    simpa [IsLocalization.Away] using
      (IsLocalization.of_ringEquiv_left (K := Localization.Away (algebraMap S A fg))
        (e := eQuot.toRingEquiv)
        (M₁ := Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (M₂ := Submonoid.powers uQ)
        rfl (fun x ↦ rfl))
  letI : IsLocalization.Away uQ (Localization.Away (algebraMap S A fg)) := haway
  -- Proof comment: after installing the owner localization instance over `Qf`, the canonical
  -- localization equivalence yields the target-side comparison map.
  dsimp only
  exact Localization.algEquiv (Submonoid.powers uQ)
    (Localization.Away (algebraMap S A fg))

/-- Helper for Chap10 Lemma 10 126 7: forgetting scalars from the quotient ring to the first away
chart turns the target-side quotient localization into an `S_f`-algebra equivalence. -/
private theorem final_away_target_isLocalizationAway
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
      (ρfgA.comp eQuot.toRingHom).toAlgebra
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    IsLocalization.Away uQ (Localization.Away (algebraMap S A fg)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  -- Route correction: package the target side first as a localization over `Qf`, and only then
  -- forget scalars back to `S_f`.
  exact
    IsLocalization.isLocalization_of_algEquiv
      (Submonoid.powers uQ)
      (final_away_target_localization_algEquiv_over_quotient
        (S := S)
        (A := A)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj)

/-- Helper for Chap10 Lemma 10 126 7: the target-side quotient localization is canonically
identified with the final target away chart as an algebra over the first away chart. -/
private noncomputable abbrev final_away_target_localization_algEquiv
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
      (ρfgA.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    Localization.Away uQ ≃ₐ[Localization.Away f]
      Localization.Away (algebraMap S A fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  let eQf :
      Localization.Away uQ ≃ₐ[Qf] Localization.Away (algebraMap S A fg) :=
    final_away_target_localization_algEquiv_over_quotient
      (S := S)
      (A := A)
      (n := n)
      (f := f)
      (g := g)
      πshift
      hπshiftSurj
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) (Localization.Away (algebraMap S A fg)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    calc
      eQf
          (algebraMap (Localization.Away f) (Localization.Away uQ)
            (algebraMap S (Localization.Away f) x)) =
        eQf
          (algebraMap Qf (Localization.Away uQ)
            (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
              (MvPolynomial.C (algebraMap S (Localization.Away f) x)))) := by
              rfl
      _ =
        algebraMap Qf (Localization.Away (algebraMap S A fg))
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
            (MvPolynomial.C (algebraMap S (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        ρfgA (πshift (MvPolynomial.C (algebraMap S (Localization.Away f) x))) := by
              exact congrArg ρfgA
                (Ideal.quotientKerAlgEquivOfSurjective_mk
                  (f := πshift)
                  hπshiftSurj
                  (MvPolynomial.C (algebraMap S (Localization.Away f) x))).symm
      _ =
        ρfgA
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f))
            (algebraMap S (Localization.Away f) x)) := by
              simp
      _ =
        algebraMap (Localization.Away f) (Localization.Away (algebraMap S A fg))
          (algebraMap S (Localization.Away f) x) := by
              rfl
  -- Proof comment: rebuilding the equivalence from the owner-side ring equivalence records the
  -- scalar compatibility once and avoids repeated transport through `restrictScalars`.
  exact
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }

/-- Helper for Chap10 Lemma 10 126 7: the target-side localization equivalence sends the class of
`ψ` to the final-away image `ρfgA (πshift ψ)`. -/
private theorem final_away_target_localization_algEquiv_apply_mk
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift)
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
      (ρfgA.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    final_away_target_localization_algEquiv
        (S := S)
        (A := A)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj
        (algebraMap Qf (Localization.Away uQ)
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
      ρfgA (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  let hloc :=
    final_away_target_localization_algEquiv_over_quotient
      (S := S)
      (A := A)
      (n := n)
      (f := f)
      (g := g)
      πshift
      hπshiftSurj
  -- Proof comment: the rebuilt `S_f`-linear equivalence has the same underlying ring map as the
  -- owner `Qf`-linear localization equivalence, so its computation is the owner `commutes` rule.
  dsimp only
  change hloc
      (algebraMap Qf (Localization.Away uQ)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
    ρfgA (πshift ψ)
  calc
    hloc
        (algebraMap Qf (Localization.Away uQ)
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
      algebraMap Qf (Localization.Away (algebraMap S A fg))
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ) := by
        rw [hloc.commutes]
    _ =
      ρfgA
        (eQuot (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) := by
        rfl
    _ = ρfgA (πshift ψ) := by
        exact congrArg ρfgA
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            (f := πshift)
            hπshiftSurj
            ψ)

/-- Helper for Chap10 Lemma 10 126 7: composing the source-side and target-side quotient
localization equivalences identifies each transported source polynomial class with its final-away
image under the shifted presentation. -/
private theorem final_away_comparison_algEquiv_apply_source_mk
    {n : ℕ} {f g : S}
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift)
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
      (Localization.awayMap (algebraMap S A) f).toAlgebra
    let fg : S := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away (algebraMap S A f))
        (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
      (ρfgA.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
    let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
      RingHom.ker πshift.toRingHom
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf :=
      Ideal.Quotient.mk K (MvPolynomial.C (algebraMap S (Localization.Away f) g))
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    let eSource :
        Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
      final_away_source_quotient_transport_algEquiv
        (R := S)
        (n := n)
        (f := f)
        (g := g)
        K
    let eTarget :
        Localization.Away uQ ≃ₐ[Localization.Away f]
          Localization.Away (algebraMap S A fg) :=
      final_away_target_localization_algEquiv
        (S := S)
        (A := A)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj
    (eSource.symm.trans eTarget)
        (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) =
      ρfgA (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap S A fg)
        (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
    RingHom.ker πshift.toRingHom
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
  let uQ : Qf :=
    Ideal.Quotient.mk K (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) K
  let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let eSource :
      Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    final_away_source_quotient_transport_algEquiv
      (R := S)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let eTarget :
      Localization.Away uQ ≃ₐ[Localization.Away f]
        Localization.Away (algebraMap S A fg) :=
    final_away_target_localization_algEquiv
      (S := S)
      (A := A)
      (n := n)
      (f := f)
      (g := g)
      πshift
      hπshiftSurj
  have hsource :
      eSource
          (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
        Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
    simpa [fg, ρfgR, K, Qf, uQ, Kfg, Tfg, eSource] using
      final_away_source_quotient_transport_algEquiv_apply_mk
        (R := S)
        (n := n)
        (f := f)
        (g := g)
        K
        ψ
  -- Proof comment: replace the target quotient class by its source-localization preimage, then
  -- compute the same class through the target-side localization equivalence.
  dsimp only
  rw [← hsource]
  calc
    (eSource.symm.trans eTarget)
        (eSource (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ))) =
      eTarget (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) := by
        simp
    _ = ρfgA (πshift ψ) := by
        simpa [fg, ρfgA, K, Qf, uQ, eTarget] using
          final_away_target_localization_algEquiv_apply_mk
            (S := S)
            (A := A)
            (n := n)
            (f := f)
            (g := g)
            πshift
            hπshiftSurj
            ψ

/-- Helper for Chap10 Lemma 10 126 7: once the final-away quotient comparison is identified with
the localized source quotient equivalence, the final shifted presentation is surjective and has
kernel equal to the span of the transported relations. -/
private theorem finalAwayShiftedPresentationSurjKer
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    {g : S}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Function.Surjective πshift)
    (relsFinal : Fin m → MvPolynomial (Fin n) (Localization.Away (f * g)))
    (hrelsFinalSpan :
      let fg : S := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom))
    (htransportedKernelLe :
      let fg : S := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
          (Localization.Away (algebraMap S A fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap S A fg)
                (Localization.Away (algebraMap S A fg)))
      let ρfgA : Localization.Away (algebraMap S A f) →+*
          Localization.Away (algebraMap S A fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap S A fg))
          (algebraMap S A f)
          (algebraMap S A g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap S A fg)) :=
        (Localization.awayMap (algebraMap S A) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap S A fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgA (πshift (MvPolynomial.X i)))
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom) :
    let fg : S := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
        (Localization.Away (algebraMap S A fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap S A fg)
              (Localization.Away (algebraMap S A fg)))
    let ρfgA : Localization.Away (algebraMap S A f) →+*
        Localization.Away (algebraMap S A fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap S A fg))
        (algebraMap S A f)
        (algebraMap S A g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap S A fg)) :=
      (Localization.awayMap (algebraMap S A) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
        (Localization.awayMap (algebraMap S A) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap S A fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgA (πshift (MvPolynomial.X i)))
    Function.Surjective πshiftFinal ∧
      RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
  -- Route correction: the remaining blocker is now isolated to one explicit bridge theorem on the
  -- already fixed data `ρfgR`, `ρfgA`, and `πshiftFinal`, rather than the earlier monolithic
  -- transport package.
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  let fg : S := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g)
      (Localization.Away (algebraMap S A fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap S A fg)
            (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g)
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap S A fg)) :=
    (Localization.awayMap (algebraMap S A) fg).toAlgebra
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap S A fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgA (πshift (MvPolynomial.X i)))
  let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
    RingHom.ker πshift.toRingHom
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
  let uQ : Qf :=
    Ideal.Quotient.mk K (MvPolynomial.C (algebraMap S (Localization.Away f) g))
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) K
  let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  let eSource :
      Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    final_away_source_quotient_transport_algEquiv
      (R := S)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra (Localization.Away (algebraMap S A f))
      (Localization.Away (algebraMap S A fg)) := ρfgA.toAlgebra
  letI : Algebra Qf (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp eQuot.toRingHom).toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A fg)) :=
    (ρfgA.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f)))).toAlgebra
  let eTarget :
      Localization.Away uQ ≃ₐ[Localization.Away f]
        Localization.Away (algebraMap S A fg) :=
    final_away_target_localization_algEquiv
      (S := S)
      (A := A)
      (n := n)
      (f := f)
      (g := g)
      πshift
      hπshiftSurj
  let e : Tfg ≃ₐ[Localization.Away f] Localization.Away (algebraMap S A fg) :=
    eSource.symm.trans eTarget
  let qComp :
      Tfg →ₐ[Localization.Away fg] Localization.Away (algebraMap S A fg) :=
    final_away_quotient_comparison
      (R := S)
      (S := A)
      (πshift := πshift)
      (f := f)
      (g := g)
      htransportedKernelLe
  have hmaps : e.toRingHom = qComp.toRingHom := by
    letI : IsLocalization.Away uQ Tfg :=
      final_away_source_quotient_isLocalizationAway
        (R := S) (n := n) (f := f) (g := g) K
    letI : IsLocalization.Away uQ (Localization.Away (algebraMap S A fg)) :=
      final_away_target_isLocalizationAway
        (S := S) (A := A) (n := n) (f := f) (g := g) πshift hπshiftSurj
    -- Proof comment: compare the two maps on the dense quotient `Qf`; the source-side transport
    -- and target-side localization formulas compute the same image on every representative.
    apply IsLocalization.ringHom_ext (Submonoid.powers uQ)
    ext ψ
    · simp only [RingHom.comp_apply]
      have hbase :
          algebraMap Qf Tfg (Ideal.Quotient.mk K (MvPolynomial.C ψ)) =
            Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ)) := by
        simpa [K, Qf, Kfg, Tfg] using
          final_away_source_quotient_algebraMap_apply_mk
            (R := S)
            (n := n)
            (f := f)
            (g := g)
            K
            (MvPolynomial.C ψ)
      rw [hbase]
      calc
        e (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ))) =
          ρfgA (πshift (MvPolynomial.C ψ)) := by
            simpa [K, Qf, uQ, Kfg, Tfg, eSource, eTarget, e] using
              final_away_comparison_algEquiv_apply_source_mk
                (S := S)
                (A := A)
                (n := n)
                (f := f)
                (g := g)
                πshift
                hπshiftSurj
                (MvPolynomial.C ψ)
        _ = qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ))) := by
            simpa [K, Qf, Kfg, Tfg, qComp] using
              (final_away_quotient_comparison_apply_mk
                (R := S)
                (S := A)
                (πshift := πshift)
                (f := f)
                (g := g)
                htransportedKernelLe
                (MvPolynomial.C ψ)).symm
    · simp only [RingHom.comp_apply]
      have hbase :
          algebraMap Qf Tfg (Ideal.Quotient.mk K (MvPolynomial.X ψ)) =
            Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ)) := by
        simpa [K, Qf, Kfg, Tfg] using
          final_away_source_quotient_algebraMap_apply_mk
            (R := S)
            (n := n)
            (f := f)
            (g := g)
            K
            (MvPolynomial.X ψ)
      rw [hbase]
      calc
        e (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ))) =
          ρfgA (πshift (MvPolynomial.X ψ)) := by
            simpa [K, Qf, uQ, Kfg, Tfg, eSource, eTarget, e] using
              final_away_comparison_algEquiv_apply_source_mk
                (S := S)
                (A := A)
                (n := n)
                (f := f)
                (g := g)
                πshift
                hπshiftSurj
                (MvPolynomial.X ψ)
        _ = qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ))) := by
            simpa [K, Qf, Kfg, Tfg, qComp] using
              (final_away_quotient_comparison_apply_mk
                (R := S)
                (S := A)
                (πshift := πshift)
                (f := f)
                (g := g)
                htransportedKernelLe
                (MvPolynomial.X ψ)).symm
  let eFg : Tfg ≃ₐ[Localization.Away fg] Localization.Away (algebraMap S A fg) :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro x
        calc
          e (algebraMap (Localization.Away fg) Tfg x) =
            qComp (algebraMap (Localization.Away fg) Tfg x) := by
              exact DFunLike.congr_fun hmaps (algebraMap (Localization.Away fg) Tfg x)
          _ = algebraMap (Localization.Away fg)
                (Localization.Away (algebraMap S A fg)) x := by
              exact qComp.commutes x }
  have he :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away fg),
        eFg (Ideal.Quotient.mk Kfg ψ) = πshiftFinal ψ := by
    intro ψ
    -- Proof comment: once the comparison map is identified with the quotient-descended final
    -- presentation, every quotient class is evaluated directly by `πshiftFinal`.
    calc
      eFg (Ideal.Quotient.mk Kfg ψ) =
        qComp (Ideal.Quotient.mk Kfg ψ) := by
          exact DFunLike.congr_fun hmaps (Ideal.Quotient.mk Kfg ψ)
      _ = πshiftFinal ψ := by
          rfl
  obtain ⟨hπsurj, hker⟩ :=
    surjective_and_kernel_span_of_quotient_comparison_algEquiv
      (π := πshiftFinal)
      (rels := relsFinal)
      (K := Kfg)
      hrelsFinalSpan
      eFg
      he
  -- Proof comment: the abstract quotient-comparison lemma now returns the exact surjectivity and
  -- kernel description needed by the shifted zero-section retraction step.
  exact ⟨hπsurj, hker⟩

/-- Helper for Chap10 Lemma 10 126 7: a finitely presented local isomorphism `S_q → A_qA`
spreads to a principal open carrying a zero-section retraction with finitely generated kernel. -/
private lemma exists_awayZeroSectionRetraction_of_bijectiveLocalRingHom
    (q : PrimeSpectrum S)
    {A : Type*} [CommRing A] [Algebra S A] [Algebra.FinitePresentation S A]
    (qA : PrimeSpectrum A)
    (hqA : qA.asIdeal.LiesOver q.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qA.asIdeal (algebraMap S A) hqA.over)) :
    ∃ f : { x : S // x ∉ q.asIdeal },
      letI : Algebra (Localization.Away f.1) (Localization.Away (algebraMap S A f.1)) :=
        (Localization.awayMap (algebraMap S A) f.1).toAlgebra
      ∃ σf : Localization.Away (algebraMap S A f.1) →ₐ[Localization.Away f.1]
          Localization.Away f.1,
        Function.LeftInverse σf
            (algebraMap (Localization.Away f.1) (Localization.Away (algebraMap S A f.1))) ∧
        (RingHom.ker σf.toRingHom).FG := by
  obtain ⟨n, π, hπsurj, hπkerfg⟩ := Algebra.FinitePresentation.out (R := S) (A := A)
  let localEquiv : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime qA.asIdeal :=
    RingEquiv.ofBijective
      (Localization.localRingHom q.asIdeal qA.asIdeal (algebraMap S A) hqA.over)
      hlocal
  let generatorPreimage : Fin n → Localization.AtPrime q.asIdeal := fun i ↦
    localEquiv.symm (algebraMap A (Localization.AtPrime qA.asIdeal) (π (MvPolynomial.X i)))
  have hgeneratorPreimage :
      ∀ i,
        (Localization.localRingHom q.asIdeal qA.asIdeal (algebraMap S A) hqA.over)
            (generatorPreimage i) =
          algebraMap A (Localization.AtPrime qA.asIdeal) (π (MvPolynomial.X i)) :=
    generator_preimage_maps_to_variable
      (R := S)
      (S := A)
      (p := q.asIdeal)
      (q := qA.asIdeal)
      hqA
      hlocal
      π
  obtain ⟨f, hf, a, ha⟩ :=
    exists_notMem_and_common_denominator_atPrime
      (R := S)
      (p := q.asIdeal)
      generatorPreimage
  obtain ⟨m, rels, hrels⟩ :
      ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) S,
        Ideal.span (Set.range rels) = RingHom.ker π.toRingHom := by
    -- Proof comment: fix one explicit finite relation family for the presentation kernel before
    -- transporting it through the localized shifted presentation.
    simpa using Submodule.fg_iff_exists_fin_generating_family.mp hπkerfg
  let ρR : Localization.Away f →+* Localization.AtPrime q.asIdeal :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q.asIdeal)) f
      (IsLocalization.map_units (Localization.AtPrime q.asIdeal) (⟨f, hf⟩ : q.asIdeal.primeCompl))
  have hfqA : algebraMap S A f ∉ qA.asIdeal := by
    intro hfqA
    exact hf <| by
      rw [hqA.over]
      simpa [Ideal.mem_comap] using hfqA
  let ρA : Localization.Away (algebraMap S A f) →+* Localization.AtPrime qA.asIdeal :=
    Localization.awayLift (algebraMap A (Localization.AtPrime qA.asIdeal)) (algebraMap S A f)
      (IsLocalization.map_units (Localization.AtPrime qA.asIdeal)
        ((⟨algebraMap S A f, hfqA⟩ : qA.asIdeal.primeCompl)))
  have hawaySquare :
      ρA.comp (Localization.awayMap (algebraMap S A) f) =
        (Localization.localRingHom q.asIdeal qA.asIdeal (algebraMap S A) hqA.over).comp ρR :=
    away_to_atPrime_square_commutes
      (R := S)
      (S := A)
      (p := q.asIdeal)
      (q := qA.asIdeal)
      hqA
      hf
  let u : Fin n → Localization.Away f :=
    let denom : Submonoid.powers f := ⟨f, ⟨1, by simp⟩⟩
    fun i ↦ IsLocalization.mk' (Localization.Away f) (a i) denom
  have hu : ∀ i, ρR (u i) = generatorPreimage i :=
    -- Proof comment: the first denominator-clearing step produces a tuple `u` in `S_f` whose
    -- stalk image is exactly the chosen inverse-local tuple of presentation generators.
    away_cleared_tuple_eq_generator_preimage
      (R := S)
      (p := q.asIdeal)
      (hf := hf)
      a
      generatorPreimage
      ha
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap S A f)) := by
        simpa using
          (inferInstance :
            IsLocalization.Away (algebraMap S A f) (Localization.Away (algebraMap S A f)))
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    (Localization.awayMap (algebraMap S A) f).toAlgebra
  letI : IsScalarTower S (Localization.Away f) (Localization.Away (algebraMap S A f)) :=
    away_localization_isScalarTower
      (R := S)
      (S := A)
      (f := f)
  have hπf :
      ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap S A f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
          (AlgHom.restrictScalars S
            (localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f).symm.toAlgHom)) =
        (AlgHom.restrictScalars S
          (MvPolynomial.aeval
            (fun i ↦
              algebraMap A (Localization.Away (algebraMap S A f))
                (π (MvPolynomial.X i))) :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                Localization.Away (algebraMap S A f))) := by
    -- Proof comment: transport the owner-side localized presentation to the explicit
    -- polynomial-over-`S_f` presentation on the current away chart.
    simpa using
      transported_away_presentation_eq_localized_aeval
        (R := S)
        (S := A)
        (π := π)
        (f := f)
  let πeval :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap A (Localization.Away (algebraMap S A f))
          (π (MvPolynomial.X i)))
  let πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap S A f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap A (Localization.Away (algebraMap S A f))
          (π (MvPolynomial.X i)) -
          algebraMap (Localization.Away f) (Localization.Away (algebraMap S A f))
            (u i))
  have hπshiftSub :
      πshift =
        πeval.comp
          (MvPolynomial.aeval (R := Localization.Away f)
            fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
    -- Proof comment: the shifted presentation is literally the translated localized presentation.
    simpa [πeval, πshift] using
      shifted_localized_presentation_eq_sub
        (v := fun i ↦
          algebraMap A (Localization.Away (algebraMap S A f))
            (π (MvPolynomial.X i)))
        (u := u)
  have hshiftX : ∀ i, ρA (πshift (MvPolynomial.X i)) = 0 := by
    -- Proof comment: under the chosen local inverse tuple, every shifted generator already
    -- vanishes in the target stalk `A_qA`.
    simpa [πshift, ρR, ρA] using
      shifted_localized_variables_vanish_at_q
        (R := S)
        (S := A)
        (p := q.asIdeal)
        (q := qA.asIdeal)
        hqA
        (hf := hf)
        π
        generatorPreimage
        hgeneratorPreimage
        u
        hu
  have hπtransportSurj :
      Function.Surjective
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap S A f)) π
            (MvPolynomial.C (σ := Fin n) f)).comp
            (AlgHom.restrictScalars S
              (localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f).symm.toAlgHom)) := by
    intro y
    obtain ⟨z, hz⟩ :=
      IsLocalization.Away.mapₐ_surjective_of_surjective
        (Aₚ := Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Bₚ := Localization.Away (algebraMap S A f))
        (f := π)
        (a := MvPolynomial.C (σ := Fin n) f)
        hπsurj
        y
    refine ⟨(localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f) z, ?_⟩
    -- Proof comment: the polynomial-localization equivalence preserves the preimage supplied by the
    -- surjective localized presentation map.
    change (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap S A f)) π
        (MvPolynomial.C (σ := Fin n) f))
        ((localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f).symm
          ((localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f) z)) = y
    have hz' :
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap S A f)) π
            (MvPolynomial.C (σ := Fin n) f))
          ((localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f).symm
            ((localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f) z)) =
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap S A f)) π
            (MvPolynomial.C (σ := Fin n) f)) z := by
      exact congrArg
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap S A f)) π
            (MvPolynomial.C (σ := Fin n) f)))
        ((localized_mvPolynomial_algEquiv_over_base (R := S) (n := n) f).symm_apply_apply z)
    exact hz'.trans hz
  have hπevalSurj : Function.Surjective πeval := by
    -- Proof comment: surjectivity transfers from the owner localized presentation to the explicit
    -- `S_f`-polynomial presentation once the two are identified by `hπf`.
    have hsurjS :
        Function.Surjective
          (AlgHom.restrictScalars S
            (MvPolynomial.aeval
              (fun i ↦
                algebraMap A (Localization.Away (algebraMap S A f))
                  (π (MvPolynomial.X i))) :
                MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                  Localization.Away (algebraMap S A f))) := by
      rw [← hπf]
      exact hπtransportSurj
    simpa [πeval] using hsurjS
  have hπshiftSurj : Function.Surjective πshift := by
    -- Proof comment: translating the polynomial variables by the fixed tuple `u` does not affect
    -- surjectivity of the localized presentation.
    exact surjective_shifted_presentation
      (πeval := πeval)
      hπevalSurj
      u
      πshift
      hπshiftSub
  obtain ⟨mShift, relsShift, hrelsShift, hconstShift⟩ :=
    exists_sign_aligned_shifted_kernel_family
      (R := S)
      (S := A)
      (p := q.asIdeal)
      (q := qA.asIdeal)
      hqA
      (hf := hf)
      (πeval := πeval)
      hπevalSurj
      u
      (πshift := πshift)
      hπshiftSub
      ρR
      ρA
      hawaySquare
      hlocal
      hshiftX
  obtain ⟨g₂, hg₂, hconstZero⟩ :=
    exists_notMem_zero_shifted_constants_after_second_shrink
      (R := S)
      (p := q.asIdeal)
      (hf := hf)
      (rels := relsShift)
      hconstShift
  let fg : S := f * g₂
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g₂
  letI : IsLocalization.Away ((algebraMap S A f) * algebraMap S A g₂)
      (Localization.Away (algebraMap S A fg)) := by
        simpa [fg, map_mul] using
          (inferInstance :
            IsLocalization.Away (algebraMap S A fg) (Localization.Away (algebraMap S A fg)))
  let ρfgA : Localization.Away (algebraMap S A f) →+*
      Localization.Away (algebraMap S A fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap S A fg))
      (algebraMap S A f)
      (algebraMap S A g₂)
  have hfinalAwaySquare :
      ρfgA.comp (Localization.awayMap (algebraMap S A) f) =
        (Localization.awayMap (algebraMap S A) fg).comp ρfgR := by
    -- Proof comment: the second shrink sits in the standard commuting away square, so the final
    -- chart comparison is a pure transport statement.
    simpa [fg, ρfgR, ρfgA] using
      final_away_square_commutes
        (R := S)
        (S := A)
        f
        g₂
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap S A fg)) :=
    (Localization.awayMap (algebraMap S A) fg).toAlgebra
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap S A fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgA (πshift (MvPolynomial.X i)))
  let relsFinal : Fin mShift → MvPolynomial (Fin n) (Localization.Away fg) :=
    fun j ↦ MvPolynomial.map ρfgR (relsShift j)
  have hrelsFinalConstZero :
      ∀ j, MvPolynomial.constantCoeff (relsFinal j) = 0 := by
    intro j
    -- Proof comment: the final-away constants vanish by the explicit choice of the second
    -- denominator `g₂`.
    dsimp [relsFinal]
    simpa [fg, ρfgR] using hconstZero j
  have hrelsFinalSpan :
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) := by
    -- Proof comment: the transported relation family is exactly the coefficient-wise image of the
    -- old shifted kernel family.
    simpa [fg, ρfgR, relsFinal] using
      final_away_relations_span_eq_map_shifted_kernel
        (R := S)
        (relsShift := relsShift)
        (K := RingHom.ker πshift.toRingHom)
        hrelsShift
  have hπshiftFinalMap :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away f),
        πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgA (πshift ψ) := by
    intro ψ
    -- Proof comment: transport the shifted presentation pointwise from `S_f` to the final chart
    -- `S_(fg)`.
    simpa [fg, ρfgR, ρfgA, πshiftFinal] using
      final_away_shifted_presentation_map
        (R := S)
        (S := A)
        (ψ := ψ)
        (πshift := πshift)
        (f := f)
        (g := g₂)
  have hrelsFinalSpanLe :
      Ideal.span (Set.range relsFinal) ≤ RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: every transported shifted relation still vanishes under the final-away
    -- presentation, so their span lands in the new kernel.
    refine Ideal.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with ⟨j, rfl⟩
    change πshiftFinal (relsFinal j) = 0
    have hrelShift : πshift (relsShift j) = 0 := by
      have hrelShiftMem : relsShift j ∈ RingHom.ker πshift.toRingHom := by
        rw [← hrelsShift]
        exact Ideal.subset_span (Set.mem_range_self j)
      simpa [RingHom.mem_ker] using hrelShiftMem
    calc
      πshiftFinal (relsFinal j) = ρfgA (πshift (relsShift j)) := by
        simpa [relsFinal] using hπshiftFinalMap (relsShift j)
      _ = 0 := by simp [hrelShift]
  have htransportedKernelLe :
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: convert the vanishing of the transported relations into the mapped-kernel
    -- containment needed by the quotient comparison.
    rw [← hrelsFinalSpan]
    exact hrelsFinalSpanLe
  have hπshiftFinal :
      Function.Surjective πshiftFinal ∧
        RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
    -- Proof comment: the final-away transport is now packaged as a single comparison theorem, so
    -- the zero-section retraction step can continue exactly as in the source proof.
    simpa [fg, ρfgR, ρfgA, πshiftFinal] using
      finalAwayShiftedPresentationSurjKer
        (A := A)
        (n := n)
        (m := mShift)
        (f := f)
        (g := g₂)
        πshift
        hπshiftSurj
        relsFinal
        hrelsFinalSpan
        htransportedKernelLe
  obtain ⟨hπshiftFinalSurj, hπshiftFinalKer⟩ := hπshiftFinal
  obtain ⟨σfg, hσfg, hσfg_comp, hkerσfg⟩ :=
    shifted_zero_section_retraction_of_zero_constant_relations
      (πshift := πshiftFinal)
      hπshiftFinalSurj
      relsFinal
      hπshiftFinalKer.symm
      hrelsFinalConstZero
  let _ := hσfg_comp
  have hkerσfgFg : (RingHom.ker σfg.toRingHom).FG := by
    -- Proof comment: finite generation of the zero-section kernel follows formally from its
    -- description as the image of the variable ideal.
    exact
      kernel_fg_of_zero_section_retraction
        (A := Localization.Away fg)
        (B := Localization.Away (algebraMap S A fg))
        (n := n)
        (σ := σfg)
        (π := πshiftFinal)
        hkerσfg
  have hfg : fg ∉ q.asIdeal := by
    -- Proof comment: the final denominator is the product of two elements already chosen outside
    -- the prime `q`.
    exact (show q.asIdeal.IsPrime from inferInstance).mul_notMem hf hg₂
  refine ⟨⟨fg, hfg⟩, ?_⟩
  dsimp
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap S A fg)) :=
    (Localization.awayMap (algebraMap S A) fg).toAlgebra
  exact ⟨σfg, hσfg, hkerσfgFg⟩

/-- Helper for Chap10 Lemma 10 126 7: after descending to the ambient chart `A := S'_{g'}`, one
can choose a source denominator and construct a zero-section retraction on the resulting away
chart. -/
private lemma descendedChartZeroSectionRetraction
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap)) :
    ∃ f : { x : S // x ∉ q.asIdeal },
      let A := Localization.Away g'.1
      letI : Algebra S A := φ.toAlgebra
      letI : Algebra (Localization.Away f.1) (Localization.Away (algebraMap S A f.1)) :=
        (Localization.awayMap (algebraMap S A) f.1).toAlgebra
      ∃ σf : Localization.Away (algebraMap S A f.1) →ₐ[Localization.Away f.1]
          Localization.Away f.1,
        Function.LeftInverse σf
            (algebraMap (Localization.Away f.1) (Localization.Away (algebraMap S A f.1))) ∧
        (RingHom.ker σf.toRingHom).FG := by
  let A := Localization.Away g'.1
  letI : Algebra S A := φ.toAlgebra
  letI : Algebra.FinitePresentation S A :=
    finitePresentation_of_baseChangeTarget (R := R) (S := S)
  have hqA : qg'.asIdeal.LiesOver q.asIdeal := ⟨by simpa using hcomap⟩
  have hlocal' :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal (algebraMap S A) hqA.over) := by
    simpa using hlocal
  -- Proof comment: after freezing the descended ambient chart as a finitely presented `S`-algebra,
  -- the generic denominator-clearing retraction lemma applies directly.
  exact
    exists_awayZeroSectionRetraction_of_bijectiveLocalRingHom
      (S := S)
      (q := q)
      (A := A)
      qg'
      hqA
      hlocal'

/-- Helper for Chap10 Lemma 10 126 7: the descended away chart admits a finite Zariski-main
subalgebra neighborhood whose localization at the tracked prime is already identified with
`S_q`. -/
private lemma descendedChartFiniteNeighborhood
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap)) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    ∃ (T : Subalgebra S A) (r : T),
      Module.Finite S T ∧ (r : A) ∉ qg'.asIdeal ∧
        Function.Bijective (Localization.awayMap T.val.toRingHom r) := by
  let A := Localization.Away g'.1
  letI : Algebra S A := φ.toAlgebra
  letI : Algebra.FinitePresentation S A := by
    exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S A
  have hqA : qg'.asIdeal.LiesOver q.asIdeal := ⟨hcomap⟩
  have hquasi : Algebra.QuasiFiniteAt S qg'.asIdeal :=
    quasiFiniteAt_of_bijective_localRingHom q.asIdeal qg'.asIdeal hqA hlocal
  -- Proof comment: once the descended chart is seen as a finitely presented `S`-algebra and the
  -- local ring map at `q` is bijective, the public quasi-finite neighborhood theorem produces the
  -- finite subalgebra basic open needed for the source-proof refinement step.
  exact
    currentAwayExistsFiniteSubalgebraAwayMapBijective qg' hquasi

/-- Helper for Chap10 Lemma 10 126 7: non-membership in the contracted source prime stays
non-membership after mapping into the descended away chart. -/
private lemma map_notMem_of_descendedPrimeComap
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    {g : S} (hg : g ∉ q.asIdeal) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    algebraMap S A g ∉ qg'.asIdeal := by
  dsimp
  -- Proof comment: membership upstairs contracts exactly to membership in `q`, so an element
  -- that avoids `q` cannot land inside the lifted prime `qg'`.
  intro hmem
  have hmem' : g ∈ Ideal.comap φ.toRingHom qg'.asIdeal := by
    change φ g ∈ qg'.asIdeal
    exact hmem
  rw [← hcomap] at hmem'
  exact hg hmem'

/-- Helper for Chap10 Lemma 10 126 7: once the transported prime on
`Spec(Localization.Away g.1 × C)` is explicitly known to lie on the left branch, the pulled-back
first-factor idempotent avoids the lifted prime. -/
private lemma firstFactorIdempotent_not_mem_of_transportedLeftBranch
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (g : { x : S // x ∉ q.asIdeal }) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
      (Localization.awayMap (algebraMap S A) g.1).toAlgebra
    ∀ {C : Type*} [CommRing C] [Algebra (Localization.Away g.1) C]
      (eProd : Localization.Away (algebraMap S A g.1) ≃ₐ[Localization.Away g.1]
        (Localization.Away g.1 × C))
      (qLift : PrimeSpectrum (Localization.Away (algebraMap S A g.1)))
      (hLeft :
        ∃ qBase : PrimeSpectrum (Localization.Away g.1),
          PrimeSpectrum.comap eProd.symm.toRingHom qLift =
            (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).symm (Sum.inl qBase)),
      eProd.symm ((1 : Localization.Away g.1), (0 : C)) ∉ qLift.asIdeal := by
  dsimp
  let A := Localization.Away g'.1
  letI : Algebra S A := φ.toAlgebra
  intro C _ _ eProd qLift hLeft
  obtain ⟨qBase, hqBase⟩ := hLeft
  exact
    firstFactorIdempotent_not_mem_of_refinedProduct
      (A := Localization.Away g.1)
      (B := Localization.Away (algebraMap S A g.1))
      (C := C)
      eProd
      qBase
      qLift
      hqBase

/-- Helper for Chap10 Lemma 10 126 7: a product decomposition of the descended away chart turns
the first factor into an iterated away localization, and that iterated denominator can then be
cleared back to an original element of the descended chart. -/
private lemma existsPositionedAwayEquivOfProductFactor
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (g : { x : S // x ∉ q.asIdeal }) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
      (Localization.awayMap (algebraMap S A) g.1).toAlgebra
    ∀ {C : Type (max v w)} [CommRing C] [Algebra (Localization.Away g.1) C],
      (Localization.Away (algebraMap S A g.1) ≃ₐ[Localization.Away g.1]
        (Localization.Away g.1 × C)) →
      ∃ u : { x : Localization.Away g'.1 // x ∉ qg'.asIdeal },
        Nonempty (Localization.Away g.1 ≃ₐ[R] Localization.Away u.1) := by
  dsimp
  let A := Localization.Away g'.1
  letI : Algebra S A := φ.toAlgebra
  letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
    (Localization.awayMap (algebraMap S A) g.1).toAlgebra
  intro C _ _ eProd
  let B := Localization.Away (algebraMap S A g.1)
  have hgA : algebraMap S A g.1 ∉ qg'.asIdeal :=
    map_notMem_of_descendedPrimeComap q q' φ qg' hcomap g.2
  obtain ⟨qLift, hqLift⟩ := exists_primeSpectrum_away_comap_eq_of_notMem qg' hgA
  have hLeft :
      ∃ qBase : PrimeSpectrum (Localization.Away g.1),
        PrimeSpectrum.comap eProd.symm.toRingHom qLift =
          (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).symm (Sum.inl qBase) := by
    let qProd :=
      PrimeSpectrum.comap eProd.symm.toRingHom qLift
    let branch := (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C) qProd
    have hbaseComap :
        PrimeSpectrum.comap
            (algebraMap (Localization.Away g.1) (Localization.Away g.1 × C))
            qProd =
          PrimeSpectrum.comap (algebraMap (Localization.Away g.1) B) qLift := by
      dsimp [qProd]
      rw [← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext x
      exact eProd.symm.commutes x
    rcases hbranch : branch with qBase | qC
    · refine ⟨qBase, ?_⟩
      refine (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).injective ?_
      simpa [branch, hbranch, qProd] using
        (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).apply_symm_apply (Sum.inl qBase)
    · have hqProdRight :
          qProd =
            (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).symm (Sum.inr qC) := by
        refine (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).injective ?_
        simpa [branch, hbranch, qProd] using
          (PrimeSpectrum.primeSpectrumProd (Localization.Away g.1) C).apply_symm_apply (Sum.inr qC)
      have hmemProd :
          ((1 : Localization.Away g.1), (0 : C)) ∈ qProd.asIdeal := by
        rw [hqProdRight]
        exact
          firstFactorIdempotent_mem_of_productPrimeRight
            (A := Localization.Away g.1)
            (C := C)
            qC
      have hmemBase :
          (1 : Localization.Away g.1) ∈
            (PrimeSpectrum.comap (algebraMap (Localization.Away g.1) B) qLift).asIdeal := by
        have hmemBase' :
            algebraMap (Localization.Away g.1) (Localization.Away g.1 × C) 1 ∈ qProd.asIdeal := by
          simpa using hmemProd
        have hbaseComapIdeal :
            (PrimeSpectrum.comap
                (algebraMap (Localization.Away g.1) (Localization.Away g.1 × C))
                qProd).asIdeal =
              (PrimeSpectrum.comap (algebraMap (Localization.Away g.1) B) qLift).asIdeal := by
          simpa using congrArg PrimeSpectrum.asIdeal hbaseComap
        change
          (1 : Localization.Away g.1) ∈
            (PrimeSpectrum.comap
              (algebraMap (Localization.Away g.1) (Localization.Away g.1 × C))
              qProd).asIdeal at hmemBase'
        rw [hbaseComapIdeal] at hmemBase'
        exact hmemBase'
      have honeNotMem :
          (1 : Localization.Away g.1) ∉
            (PrimeSpectrum.comap (algebraMap (Localization.Away g.1) B) qLift).asIdeal := by
        simpa [Ideal.eq_top_iff_one] using
          (PrimeSpectrum.comap (algebraMap (Localization.Away g.1) B) qLift).2.ne_top
      exact (honeNotMem hmemBase).elim
  let b0 : B := eProd.symm ((1 : Localization.Away g.1), (0 : C))
  have hb0 :
      b0 ∉ qLift.asIdeal := by
    simpa [b0] using
      firstFactorIdempotent_not_mem_of_transportedLeftBranch
        q
        q'
        φ
        qg'
        hcomap
        g
        eProd
        qLift
        hLeft
  have hu :
      (algebraMap S A g.1 * (IsLocalization.Away.sec (algebraMap S A g.1) b0).1) ∉
        qg'.asIdeal := by
    simpa [b0] using
      notMem_original_away_of_iterated_away
        (R := R)
        (A := A)
        qg'
        hgA
        qLift
        hqLift
        hb0
  let u : { x : A // x ∉ qg'.asIdeal } :=
    ⟨algebraMap S A g.1 * (IsLocalization.Away.sec (algebraMap S A g.1) b0).1, hu⟩
  let σ : B →+* Localization.Away g.1 :=
    (RingHom.fst (Localization.Away g.1) C).comp eProd.toRingHom
  letI : Algebra B (Localization.Away g.1) := σ.toAlgebra
  have hfirstFactorLocalization :
      IsLocalization.Away b0 (Localization.Away g.1) := by
    letI : Algebra (Localization.Away g.1 × C) (Localization.Away g.1) :=
      (RingHom.fst (Localization.Away g.1) C).toAlgebra
    letI :
        IsLocalization.Away (((1 : Localization.Away g.1), (0 : C)) : Localization.Away g.1 × C)
          (Localization.Away g.1) :=
      prodFst_isLocalizationAwayOneZero (B := Localization.Away g.1) (C := C)
    exact
      IsLocalization.of_ringEquiv_left
        (K := Localization.Away g.1)
        eProd.toRingEquiv
        (M₁ := Submonoid.powers (((1 : Localization.Away g.1), (0 : C)) : Localization.Away g.1 × C))
        (M₂ := Submonoid.powers b0)
        (by simpa [b0] using
          (Submonoid.map_powers eProd.toRingEquiv.toMonoidHom b0))
        (fun x ↦ rfl)
  letI : IsLocalization.Away b0 (Localization.Away g.1) := hfirstFactorLocalization
  let eRecover : Localization.Away g.1 ≃ₐ[R] Localization.Away u.1 := by
    classical
    let eSingle :=
      Classical.choice <|
        singleOriginalAwayAlgEquiv
        (R := R)
        (A := A)
        (algebraMap S A g.1)
        b0
    exact
      (AlgEquiv.restrictScalars R
        ((Localization.algEquiv (Submonoid.powers b0) (Localization.Away g.1)).symm)).trans eSingle
  exact ⟨u, ⟨eRecover⟩⟩

/-- Helper for Chap10 Lemma 10 126 7: on the first away chart of the descended target, a
zero-section retraction with finitely generated kernel and projective quotient already gives the
required product decomposition. -/
private lemma descendedChartPureKernelNeighborhood
    (q : PrimeSpectrum S)
    {A : Type*} [CommRing A] [Algebra S A]
    (f : { x : S // x ∉ q.asIdeal }) :
    letI : Algebra (Localization.Away f.1) (Localization.Away (algebraMap S A f.1)) :=
      (Localization.awayMap (algebraMap S A) f.1).toAlgebra
    ∀ (σf : Localization.Away (algebraMap S A f.1) →ₐ[Localization.Away f.1]
        Localization.Away f.1)
      (hσf :
        Function.LeftInverse σf
          (algebraMap (Localization.Away f.1) (Localization.Away (algebraMap S A f.1))))
      (hkerσfFg : (RingHom.ker σf.toRingHom).FG),
      ∃ (C : Type (max v w)) (_ : CommRing C) (_ : Algebra (Localization.Away f.1) C),
        Nonempty
          (Localization.Away (algebraMap S A f.1) ≃ₐ[Localization.Away f.1]
            (Localization.Away f.1 × C)) := by
  dsimp
  letI : Algebra (Localization.Away f.1) (Localization.Away (algebraMap S A f.1)) :=
    (Localization.awayMap (algebraMap S A) f.1).toAlgebra
  intro σf hσf hkerσfFg
  let hkerPure :
      (RingHom.ker σf.toRingHom).Pure :=
    idealPure_of_kernelQuotientRetraction
      (R := S)
      (A := A)
      (f := f.1)
      σf
      hσf
  -- Proof comment: the quotient is already projective over the base away ring, so its kernel is
  -- pure; combining purity with finite generation is exactly the split-product input from
  -- Lemma 10.126.6.
  exact
    awayProductDecomposition_of_pureKernel_ulift
      (A := Localization.Away f.1)
      (B := Localization.Away (algebraMap S A f.1))
      σf
      hσf
      hkerPure
      hkerσfFg

/-- Helper for Chap10 Lemma 10 126 7: after descending the target localization chart
`φ : S → A`, specialize the Lemma 10.126.6 product-decomposition mechanism directly to
`S → A` instead of detouring through an auxiliary finite subalgebra chart. -/
private lemma descendedChartAmbientProductDecomposition
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap)) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    ∃ g : { x : S // x ∉ q.asIdeal },
      letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
        (Localization.awayMap (algebraMap S A) g.1).toAlgebra
      ∃ (C : Type (max v w)),
      ∃ _ : CommRing C,
      ∃ _ : Algebra (Localization.Away g.1) C,
        Nonempty
          (Localization.Away (algebraMap S A g.1) ≃ₐ[Localization.Away g.1]
            (Localization.Away g.1 × C)) := by
  let A := Localization.Away g'.1
  letI : Algebra S A := φ.toAlgebra
  obtain ⟨g, σg, hσg, hkerσgFg⟩ :=
    descendedChartZeroSectionRetraction q q' φ qg' hcomap hlocal
  letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
    (Localization.awayMap (algebraMap S A) g.1).toAlgebra
  obtain ⟨C, hC, hAlgC, heProd⟩ :=
    descendedChartPureKernelNeighborhood
      (q := q)
      (A := A)
      g
      σg
      hσg
      hkerσgFg
  exact ⟨g, C, hC, hAlgC, heProd⟩

/-- Helper for Chap10 Lemma 10 126 7: after descending the target localization chart
`φ : S → A`, specialize the Lemma 10.126.6 product-decomposition mechanism directly to
`S → A` instead of detouring through an auxiliary finite subalgebra chart. -/
private lemma existsAwayProductDecompositionOfDescendedLocalIso
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap)) :
    let A := Localization.Away g'.1
    letI : Algebra S A := φ.toAlgebra
    ∃ g : { x : S // x ∉ q.asIdeal },
      letI : Algebra (Localization.Away g.1) (Localization.Away (algebraMap S A g.1)) :=
        (Localization.awayMap (algebraMap S A) g.1).toAlgebra
      ∃ (C : Type (max v w)),
      ∃ _ : CommRing C,
      ∃ _ : Algebra (Localization.Away g.1) C,
        Nonempty
          (Localization.Away (algebraMap S A g.1) ≃ₐ[Localization.Away g.1]
            (Localization.Away g.1 × C)) := by
  -- Proof comment: this wrapper is exactly the ambient chart product decomposition proved just
  -- above, so no further refinement is needed here.
  exact descendedChartAmbientProductDecomposition q q' φ qg' hcomap hlocal

/-- Helper for Chap10 Lemma 10 126 7: once the descended chart has a bijective local ring map at
the tracked prime, one can refine to a source principal open that is isomorphic to an iterated
away localization of the target chart. -/
private lemma exists_iteratedAwayAlgEquiv_of_bijective_localRingHom
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    {g' : { x : S' // x ∉ q'.asIdeal }}
    (φ : S →ₐ[R] Localization.Away g'.1)
    (qg' : PrimeSpectrum (Localization.Away g'.1))
    (hcomap : q.asIdeal = Ideal.comap φ.toRingHom qg'.asIdeal)
    (hlocal :
      Function.Bijective
        (Localization.localRingHom q.asIdeal qg'.asIdeal φ.toRingHom hcomap)) :
    ∃ g : { x : S // x ∉ q.asIdeal },
      ∃ u : { x : Localization.Away g'.1 // x ∉ qg'.asIdeal },
        Nonempty (Localization.Away g.1 ≃ₐ[R] Localization.Away u.1) :=
  by
  -- Proof comment: first obtain the product decomposition on a source basic open of the descended
  -- chart, then isolate the first factor as an iterated away localization and clear the remaining
  -- denominator back to an original element of `Localization.Away g'.1`.
  obtain ⟨g, C, _, _, heProd⟩ :=
    existsAwayProductDecompositionOfDescendedLocalIso q q' φ qg' hcomap hlocal
  obtain ⟨eProd⟩ := heProd
  have hPositioned :
      ∃ u : { x : Localization.Away g'.1 // x ∉ qg'.asIdeal },
        Nonempty (Localization.Away g.1 ≃ₐ[R] Localization.Away u.1) :=
    existsPositionedAwayEquivOfProductFactor q q' φ qg' hcomap g eProd
  obtain ⟨u, hu⟩ := hPositioned
  exact ⟨g, u, hu⟩

/-- Chap10 Lemma 10 126 7

Let `R` be a ring. Let `S` and `S'` be of finite presentation over `R`. Let `q ⊂ S` and
`q' ⊂ S'` be primes. If `S_q ≅ S'_{q'}` as `R`-algebras, then there exist `g ∈ S`, `g ∉ q`
and `g' ∈ S'`, `g' ∉ q'` such that `S_g ≅ S'_{g'}` as `R`-algebras. -/
@[stacks 00QS]
theorem exists_awayAlgEquiv_of_localizationAtPrime_algEquiv
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    (h :
      Localization.AtPrime q.asIdeal ≃ₐ[R]
        Localization.AtPrime q'.asIdeal) :
    ∃ g : { x : S // x ∉ q.asIdeal },
      ∃ g' : { x : S' // x ∉ q'.asIdeal },
        Nonempty (Localization.Away g.1 ≃ₐ[R] Localization.Away g'.1) := by
  -- Proof comment: first descend the stalk equivalence to one target principal-open chart and a
  -- lifted prime over `q'`, then refine that chart to a source principal open, and finally clear
  -- the remaining iterated target denominator back to an original element of `S'`.
  obtain ⟨g', φ, qg', hcomap, hqg', hlocal⟩ :=
    exists_descendedAwayAlgHom_of_localizationAtPrime_algEquiv q q' h
  obtain ⟨g, u, heIter⟩ :=
    exists_iteratedAwayAlgEquiv_of_bijective_localRingHom q q' φ qg' hcomap hlocal
  obtain ⟨eIter⟩ := heIter
  have hSingle :
      let h' : S' := g'.1 * (IsLocalization.Away.sec g'.1 u.1).1
      Nonempty (Localization.Away u.1 ≃ₐ[R] Localization.Away h') :=
    singleOriginalAwayAlgEquiv g'.1 u.1
  obtain ⟨eSingle⟩ := hSingle
  let h' : S' := g'.1 * (IsLocalization.Away.sec g'.1 u.1).1
  have hh' : h' ∉ q'.asIdeal :=
    notMem_original_away_of_iterated_away
      (R := R)
      (A := S')
      q'
      g'.2
      qg'
      hqg'
      u.2
  exact ⟨g, ⟨h', hh'⟩, ⟨eIter.trans eSingle⟩⟩

end
