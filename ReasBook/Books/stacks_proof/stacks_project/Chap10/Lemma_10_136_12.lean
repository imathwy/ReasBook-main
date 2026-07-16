import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Definition_10_135_1
import stacks_proof.stacks_project.Chap10.Lemma_10_52_13
import stacks_proof.stacks_project.Chap10.Lemma_10_112_6
import stacks_proof.stacks_project.Chap10.Lemma_10_23_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_6
import stacks_proof.stacks_project.Chap10.Lemma_10_69_2
import stacks_proof.stacks_project.Chap10.Lemma_10_8_8
import stacks_proof.stacks_project.Chap10.Lemma_10_99_3
import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.QuotientLocalization
import stacks_proof.stacks_project.Chap10.Lemma_10_135_4
import stacks_proof.stacks_project.Chap10.Lemma_10_136_9
import stacks_proof.stacks_project.Chap10.Lemma_10_136_11
import Mathlib.RingTheory.Ideal.Cotangent

noncomputable section

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ}
variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))
local notation "PolynomialRing" => MvPolynomial (Fin n) R
local notation "PresentedFreeModule" => Fin c → PresentedAlgebra

/-- Helper for Chap10 Lemma 10 136 12: the source-faithful fiber-dimension condition
`ringKrullDim (κ(p) ⊗[R] S) + c = n` implies the imported presentation-level
`IsRelativeGlobalCompleteIntersection` predicate, whose dimension owner is the truncated natural
number `n - c`. -/
private theorem sourceFiberDimension_to_relativeGciPresentation
    (hc : c ≤ n)
    (hPdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
        ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n) :
    Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation := by
  have _ := hc
  intro p hp
  have hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n := hPdim p hp
  calc
    ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) =
        (ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c) - c := by
          exact (Nat.add_sub_cancel_right (ringKrullDim (p.asIdeal.Fiber PresentedAlgebra)) c).symm
    _ = n - c := by rw [hdim]
    _ = PresentedPresentation.dimension := by
          simp [Algebra.Presentation.dimension]

/-- Helper for Chap10 Lemma 10 136 12: expose the quotient ring as a module over itself so the
free rank-`c` source elaborates without expensive instance search. -/
@[reducible] noncomputable instance presentedAlgebra_selfModule :
    Module PresentedAlgebra PresentedAlgebra :=
  Semiring.toModule

/-- Helper for Chap10 Lemma 10 136 12: after localizing at `q'`, the extension of the maximal
ideal of `R_(q' ∩ R)` agrees with the localized ideal `(q' ∩ R) (R[x₁, …, xₙ])_{q'}`. -/
private theorem localClosedFiberAtPrimeIdeal_eq
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : Ideal R := q'.asIdeal.under R
    let A := Localization.AtPrime q'.asIdeal
    Ideal.map (algebraMap (Localization.AtPrime p) A)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
      Ideal.map (algebraMap R A) p := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let p : Ideal R := q'.asIdeal.under R
  let A := Localization.AtPrime q'.asIdeal
  -- Proof comment: rewrite the maximal ideal of `R_p` inside `A` as the extension `pA`.
  simpa [p, A] using
    localized_base_prime_eq_map_maximalIdeal
      (R := R) (S := PolynomialRing) p q'.asIdeal (Ideal.over_under q'.asIdeal)

/-- Helper for Chap10 Lemma 10 136 12: base changing a relative-global-complete-intersection
presentation to a residue field produces a global complete intersection on that fiber. -/
private theorem fiber_isGlobalCompleteIntersection_of_relativeGciPresentation
    (hc : c ≤ n)
    (hPdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
        ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n)
    (p : PrimeSpectrum R) :
    IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber PresentedAlgebra) := by
  let P : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c) := PresentedPresentation
  have hP :
      Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation :=
    sourceFiberDimension_to_relativeGciPresentation
      (R := R) (n := n) (c := c) (f := f) hc hPdim
  by_cases hsub : Subsingleton (p.asIdeal.Fiber PresentedAlgebra)
  · letI : Subsingleton (p.asIdeal.Fiber PresentedAlgebra) := hsub
    exact inferInstance
  · -- Proof comment: the relative-GCI dimension formula on the chosen presentation is exactly
    -- the field-side global-CI dimension formula after base change to `κ(p)`.
    refine ⟨Or.inr ?_⟩
    refine ⟨n, c, P.baseChange p.asIdeal.ResidueField, ?_⟩
    have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mpr (not_subsingleton_iff_nontrivial.mp hsub)
    calc
      ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = P.dimension := by
        exact hP p hp_nonempty
      _ = (P.baseChange p.asIdeal.ResidueField).dimension := by
        simp [Algebra.Presentation.dimension]

/-- Helper for Chap10 Lemma 10 136 12: every prime of the fiber ring has a trivial global-CI
neighborhood once the full fiber ring is a global complete intersection. -/
private theorem fiber_isGlobalCompleteIntersectionNearPrime
    (hc : c ≤ n)
    (hPdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
        ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n)
    (p : PrimeSpectrum R) (qF : PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) :
    PolynomialPresentationAtPrime.isGlobalCompleteIntersectionNearPrime
      p.asIdeal.ResidueField qF := by
  letI : IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber PresentedAlgebra) :=
    fiber_isGlobalCompleteIntersection_of_relativeGciPresentation
      (R := R) (n := n) (c := c) (f := f) hc hPdim p
  -- Proof comment: for a globally complete-intersection fiber, the basic open `D(1)` already
  -- covers the chosen prime.
  refine ⟨1, ?_, inferInstance⟩
  simp

/-- Helper for Chap10 Lemma 10 136 12: the literal closed fiber of
`R_(q' ∩ R) → (R[x₁, …, xₙ])_{q'}` is canonically the quotient by the extended prime ideal
`(q' ∩ R) (R[x₁, …, xₙ])_{q'}`. -/
private noncomputable def localClosedFiberAtPrimeQuotientRingEquiv
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : Ideal R := q'.asIdeal.under R
    let A := Localization.AtPrime q'.asIdeal
    ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).Fiber A) ≃ₐ[A]
      (A ⧸ Ideal.map (algebraMap R A) p) :=
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let p : Ideal R := q'.asIdeal.under R
  let A := Localization.AtPrime q'.asIdeal
  -- Proof comment: transport the canonical quotient model of the closed fiber along the ideal
  -- equality `maximalIdeal(R_p) A = pA`.
  ((closedFiber_quotient_equiv
    (A := Localization.AtPrime p) (B := A)).symm).trans
    (Ideal.quotientEquivAlgOfEq A (localClosedFiberAtPrimeIdeal_eq (R := R) (n := n) (c := c)
      (f := f) q))

/-- Helper for Chap10 Lemma 10 136 12: elements of `pS` vanish in the fiber ring
`κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map_at_under
    {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  let φ : (R ⧸ p.asIdeal) ⊗[R] S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x :
        S ⧸ Ideal.map (algebraMap R S) p.asIdeal) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
    have hx' :
        e (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x) =
          (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x := rfl
    rw [← hx', hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p.asIdeal) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  -- Proof comment: the quotient class `x mod pS` is already zero, so its fiber image is zero.
  simpa [φ] using hφ

/-- Helper for Chap10 Lemma 10 136 12: the quotient `S / pS` acts canonically on the fiber ring
over `p`. -/
private noncomputable instance fiberQuotientAlgebraAtUnder
    {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    Algebra (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ (Ideal.map (algebraMap R S) p.asIdeal)
    (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map_at_under (R := R) p hx)).toRingHom.toAlgebra

/-- Helper for Chap10 Lemma 10 136 12: the class of `s : S` in `S / pS` maps to the pure tensor
`1 ⊗ s` in the fiber ring over `p`. -/
private theorem quotientToFiber_algebraMap_mk_at_under
    {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) (s : S) :
    algebraMap (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) s) =
        1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Chap10 Lemma 10 136 12: the quotient-base-changed fiber presentation recovers the
usual fiber ring over `p` as an algebra over `S / pS`. -/
private noncomputable def fiberTensorOverQuotientAlgEquivAtUnder
    {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ⊗[R ⧸ p.asIdeal] p.asIdeal.ResidueField ≃ₐ[
      S ⧸ Ideal.map (algebraMap R S) p.asIdeal] p.asIdeal.Fiber S :=
  let eRing :
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ⊗[R ⧸ p.asIdeal] p.asIdeal.ResidueField ≃+*
        p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.commRight (R ⧸ p.asIdeal)
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) p.asIdeal.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
            p.asIdeal.ResidueField)
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal)).trans
        (Algebra.TensorProduct.cancelBaseChange R (R ⧸ p.asIdeal) p.asIdeal.ResidueField
          p.asIdeal.ResidueField S)).toRingEquiv
  { toRingEquiv := eRing
    commutes' := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Proof comment: both quotient-side and tensor-side algebra maps send `s mod pS`
      -- to the same pure tensor `1 ⊗ s`.
      simpa [eRing, quotientToFiber_algebraMap_mk_at_under (R := R) p s,
        Algebra.TensorProduct.cancelBaseChange_tmul] }

/-- Helper for Chap10 Lemma 10 136 12: the fiber ring over `p` is the localization of `S / pS`
at the image of the nonzerodivisors of `R / p`. -/
private noncomputable def fiberQuotientLocalizationAlgEquivAtUnder
    {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    Localization
        (Algebra.algebraMapSubmonoid
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (nonZeroDivisors (R ⧸ p.asIdeal))) ≃ₐ[
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal)] p.asIdeal.Fiber S :=
  -- Proof comment: this is the standard presentation `(S / pS)[(R / p)^\times] ≃ κ(p) ⊗[R] S`.
  ((Localization.tensorLeftAlgEquiv
      (nonZeroDivisors (R ⧸ p.asIdeal))
      (S ⧸ Ideal.map (algebraMap R S) p.asIdeal)).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) ≃ₐ[
            S ⧸ Ideal.map (algebraMap R S) p.asIdeal]
              (S ⧸ Ideal.map (algebraMap R S) p.asIdeal))
        (IsLocalization.algEquiv
          (nonZeroDivisors (R ⧸ p.asIdeal))
          (Localization (nonZeroDivisors (R ⧸ p.asIdeal)))
          p.asIdeal.ResidueField))).trans
    (fiberTensorOverQuotientAlgEquivAtUnder (R := R) p)

/-- Helper for Chap10 Lemma 10 136 12: the quotient presentation `S_q / (q ∩ R)S_q` identifies
with the canonical fiber local ring at `q`. -/
private noncomputable def localizedQuotientRingEquivFiberLocalRingAt
    {S : Type*} [CommRing S] [Algebra R S] (q : PrimeSpectrum S) :
    ((Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) ≃+*
        fiberLocalRingAt R S q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let I : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- Proof comment: extending `p` to `S` and then localizing is the same as extending `p`
    -- directly to `S_q`.
    dsimp [I]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using
      (Ideal.map_map (I := p.asIdeal) (f := algebraMap R S)
        (g := algebraMap S (Localization.AtPrime q.asIdeal)))
  let eTarget :
      Qloc ≃+*
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) :=
    Ideal.quotEquivOfEq hQloc
  have hqbarPrime : (Ideal.map (Ideal.Quotient.mk I) q.asIdeal).IsPrime := by
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective <| by
        simpa [Ideal.mk_ker] using hI_le_q
  let qbar : PrimeSpectrum (S ⧸ I) :=
    ⟨Ideal.map (Ideal.Quotient.mk I) q.asIdeal, hqbarPrime⟩
  let M : Submonoid (S ⧸ I) := Algebra.algebraMapSubmonoid (S ⧸ I) q.asIdeal.primeCompl
  let eLoc :
      Localization M ≃ₐ[S ⧸ I] Qloc :=
    Localization.algEquiv M Qloc
  have hSub :
      M = qbar.asIdeal.primeCompl := by
    -- Proof comment: quotienting by `pS` turns `q` into the induced prime `q̄`.
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid_at_under I q.asIdeal hI_le_q
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl (Localization.AtPrime qbar.asIdeal))
  let eQuot :
      Qloc ≃ₐ[S ⧸ I] Localization.AtPrime qbar.asIdeal :=
    eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))
  let T : Submonoid (S ⧸ I) :=
    Algebra.algebraMapSubmonoid (S ⧸ I) (nonZeroDivisors (R ⧸ p.asIdeal))
  let eFiber :
      Localization T ≃ₐ[S ⧸ I] p.asIdeal.Fiber S :=
    fiberQuotientLocalizationAlgEquivAtUnder (R := R) (S := S) p
  let qT : PrimeSpectrum (Localization T) :=
    PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt R S q)
  have hI_le_q : I ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    simpa [I, p, PrimeSpectrum.comap_asIdeal]
  have hqTcomap :
      Ideal.comap (algebraMap (S ⧸ I) (Localization T)) qT.asIdeal = qbar.asIdeal := by
    -- Proof comment: the prime of the fiber ring corresponding to `q` contracts back to the
    -- induced quotient prime `q̄`.
    have hFiberComap :
        Ideal.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q).asIdeal =
          q.asIdeal := by
      have hleft :
          ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) = q := by
        simpa [p, fiberPrimeAt] using
          congrArg Subtype.val
            ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
      have hcomap :
          PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) = q := by
        calc
          PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q) =
              ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) := by
                change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                    (fiberPrimeAt R S q) =
                  ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q))
                rfl
          _ = q := hleft
      simpa using congrArg PrimeSpectrum.asIdeal hcomap
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
    rw [show
        eFiber.toRingHom.comp
            ((algebraMap (S ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) =
          algebraMap S (p.asIdeal.Fiber S) by
            ext s
            -- Proof comment: the quotient presentation and the canonical inclusion of `S`
            -- into the fiber ring agree on generators.
            calc
              eFiber.toRingHom
                  ((algebraMap (S ⧸ I) (Localization T)) (Ideal.Quotient.mk I s)) =
                  algebraMap (S ⧸ I) (p.asIdeal.Fiber S) (Ideal.Quotient.mk I s) := by
                    exact eFiber.commutes (Ideal.Quotient.mk I s)
              _ = algebraMap S (p.asIdeal.Fiber S) s := by
                    rw [quotientToFiber_algebraMap_mk_at_under (R := R) p]
                    rfl]
    simpa [qbar, I, Ideal.comap_map_mk hI_le_q] using
      hFiberComap
  let qbar' : PrimeSpectrum (S ⧸ I) :=
    PrimeSpectrum.comap (algebraMap (S ⧸ I) (Localization T)) qT
  let eSource :
      Localization.AtPrime qbar.asIdeal ≃+* Localization.AtPrime qbar'.asIdeal :=
    Localization.localRingEquiv qbar.asIdeal qbar'.asIdeal (RingEquiv.refl (S ⧸ I))
      (by simpa [qbar'] using hqTcomap.symm)
  let eTower :
      Localization.AtPrime qbar'.asIdeal ≃+* Localization.AtPrime qT.asIdeal :=
    -- Proof comment: localizing the quotient presentation again at the prime over `q̄`
    -- collapses the localization tower.
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := T) qT.asIdeal).toRingEquiv
  let eFiberLocal0 :
      Localization.AtPrime qT.asIdeal ≃+*
        Localization.AtPrime (fiberPrimeAt R S q).asIdeal :=
    -- Proof comment: localizing corresponding primes along the quotient-to-fiber equivalence
    -- recovers the canonical fiber local ring.
    Localization.localRingEquiv qT.asIdeal (fiberPrimeAt R S q).asIdeal eFiber.toRingEquiv
      (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt R S q))
  let eFiberLocal :
      Localization.AtPrime qT.asIdeal ≃+* fiberLocalRingAt R S q := by
    simpa [fiberLocalRingAt] using eFiberLocal0
  -- Proof comment: composing the quotient-localization comparison with the fiber presentation
  -- gives the canonical quotient model of the local fiber ring.
  simpa [p] using
    ((((eTarget.symm.trans eQuot.toRingEquiv).trans eSource).trans eTower).trans eFiberLocal)

/-- Helper for Chap10 Lemma 10 136 12: the literal closed fiber of
`R_(q' ∩ R) → (R[x₁, …, xₙ])_{q'}` matches the canonical fiber local ring of the polynomial ring
at `q'`. -/
private noncomputable def localClosedFiberAtPrimeRingEquivFiberLocalRingAt
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : Ideal R := q'.asIdeal.under R
    let A := Localization.AtPrime q'.asIdeal
    ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).Fiber A) ≃+*
      fiberLocalRingAt R PolynomialRing q' :=
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  -- Proof comment: first rewrite the literal closed fiber as `A / pA`, then use the canonical
  -- quotient presentation of the polynomial-ring fiber local ring.
  (localClosedFiberAtPrimeQuotientRingEquiv (R := R) (n := n) (c := c) (f := f) q).toRingEquiv.trans
    (localizedQuotientRingEquivFiberLocalRingAt (R := R) (S := PolynomialRing) q')

/-- Helper for Chap10 Lemma 10 136 12: under the quotient model of the literal closed fiber, the
class of `x : A` maps back to the canonical image of `x` in that closed fiber. -/
@[simp] private theorem localClosedFiberAtPrimeQuotientRingEquiv_symm_algebraMap
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : Ideal R := q'.asIdeal.under R
    let A := Localization.AtPrime q'.asIdeal
    ∀ x : A,
      (localClosedFiberAtPrimeQuotientRingEquiv (R := R) (n := n) (c := c) (f := f) q).symm
        (Ideal.Quotient.mk (Ideal.map (algebraMap R A) p) x) =
      algebraMap A ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).Fiber A) x := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let p : Ideal R := q'.asIdeal.under R
  let A := Localization.AtPrime q'.asIdeal
  intro x
  -- Proof comment: normalize the ideal-transport equivalence on quotient generators and then use
  -- the standard quotient description of the closed fiber.
  simp [localClosedFiberAtPrimeQuotientRingEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- Helper for Chap10 Lemma 10 136 12: after localizing the polynomial ring at `q'`, the mapped
presentation ideal is still the list ideal generated by the displayed relations. -/
private theorem mappedPresentedIdeal_eq_ofListAtPrime
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    Ideal.map (algebraMap PolynomialRing A) PresentedIdeal =
      Ideal.ofList ((List.ofFn f).map (algebraMap PolynomialRing A)) := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let A := Localization.AtPrime q'.asIdeal
  calc
    Ideal.map (algebraMap PolynomialRing A) PresentedIdeal =
        Ideal.span ((algebraMap PolynomialRing A) '' Set.range f) := by
      -- Proof comment: first rewrite the presentation ideal through its span-of-generators model.
      rw [Ideal.map_span]
    _ = Ideal.span (Set.range fun i : Fin c ↦ algebraMap PolynomialRing A (f i)) := by
      -- Proof comment: the image of the displayed family is exactly the range of the mapped family.
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    _ = Ideal.ofList ((List.ofFn f).map (algebraMap PolynomialRing A)) := by
      -- Proof comment: convert the `Fin`-indexed generating range back to the canonical list form.
      simp [Ideal.ofList, List.mem_ofFn', Set.range]

/-- Helper for Chap10 Lemma 10 136 12: the presentation ideal lies under the source prime `q'`
lying over a prime `q` of the quotient presentation. -/
private theorem presentedIdeal_le_sourcePrime
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    PresentedIdeal ≤ q'.asIdeal := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  intro x hx
  -- Proof comment: every presentation relation maps to zero in the quotient, hence lies in every
  -- prime lying over that quotient point.
  change Ideal.Quotient.mk PresentedIdeal x ∈ q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hx

/-- Helper for Chap10 Lemma 10 136 12: localizing the source polynomial ring at `q'` and then
contracting the mapped presentation ideal recovers the original presentation ideal. -/
private theorem comap_mappedPresentedIdeal_eq_presentedIdeal
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
    Ideal.comap (algebraMap PolynomialRing A) Kq = PresentedIdeal := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let A := Localization.AtPrime q'.asIdeal
  let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
  have hdisj : Disjoint q'.asIdeal.primeCompl PresentedIdeal := by
    -- Proof comment: an element of the presentation ideal cannot become a unit in the
    -- localization at a prime containing that ideal.
    refine Set.disjoint_left.mpr ?_
    intro x hxS hxI
    exact hxS ((presentedIdeal_le_sourcePrime (R := R) (n := n) (c := c) (f := f) q) hxI)
  -- Proof comment: this is the standard contraction-of-extension identity for ideals contained in
  -- the prime used for localization.
  simpa [A, Kq] using
    (IsLocalization.comap_map_of_isPrime_disjoint
      q'.asIdeal.primeCompl A (show q'.asIdeal.IsPrime by infer_instance) hdisj)

/-- Helper for Chap10 Lemma 10 136 12: the prime complement in the quotient presentation is the
image of the source-prime complement `q'ᶜ` under the quotient map. -/
private theorem presentedPrimeCompl_eq_sourceAlgebraMapSubmonoid
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    Algebra.algebraMapSubmonoid PresentedAlgebra q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  have hPresented_le_q' : PresentedIdeal ≤ q'.asIdeal :=
    presentedIdeal_le_sourcePrime (R := R) (n := n) (c := c) (f := f) q
  -- Proof comment: quotienting by the presentation ideal sends the source prime `q'` to the
  -- target prime `q`, so the corresponding localization submonoids agree.
  simpa [q', PresentedAlgebra] using
    quotient_primeCompl_eq_algebraMapSubmonoid_at_under
      PresentedIdeal q'.asIdeal hPresented_le_q'

/-- Helper for Chap10 Lemma 10 136 12: an ideal maps into the comap of its image ideal under an
algebra equivalence. -/
private theorem ideal_le_comap_mapAlgEquivLocal
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I ≤ Ideal.comap e.toAlgHom (I.map e.toRingHom) := by
  -- Proof comment: any element of `I` maps directly into the image ideal.
  intro x hx
  exact Ideal.mem_map_of_mem e.toRingHom hx

/-- Helper for Chap10 Lemma 10 136 12: the image ideal under an algebra equivalence maps back
into the original ideal under the inverse equivalence. -/
private theorem ideal_mapAlgEquiv_le_comapSymmLocal
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.map e.toRingHom ≤ Ideal.comap e.symm.toAlgHom I := by
  -- Proof comment: rewrite the image ideal through the inverse ring equivalence and read off the
  -- resulting comap inclusion.
  intro y hy
  change y ∈ Ideal.comap e.toRingEquiv.symm I
  rw [← Ideal.map_comap_of_equiv (I := I) e.toRingEquiv]
  exact hy

/-- Helper for Chap10 Lemma 10 136 12: an algebra equivalence transports the cotangent module of
an ideal to the cotangent module of its image ideal. -/
private noncomputable def cotangentEquivMapAlgEquivLocal
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent := by
  let forward :
      I.Cotangent →ₗ[R] (I.map e.toRingHom).Cotangent :=
    Ideal.mapCotangent I (I.map e.toRingHom) e
      (ideal_le_comap_mapAlgEquivLocal (R := R) e I)
  let backward :
      (I.map e.toRingHom).Cotangent →ₗ[R] I.Cotangent :=
    (I.map e.toRingHom).mapCotangent I e.symm
      (ideal_mapAlgEquiv_le_comapSymmLocal (R := R) e I)
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · -- Proof comment: verify the composite on cotangent generators of the image ideal.
    ext x
    obtain ⟨x, rfl⟩ := (I.map e.toRingHom).toCotangent_surjective x
    rw [LinearMap.comp_apply]
    unfold forward backward
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    apply (I.map e.toRingHom).toCotangent_eq.mpr
    simp
  · -- Proof comment: the reverse composite is checked on cotangent generators of the source
    -- ideal in the same way.
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    rw [LinearMap.comp_apply]
    unfold forward backward
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    apply I.toCotangent_eq.mpr
    simp

/-- Helper for Chap10 Lemma 10 136 12: the cotangent transport induced by an algebra equivalence
sends a cotangent generator to the corresponding generator of the image ideal. -/
private theorem cotangentEquivMapAlgEquivLocal_toCotangent
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) (x : I) :
    cotangentEquivMapAlgEquivLocal (R := R) e I (Ideal.toCotangent I x) =
      Ideal.toCotangent (I.map e.toRingHom) ⟨e x, Ideal.mem_map_of_mem e.toRingHom x.2⟩ := by
  -- Proof comment: unfold the transported cotangent equivalence and evaluate the forward
  -- `Ideal.mapCotangent` map on a distinguished generator.
  rfl

/-- Helper for Chap10 Lemma 10 136 12: localizing the conormal module at the source prime `q'`
rewrites to the literal quotient owner `I_{q'} / I_{q'} I_{q'}` in the localized polynomial ring. -/
private noncomputable def localizedPresentedCotangentQuotientAtPrime
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
    LocalizedModule.AtPrime q'.asIdeal (Ideal.Cotangent PresentedIdeal) ≃ₗ[A]
      (LocalizedModule.AtPrime q'.asIdeal PresentedIdeal ⧸
        (Kq • (⊤ : Submodule A (LocalizedModule.AtPrime q'.asIdeal PresentedIdeal)))) := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let A := Localization.AtPrime q'.asIdeal
  let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
  -- Proof comment: specialize the quotient-localization comparison to the ideal module itself.
  simpa [A, Kq, Ideal.Cotangent] using
    localized_quotient_equiv_mapped_ideal
      (R := PolynomialRing) (S := PolynomialRing) (M := PresentedIdeal)
      (I := PresentedIdeal) q'

/-- Helper for Chap10 Lemma 10 136 12: localizing the presentation ideal at the source prime `q'`
identifies the localized ideal module with the mapped ideal inside `(R[x₁, …, xₙ])_{q'}`. -/
private noncomputable def localizedPresentedIdealAtPrime
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
    LocalizedModule.AtPrime q'.asIdeal PresentedIdeal ≃ₗ[PolynomialRing] Kq := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let A := Localization.AtPrime q'.asIdeal
  let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
  -- Proof comment: specialize the standard ideal-localization owner bridge to the presentation
  -- ideal inside the polynomial ring, keeping the localized target as the literal mapped ideal.
  simpa [A, Kq] using
    localized_under_ideal_linearEquiv_mapped_ideal
      (R := PolynomialRing) (S := PolynomialRing) PresentedIdeal q'

/-- Helper for Chap10 Lemma 10 136 12: the localized-ideal owner bridge sends the localized class
of a presentation relation to the corresponding element of the mapped ideal. -/
@[simp] private theorem localizedPresentedIdealAtPrime_apply_mk
    (q : PrimeSpectrum PresentedAlgebra) (x : PresentedIdeal) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    localizedPresentedIdealAtPrime (R := R) (n := n) (c := c) (f := f) q
      (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl PresentedIdeal x) =
      Algebra.idealMap PresentedIdeal
        (S := Localization.AtPrime q'.asIdeal) x := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  -- Proof comment: both sides are the canonical image of `x` under the imported ideal-localization
  -- equivalence, so the statement is exactly the companion computation lemma from `10.99.11`.
  simpa [localizedPresentedIdealAtPrime] using
    localized_under_ideal_linearEquiv_mapped_ideal_apply_mk
      (R := PolynomialRing) (S := PolynomialRing) PresentedIdeal q' x

/-- Helper for Chap10 Lemma 10 136 12: the source-prime quotient-localization comparison sends
the localized cotangent class of a displayed relation to the localized numerator class in `I_{q'}`. -/
@[simp] private theorem localizedPresentedCotangentQuotientAtPrime_toCotangent
    (q : PrimeSpectrum PresentedAlgebra) (x : PresentedIdeal) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
    localizedPresentedCotangentQuotientAtPrime (R := R) (n := n) (c := c) (f := f) q
      (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl
        (Ideal.Cotangent PresentedIdeal) (Ideal.toCotangent PresentedIdeal x)) =
      Submodule.Quotient.mk
        (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl PresentedIdeal x) := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let A := Localization.AtPrime q'.asIdeal
  let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
  -- Proof comment: this is the generator formula built into the quotient-localization equivalence.
  simpa [A, Kq, Ideal.Cotangent] using
    localized_quotient_equiv_mapped_ideal_apply_mk
      (R := PolynomialRing) (S := PolynomialRing) (M := PresentedIdeal)
      (I := PresentedIdeal) q' x

/-- Helper for Chap10 Lemma 10 136 12: a ring equivalence transports a regular sequence to the
mapped coefficient list. -/
private theorem regularSequence_iff_map_regularSequence_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (rs : List A) :
    RingTheory.Sequence.IsRegular A rs ↔ RingTheory.Sequence.IsRegular B (rs.map e) := by
  -- Proof comment: regularity is stated on the regular module, so the ring equivalence only needs
  -- to preserve multiplication.
  refine e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  simpa [Algebra.smul_def] using e.map_mul a x

/-- Helper for Chap10 Lemma 10 136 12: localizing `R → R[x₁, …, xₙ]` at `p = q' ∩ R` and `q'`
gives a flat local map `R_p → (R[x₁, …, xₙ])_{q'}`. -/
private theorem localizedPolynomial_algebraMap_flat_local_atPrime
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R PolynomialRing) q'
    (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q'.asIdeal)).Flat ∧
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q'.asIdeal)) := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R PolynomialRing) q'
  have halg :
      Localization.localRingHom p.asIdeal q'.asIdeal (algebraMap R PolynomialRing)
          (q'.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q'.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      rw [← IsScalarTower.algebraMap_apply R PolynomialRing (Localization.AtPrime q'.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q'.asIdeal) x]
  have hflatPoly : (algebraMap R PolynomialRing).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q'.asIdeal)).Flat := by
    -- Proof comment: flatness survives localization along the canonical local ring map.
    simpa [halg] using
      (RingHom.Flat.localRingHom hflatPoly q'.asIdeal p.asIdeal (q'.asIdeal.over_def p.asIdeal))
  have hlocal :
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q'.asIdeal)) := by
    -- Proof comment: the universal localized map is local by construction.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q'.asIdeal
        (algebraMap R PolynomialRing) (q'.asIdeal.over_def p.asIdeal))
  exact ⟨hflat, hlocal⟩

/-- Helper for Chap10 Lemma 10 136 12: once the images of the displayed relations are regular in
the quotient closed fiber `A / pA`, Lemma `10.99.3` upgrades them to regularity in `A` and
flatness of every localized prefix quotient. -/
private theorem localizedRelationsRegularAndFlat_of_closedFiberRegular
    [IsNoetherianRing R]
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R PolynomialRing) q'
    let A := Localization.AtPrime q'.asIdeal
    let fsA := (List.ofFn f).map (algebraMap PolynomialRing A)
    RingTheory.Sequence.IsRegular
      (A ⧸ Ideal.map (algebraMap R A) p.asIdeal)
      (fsA.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) p.asIdeal))) →
    RingTheory.Sequence.IsRegular A fsA ∧
      ∀ i : Fin c, Module.Flat R (A ⧸ Ideal.ofList (fsA.take i.1.succ)) := by
  let q' : PrimeSpectrum PolynomialRing := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R PolynomialRing) q'
  let Rp := Localization.AtPrime p.asIdeal
  let A := Localization.AtPrime q'.asIdeal
  let fsA := (List.ofFn f).map (algebraMap PolynomialRing A)
  intro hclosed
  have hflatLocal :=
    localizedPolynomial_algebraMap_flat_local_atPrime (R := R) (n := n) (c := c) (f := f) q
  letI : Module.Flat Rp A := (RingHom.flat_algebraMap_iff).mp hflatLocal.1
  letI : IsLocalHom (algebraMap Rp A) := hflatLocal.2
  have heq :
      Ideal.map (algebraMap Rp A) (IsLocalRing.maximalIdeal Rp) =
        Ideal.map (algebraMap R A) p.asIdeal := by
    -- Proof comment: rewrite the maximal ideal of `R_p` inside `A` as the extension `pA`.
    simpa [Rp, A] using
      localized_base_prime_eq_map_maximalIdeal
        (R := R) (S := PolynomialRing) p.asIdeal q'.asIdeal (Ideal.over_under q'.asIdeal)
  have hclosed' :
      RingTheory.Sequence.IsRegular
        (A ⧸ Ideal.map (algebraMap Rp A) (IsLocalRing.maximalIdeal Rp))
        (fsA.map (Ideal.Quotient.mk (Ideal.map (algebraMap Rp A) (IsLocalRing.maximalIdeal Rp)))) := by
    let e :
        (A ⧸ Ideal.map (algebraMap R A) p.asIdeal) ≃+*
          (A ⧸ Ideal.map (algebraMap Rp A) (IsLocalRing.maximalIdeal Rp)) :=
      (Ideal.quotientEquivAlgOfEq A heq).symm.toRingEquiv
    have hmap :
        (fsA.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) p.asIdeal))).map e =
          fsA.map (Ideal.Quotient.mk (Ideal.map (algebraMap Rp A) (IsLocalRing.maximalIdeal Rp))) := by
      ext x
      simp [e, Ideal.quotientEquivAlgOfEq_mk]
    have htransport :=
      regularSequence_iff_map_regularSequence_of_ringEquiv e
        (fsA.map (Ideal.Quotient.mk (Ideal.map (algebraMap R A) p.asIdeal)))
    simpa [hmap] using htransport.mp hclosed
  obtain ⟨hregularA, hflatPrefixRp⟩ :=
    RingTheory.Sequence.isRegular_and_flat_quotient_take_of_closedFiber_isRegular
      (R := Rp) (S := A) fsA hclosed'
  refine ⟨hregularA, ?_⟩
  intro i
  have hflatRp :
      Module.Flat Rp (A ⧸ Ideal.ofList (fsA.take i.1.succ)) := by
    simpa [fsA] using hflatPrefixRp ⟨i.1, by simpa [fsA] using i.2⟩
  exact
    (Module.flat_iff_of_isLocalization Rp p.asIdeal.primeCompl
      (A ⧸ Ideal.ofList (fsA.take i.1.succ))).mp hflatRp

/-- Helper for Chap10 Lemma 10 136 12: package the prime-local regularity of the displayed
relations together with the flatness of every localized partial quotient. -/
-- Source note: the Stacks statement treats `c` as the actual codimension, so in this
-- `Nat`-valued presentation we keep `c ≤ n` explicit to rule out truncated-dimension witnesses.
private theorem localizedRelationsRegularAndFlat
    (hc : c ≤ n)
    (hPdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
        ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    RingTheory.Sequence.IsRegular A ((List.ofFn f).map (algebraMap PolynomialRing A)) ∧
      ∀ i : Fin c,
        Module.Flat R
          (A ⧸ Ideal.ofList (((List.ofFn f).map (algebraMap PolynomialRing A)).take i.1.succ)) := by
  -- Proof comment: both public local statements come from the same source-local package, so the
  -- re-plan frontier should keep them bundled instead of duplicating the future descent argument.
  -- Route correction: the fiber itself is already a global complete intersection by
  -- `fiber_isGlobalCompleteIntersection_of_relativeGciPresentation`, so the remaining blocker is
  -- the quotient closed-fiber regularity statement for `A / pA`. Once that is supplied at a
  -- Noetherian stage, `localizedRelationsRegularAndFlat_of_closedFiberRegular` already packages
  -- the `10.99.3` upgrade to regularity in `A` and flatness of every localized prefix quotient,
  -- leaving only the filtered-colimit descent back to the ambient localized ring.
  obtain ⟨R₀, _hR₀ft, f₀, hf₀, hfgci₀⟩ :=
    exists_finiteType_zSubalgebra_of_relativeGCIQuotient (f := f)
      (hfgci := Algebra.Presentation.toIsRelativeGlobalCompleteIntersection
        (sourceFiberDimension_to_relativeGciPresentation
          (R := R) (n := n) (c := c) (f := f) hc hPdim))
  -- Proof comment: the finite-type stage `R₀` and descended relations `f₀` are the verified
  -- prefix of the non-Noetherian descent route. The remaining blocker is to compare the ambient
  -- localization at `q` with the directed system of localizations over larger finite-type
  -- `ℤ`-subalgebras containing `R₀`, and to feed the stage-local Noetherian package into the
  -- colimit exactness/flatness descent.
  have hf₀_lifts : ∀ i, MvPolynomial.map R₀.val (f₀ i) = f i := hf₀
  have hstage : IsRelativeGlobalCompleteIntersection R₀
      (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := hfgci₀
  -- TODO: first package the finite-type Noetherian stage-local statement
  -- `stageLocalizedRelationsRegularAndFlat` for stages containing `R₀`, then prove the ambient
  -- localized prefix quotients are the filtered colimit of the stage-local prefix quotients and
  -- descend flatness/exactness along `flat_of_stagewise_restrictScalars_flat` and
  -- `module_system_homology_comparison_isIso`.
  sorry

/-- Helper for Chap10 Lemma 10 136 12: the canonical free map sends the `i`th standard basis
vector of `PresentedAlgebra^c` to the cotangent class of `f i`. -/
private noncomputable def presentedCotangentFreeCover :
    PresentedFreeModule →ₗ[PresentedAlgebra] Ideal.Cotangent PresentedIdeal :=
  Fintype.linearCombination PresentedAlgebra fun i ↦
    Ideal.toCotangent PresentedIdeal
      ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩

/-- Helper for Chap10 Lemma 10 136 12: evaluate the canonical free cover on a standard basis
vector. -/
private theorem presentedCotangentFreeCover_basisFun
    (i : Fin c) :
    presentedCotangentFreeCover (f := f)
        ((Pi.basisFun PresentedAlgebra (Fin c)) i) =
      Ideal.toCotangent PresentedIdeal
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := by
  -- Proof comment: the free cover is defined by basis recursion, so its values on basis vectors
  -- are the defining cotangent generator classes.
  have hsingle :
      (Pi.basisFun PresentedAlgebra (Fin c)) i = Pi.single i (1 : PresentedAlgebra) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [Pi.basisFun]
    · simp [Pi.basisFun, h]
  rw [hsingle, presentedCotangentFreeCover]
  simpa using
    (Fintype.linearCombination_apply_single
      (R := PresentedAlgebra)
      (v := fun j : Fin c ↦
        Ideal.toCotangent PresentedIdeal
          ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩)
      i (1 : PresentedAlgebra))

/-- Helper for Chap10 Lemma 10 136 12: the cotangent classes of the displayed relations span the
conormal module. -/
private theorem presentedCotangentGenerators_span :
    Submodule.span PresentedAlgebra
      (Set.range fun i : Fin c ↦
        Ideal.toCotangent PresentedIdeal
          ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro z
  obtain ⟨y, rfl⟩ := PresentedIdeal.toCotangent_surjective z
  have hyspan : (y : PolynomialRing) ∈ Ideal.span (Set.range f) := by
    simpa using y.2
  -- Proof comment: span-induct on the ideal generator expression for `y`, transporting each
  -- algebra operation through `Ideal.toCotangent`.
  refine Submodule.span_induction
    (p := fun x hx ↦
      Ideal.toCotangent PresentedIdeal ⟨x, hx⟩ ∈
        Submodule.span PresentedAlgebra
          (Set.range fun i : Fin c ↦
            Ideal.toCotangent PresentedIdeal
              ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩))
    ?mem ?zero ?add ?smul hyspan
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · dsimp
    convert Submodule.zero_mem
      (Submodule.span PresentedAlgebra
        (Set.range fun i : Fin c ↦
          Ideal.toCotangent PresentedIdeal
            ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩)) using 1
  · intro x y hx hy hxmem hymem
    dsimp
    convert Submodule.add_mem _ hxmem hymem using 1
  · intro a x hx hxmem
    dsimp
    have hx' := Submodule.smul_mem
      (Submodule.span PresentedAlgebra
        (Set.range fun i : Fin c ↦
          Ideal.toCotangent PresentedIdeal
            ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩))
      (Ideal.Quotient.mk PresentedIdeal a) hxmem
    convert hx' using 1

/-- Helper for Chap10 Lemma 10 136 12: the canonical free cover of the conormal module is
surjective because the displayed cotangent generators already span. -/
private theorem presentedCotangentFreeCover_surjective :
    Function.Surjective (presentedCotangentFreeCover (f := f)) := by
  have hrange :
      LinearMap.range (presentedCotangentFreeCover (f := f)) =
        Submodule.span PresentedAlgebra
          (Set.range fun i : Fin c ↦
            Ideal.toCotangent PresentedIdeal
              ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) := by
    rw [presentedCotangentFreeCover, Fintype.range_linearCombination]
  -- Proof comment: `Fintype.linearCombination` has range equal to the span of its chosen family.
  exact LinearMap.range_eq_top.1
    (hrange.trans (presentedCotangentGenerators_span (R := R) (n := n) (c := c) (f := f)))

/-- Helper for Chap10 Lemma 10 136 12: bijectivity of the canonical free cover upgrades the
displayed cotangent classes to the advertised basis. -/
private theorem conormalBasisOfPresentedCotangentFreeCoverBijective
    (hbij : Function.Bijective (presentedCotangentFreeCover (f := f))) :
    ∃ b : Module.Basis (Fin c) PresentedAlgebra (Ideal.Cotangent PresentedIdeal),
      ∀ i, b i = Ideal.toCotangent PresentedIdeal
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := by
  let e :
      PresentedFreeModule ≃ₗ[PresentedAlgebra] Ideal.Cotangent PresentedIdeal :=
    LinearEquiv.ofBijective (presentedCotangentFreeCover (f := f)) hbij
  refine ⟨(Pi.basisFun PresentedAlgebra (Fin c)).map e, ?_⟩
  intro i
  -- Proof comment: transport the standard basis of `PresentedAlgebra^c` across the resulting
  -- linear equivalence and then evaluate on the `i`th basis vector.
  change e ((Pi.basisFun PresentedAlgebra (Fin c)) i) =
    Ideal.toCotangent PresentedIdeal
      ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩
  exact presentedCotangentFreeCover_basisFun (f := f) i

/-- Helper for Chap10 Lemma 10 136 12: the canonical free cover of the conormal module is
bijection. -/
private theorem presentedCotangentFreeCover_bijective
    (hc : c ≤ n)
    (hPdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
        ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) + c = n) :
    Function.Bijective (presentedCotangentFreeCover (f := f)) := by
  constructor
  · -- Proof comment: injectivity still reduces to the prime-local comparison between the
    -- localized presentation cotangent owner and the cotangent of the localized list ideal.
    have htfae :
        List.TFAE [
          Function.Injective (presentedCotangentFreeCover (f := f)),
          ∀ (q : Ideal PresentedAlgebra) [q.IsPrime],
            Function.Injective
              (LocalizedModule.map q.primeCompl (presentedCotangentFreeCover (f := f))),
          ∀ (q : Ideal PresentedAlgebra) [q.IsMaximal],
            Function.Injective
              (LocalizedModule.map q.primeCompl (presentedCotangentFreeCover (f := f)))
        ] :=
      injective_localization_tfae (presentedCotangentFreeCover (f := f))
    suffices hprime :
        ∀ (q : Ideal PresentedAlgebra) [q.IsPrime],
          Function.Injective
            (LocalizedModule.map q.primeCompl (presentedCotangentFreeCover (f := f))) by
      exact (htfae.out 0 1).mpr hprime
    intro q hq
    letI : q.IsPrime := hq
    let qSpec : PrimeSpectrum PresentedAlgebra := ⟨q, hq⟩
    let q' : PrimeSpectrum PolynomialRing :=
      PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) qSpec
    let A := Localization.AtPrime q'.asIdeal
    let Kq : Ideal A := Ideal.map (algebraMap PolynomialRing A) PresentedIdeal
    have hIdeal :
        LocalizedModule.AtPrime q'.asIdeal PresentedIdeal ≃ₗ[PolynomialRing] Kq :=
      localizedPresentedIdealAtPrime (R := R) (n := n) (c := c) (f := f) qSpec
    -- Proof comment: the global injectivity problem is now reduced to one prime-local goal. The
    -- localized ideal owner is now fixed by `hIdeal`; the remaining blocker is to transport the
    -- localized cotangent module from the quotient-prime owner to `Kq.Cotangent`, and then
    -- identify the localized free cover with the quasi-regular source map after that transport.
    -- TODO: build the target-prime cotangent equivalence
    -- `LocalizedModule.AtPrime q.asIdeal (Ideal.Cotangent PresentedIdeal) ≃ₗ[Localization.AtPrime q.asIdeal] Kq.Cotangent`
    -- from `source_localized_quotient_localization_algEquiv`, using
    -- `comap_mappedPresentedIdeal_eq_presentedIdeal` and
    -- `presentedPrimeCompl_eq_sourceAlgebraMapSubmonoid` to normalize the owner rings/submonoids,
    -- then conjugate the localized free cover to the quasi-regular source map and apply
    -- `RingTheory.Sequence.isQuasiRegular_iff_injective`.
    sorry
  · -- Proof comment: surjectivity is already global because the displayed cotangent generators
    -- span the conormal module.
    exact presentedCotangentFreeCover_surjective (R := R) (n := n) (c := c) (f := f)

/-- Chap10 Lemma 10 136 12 (1): if
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection, then for every
prime `q` of `S`,
writing `q'` for the corresponding prime of `R[x₁, …, xₙ]`, the sequence `f₁, …, f_c` is
regular in the local ring `R[x₁, …, xₙ]_{q'}`. -/
@[stacks 00SV]
theorem relativeGCI_localized_relations_isRegular
    (hP : PresentedPresentation.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    RingTheory.Sequence.IsRegular A ((List.ofFn f).map (algebraMap PolynomialRing A)) := sorry

/-- Chap10 Lemma 10 136 12 (2): if
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection, then for every
prime `q` of `S`,
each localized partial quotient `R[x₁, …, xₙ]_{q'} / (f₁, …, f_i)` is flat over `R`. -/
@[stacks 00SV]
theorem relativeGCI_localized_partial_quotients_flat
    (hP : PresentedPresentation.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    ∀ i : Fin c,
      Module.Flat R
        (A ⧸ Ideal.ofList (((List.ofFn f).map (algebraMap PolynomialRing A)).take i.1.succ)) :=
      sorry

/-- Chap10 Lemma 10 136 12 (3): if
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection, then the conormal
module
`(f₁, …, f_c) / (f₁, …, f_c)^2` is free with basis given by the classes of the displayed
relations. -/
@[stacks 00SV]
theorem relativeGCI_conormalModule_has_basis
    (hP : PresentedPresentation.IsRelativeGlobalCompleteIntersection) :
    ∃ b : Module.Basis (Fin c) PresentedAlgebra (Ideal.Cotangent PresentedIdeal),
      ∀ i, b i = Ideal.toCotangent PresentedIdeal
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := sorry

end

end Algebra
