import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_112_5
import stacks_proof.stacks_project.Chap10.Definition_10_137_10
import stacks_proof.stacks_project.Chap10.Lemma_10_52_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
open Ideal.Quotient (eq_zero_iff_mem)

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- The proof below follows the source route: first replace the original prime by a prime on a
finite-presentation basic-open chart, then compare the local rings and fiber point through the
standard localization bridges. -/

/-- Helper for Chap10 Lemma 10 137 16: a prime of an away localization lying over `q` has the
same contraction to the base ring as `q`. -/
private lemma localizationAway_comap_under_eq
    (q : PrimeSpectrum S) {g : S} {qg : PrimeSpectrum (Localization.Away g)}
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q) :
    qg.asIdeal.under R = q.asIdeal.under R := by
  -- Proof comment: applying `asIdeal` to the equality over `S` turns the desired contraction
  -- comparison into the scalar-tower identity for `R → S → S_g`.
  have hqgIdeal : Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal = q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg
  ext r
  change algebraMap R (Localization.Away g) r ∈ qg.asIdeal ↔ algebraMap R S r ∈ q.asIdeal
  rw [← hqgIdeal]
  rfl

/-- Helper for Chap10 Lemma 10 137 16: the local ring at a prime and the local ring at a lifted
prime in an away localization are equivalent, compatibly with the localized base maps. -/
private lemma localizationAway_atPrimeRingEquivWithLocalMap
    (q : PrimeSpectrum S) {g : S} {qg : PrimeSpectrum (Localization.Away g)}
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q) :
    ∃ e : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime qg.asIdeal,
      e.toRingHom.comp
          (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl) =
        Localization.localRingHom (q.asIdeal.under R) qg.asIdeal
          (algebraMap R (Localization.Away g))
          (by rw [← localizationAway_comap_under_eq (R := R) q hqg]) := by
  -- Proof comment: compare `S_q` with the localization at the contracted ideal in `S`, then use
  -- the standard iterated-localization equivalence for the principal localization `S_g`.
  let qI : Ideal S := Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal
  have hqI : q.asIdeal = Ideal.comap (AlgEquiv.refl : S ≃ₐ[S] S) qI := by
    have hq : q.asIdeal = qI := by
      simpa [qI, PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hqg).symm
    rw [hq]
    exact (Ideal.comap_id qI).symm
  let eSource : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qI :=
    Localization.localAlgEquiv q.asIdeal qI (AlgEquiv.refl : S ≃ₐ[S] S) hqI
  let eTower : Localization.AtPrime qI ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g) qg.asIdeal
  let eAlg : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    eSource.trans eTower
  refine ⟨eAlg.toRingEquiv, ?_⟩
  -- Proof comment: both maps out of `R_(q ∩ R)` agree on `R`, so uniqueness of maps from a
  -- localization identifies them.
  symm
  apply Localization.localRingHom_unique
  intro r
  calc
    eAlg.toRingEquiv.toRingHom.comp
        (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl)
        (algebraMap R (Localization.AtPrime (q.asIdeal.under R)) r)
        =
          eAlg (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S r)) := by
            rw [RingHom.comp_apply, Localization.localRingHom_to_map]
            rfl
    _ = algebraMap S (Localization.AtPrime qg.asIdeal) (algebraMap R S r) := by
          exact eAlg.commutes (algebraMap R S r)
    _ = algebraMap R (Localization.AtPrime qg.asIdeal) r := by
          rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime qg.asIdeal)]

/-- Helper for Chap10 Lemma 10 137 16: the chart-local equivalence is compatible with the
localized base ring. -/
private lemma nonempty_localizationAway_atPrimeAlgEquivWithLocalMap
    (q : PrimeSpectrum S) {g : S} {qg : PrimeSpectrum (Localization.Away g)}
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q) :
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R)) (Localization.AtPrime qg.asIdeal) :=
      RingHom.toAlgebra
        (Localization.localRingHom (q.asIdeal.under R) qg.asIdeal
          (algebraMap R (Localization.Away g))
          (by rw [← localizationAway_comap_under_eq (R := R) (S := S) q hqg]))
    Nonempty
      (Localization.AtPrime q.asIdeal ≃ₐ[Localization.AtPrime (q.asIdeal.under R)]
        Localization.AtPrime qg.asIdeal) := by
  -- Proof comment: upgrade the ring equivalence by using its recorded equality on the localized
  -- base map as the `commutes'` field for an algebra equivalence.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R)) (Localization.AtPrime qg.asIdeal) :=
    RingHom.toAlgebra
      (Localization.localRingHom (q.asIdeal.under R) qg.asIdeal
        (algebraMap R (Localization.Away g))
        (by rw [← localizationAway_comap_under_eq (R := R) (S := S) q hqg]))
  obtain ⟨e, he⟩ := localizationAway_atPrimeRingEquivWithLocalMap (R := R) (S := S) q hqg
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_⟩
  intro x
  exact DFunLike.congr_fun he x

/-- Helper for Chap10 Lemma 10 137 16: a prime avoiding an away parameter lifts to the away
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

/-- Helper for Chap10 Lemma 10 137 16: the canonical prime of a fiber ring contracts back to
the ambient prime along the right tensor-factor inclusion. -/
private lemma fiberPrimeAt_comap_asIdeal_eq
    (q : PrimeSpectrum S) :
    Ideal.comap (algebraMap S ((q.asIdeal.under R).Fiber S))
        (fiberPrimeAt R S q).asIdeal =
      q.asIdeal := by
  -- Proof comment: `fiberPrimeAt` is defined through the fiber equivalence, whose inverse
  -- remembers exactly the original prime of `S`.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm
      (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩)).1.asIdeal =
      q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)

/-- Helper for Chap10 Lemma 10 137 16: if `g` avoids `q`, its image in the fiber over `q ∩ R`
avoids the canonical fiber prime. -/
private lemma algebraMap_notMem_fiberPrimeAt_of_notMem
    (q : PrimeSpectrum S) {g : S} (hgq : g ∉ q.asIdeal) :
    algebraMap S ((q.asIdeal.under R).Fiber S) g ∉ (fiberPrimeAt R S q).asIdeal := by
  -- Proof comment: rewrite membership in the contracted fiber prime as membership in `q`.
  intro hg
  have hg_comap :
      g ∈ Ideal.comap (algebraMap S ((q.asIdeal.under R).Fiber S))
        (fiberPrimeAt R S q).asIdeal := hg
  rw [fiberPrimeAt_comap_asIdeal_eq (R := R) q] at hg_comap
  exact hgq hg_comap

/-- Helper for Chap10 Lemma 10 137 16: the maximal ideal of `R_(q ∩ R)`, extended to `S_q`,
is the direct extension of `q ∩ R` to `S_q`. -/
private lemma atPrimeMap_maximalIdeal_eq_map_under
    (q : PrimeSpectrum S) :
    Ideal.map (algebraMap (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))) =
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R) := by
  -- Proof comment: first rewrite the localized maximal ideal as `pR_p`, then compose the two
  -- localization maps using the scalar-tower algebra-map identity.
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.map_map]
  rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime (q.asIdeal.under R))
    (Localization.AtPrime q.asIdeal)]

/-- Helper for Chap10 Lemma 10 137 16: quotienting by `I ≤ q` sends the prime complement of `q`
to the induced prime complement in the quotient. -/
private lemma quotient_primeCompl_eq_algebraMapSubmonoid_of_le
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: pulling quotient-prime membership back along the quotient map recovers
    -- membership in `q`, contradicting that the chosen denominator avoids `q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: if a lift landed in `q`, its quotient class would land in the induced
    -- quotient prime, contrary to the prime-complement assumption on the quotient class.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Chap10 Lemma 10 137 16: elements of the extension `pS` vanish in the fiber ring
`κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map_under (p : PrimeSpectrum R) {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  -- Proof comment: compare the quotient presentation `S / pS` with the tensor presentation of
  -- the fiber and send the resulting zero tensor to the residue-field base change.
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
  simpa [φ] using hφ

/-- Helper for Chap10 Lemma 10 137 16: the quotient `S / pS` acts canonically on the fiber ring
over `p`. -/
private noncomputable instance fiberQuotientAlgebraAtUnder (p : PrimeSpectrum R) :
    Algebra (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ (Ideal.map (algebraMap R S) p.asIdeal)
    (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map_under (R := R) (S := S) p hx)).toRingHom.toAlgebra

/-- Helper for Chap10 Lemma 10 137 16: a quotient generator maps to the corresponding pure tensor
in the fiber ring. -/
private theorem quotient_to_fiber_algebraMap_mk_under (p : PrimeSpectrum R) (s : S) :
    algebraMap (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (p.asIdeal.Fiber S)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) s) =
        1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Chap10 Lemma 10 137 16: the quotient-base-changed fiber presentation recovers the
usual fiber ring over `p` as an algebra over `S / pS`. -/
private noncomputable def fiberTensorOverQuotientAlgEquivAtUnder (p : PrimeSpectrum R) :
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
      -- Proof comment: both quotient-side and tensor-side algebra maps send `s mod pS` to
      -- `1 ⊗ s`.
      simpa [eRing, quotient_to_fiber_algebraMap_mk_under (R := R) (S := S) p s,
        Algebra.TensorProduct.cancelBaseChange_tmul] }

/-- Helper for Chap10 Lemma 10 137 16: the fiber ring over `p` is the localization of `S / pS`
at the image of the nonzerodivisors of `R / p`. -/
private noncomputable def fiberQuotientLocalizationAlgEquivAtUnder (p : PrimeSpectrum R) :
    Localization
        (Algebra.algebraMapSubmonoid
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal) (nonZeroDivisors (R ⧸ p.asIdeal))) ≃ₐ[
          (S ⧸ Ideal.map (algebraMap R S) p.asIdeal)] p.asIdeal.Fiber S :=
  -- Proof comment: this is the standard presentation
  -- `(S / pS)[(R / p)^-1] ≃ κ(p) ⊗[R] S`.
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
    (fiberTensorOverQuotientAlgEquivAtUnder (R := R) (S := S) p)

/-- Helper for Chap10 Lemma 10 137 16: the quotient presentation `S_q / (q ∩ R)S_q` identifies
with the canonical fiber local ring at `q`. -/
private lemma nonempty_localizedQuotientRingEquivFiberLocalRingAt
    (q : PrimeSpectrum S) :
    Nonempty
      (((Localization.AtPrime q.asIdeal) ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) ≃+*
          fiberLocalRingAt R S q) := by
  -- Proof comment: localize the quotient `S / pS` at the induced quotient prime and then compare
  -- the resulting local ring with the localization of the standard fiber presentation.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let I : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
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
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid_of_le I q.asIdeal
        (by
          rw [Ideal.map_le_iff_le_comap]
          simpa [I, p, PrimeSpectrum.comap_asIdeal])
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
    have hFiberComap :
        Ideal.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q).asIdeal =
          q.asIdeal := by
      simpa [p] using fiberPrimeAt_comap_asIdeal_eq (R := R) (S := S) q
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
    rw [show
        eFiber.toRingHom.comp
            ((algebraMap (S ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) =
          algebraMap S (p.asIdeal.Fiber S) by
            ext s
            -- Proof comment: the quotient presentation and canonical inclusion of `S` into the
            -- fiber ring agree on generators.
            calc
              eFiber.toRingHom
                  ((algebraMap (S ⧸ I) (Localization T)) (Ideal.Quotient.mk I s)) =
                  algebraMap (S ⧸ I) (p.asIdeal.Fiber S) (Ideal.Quotient.mk I s) := by
                    exact eFiber.commutes (Ideal.Quotient.mk I s)
              _ = algebraMap S (p.asIdeal.Fiber S) s := by
                    rw [quotient_to_fiber_algebraMap_mk_under (R := R) (S := S) (p := p)]
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
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := T) qT.asIdeal).toRingEquiv
  let eFiberLocal0 :
      Localization.AtPrime qT.asIdeal ≃+*
        Localization.AtPrime (fiberPrimeAt R S q).asIdeal :=
    Localization.localRingEquiv qT.asIdeal (fiberPrimeAt R S q).asIdeal eFiber.toRingEquiv
      (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt R S q))
  let eFiberLocal :
      Localization.AtPrime qT.asIdeal ≃+* fiberLocalRingAt R S q := by
    simpa [fiberLocalRingAt] using eFiberLocal0
  refine ⟨?_⟩
  simpa [p] using
    ((((eTarget.symm.trans eQuot.toRingEquiv).trans eSource).trans eTower).trans eFiberLocal)

/-- Helper for Chap10 Lemma 10 137 16: the closed fiber of the localized map
`R_(q ∩ R) → S_q`, named to keep typeclass search out of expanded fiber expressions. -/
private noncomputable abbrev closedFiberAtPrimeUnder (q : PrimeSpectrum S) : Type _ :=
  let Rp := Localization.AtPrime (q.asIdeal.under R)
  let Sq := Localization.AtPrime q.asIdeal
  (IsLocalRing.maximalIdeal Rp).Fiber Sq

/-- Helper for Chap10 Lemma 10 137 16: the named closed fiber is a commutative ring. -/
private noncomputable instance closedFiberAtPrimeUnderCommRing (q : PrimeSpectrum S) :
    CommRing (closedFiberAtPrimeUnder (R := R) (S := S) q) := by
  dsimp [closedFiberAtPrimeUnder]
  infer_instance

/-- Helper for Chap10 Lemma 10 137 16: the named closed fiber is a semiring. -/
private noncomputable instance closedFiberAtPrimeUnderSemiring (q : PrimeSpectrum S) :
    Semiring (closedFiberAtPrimeUnder (R := R) (S := S) q) := by
  dsimp [closedFiberAtPrimeUnder]
  infer_instance

/-- Helper for Chap10 Lemma 10 137 16: multiplication on the named closed fiber is inherited from
its commutative-ring structure. -/
private noncomputable instance closedFiberAtPrimeUnderMul (q : PrimeSpectrum S) :
    Mul (closedFiberAtPrimeUnder (R := R) (S := S) q) :=
  (closedFiberAtPrimeUnderSemiring (R := R) (S := S) q).toNonAssocSemiring.toDistrib.toMul

/-- Helper for Chap10 Lemma 10 137 16: addition on the named closed fiber is inherited from its
commutative-ring structure. -/
private noncomputable instance closedFiberAtPrimeUnderAdd (q : PrimeSpectrum S) :
    Add (closedFiberAtPrimeUnder (R := R) (S := S) q) :=
  (closedFiberAtPrimeUnderSemiring (R := R) (S := S) q).toNonAssocSemiring.toDistrib.toAdd

/-- Helper for Chap10 Lemma 10 137 16: the literal closed fiber of the localized stalk map is
ring-equivalent to the canonical local fiber ring. -/
private lemma nonempty_closedFiberAtPrimeRingEquivFiberLocalRingAt
    (q : PrimeSpectrum S) :
    Nonempty (closedFiberAtPrimeUnder (R := R) (S := S) q ≃+* fiberLocalRingAt R S q) := by
  -- Proof comment: rewrite the closed fiber to the quotient by the extended maximal ideal, use
  -- the ideal rewrite `mR_p S_q = (q ∩ R)S_q`, then use the quotient-local fiber bridge.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  let C0 := (IsLocalRing.maximalIdeal Rp).Fiber Sq
  letI : Semiring C0 := by
    dsimp [C0]
    infer_instance
  letI : Mul C0 :=
    (inferInstance : Semiring C0).toNonAssocSemiring.toDistrib.toMul
  letI : Add C0 :=
    (inferInstance : Semiring C0).toNonAssocSemiring.toDistrib.toAdd
  let eClosedFiber0 :
      C0 ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (A := Rp) (B := Sq)).symm.toRingEquiv
  let eClosedFiber :
      closedFiberAtPrimeUnder (R := R) (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := by
    simpa [closedFiberAtPrimeUnder, p, Rp, Sq, C0] using eClosedFiber0
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) :=
    Ideal.quotEquivOfEq (atPrimeMap_maximalIdeal_eq_map_under (R := R) (S := S) q)
  obtain ⟨eQuotToFiber⟩ := nonempty_localizedQuotientRingEquivFiberLocalRingAt (R := R) (S := S) q
  refine ⟨?_⟩
  simpa [closedFiberAtPrimeUnder, p, Rp, Sq] using
    (eClosedFiber.trans eRewrite).trans eQuotToFiber

/-- Helper for Chap10 Lemma 10 137 16: the canonical residue-field algebra structure on the
local fiber ring factors through the global fiber ring. -/
private lemma fiberLocalRingAtResidueFieldFiberIsScalarTower
    (q : PrimeSpectrum S) :
    IsScalarTower (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
      (fiberLocalRingAt R S q) := by
  -- Proof comment: unfold the class to the equality of the two canonical algebra maps.
  exact IsScalarTower.of_algebraMap_eq' (R := (q.asIdeal.under R).ResidueField)
    (S := (q.asIdeal.under R).Fiber S) (A := fiberLocalRingAt R S q) rfl

/-- Helper for Chap10 Lemma 10 137 16: base elements map to the local fiber ring through the
canonical residue-field scalar action. -/
private lemma toFiberLocalRingAt_algebraMap_eq_residue
    (q : PrimeSpectrum S) (r : R) :
    toFiberLocalRingAt R S q (algebraMap R S r) =
      algebraMap (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)
        (algebraMap R (q.asIdeal.under R).ResidueField r) := by
  -- Proof comment: unfold the two canonical scalar maps and use the residue-map presentation of
  -- the fiber tensor algebra.
  letI :
      IsScalarTower (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
        (fiberLocalRingAt R S q) :=
    fiberLocalRingAtResidueFieldFiberIsScalarTower (R := R) q
  simpa [toFiberLocalRingAt] using
    (IsScalarTower.algebraMap_apply (q.asIdeal.under R).ResidueField
      ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)
      (algebraMap R (q.asIdeal.under R).ResidueField r)).symm

/-- Helper for Chap10 Lemma 10 137 16: smoothness on a basic open neighborhood of the canonical
fiber prime makes the local fiber ring formally smooth over the residue field. -/
private lemma formallySmooth_fiberLocalRingAt_of_smoothAtPrime
    (q : PrimeSpectrum S)
    (hfiber :
      SmoothAtPrime (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
        (fiberPrimeAt R S q)) :
    Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) := by
  -- Proof comment: unpack the smooth principal-open witness in the fiber ring.
  rcases hfiber with ⟨a, ha, hsmooth⟩
  let F := (q.asIdeal.under R).Fiber S
  let m := (fiberPrimeAt R S q).asIdeal
  have hpowers_le : Submonoid.powers a ≤ m.primeCompl := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    cases n with
    | zero =>
        exact m.primeCompl.one_mem
    | succ n =>
        exact fun hxpow =>
          ha ((Ideal.IsPrime.pow_mem_iff_mem (I := m) inferInstance (n + 1)
            (Nat.succ_pos n)).mp hxpow)
  -- Proof comment: the local fiber ring is a further localization of the smooth fiber chart.
  letI : Algebra (Localization.Away a) (fiberLocalRingAt R S q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away a)
      (fiberLocalRingAt R S q) (Submonoid.powers a) m.primeCompl hpowers_le
  letI : IsScalarTower F (Localization.Away a) (fiberLocalRingAt R S q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away a)
      (fiberLocalRingAt R S q) (Submonoid.powers a) m.primeCompl hpowers_le
  letI :
      IsScalarTower (q.asIdeal.under R).ResidueField F (Localization.Away a) :=
    inferInstance
  letI :
      IsScalarTower (q.asIdeal.under R).ResidueField F (fiberLocalRingAt R S q) :=
    -- Proof comment: after adding the chart-local algebra structure on the target localization,
    -- pin the residue-field/fiber/local-fiber tower explicitly so the canonical fiber algebra is
    -- used in the comparison.
    fiberLocalRingAtResidueFieldFiberIsScalarTower (R := R) q
  letI :
      IsScalarTower (q.asIdeal.under R).ResidueField (Localization.Away a)
        (fiberLocalRingAt R S q) :=
    IsScalarTower.to₁₃₄ (q.asIdeal.under R).ResidueField F
      (Localization.Away a) (fiberLocalRingAt R S q)
  letI : CommSemiring (Localization.Away a) := inferInstance
  let φ : ((q.asIdeal.under R).Fiber S) →* Localization.Away a :=
    (algebraMap ((q.asIdeal.under R).Fiber S) (Localization.Away a)).toMonoidHom
  let Mloc : Submonoid (Localization.Away a) := Submonoid.map φ m.primeCompl
  letI : IsLocalization Mloc (fiberLocalRingAt R S q) := by
    -- Proof comment: name the mapped prime-complement submonoid before applying the
    -- iterated-localization API; this avoids fragile inline inference for `Submonoid.map`.
    exact IsLocalization.isLocalization_of_submonoid_le (Localization.Away a)
      (fiberLocalRingAt R S q) (Submonoid.powers a) m.primeCompl hpowers_le
  letI : Algebra.FormallySmooth (Localization.Away a) (fiberLocalRingAt R S q) :=
    Algebra.FormallySmooth.of_isLocalization Mloc
  exact Algebra.FormallySmooth.comp (q.asIdeal.under R).ResidueField
    (Localization.Away a) (fiberLocalRingAt R S q)

/-- Helper for Chap10 Lemma 10 137 16: a finite-presentation chart upgrades the canonical local
smoothness predicate at `q` to the source-facing principal-open smoothness condition. -/
private lemma smoothAtPrime_of_isSmoothAt_of_finitePresentation_nearPrime
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hIs : IsSmoothAt R q.asIdeal) :
    SmoothAtPrime R S q := by
  -- Proof comment: move the local smoothness predicate to the finite-presentation chart.
  rcases hfp with ⟨g, hgq, hfinite⟩
  rcases exists_primeSpectrum_away_comap_eq_of_notMem q hgq with ⟨qg, hqg⟩
  have hqgIdeal :
      Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal = q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg
  have hqgSmooth : IsSmoothAt R qg.asIdeal := by
    have hpre :
        qg ∈ PrimeSpectrum.comap (algebraMap S (Localization.Away g)) ⁻¹'
          smoothLocus R S := by
      change PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg ∈
        smoothLocus R S
      rw [hqg]
      simpa [smoothLocus] using hIs
    rwa [Algebra.smoothLocus_comap_of_isLocalization (R := R) (A := S)
      (Af := Localization.Away g) g] at hpre
  -- Proof comment: the finite-presentation chart converts `IsSmoothAt` into a smooth basic open.
  letI : FinitePresentation R (Localization.Away g) := hfinite
  have hchart : SmoothAtPrime R (Localization.Away g) qg :=
    (smoothAtPrime_iff_isSmoothAt (R := R) (S := Localization.Away g) qg).2 hqgSmooth
  rcases hchart with ⟨a, ha, hsmooth⟩
  let b : S := (IsLocalization.Away.sec g a).1
  have hbq : b ∉ q.asIdeal := by
    intro hb
    have hbqg : algebraMap S (Localization.Away g) b ∈ qg.asIdeal := by
      change b ∈ Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal
      rwa [hqgIdeal]
    have ha_mem : a ∈ qg.asIdeal :=
      (Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g a)).mp hbqg
    exact ha ha_mem
  -- Proof comment: clear the denominator of the chart element and transfer smoothness across the
  -- canonical away-localization equivalence.
  refine ⟨g * b, ?_, ?_⟩
  · intro hgb
    rcases (Ideal.IsPrime.mem_or_mem (I := q.asIdeal) inferInstance hgb) with hg | hb
    · exact hgq hg
    · exact hbq hb
  · let T := Localization.Away a
    letI : IsLocalization.Away (g * b) T :=
      IsLocalization.Away.mul_of_associated (S := Localization.Away g) g b a
        (IsLocalization.Away.associated_sec_fst g a)
    let e : Localization.Away (g * b) ≃ₐ[R] T :=
      (IsLocalization.algEquiv (Submonoid.powers (g * b))
        (Localization.Away (g * b)) T).restrictScalars R
    letI : Smooth R T := hsmooth
    exact Algebra.Smooth.of_equiv e.symm

/-- Helper for Chap10 Lemma 10 137 16: membership in the canonical fiber prime can be tested
after contracting back to `S`. -/
private lemma algebraMap_mem_fiberPrimeAt_iff
    (q : PrimeSpectrum S) (s : S) :
    algebraMap S ((q.asIdeal.under R).Fiber S) s ∈ (fiberPrimeAt R S q).asIdeal ↔
      s ∈ q.asIdeal := by
  -- Proof comment: rewrite membership as membership in the contracted ideal and use the
  -- canonical contraction computation for `fiberPrimeAt`.
  change s ∈ Ideal.comap (algebraMap S ((q.asIdeal.under R).Fiber S))
      (fiberPrimeAt R S q).asIdeal ↔ s ∈ q.asIdeal
  rw [fiberPrimeAt_comap_asIdeal_eq (R := R) q]

/-- Helper for Chap10 Lemma 10 137 16: flatness of a displayed local ring homomorphism is
module flatness for its target over its source. -/
private lemma moduleFlat_atPrime_of_localRingHom_flat
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R A) (q.over_def p)).Flat) :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
  -- Proof comment: `RingHom.Flat` is defined as module flatness after algebraizing the map.
  simpa [RingHom.Flat] using hflat

/-- Helper for Chap10 Lemma 10 137 16: localizing a finite-presentation algebra after base
localization is still finite presentation. -/
private lemma finitePresentation_localizationAtPrime_to_localizedTarget
    {A : Type*} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (p : Ideal R) [p.IsPrime] :
    Algebra.FinitePresentation (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)) := by
  -- Proof comment: base-change finite presentation from `R` to `R_p`, then identify the tensor
  -- product with the standard localization of `A`.
  let e : TensorProduct R (Localization.AtPrime p) A ≃ₐ[Localization.AtPrime p]
      Localization (Algebra.algebraMapSubmonoid A p.primeCompl) :=
    Localization.tensorRightAlgEquiv p.primeCompl A
  exact Algebra.FinitePresentation.equiv e

/-- Helper for Chap10 Lemma 10 137 16: elements of `A` coming from `R \ p` become units in
`A_q` when `q` lies over `p`. -/
private lemma localizedTargetToAtPrime_map_units
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    ∀ y : Algebra.algebraMapSubmonoid A p.primeCompl,
      IsUnit ((Algebra.ofId A (Localization.AtPrime q)) y) := by
  -- Proof comment: lying over rewrites nonmembership in `p` to nonmembership in `q`, and the
  -- target localization inverts exactly `A \ q`.
  rintro ⟨_, x, hx, rfl⟩
  have hxq : algebraMap R A x ∉ q := by
    simpa [q.over_def p] using hx
  exact IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
    ⟨algebraMap R A x, hxq⟩

/-- Helper for Chap10 Lemma 10 137 16: the canonical map from `A[p⁻¹]` to `A_q`. -/
private noncomputable def localizedTargetToAtPrimeAlgHom
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    Localization (Algebra.algebraMapSubmonoid A p.primeCompl) →ₐ[A] Localization.AtPrime q :=
  IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid A p.primeCompl)
    (f := Algebra.ofId _ _) (localizedTargetToAtPrime_map_units (R := R) p q)

/-- Helper for Chap10 Lemma 10 137 16: `A_q` is the localization of `A[p⁻¹]` at the image of
`A \ q`. -/
private lemma isLocalization_localizedTarget_to_atPrime
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    let Ap := Localization (Algebra.algebraMapSubmonoid A p.primeCompl)
    let Aq := Localization.AtPrime q
    let f : Ap →ₐ[A] Aq := localizedTargetToAtPrimeAlgHom (R := R) p q
    letI : Algebra Ap Aq := f.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Ap q.primeCompl) Aq := by
  -- Proof comment: the already-inverted base denominators map into `A \ q`, so the iterated
  -- localization criterion applies.
  let Ap := Localization (Algebra.algebraMapSubmonoid A p.primeCompl)
  let Aq := Localization.AtPrime q
  let f : Ap →ₐ[A] Aq := localizedTargetToAtPrimeAlgHom (R := R) p q
  letI : Algebra Ap Aq := f.toAlgebra
  refine .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid A p.primeCompl) _ ?_
  rintro _ ⟨x, hx, rfl⟩
  simp_all [q.over_def p]

/-- Helper for Chap10 Lemma 10 137 16: the local flat smooth-fiber criterion over a
finite-presentation chart. -/
private lemma formallySmooth_atPrime_of_flat_localRingHom_of_formallySmooth_closedFiber
    {A : Type*} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R A) (q.over_def p)).Flat)
    (hfiber :
      Algebra.FormallySmooth (IsLocalRing.ResidueField (Localization.AtPrime p))
        (TensorProduct (Localization.AtPrime p)
          (IsLocalRing.ResidueField (Localization.AtPrime p)) (Localization.AtPrime q))) :
    Algebra.FormallySmooth R (Localization.AtPrime q) := by
  -- Proof comment: cache the local flatness as a module instance before introducing the
  -- intermediate localization chart.
  have hflat' : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    moduleFlat_atPrime_of_localRingHom_flat (R := R) p q hflat
  let Rp := Localization.AtPrime p
  let Ap := Localization (Algebra.algebraMapSubmonoid A p.primeCompl)
  let Aq := Localization.AtPrime q
  let f : Ap →ₐ[A] Aq := localizedTargetToAtPrimeAlgHom (R := R) p q
  algebraize [f.toRingHom]
  letI : Module.Flat Rp Aq := hflat'
  letI :
      Algebra.FormallySmooth (IsLocalRing.ResidueField Rp)
        (TensorProduct Rp (IsLocalRing.ResidueField Rp) Aq) := by
    simpa only [Rp, Aq] using hfiber
  have : IsScalarTower R Ap Aq := .to₁₃₄ _ A _ _
  have : IsScalarTower Rp Ap Aq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Ap q.primeCompl) Aq :=
    isLocalization_localizedTarget_to_atPrime (R := R) p q
  have : FinitePresentation Rp Ap :=
    finitePresentation_localizationAtPrime_to_localizedTarget (R := R) (A := A) p
  -- Proof comment: mathlib's criterion gives formal smoothness over `R_p`, and composition
  -- returns formal smoothness over the original base.
  have := Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Aq) (P := Ap) (Algebra.algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Aq

/-- Helper for Chap10 Lemma 10 137 16: localizing the fiber tensor at `q` is the canonical
residue-field tensor over the base stalk, first as an `R`-algebra equivalence. -/
private noncomputable def fiberTensorAtPrimeBaseChangeAlgEquivR
    (q : PrimeSpectrum S) :
    (((q.asIdeal.under R).Fiber S) ⊗[S] Localization.AtPrime q.asIdeal) ≃ₐ[
      R]
      ((q.asIdeal.under R).ResidueField ⊗[Localization.AtPrime (q.asIdeal.under R)]
        Localization.AtPrime q.asIdeal) :=
  let p := q.asIdeal.under R
  let Sq := Localization.AtPrime q.asIdeal
  let K := p.ResidueField
  let e : K ⊗[R] S ≃ₐ[S] S ⊗[R] K :=
    (Algebra.TensorProduct.commRight R S K).symm
  ((Algebra.TensorProduct.comm S (K ⊗[R] S) Sq).restrictScalars R).trans <|
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : Sq ≃ₐ[S] Sq) e).restrictScalars R).trans <|
  ((Algebra.TensorProduct.cancelBaseChange R S S Sq K).restrictScalars R).trans <|
  (Algebra.TensorProduct.comm R Sq K).trans
    (Algebra.TensorProduct.equivOfCompatibleSMul ..)

/-- Helper for Chap10 Lemma 10 137 16: the tensor/base-change equivalence preserves the
canonical residue-field scalars. -/
private lemma fiberTensorAtPrimeBaseChangeAlgEquivR_commutes_residueField
    (q : PrimeSpectrum S) :
    ∀ x : (q.asIdeal.under R).ResidueField,
      fiberTensorAtPrimeBaseChangeAlgEquivR (R := R) (S := S) q
        (algebraMap (q.asIdeal.under R).ResidueField
          (((q.asIdeal.under R).Fiber S) ⊗[S] Localization.AtPrime q.asIdeal) x) =
        algebraMap (q.asIdeal.under R).ResidueField
          ((q.asIdeal.under R).ResidueField ⊗[Localization.AtPrime (q.asIdeal.under R)]
            Localization.AtPrime q.asIdeal) x := by
  intro x
  -- Proof comment: as in mathlib's smooth-fiber criterion, it is enough to compare the two
  -- `R`-algebra maps from the residue field; extensionality sees the same tensor generator.
  let p := q.asIdeal.under R
  let Sq := Localization.AtPrime q.asIdeal
  let K := p.ResidueField
  let e := fiberTensorAtPrimeBaseChangeAlgEquivR (R := R) (S := S) q
  have h :
      e.toAlgHom.comp (IsScalarTower.toAlgHom R K _) =
        IsScalarTower.toAlgHom R K _ := by
    ext
  exact DFunLike.congr_fun h x

/-- Helper for Chap10 Lemma 10 137 16: localizing the fiber tensor at `q` is the canonical
residue-field tensor over the base stalk. -/
private noncomputable def residueFieldTensorAtPrimeAlgEquiv
    (q : PrimeSpectrum S) :
    (((q.asIdeal.under R).Fiber S) ⊗[S] Localization.AtPrime q.asIdeal) ≃ₐ[
      (q.asIdeal.under R).ResidueField]
      ((q.asIdeal.under R).ResidueField ⊗[Localization.AtPrime (q.asIdeal.under R)]
        Localization.AtPrime q.asIdeal) :=
  -- Proof comment: upgrade the already normalized `R`-algebra equivalence by the named
  -- residue-field scalar-compatibility computation.
  { __ := fiberTensorAtPrimeBaseChangeAlgEquivR (R := R) (S := S) q
    commutes' := fiberTensorAtPrimeBaseChangeAlgEquivR_commutes_residueField (R := R) (S := S) q }

/-- Helper for Chap10 Lemma 10 137 16: the formal smoothness of the owner fiber local ring
transfers to the fiber tensor localized at `q`. -/
private lemma formallySmooth_fiberTensor_atPrime_of_fiberLocalRingAt
    (q : PrimeSpectrum S)
    (hfiberLocal :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)) :
    Algebra.FormallySmooth (q.asIdeal.under R).ResidueField
      (((q.asIdeal.under R).Fiber S) ⊗[S] Localization.AtPrime q.asIdeal) := by
  -- Proof comment: both rings are localizations of the same fiber ring at the canonical fiber
  -- prime, so the localization universal property gives the required scalar-compatible bridge.
  let F := (q.asIdeal.under R).Fiber S
  let N : Submonoid F := (fiberPrimeAt R S q).asIdeal.primeCompl
  letI : Algebra F (F ⊗[S] Localization.AtPrime q.asIdeal) :=
    Algebra.TensorProduct.leftAlgebra
  have hloc : IsLocalization N (F ⊗[S] Localization.AtPrime q.asIdeal) := by
    -- TODO: prove the denominator-saturation lemma saying that every element outside the
    -- canonical fiber prime divides an image of some `s : S` with `s ∉ q.asIdeal`; then apply
    -- `IsLocalization.iff_of_le_of_exists_dvd` to the tensor localization at `S \ q`.
    sorry
  letI : IsLocalization N (F ⊗[S] Localization.AtPrime q.asIdeal) := hloc
  let eF : (F ⊗[S] Localization.AtPrime q.asIdeal) ≃ₐ[F] fiberLocalRingAt R S q :=
    IsLocalization.algEquiv N (F ⊗[S] Localization.AtPrime q.asIdeal)
      (fiberLocalRingAt R S q)
  letI :
      IsScalarTower (q.asIdeal.under R).ResidueField F (fiberLocalRingAt R S q) :=
    fiberLocalRingAtResidueFieldFiberIsScalarTower (R := R) q
  let eK := eF.restrictScalars (q.asIdeal.under R).ResidueField
  letI : Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) :=
    hfiberLocal
  exact Algebra.FormallySmooth.of_equiv eK.symm

/-- Helper for Chap10 Lemma 10 137 16: formal smoothness of the owner fiber local ring gives
formal smoothness of the residue-field tensor closed fiber of the original stalk map. -/
private lemma formallySmooth_residueFieldTensor_atPrime_of_fiberLocalRingAt
    (q : PrimeSpectrum S)
    (hfiberLocal :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    Algebra.FormallySmooth (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := by
  -- Proof comment: first put the closed fiber tensor into the same base-change normal form as
  -- mathlib's local smooth-fiber criterion.
  let p : Ideal R := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  have hFiberTensor :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField
        (((q.asIdeal.under R).Fiber S) ⊗[S] Sq) :=
    formallySmooth_fiberTensor_atPrime_of_fiberLocalRingAt (R := R) (S := S) q hfiberLocal
  let eTensor := residueFieldTensorAtPrimeAlgEquiv (R := R) (S := S) q
  letI :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField
        (((q.asIdeal.under R).Fiber S) ⊗[S] Sq) := hFiberTensor
  simpa [p, Rp, Sq] using
    Algebra.FormallySmooth.of_equiv eTensor

/-- Helper for Chap10 Lemma 10 137 16: the corrected local criterion packages the finite
presentation chart, the flat stalk map, and the canonical local fiber ring into formal smoothness
of the stalk `S_q` over `R`. -/
private lemma formallySmooth_atPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberLocalRingAt
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiberLocal :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)) :
    Algebra.FormallySmooth R (Localization.AtPrime q.asIdeal) := by
  -- Route correction: the previous plan tried to apply
  -- `FormallySmooth.of_formallySmooth_residueField_tensor` with `P = S_q`.  That would require
  -- `FinitePresentation R_(q ∩ R) S_q`, which is not available and is not the right mathematical
  -- normal form for an arbitrary prime localization.  The corrected route must keep the chosen
  -- finite-presentation basic-open chart as `P`, prove that its localization maps to `S_q`, and
  -- separately identify the closed fiber of `R_(q ∩ R) → S_q` with `fiberLocalRingAt R S q`.
  -- Proof comment: choose the finite-presentation away chart and the prime of that chart lying
  -- above `q`.
  rcases hfp with ⟨g, hgq, hfinite⟩
  rcases exists_primeSpectrum_away_comap_eq_of_notMem q hgq with
    ⟨qg, hqg⟩
  let A := Localization.Away g
  let Sq := Localization.AtPrime q.asIdeal
  let Aqg := Localization.AtPrime qg.asIdeal
  -- Proof comment: first convert the local-fiber hypothesis into formal smoothness of the
  -- closed fiber tensor for the original stalk.
  have hclosedSq :
      Algebra.FormallySmooth (IsLocalRing.ResidueField
        (Localization.AtPrime (q.asIdeal.under R)))
        (TensorProduct (Localization.AtPrime (q.asIdeal.under R))
          (IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))) Sq) := by
    simpa [Sq] using
      formallySmooth_residueFieldTensor_atPrime_of_fiberLocalRingAt
        (R := R) (S := S) q hfiberLocal
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R)) Aqg :=
    RingHom.toAlgebra
      (Localization.localRingHom (q.asIdeal.under R) qg.asIdeal
        (algebraMap R A)
        (by
          rw [← localizationAway_comap_under_eq (R := R) (S := S) q hqg]))
  obtain ⟨eRing, heRing⟩ :=
    localizationAway_atPrimeRingEquivWithLocalMap (R := R) (S := S) q hqg
  obtain ⟨eRp⟩ :=
    nonempty_localizationAway_atPrimeAlgEquivWithLocalMap (R := R) (S := S) q hqg
  -- Proof comment: transport the closed fiber tensor across the chart-local equivalence.
  have hclosedAqg_base :
      Algebra.FormallySmooth (IsLocalRing.ResidueField
        (Localization.AtPrime (q.asIdeal.under R)))
        (TensorProduct (Localization.AtPrime (q.asIdeal.under R))
          (IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))) Aqg) := by
    let eTensor :
        TensorProduct (Localization.AtPrime (q.asIdeal.under R))
          (IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))) Sq ≃ₐ[
            IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))]
          TensorProduct (Localization.AtPrime (q.asIdeal.under R))
            (IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))) Aqg :=
      Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R)) ≃ₐ[
            IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))]
            IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R)))
        eRp
    letI :
        Algebra.FormallySmooth (IsLocalRing.ResidueField
          (Localization.AtPrime (q.asIdeal.under R)))
          (TensorProduct (Localization.AtPrime (q.asIdeal.under R))
            (IsLocalRing.ResidueField (Localization.AtPrime (q.asIdeal.under R))) Sq) :=
      hclosedSq
    exact Algebra.FormallySmooth.of_equiv eTensor
  have hp_eq : qg.asIdeal.under R = q.asIdeal.under R :=
    localizationAway_comap_under_eq (R := R) (S := S) q hqg
  have hqgLies : qg.asIdeal.LiesOver (q.asIdeal.under R) := by
    rw [← hp_eq]
    infer_instance
  letI : qg.asIdeal.LiesOver (q.asIdeal.under R) := hqgLies
  -- Proof comment: the chart-local equivalence also transports the supplied local flatness.
  have hflatA_base :
      (Localization.localRingHom (q.asIdeal.under R) qg.asIdeal (algebraMap R A)
        (by rw [← hp_eq])).Flat := by
    have hflat_comp :
        (eRing.toRingHom.comp
          (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl)).Flat :=
      RingHom.Flat.comp hflat (RingHom.Flat.of_bijective eRing.bijective)
    rw [heRing] at hflat_comp
    simpa using hflat_comp
  have hflatA :
      (Localization.localRingHom (q.asIdeal.under R) qg.asIdeal (algebraMap R A)
        (qg.asIdeal.over_def (q.asIdeal.under R))).Flat := by
    simpa using hflatA_base
  letI : FinitePresentation R A := hfinite
  -- Proof comment: apply the finite-presentation chart version of the local smooth-fiber
  -- criterion, then transport formal smoothness back to the original stalk.
  have hAqg : Algebra.FormallySmooth R Aqg :=
    formallySmooth_atPrime_of_flat_localRingHom_of_formallySmooth_closedFiber
      (R := R) (A := A) (p := q.asIdeal.under R) (q := qg.asIdeal) hflatA hclosedAqg_base
  let eR : Sq ≃ₐ[R] Aqg := eRp.restrictScalars R
  letI : Algebra.FormallySmooth R Aqg := hAqg
  exact Algebra.FormallySmooth.of_equiv eR.symm

/-- Helper for Chap10 Lemma 10 137 16: the remaining local criterion identifies the closed fiber
of `R_(q ∩ R) → S_q` with the canonical local fiber ring and applies the flat
finite-presentation formal-smoothness theorem. -/
private lemma isSmoothAt_of_exists_finitePresentation_nearPrime_flat_and_fiberLocalRingAt
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiberLocal :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)) :
    IsSmoothAt R q.asIdeal := by
  -- Proof comment: `IsSmoothAt` is the canonical local predicate, namely formal smoothness of the
  -- target stalk over `R`; the previous helper isolates the remaining chart and closed-fiber work.
  exact
    formallySmooth_atPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberLocalRingAt
      (R := R) q hfp hflat hfiberLocal

/- Domain-style sampling:
- primary domain: local smoothness criteria for commutative algebras at a prime, with fiber rings
  over residue fields;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.fiberPrimeAt`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `SmoothAtPrime` is the source-facing owner for smoothness on a basic open
  neighborhood, and `fiberPrimeAt R S q` is the chapter-owned point of the fiber ring over
  `q ∩ R`; the fiber smoothness hypothesis should therefore be stated directly as
  `SmoothAtPrime` at `fiberPrimeAt R S q`, not via a parallel witness prime plus compatibility
  equality;
- primitive vs. derived:
  the primitive source-facing inputs are the point `q`, a finite-presentation neighborhood near
  `q`, the local flatness of `R_(q ∩ R) → S_q`, and smoothness of the fiber ring at the canonical
  fiber prime. The auxiliary prime `qf` and the equality
  `q.asIdeal = qf.asIdeal.comap includeRight.toRingHom` were derived bridge data already owned by
  `fiberPrimeAt`.

Source/core/bridge triage:
- `source-facing`: the local Stacks criterion proving `SmoothAtPrime R S q`;
- `core/canonical`: `SmoothAtPrime`, `fiberPrimeAt`, and the local owner `IsSmoothAt`;
- `bridge/view`: the finite-presentation neighborhood witness and the implicit identification of
  `q` with the canonical fiber prime.
-/

-- Proof sketch: choose `g ∉ q` such that `R → S_g` is of finite presentation. The local map
-- `R_(q ∩ R) → S_q` is unchanged after replacing `S` by `S_g`, and the prime `qf` of the fiber
-- ring corresponds to `q`. The fiber smoothness hypothesis gives a principal-open neighborhood of
-- `qf` on which the fiber is smooth over `κ(q ∩ R)`, and the finitely presented local flatness +
-- smooth-fiber criterion then produces a principal-open neighborhood of `q` on which `R → S` is
-- smooth.
/-- Lemma 10.137.16: if some basic open neighborhood `S_g` of `q` is of finite presentation over
`R`, the local ring homomorphism `R_(q ∩ R) → S_q` is flat, and the fiber
`κ(q ∩ R) ⊗[R] S` is smooth over `κ(q ∩ R)` at the prime corresponding to `q`, then `R → S` is
smooth at `q`, i.e. some localization `S_h` with `h ∉ q` is smooth over `R`. -/
@[stacks 00TF]
lemma smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiber :
      SmoothAtPrime (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
        (fiberPrimeAt R S q)) :
    SmoothAtPrime R S q := by
  -- Proof comment: first convert the source-facing fiber hypothesis to the canonical local fiber
  -- formal smoothness used by the local criterion.
  have hfiberLocal :
      Algebra.FormallySmooth (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) :=
    formallySmooth_fiberLocalRingAt_of_smoothAtPrime (R := R) q hfiber
  -- Proof comment: apply the unresolved local formal-smoothness criterion at the original stalk.
  have hIs : IsSmoothAt R q.asIdeal :=
    isSmoothAt_of_exists_finitePresentation_nearPrime_flat_and_fiberLocalRingAt
      (R := R) q hfp hflat hfiberLocal
  -- Proof comment: the finite-presentation chart now only packages local smoothness as a smooth
  -- principal open neighborhood of `q`.
  exact smoothAtPrime_of_isSmoothAt_of_finitePresentation_nearPrime (R := R) q hfp hIs

end Algebra
