import Mathlib
import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Definition_10_112_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum
open Ideal.Quotient

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- The quotient presentation
`(Localization.AtPrime q.asIdeal) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
    (Ideal.comap (algebraMap R S) q.asIdeal)`
has the same Krull dimension as the canonical local fiber ring at `q`. This is the bridge from the
presentation-level quotient to the Chapter 10 owner abstraction `fiberLocalRingAt`. -/
theorem ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
    (q : PrimeSpectrum S) :
    ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) =
      ringKrullDim (fiberLocalRingAt R S q) := by
  let p : PrimeSpectrum R := comap (algebraMap R S) q
  let Sq := Localization.AtPrime q.asIdeal
  let I : Ideal Sq := Ideal.map (algebraMap R Sq) p.asIdeal
  let qOver : ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) := ⟨q, rfl⟩
  let Z : Set (PrimeSpectrum Sq) := PrimeSpectrum.zeroLocus I
  let eQuot : PrimeSpectrum (Sq ⧸ I) ≃o Z :=
    I.primeSpectrumQuotientOrderIsoZeroLocus
  let eLoc : PrimeSpectrum Sq ≃o Set.Iic q :=
    IsLocalization.AtPrime.primeSpectrumOrderIso Sq q.asIdeal
  let eZero : Z ≃o Set.Iic qOver :=
    { toEquiv :=
        { toFun := fun x ↦ by
            let y : Set.Iic q := eLoc x.1
            have hp_le :
                p.asIdeal ≤ Ideal.comap (algebraMap R Sq) x.1.asIdeal :=
              Ideal.map_le_iff_le_comap.mp x.2
            have hy_eq : comap (algebraMap R S) y.1 = p := by
              apply PrimeSpectrum.ext
              refine le_antisymm ?_ ?_
              · simpa [p] using Ideal.comap_mono y.2
              · simpa [y, eLoc, p, Sq, PrimeSpectrum.comap_asIdeal,
                  IsScalarTower.algebraMap_eq R S Sq] using hp_le
            refine ⟨⟨y.1, hy_eq⟩, ?_⟩
            change y.1 ≤ q
            exact y.2
          invFun := fun y ↦ by
            let y' : Set.Iic q := ⟨y.1.1, y.2⟩
            refine ⟨eLoc.symm y', ?_⟩
            have hy' : comap (algebraMap R S) y'.1 = p := y.1.2
            have hright : (eLoc (eLoc.symm y')).1 = y'.1 :=
              congrArg Subtype.val (eLoc.right_inv y')
            have hcomap :
                Ideal.comap (algebraMap S Sq) (eLoc.symm y').asIdeal = y'.1.asIdeal := by
              change (eLoc (eLoc.symm y')).1.asIdeal = y'.1.asIdeal
              simpa using congrArg PrimeSpectrum.asIdeal hright
            have hcomapR : Ideal.comap (algebraMap R Sq) (eLoc.symm y').asIdeal = p.asIdeal := by
              change Ideal.comap (algebraMap R S)
                  (Ideal.comap (algebraMap S Sq) (eLoc.symm y').asIdeal) = p.asIdeal
              rw [hcomap]
              simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hy'
            change eLoc.symm y' ∈ PrimeSpectrum.zeroLocus I
            exact Ideal.map_le_iff_le_comap.mpr hcomapR.ge
          left_inv := fun x ↦ by
            apply Subtype.ext
            simpa [eLoc, qOver] using eLoc.left_inv x.1
          right_inv := fun y ↦ by
            apply Subtype.ext
            apply Subtype.ext
            simpa [eLoc, qOver] using congrArg Subtype.val (eLoc.right_inv ⟨y.1.1, y.2⟩) }
      map_rel_iff' := by
        intro x y
        change eLoc x.1 ≤ eLoc y.1 ↔ x.1 ≤ y.1
        exact eLoc.map_rel_iff' }
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ≃o PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageOrderIsoFiber R S p
  let eFiber : Set.Iic qOver ≃o Set.Iic (fiberPrimeAt R S q) :=
    { toEquiv :=
        { toFun := fun x ↦ by
            refine ⟨ePre x.1, ?_⟩
            have hx : ePre x.1 ≤ ePre qOver := (ePre.map_rel_iff').2 x.2
            simpa [fiberPrimeAt, p, qOver] using hx
          invFun := fun y ↦ by
            refine ⟨ePre.symm y.1, ?_⟩
            have hy : y.1 ≤ ePre qOver := by
              change y.1 ≤ fiberPrimeAt R S q
              exact y.2
            have hy' : ePre (ePre.symm y.1) ≤ ePre qOver := by
              simpa using hy
            exact (ePre.map_rel_iff').1 hy'
          left_inv := fun x ↦ by
            apply Subtype.ext
            simpa using ePre.left_inv x.1
          right_inv := fun y ↦ by
            apply Subtype.ext
            simpa using ePre.right_inv y.1 }
      map_rel_iff' := by
        intro x y
        change ePre x.1 ≤ ePre y.1 ↔ x.1 ≤ y.1
        exact ePre.map_rel_iff' }
  calc
    ringKrullDim (Sq ⧸ I) = Order.krullDim (PrimeSpectrum (Sq ⧸ I)) := rfl
    _ = Order.krullDim (Set.Iic (fiberPrimeAt R S q)) := by
      exact Order.krullDim_eq_of_orderIso (eQuot.trans (eZero.trans eFiber))
    _ = ringKrullDim (fiberLocalRingAt R S q) := by
      simpa [ringKrullDim, fiberLocalRingAt] using
        (Order.krullDim_eq_of_orderIso
          (IsLocalization.AtPrime.primeSpectrumOrderIso
            (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal)).symm

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Helper for Lemma 10.112.6: after localizing at a prime `q` lying over `p`, the extension of
the maximal ideal of `R_p` to `S_q` is exactly the localized ideal `pS_q`. -/
lemma localized_base_prime_eq_map_maximalIdeal
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
    Ideal.map (algebraMap R (Localization.AtPrime q)) p := by
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  letI : q.LiesOver p := hq
  -- Rewrite `𝔪_{R_p}` as the localization of `p`, then compose the two localization maps.
  calc
    Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp) =
        Ideal.map (algebraMap Rp Sq) (Ideal.map (algebraMap R Rp) p) := by
          rw [Localization.AtPrime.map_eq_maximalIdeal]
    _ = Ideal.map ((algebraMap Rp Sq).comp (algebraMap R Rp)) p := by
          simpa using (Ideal.map_map (I := p) (algebraMap R Rp) (algebraMap Rp Sq))
    _ = Ideal.map (algebraMap R Sq) p := by
          congr 1
          ext x
          simp [Rp, Sq, IsScalarTower.algebraMap_eq R Rp Sq]

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Helper for Lemma 10.112.6: a quotient parameter ideal in `S_q / pS_q` lifts to an ideal
`K ⊆ S_q` whose image is exactly that parameter ideal. This packages the quotient-side generator
lifting used in the source proof. -/
lemma exists_lift_parameterIdeal_of_quotient
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [Nontrivial ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q)) p)]
    [IsLocalRing ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q)) p)]
    {e : ℕ}
    (y : Fin e → IsLocalRing.maximalIdeal
      ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q)) p))
    :
    ∃ K : Ideal (Localization.AtPrime q),
      Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime q)) p)) K =
        IsLocalRing.parameterIdeal y ∧
      K ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  let Sq := Localization.AtPrime q
  let I : Ideal Sq := Ideal.map (algebraMap R Sq) p
  let Q := Sq ⧸ I
  let P : Ideal Sq := IsLocalRing.maximalIdeal Sq
  have hmax : P.map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal Q := by
    -- The quotient map is surjective and local, so it sends the maximal ideal onto the quotient
    -- maximal ideal.
    dsimp [P, Q]
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hy_mem :
      ∀ i : Fin e, (y i : Q) ∈ Ideal.map (Ideal.Quotient.mk I) P := by
    intro i
    simpa [Q, hmax] using (y i).2
  have hlift :
      ∀ i : Fin e, ∃ r : Sq, r ∈ P ∧ Ideal.Quotient.mk I r = (y i : Q) := by
    intro i
    simpa [Q] using
      (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
        (hf := Ideal.Quotient.mk_surjective) (I := P) (y := (y i : Q))).1 (hy_mem i)
  choose r hr_mem hr_eq using hlift
  let ySq : Fin e → P := fun i ↦ ⟨r i, hr_mem i⟩
  let K : Ideal Sq := IsLocalRing.parameterIdeal ySq
  have hK_le : K ≤ P := by
    -- The lifted generators still lie in the maximal ideal of `S_q`.
    rw [show K = IsLocalRing.parameterIdeal ySq by rfl, IsLocalRing.parameterIdeal_eq_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (ySq i).2
  have hmapK : Ideal.map (Ideal.Quotient.mk I) K = IsLocalRing.parameterIdeal y := by
    -- The quotient image of the lifted generators recovers exactly the original parameter ideal.
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, IsLocalRing.parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_comap.2 ?_
      change Ideal.Quotient.mk I ((ySq i : P) : Sq) ∈ IsLocalRing.parameterIdeal y
      rw [show Ideal.Quotient.mk I ((ySq i : P) : Sq) = (y i : Q) by
        simpa [ySq] using hr_eq i]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [IsLocalRing.parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hyi_mem : ((ySq i : P) : Sq) ∈ K := by
        rw [show K = IsLocalRing.parameterIdeal ySq by rfl, IsLocalRing.parameterIdeal_eq_span]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hyi_map_mem : (y i : Q) ∈ Ideal.map (Ideal.Quotient.mk I) K := by
        refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
          (hf := Ideal.Quotient.mk_surjective) (I := K) (y := (y i : Q))).2 ?_
        refine ⟨((ySq i : P) : Sq), hyi_mem, ?_⟩
        simpa [ySq] using hr_eq i
      simpa using hyi_map_mem
  exact ⟨K, hmapK, hK_le⟩

-- Proof sketch: apply the canonical height inequality
-- `Ideal.height_le_height_add_of_liesOver` to the maximal ideal of `S_q`, viewed as a prime of
-- `Localization.AtPrime q` lying over `p`. Then rewrite the three height terms as the Krull
-- dimensions of `S_q`, `R_p`, and the quotient `S_q / pS_q`, using the local-ring maximal-ideal
-- formula and `IsLocalization.AtPrime.ringKrullDim_eq_height`.
/-- Lemma 10.112.6: if `R → S` is a homomorphism of Noetherian rings, `p` is a prime ideal of
`R`, and `q` is a prime ideal of `S` lying over `p`, then the Krull dimension of `S_q` is at most
the sum of the Krull dimension of `R_p` and the Krull dimension of the local fiber ring at the
corresponding point of `Spec (κ(p) ⊗[R] S)`. -/
@[stacks 00OM]
theorem ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) ≤
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim (fiberLocalRingAt R S ⟨q, inferInstance⟩) := by
  let Sq := Localization.AtPrime q
  let Rp := Localization.AtPrime p
  let P : Ideal Sq := IsLocalRing.maximalIdeal Sq
  let I : Ideal Sq := Ideal.map (algebraMap R Sq) p
  let Q := Sq ⧸ I
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  have hPq : P.LiesOver q := by
    dsimp [P, Sq]
    infer_instance
  letI := hPq
  letI := hq
  have hPp : P.LiesOver p := Ideal.LiesOver.trans P q p
  letI := hPp
  have hq_under : Ideal.comap (algebraMap R S) q = p := by
    simpa using hq.over.symm
  have hI_le : I ≤ P := Ideal.map_le_iff_le_comap.mpr hPp.over.le
  have hI_ne_top : I ≠ ⊤ := by
    intro hI
    have hP_ne_top : P ≠ ⊤ := by
      dsimp [P, Sq]
      exact (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top
    exact hP_ne_top (top_le_iff.mp (hI ▸ hI_le))
  have hmain : P.height ≤ p.height + (P.map (Ideal.Quotient.mk I)).height := by
    simpa [I, Sq] using
      (Ideal.height_le_height_add_of_liesOver (R := R) (S := Sq) p P)
  haveI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 hI_ne_top
  haveI : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : P.map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal Q := by
    dsimp [P, Q]
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hSq : ringKrullDim Sq = ↑P.height := by
    dsimp [P]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
  have hp' : ↑p.height = ringKrullDim Rp := by
    simpa [Rp] using (IsLocalization.AtPrime.ringKrullDim_eq_height p Rp).symm
  have hQ :
      ↑(IsLocalRing.maximalIdeal Q).height = ringKrullDim (fiberLocalRingAt R S q') := by
    rw [← ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt q']
    have hQquot :
        ringKrullDim
            ((Localization.AtPrime q'.asIdeal) ⧸
              Ideal.map (algebraMap R (Localization.AtPrime q'.asIdeal))
                (Ideal.comap (algebraMap R S) q'.asIdeal)) =
          ringKrullDim Q := by
      rw [hq_under]
    rw [hQquot]
    have hmaxQ : (IsLocalRing.maximalIdeal Q).height = ringKrullDim Q :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim
    exact hmaxQ
  simpa [Sq, Rp, Q, I] using
    calc
    ringKrullDim Sq = ↑P.height := hSq
    _ ≤ ↑p.height + ↑(P.map (Ideal.Quotient.mk I)).height := by
      exact_mod_cast hmain
    _ = ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q') := by
      rw [hp', hmax, hQ]

end
