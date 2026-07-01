import Mathlib
import stacks_project.Chap10.Definition_10_112_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum
open Ideal.Quotient

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing S]

omit [IsNoetherianRing S] in
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

-- Proof sketch: apply the canonical height inequality
-- `Ideal.height_le_height_add_of_liesOver` to the maximal ideal of `S_q`, viewed as a prime of
-- `Localization.AtPrime q` lying over `p`. Then rewrite the three height terms as the Krull
-- dimensions of `S_q`, `R_p`, and the quotient `S_q / pS_q`, using the local-ring maximal-ideal
-- formula and `IsLocalization.AtPrime.ringKrullDim_eq_height`.
/-- Lemma 10.112.6: if `R → S` is a ring homomorphism, `S` is Noetherian, `p` is a prime ideal of
`R`, and `q` is a prime ideal of `S` lying over `p`, then the Krull dimension of `S_q` is at most
the sum of the Krull dimension of `R_p` and the Krull dimension of the local fiber ring at the
corresponding point of `Spec (κ(p) ⊗[R] S)`. -/
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
  have hmain : P.height ≤ p.height + (P.map (Ideal.Quotient.mk I)).height :=
    by
      -- Reduce to the noetherian-source case and apply
      -- `Ideal.height_le_height_add_of_liesOver`.
      sorry
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
