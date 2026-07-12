import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Definition_10_69_1
import StacksProject_2024.Chap10.Lemma_10_137_12
import StacksProject_2024.Chap10.Lemma_10_137_16
import StacksProject_2024.Chap15.Lemma_15_31_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory
open scoped TensorProduct

namespace RingTheory.Sequence

section

variable {A' : Type u} [CommRing A']
variable {B' : Type u} [CommRing B'] [Algebra A' B']
variable [Module.Flat A' B'] [Algebra.FinitePresentation A' B']
variable {I : Ideal A'} {r : ℕ} (f' : Fin r → B')

local notation "IB" => Ideal.map (algebraMap A' B') I
local notation "FiberRing" => B' ⧸ IB
local notation "fbar" => fun i : Fin r ↦ Ideal.Quotient.mk IB (f' i)
local notation "FiberQuot" => FiberRing ⧸ Ideal.span (Set.range fbar)
local notation "Quot" => B' ⧸ Ideal.span (Set.range f')

/- Domain-style sampling for Lemma 15.31.6:
* primary domain: smooth quotients by finite quasi-regular sequences across a locally nilpotent
  thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent`,
  `Algebra.smooth_iff_forall_smoothAtPrime`;
* best owner abstraction: this theorem is `source-facing` and should remain a direct smoothness
  statement for the quotient ring, while the ambient flatness and finite presentation of
  `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive inputs are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, the tuple `f'`, and the smooth closed fiber `FiberQuot`; the quotient
  presentations `FiberRing`, `FiberQuot`, and `Quot` are only bridge views.

Source/core/bridge triage:
* `source-facing`: the smoothness of `Quot` over `A'`;
* `core/canonical`: `Algebra.Smooth`, `Module.Flat`, `Algebra.FinitePresentation`,
  `Ideal.IsLocallyNilpotent`, and `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: Lemma `15.31.5` gives flatness of `Quot` over `A'`. Smoothness of the closed
-- fiber `FiberQuot` over `A' ⧸ I` implies finite presentation of `FiberQuot`, hence finite
-- presentation of `Quot` over `A'` across the locally nilpotent thickening. For every prime of
-- `Quot`, reduction modulo `I` leaves the fiber over the corresponding prime of `A'` unchanged,
-- so the fiber is smooth by
-- the hypothesis on `FiberQuot`. The flat finitely presented smooth-fiber criterion then yields
-- smoothness of `Quot` over `A'`.
--
-- Route correction: `Lemma_15_31_5` is the canonical owner of the locally nilpotent/prime and
-- residue-field quotient helpers, so this file reuses those imported declarations instead of
-- redeclaring local copies.

/-- Helper for Lemma 15.31.6: quotienting `Quot` by the extended ideal from `I` recovers the
closed-fiber quotient `FiberQuot`. -/
noncomputable abbrev quotient_mod_extendedIdeal_algEquiv_fiberQuot :
    (Quot ⧸ Ideal.map (algebraMap A' Quot) I) ≃ₐ[A' ⧸ I] FiberQuot := by
  let J : Ideal B' := Ideal.span (Set.range f')
  let Jbar : Ideal FiberRing := Ideal.map (Ideal.Quotient.mk IB) J
  let φ : Quot →ₐ[A'] (FiberRing ⧸ Jbar) :=
    Ideal.quotientMapₐ Jbar (Ideal.Quotient.mkₐ A' IB) Ideal.le_comap_map
  have hJbar : Jbar = Ideal.span (Set.range fbar) := by
    have hImage :
        (Ideal.Quotient.mk IB) '' Set.range f' = Set.range fbar := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f' i, ⟨i, rfl⟩, rfl⟩
    -- Mapping the span of the generators `f'` into `FiberRing` produces exactly the span of the
    -- induced classes `fbar`.
    calc
      Jbar = Ideal.span ((Ideal.Quotient.mk IB) '' Set.range f') := by
        simp [Jbar, J, Ideal.map_span]
      _ = Ideal.span (Set.range fbar) := by
        rw [hImage]
  have hmapI :
      Ideal.map (Ideal.Quotient.mk J) IB = Ideal.map (algebraMap A' Quot) I := by
    -- Quotienting `B'` first by `(f')` sends the extended ideal `IB` to the extended ideal of
    -- `I` in the quotient ring `Quot`.
    change Ideal.map (Ideal.Quotient.mk J) (Ideal.map (algebraMap A' B') I) =
      Ideal.map (algebraMap A' Quot) I
    rw [Ideal.map_map]
    rfl
  have hker :
      RingHom.ker φ.toRingHom = Ideal.map (algebraMap A' Quot) I := by
    -- The kernel of the canonical quotient-of-quotient map is the image of `IB` in `Quot`.
    calc
      RingHom.ker φ.toRingHom = Ideal.map (Ideal.Quotient.mk J) IB := by
        simpa [Jbar, φ] using (Ideal.ker_quotientMap_mk (I := IB) (J := J))
      _ = Ideal.map (algebraMap A' Quot) I := hmapI
  have hsurj : Function.Surjective φ := by
    -- Surjectivity is inherited from the two successive quotient maps.
    intro y
    rcases Ideal.Quotient.mk_surjective y with ⟨a, rfl⟩
    rcases Ideal.Quotient.mk_surjective a with ⟨x, rfl⟩
    exact ⟨Ideal.Quotient.mk J x, rfl⟩
  letI : Algebra (A' ⧸ I) (Quot ⧸ RingHom.ker φ.toRingHom) :=
    RingHom.toAlgebra <|
      Ideal.Quotient.lift I
        (algebraMap A' (Quot ⧸ RingHom.ker φ.toRingHom))
        (fun a ha ↦ by
          change Ideal.Quotient.mk (RingHom.ker φ.toRingHom) ((algebraMap A' Quot) a) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, hker]
          exact Ideal.mem_map_of_mem (algebraMap A' Quot) ha)
  let eDomain :
      (Quot ⧸ Ideal.map (algebraMap A' Quot) I) ≃ₐ[A' ⧸ I]
        (Quot ⧸ RingHom.ker φ.toRingHom) :=
    AlgEquiv.ofRingEquiv
      (R := A' ⧸ I)
      (f := Ideal.quotEquivOfEq hker.symm)
      (fun x ↦ by
        refine Quotient.inductionOn x ?_
        intro a
        change Ideal.quotEquivOfEq hker.symm
            (Ideal.Quotient.mk (Ideal.map (algebraMap A' Quot) I) ((algebraMap A' Quot) a)) =
          algebraMap (A' ⧸ I) (Quot ⧸ RingHom.ker φ.toRingHom) (Ideal.Quotient.mk I a)
        rfl)
  let eKer : (Quot ⧸ RingHom.ker φ.toRingHom) ≃ₐ[A' ⧸ I] (FiberRing ⧸ Jbar) :=
    AlgEquiv.ofRingEquiv
      (R := A' ⧸ I)
      (f := (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurj).toRingEquiv)
      (fun x ↦ by
        refine Quotient.inductionOn x ?_
        intro a
        -- On scalar classes, the quotient-kernel equivalence is still the canonical quotient map.
        change (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurj)
            (Ideal.Quotient.mk (RingHom.ker φ.toRingHom) ((algebraMap A' Quot) a)) =
          algebraMap (A' ⧸ I) (FiberRing ⧸ Jbar) (Ideal.Quotient.mk I a)
        have hcomm :
            φ (algebraMap A' Quot a) =
              algebraMap (A' ⧸ I) (FiberRing ⧸ Jbar) (Ideal.Quotient.mk I a) := by
          calc
            φ (algebraMap A' Quot a) = algebraMap A' (FiberRing ⧸ Jbar) a := φ.commutes a
            _ = algebraMap (A' ⧸ I) (FiberRing ⧸ Jbar) (Ideal.Quotient.mk I a) := by
              rfl
        calc
          (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurj)
              (Ideal.Quotient.mk (RingHom.ker φ.toRingHom) ((algebraMap A' Quot) a)) =
            φ (algebraMap A' Quot a) := by
              exact Ideal.quotientKerAlgEquivOfSurjective_mk
                (f := φ) hsurj (algebraMap A' Quot a)
          _ = algebraMap (A' ⧸ I) (FiberRing ⧸ Jbar) (Ideal.Quotient.mk I a) := hcomm
      )
  -- Reidentify the kernel quotient with `Quot / IQuot`, then rewrite the target quotient ideal as
  -- the textbook closed-fiber ideal generated by the classes `fbar`.
  exact
    eDomain.trans <|
      eKer.trans <|
        Ideal.quotientEquivAlgOfEq (A' ⧸ I) hJbar

/-- Helper for Lemma 15.31.6: the canonical tensor base change of `Quot` along `A' → A' ⧸ I`
identifies with the closed-fiber quotient `FiberQuot`. -/
noncomputable abbrev mod_ideal_baseChange_algEquiv_fiberQuot :
    ((A' ⧸ I) ⊗[A'] Quot) ≃ₐ[A' ⧸ I] FiberQuot :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Quot I).symm.trans
    (quotient_mod_extendedIdeal_algEquiv_fiberQuot (f' := f'))

/-- Helper for Lemma 15.31.6: the fiber ring of `A' → Quot` at `q` is the residue-field base
change of `FiberQuot`. -/
noncomputable abbrev fiber_quotient_baseChange_equiv
    (p : PrimeSpectrum A')
    [Algebra (A' ⧸ I) p.asIdeal.ResidueField]
    [IsScalarTower A' (A' ⧸ I) p.asIdeal.ResidueField] :
    p.asIdeal.Fiber Quot ≃ₐ[p.asIdeal.ResidueField]
      p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot := by
  -- Route correction: factor the fiber comparison through the canonical tensor base change first,
  -- then cancel the redundant middle tensor product over `A' ⧸ I`.
  exact
    (Algebra.TensorProduct.cancelBaseChange A' (A' ⧸ I) p.asIdeal.ResidueField
      p.asIdeal.ResidueField Quot).symm.trans <|
      Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField) <|
        mod_ideal_baseChange_algEquiv_fiberQuot (f' := f')

/-- Helper for Lemma 15.31.6: the fiber of `A' → Quot` at a prime of `Quot` is smooth because it
is the base change of the smooth quotient over `A' ⧸ I`. -/
lemma fiber_smoothAtPrime_of_smooth_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hsmooth : Algebra.Smooth (A' ⧸ I) FiberQuot)
    (q : PrimeSpectrum Quot) :
    Algebra.SmoothAtPrime (q.asIdeal.under A').ResidueField
      ((q.asIdeal.under A').Fiber Quot) (fiberPrimeAt A' Quot q) := by
  let p : PrimeSpectrum A' := PrimeSpectrum.comap (algebraMap A' Quot) q
  have hpI : I ≤ p.asIdeal := locallyNilpotent_le_prime (I := I) hI p
  let _ : Algebra (A' ⧸ I) p.asIdeal.ResidueField := residueField_quotient_algebra (I := I) p hpI
  letI : IsScalarTower A' (A' ⧸ I) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A' p.asIdeal.ResidueField a =
        Ideal.Quotient.lift I (algebraMap A' p.asIdeal.ResidueField)
          (fun b hb ↦ by
            simpa [Ideal.algebraMap_quotient_residueField_mk] using (hpI hb : b ∈ p.asIdeal))
          (Ideal.Quotient.mk I a)
      rw [Ideal.Quotient.lift_mk]
  let e :
      p.asIdeal.Fiber Quot ≃ₐ[p.asIdeal.ResidueField]
        p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot :=
    fiber_quotient_baseChange_equiv (f' := f') (I := I) p
  have hsmoothBase :
      Algebra.Smooth p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot) := by
    -- Base change preserves smoothness from `A' ⧸ I → FiberQuot` to the residue field.
    letI : Algebra.Smooth (A' ⧸ I) FiberQuot := hsmooth
    infer_instance
  have hsmoothFiber : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber Quot) := by
    -- Transport the smooth base-changed fiber back across the canonical fiber equivalence.
    letI :
        Algebra.Smooth p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot) := hsmoothBase
    let e' :
        p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot ≃ₐ[p.asIdeal.ResidueField]
          p.asIdeal.Fiber Quot := e.symm
    exact
      (Algebra.Smooth.of_equiv
        (R := p.asIdeal.ResidueField)
        (A := p.asIdeal.ResidueField ⊗[A' ⧸ I] FiberQuot)
        (B := p.asIdeal.Fiber Quot) e')
  letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber Quot) := hsmoothFiber
  -- Every prime of a smooth algebra is smooth, so the canonical fiber prime is smooth.
  exact
    (Algebra.smooth_iff_forall_smoothAtPrime p.asIdeal.ResidueField (p.asIdeal.Fiber Quot)).1
      inferInstance (fiberPrimeAt A' Quot q)

/-- Lemma 15.31.6: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient
`(B' / I B') / (f'_1, \ldots, f'_r)` is smooth over `A' / I`, then `B' / (f'_1, \ldots, f'_r)`
is smooth over `A'`. -/
@[stacks 0CER]
theorem smooth_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hsmooth : Algebra.Smooth (A' ⧸ I) FiberQuot) :
    Algebra.Smooth A' Quot := by
  -- The closed-fiber quotient is smooth, hence flat, so Lemma `15.31.5` upgrades flatness to the
  -- target quotient over `A'`.
  have hflatFiber : Module.Flat (A' ⧸ I) FiberQuot := by
    letI : Algebra.Smooth (A' ⧸ I) FiberQuot := hsmooth
    infer_instance
  have hflatQuot : Module.Flat A' Quot :=
    flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent (f' := f') hI hqr hflatFiber
  letI : Module.Flat A' Quot := hflatQuot
  -- The quotient ideal is finitely generated by the finite family `f'`, so `Quot` is finitely
  -- presented over `A'`.
  have hfg : (Ideal.span (Set.range f')).FG := by
    simpa using (Submodule.fg_span (Set.finite_range f') : (Ideal.span (Set.range f')).FG)
  letI : Algebra.FinitePresentation A' Quot := Algebra.FinitePresentation.quotient hfg
  -- Apply the source proof's primewise smoothness criterion.
  refine (Algebra.smooth_iff_forall_smoothAtPrime A' Quot).2 ?_
  intro q
  have hfp : ∃ g : Quot, g ∉ q.asIdeal ∧ Algebra.FinitePresentation A' (Localization.Away g) := by
    -- Global finite presentation gives the neighborhood witness with `g = 1`.
    refine ⟨1, ?_, inferInstance⟩
    intro h1
    have htop : q.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem q.asIdeal h1 (isUnit_one)
    exact (Ideal.IsPrime.ne_top (I := q.asIdeal) inferInstance) htop
  have hflat :
      (Localization.localRingHom (q.asIdeal.under A') q.asIdeal (algebraMap A' Quot) rfl).Flat := by
    -- Flatness localizes from `A' → Quot` to the local map at `q`.
    have hflatAlg : (algebraMap A' Quot).Flat := by
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    exact RingHom.Flat.localRingHom hflatAlg q.asIdeal (q.asIdeal.under A') rfl
  -- The remaining work is the fiber comparison with the smooth quotient modulo `I`.
  exact
    Algebra.smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
      q hfp hflat
      (fiber_smoothAtPrime_of_smooth_mod_locallyNilpotent (f' := f') hI hsmooth q)

end

end RingTheory.Sequence
