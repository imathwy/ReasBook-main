import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_112_1 (from Chap10) -/
universe u v

/-
Domain-style sampling for Lemma 10.112.1:
- primary domain: Krull dimension of prime spectra under going up / going down.
- owner declarations inspected:
  `topologicalKrullDim_le_of_surjective_specializing_or_generalizing`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `SpecializingMap (PrimeSpectrum.comap f)`,
  `GeneralizingMap (PrimeSpectrum.comap f)`.
- best owner abstraction: the topological Krull-dimension comparison for a surjective map with
  specialization/generalization lifting, specialized along the canonical spectrum map
  `PrimeSpectrum.comap f`.
- primitive data: only the surjectivity of `PrimeSpectrum.comap f` and one of the two canonical
  lifting predicates.
- derived API: the ring-level inequality on `ringKrullDim`.

Layer triage:
- `source-facing`: the ring-theoretic dimension inequality for a ring homomorphism.
- `core/canonical`: `topologicalKrullDim_le_of_surjective_specializing_or_generalizing` and
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
- `bridge/view`: this file's theorem, transporting the topological owner theorem to
  `ringKrullDim`.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Proof sketch: this is exactly the Chapter 5 topological Krull-dimension comparison specialized
-- to the canonical spectrum map `PrimeSpectrum.comap f`, then transported back to ring-theoretic
-- Krull dimension by `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
/-- Lemma 10.112.1: if the induced map `Spec(S) → Spec(R)` is surjective and lifts either
specializations or generalizations, equivalently if the ring map satisfies going up or going down,
then `dim(R) ≤ dim(S)`. -/
theorem ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
    (f : R →+* S) (hSurj : Function.Surjective (PrimeSpectrum.comap f))
    (hLift :
      SpecializingMap (PrimeSpectrum.comap f) ∨
        GeneralizingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := by
  let comap : PrimeSpectrum S → PrimeSpectrum R := PrimeSpectrum.comap f
  -- Repackage the source hypotheses along the local alias so they match the Chapter 5 theorem.
  have hSurj' : Function.Surjective comap := by
    simpa [comap] using hSurj
  have hLift' : SpecializingMap comap ∨ GeneralizingMap comap := by
    simpa [comap] using hLift
  -- Apply the topological Krull-dimension inequality on spectra, then translate back to rings.
  simpa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
    topologicalKrullDim_le_of_surjective_specializing_or_generalizing
      (PrimeSpectrum.continuous_comap f) hSurj' hLift'

end

/-! ### Lemma_10_112_2 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: view the maximal ideal `q` as a closed point of `Spec(S)`. A specializing map
-- sends the closure of a singleton to a closed set; since `q` is already closed, its image in
-- `Spec(R)` is a closed point. Translating closed points back to maximal ideals gives the result.
/-- Lemma 10.112.2: for a ring map `R → S` with the going-up property, the inverse image in `R` of
a maximal ideal of `S` is again a maximal ideal. -/
theorem isMaximal_comap_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (q : Ideal S) [q.IsMaximal] :
    (q.comap (algebraMap R S)).IsMaximal := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  have hx : IsClosed ({x} : Set (PrimeSpectrum S)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2 inferInstance
  have hclosed :
      IsClosed (PrimeSpectrum.comap (algebraMap R S) '' closure ({x} : Set (PrimeSpectrum S))) :=
    (specializingMap_iff_isClosed_image_closure_singleton
      (PrimeSpectrum.continuous_comap (algebraMap R S))).1 hgu x
  have hclosed' : IsClosed ({PrimeSpectrum.comap (algebraMap R S) x} : Set (PrimeSpectrum R)) := by
    simpa [hx.closure_eq] using hclosed
  simpa [x, PrimeSpectrum.comap_asIdeal] using
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap (algebraMap R S) x)).1
      hclosed'

end

/-! ### Lemma_10_112_3 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

-- Proof sketch: contraction along an integral ring map is strictly monotone on prime ideals.
-- Indeed, if `q ⊊ q'` in `S`, choose `x ∈ q' \ q`; since `x` is integral over `R`,
-- `Ideal.comap_lt_comap_of_integral_mem_sdiff` shows `q ∩ R ⊊ q' ∩ R`. Applying the canonical
-- order-theoretic Krull-dimension monotonicity theorem to `PrimeSpectrum.comap (algebraMap R S)`
-- gives the result directly.
/-- Lemma 10.112.3 (1): if `R → S` is an integral ring map, then the Krull dimension of `S` is at
most the Krull dimension of `R`. -/
theorem ringKrullDim_le_of_isIntegral :
    ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun {q q'} hqq' ↦ by
    change Ideal.comap (algebraMap R S) q.asIdeal < Ideal.comap (algebraMap R S) q'.asIdeal
    have hqq'_ideal : q.asIdeal < q'.asIdeal := by
      simpa using hqq'
    rcases SetLike.lt_iff_le_and_exists.mp hqq'_ideal with ⟨hqq', x, hxq', hxq⟩
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hqq' ⟨hxq', hxq⟩
      (Algebra.IsIntegral.isIntegral x)

/- Lemma 10.112.3 (2): if `q` is a closed point of `Spec(S)` for an integral ring map `R → S`,
then its image in `Spec(R)` is a closed point. This is exactly the canonical mathlib theorem
`PrimeSpectrum.isClosed_comap_singleton_of_isIntegral` specialized to `algebraMap R S`. -/
recall PrimeSpectrum.isClosed_comap_singleton_of_isIntegral

end

/-! ### Lemma_10_112_4 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

-- Proof sketch: combine the upper bound `ringKrullDim S ≤ ringKrullDim R` from Lemma `10.112.3`
-- with the lower bound `ringKrullDim R ≤ ringKrullDim S` obtained from the surjectivity of
-- `Spec(S) → Spec(R)` for an integral map with injective `algebraMap`, using the canonical owner
-- theorem `RingHom.IsIntegral.comap_surjective` and the specializing-map comparison of
-- Lemma `10.112.1`.
/-- Lemma 10.112.4: if `R` is identified with a subring of `S` and `S` is integral over `R`, then
the Krull dimensions of `R` and `S` are equal. -/
theorem ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  have hInt : (algebraMap R S).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  apply le_antisymm
  · exact ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
      (algebraMap R S)
      (RingHom.IsIntegral.comap_surjective hInt hinj)
      (.inl <| (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S) hInt).specializingMap)
  · exact ringKrullDim_le_of_isIntegral

end

/-! ### Definition_10_112_5 (from Chap10) -/
noncomputable section

universe u v

open PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The prime of the fiber ring `κ(q ∩ R) ⊗[R] S` corresponding to `q : Spec S`. -/
abbrev fiberPrimeAt (q : PrimeSpectrum S) : PrimeSpectrum ((q.asIdeal.under R).Fiber S) :=
  preimageEquivFiber R S (comap (algebraMap R S) q) ⟨q, rfl⟩

/-- Definition 10.112.5: for a prime `q : Spec S`, the local ring of the fiber at `q` is the
local ring of the fiber ring `κ(q ∩ R) ⊗[R] S` at the corresponding prime. -/
def fiberLocalRingAt (q : PrimeSpectrum S) : Type _ :=
  Localization.AtPrime (fiberPrimeAt R S q).asIdeal

/-- The local ring of the fiber at `q` is canonically a commutative ring. -/
instance fiberLocalRingAtCommRing (q : PrimeSpectrum S) : CommRing (fiberLocalRingAt R S q) := by
  change CommRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically a local ring. -/
instance fiberLocalRingAtIsLocalRing (q : PrimeSpectrum S) : IsLocalRing (fiberLocalRingAt R S q) := by
  change IsLocalRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically a module over itself. -/
instance fiberLocalRingAtModule (q : PrimeSpectrum S) :
    Module (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) :=
  Semiring.toModule

/-- The local ring of the fiber at `q` is canonically an algebra over the fiber ring. -/
instance fiberLocalRingAtFiberAlgebra (q : PrimeSpectrum S) :
    Algebra ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q) := by
  change Algebra ((q.asIdeal.under R).Fiber S)
    (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically an algebra over the residue field
`κ(q ∩ R)`. -/
noncomputable instance fiberLocalRingAtResidueFieldAlgebra (q : PrimeSpectrum S) :
    Algebra (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) := by
  change Algebra (q.asIdeal.under R).ResidueField
    (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The canonical ring map `S → (κ(q ∩ R) ⊗[R] S)_(\bar q)` to the local fiber ring at `q`. -/
abbrev toFiberLocalRingAt (q : PrimeSpectrum S) : S →+* fiberLocalRingAt R S q :=
  (algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)).comp
    (includeRight : S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom

/-- The local ring of the fiber at `q` is canonically an `S`-algebra. -/
noncomputable instance fiberLocalRingAtAlgebra (q : PrimeSpectrum S) :
    Algebra S (fiberLocalRingAt R S q) :=
  RingHom.toAlgebra (toFiberLocalRingAt R S q)

/-- The local ring of the fiber at `q` is the localization of the fiber ring at the prime
corresponding to `q`. -/
-- Proof sketch: unfold `fiberLocalRingAt`; it is defined to be `Localization.AtPrime` of the
-- corresponding prime `fiberPrimeAt q`, so the standard localization instance applies.
instance fiberLocalRingAtIsLocalization (q : PrimeSpectrum S) :
    IsLocalization.AtPrime (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal := by
  change IsLocalization.AtPrime (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
    (fiberPrimeAt R S q).asIdeal
  infer_instance

theorem fiberLocalRingAt_isLocalization (q : PrimeSpectrum S) :
    IsLocalization.AtPrime (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal :=
  fiberLocalRingAtIsLocalization R S q

end

namespace PrimeSpectrum

section

variable {S : Type v} [CommRing S]

/-- The images of `fs : List S` in the local fiber ring at `q` form a regular sequence. This is
the thin pointwise bridge from the owner fiber local ring `fiberLocalRingAt R S q` to the
canonical predicate `RingTheory.Sequence.IsRegular`. -/
def IsRegularInFiberLocalRing (q : PrimeSpectrum S) (R : Type u) [CommRing R] [Algebra R S]
    (fs : List S) : Prop := by
  exact
    @RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)
      _ _ (fiberLocalRingAtModule R S q) (fs.map (toFiberLocalRingAt R S q))

end

end PrimeSpectrum

/-! ### Lemma_10_112_6 (from Chap10) -/
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

/-! ### Lemma_10_112_7 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]

-- Proof sketch: let `P` be the maximal ideal of `S_q` and `I = (q ∩ R)S_q`. Lemma `10.112.6`
-- gives the upper bound `ht P ≤ ht (q ∩ R) + ht (P/I)`, after rewriting heights as the Krull
-- dimensions of `S_q`, `R_(q ∩ R)`, and the canonical local fiber ring via
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`,
-- `IsLocalization.AtPrime.ringKrullDim_eq_height`, and the quotient-to-fiber bridge from
-- Lemma `10.112.6`. For the reverse inequality, lift a maximal chain under `q ∩ R` to `S_q`
-- using going down and splice it with a maximal chain in `Spec (S_q / I)`, recovering the
-- matching lower bound on heights.
/-- Lemma 10.112.7: if `R → S` is a homomorphism of Noetherian rings, `q` is a point of
`Spec S`, and `R → S` satisfies going down, then the Krull dimension of `S_q` is the sum of the
Krull dimensions of `R_(q ∩ R)` and of the canonical local fiber ring at the corresponding point of
`Spec (κ(q ∩ R) ⊗[R] S)`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
    (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim (fiberLocalRingAt R S q) := by
  let p : Ideal R := q.asIdeal.under R
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let Sq := Localization.AtPrime q.asIdeal
  let Rp := Localization.AtPrime p
  let P : Ideal Sq := IsLocalRing.maximalIdeal Sq
  let I : Ideal Sq := Ideal.map (algebraMap R Sq) p
  have hPq : P.LiesOver q.asIdeal := by
    dsimp [P, Sq]
    infer_instance
  letI := hPq
  letI : q.asIdeal.LiesOver p := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  have hPp : P.LiesOver p := Ideal.LiesOver.trans P q.asIdeal p
  letI := hPp
  have hI_le : I ≤ P := Ideal.map_le_iff_le_comap.mpr hPp.over.le
  have hI_ne_top : I ≠ ⊤ := by
    intro hI
    have hP_ne_top : P ≠ ⊤ := by
      dsimp [P, Sq]
      exact (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top
    exact hP_ne_top (top_le_iff.mp (hI ▸ hI_le))
  haveI : Algebra.HasGoingDown S Sq := by infer_instance
  haveI : Algebra.HasGoingDown R Sq := Algebra.HasGoingDown.trans R S Sq
  haveI : Nontrivial (Sq ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI_ne_top
  haveI : IsLocalRing (Sq ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : P.map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (Sq ⧸ I) := by
    dsimp [P]
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hSq : ringKrullDim Sq = ↑P.height := by
    dsimp [P]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
  have hp' : ↑p.height = ringKrullDim Rp := by
    simpa [Rp] using (IsLocalization.AtPrime.ringKrullDim_eq_height p Rp).symm
  have hQdim : ringKrullDim (Sq ⧸ I) = ringKrullDim (fiberLocalRingAt R S q) := by
    simpa [Sq, I, p] using
      ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt q
  have hQ : ↑(P.map (Ideal.Quotient.mk I)).height = ringKrullDim (fiberLocalRingAt R S q) := by
    rw [hmax]
    calc
      ↑(IsLocalRing.maximalIdeal (Sq ⧸ I)).height = ringKrullDim (Sq ⧸ I) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      _ = ringKrullDim (fiberLocalRingAt R S q) := hQdim
  have hp_le_hP : p.height ≤ P.height := by
    rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
    refine Order.height_le_iff'.2 ?_
    intro l hl
    letI : P.LiesOver l.last.asIdeal := by
      rw [hl]
      exact hPp
    obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
    have hL : L.length ≤ Order.height L.last := Order.length_le_height_last
    simpa [Ideal.primeHeight, hlen, hlast] using hL
  haveI : p.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr <| Or.inr <| by
    have hP_height_lt_top : P.height < ⊤ :=
      Ideal.height_lt_top ((IsLocalRing.maximalIdeal.isMaximal Sq).ne_top)
    exact lt_of_le_of_lt hp_le_hP <|
      hP_height_lt_top
  have hmain_ge : p.height + (P.map (Ideal.Quotient.mk I)).height ≤ P.height := by
    obtain ⟨lp, hlp, hlenp⟩ := p.exists_ltSeries_length_eq_height
    obtain ⟨lq, hlq, hlenq⟩ :=
      (P.map (Ideal.Quotient.mk I)).exists_ltSeries_length_eq_height
    let l' : LTSeries (PrimeSpectrum Sq) :=
      lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
    let Q : Ideal Sq := l'.head.asIdeal
    have hPp_comap : Ideal.comap (algebraMap R Sq) P = p := by
      simpa [Ideal.under_def] using hPp.over.symm
    have hhead : Q.LiesOver lp.last.asIdeal := by
      refine ⟨?_⟩
      refine le_antisymm ?_ ?_
      · dsimp [Q]
        rw [LTSeries.head_map, hlp, Ideal.under_def, PrimeSpectrum.comap_asIdeal]
        rw [← Ideal.map_le_iff_le_comap]
        rw [← Ideal.map_le_iff_le_comap]
        have hbot :
            Ideal.map (Ideal.Quotient.mk I) (Ideal.map (algebraMap R Sq) p) = ⊥ := by
          simp [I]
        rw [hbot]
        exact bot_le
      · dsimp [Q]
        rw [LTSeries.head_map, hlp]
        change Ideal.comap (algebraMap R Sq) (Ideal.comap (Ideal.Quotient.mk I) lq.head.asIdeal) ≤ p
        refine le_trans (Ideal.comap_mono (Ideal.comap_mono lq.head_le_last)) ?_
        rw [hlq]
        change Ideal.comap (algebraMap R Sq) (Ideal.comap (Ideal.Quotient.mk I)
          (Ideal.map (Ideal.Quotient.mk I) P)) ≤ p
        rw [Ideal.comap_map_mk hI_le]
        exact hPp_comap.le
    obtain ⟨lp', hlp'len, hlp', _⟩ := Ideal.exists_ltSeries_of_hasGoingDown lp Q
    have hlen : (lp'.smash l' hlp').length = lp.length + lq.length := by
      simp [hlp'len, l']
    rw [← hlenp, ← hlenq, ← Nat.cast_add, ← hlen, Ideal.height_eq_primeHeight]
    apply Order.length_le_height
    rw [RelSeries.last_smash, LTSeries.last_map, hlq]
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) P) ≤ P
    rw [Ideal.comap_map_mk hI_le]
  have hmain_le : P.height ≤ p.height + (P.map (Ideal.Quotient.mk I)).height := by
    have hdim_le :
        ringKrullDim Sq ≤ ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q) := by
      simpa [Sq, Rp, p] using
        ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver
          p q.asIdeal (by simpa [p] using Ideal.over_under q.asIdeal)
    have hdim_le' :
        (↑P.height : WithBot ℕ∞) ≤ ↑p.height + ↑(P.map (Ideal.Quotient.mk I)).height := by
      simpa [hSq, hp', hQ] using hdim_le
    exact_mod_cast hdim_le'
  have hmain : P.height = p.height + (P.map (Ideal.Quotient.mk I)).height :=
    le_antisymm hmain_le hmain_ge
  simpa [Sq, Rp, p] using
    calc
      ringKrullDim Sq = ↑P.height := hSq
      _ = ↑p.height + ↑(P.map (Ideal.Quotient.mk I)).height := by
        exact_mod_cast hmain
      _ = ringKrullDim Rp + ringKrullDim (fiberLocalRingAt R S q) := by
        rw [hp', hQ]

/-- Explicit lies-over restatement of Lemma `10.112.7`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver_of_hasGoingDown
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim (fiberLocalRingAt R S ⟨q, inferInstance⟩) := by
  have hp : p = q.under R := by
    simpa using hq.over
  subst p
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  simpa [q'] using
    ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
      q'

-- Proof sketch: rewrite the canonical local fiber ring in Lemma `10.112.7` by the quotient
-- presentation `S_q / (q ∩ R)S_q`.
/-- Quotient-form companion to Lemma `10.112.7`: rewriting the canonical local fiber ring at `q`
by its quotient presentation recovers the formula with `S_q / (q ∩ R)S_q`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
    (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
  have hbridge :
      ringKrullDim (fiberLocalRingAt R S q) =
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
    simpa using
      (ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt q).symm
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R S q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim
            ((Localization.AtPrime q.asIdeal) ⧸
              Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := by
      rw [hbridge]

/-- Explicit lies-over restatement of the quotient form of Lemma `10.112.7`. -/
theorem ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap R (Localization.AtPrime q)) p) := by
  have hp : p = q.under R := by
    simpa using hq.over
  subst p
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  simpa [q'] using
    ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
      q'

end

/-! ### Lemma_10_112_8 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-- The canonical quotient presentation of the closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`. -/
noncomputable def closedFiberQuotAlgEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- The canonical closed fiber is regular as soon as its quotient presentation
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is regular. -/
theorem isRegularLocalRing_closedFiber_of_quotient
    [IsRegularLocalRing (S ⧸ 𝔪S)] :
    IsRegularLocalRing ClosedFiber := by
  simpa using
    (IsRegularLocalRing.of_ringEquiv closedFiberQuotAlgEquiv.toRingEquiv.symm :
      IsRegularLocalRing ClosedFiber)

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsRegularLocalRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain sampling pass:
* primary domain: local commutative algebra of closed fibers of local ring maps;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(p) ⊗[R] S`;
  - the induced local-ring instance on `ClosedFiber` for local maps;
  - the canonical quotient view `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`;
  - downstream chapter usage already centered on `((maximalIdeal A).Fiber B)`, for example in
    `Lemma_15_78_6`.

Source/core/bridge triage:
* source-facing: the regular-closed-fiber criterion for a flat local homomorphism of local rings;
* core/canonical: the owner predicate `IsRegularLocalRing` on the owner fiber ring
  `ClosedFiber`;
* bridge/view: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.

Primitive data are the ambient flat local algebra map and regularity of the closed fiber. The
local and Noetherian structure on `ClosedFiber` are derived from the owner assumption
`IsRegularLocalRing ClosedFiber`, so no extra wrapper or auxiliary data should be introduced here.
-/
-- Proof sketch: combine Lemma `10.112.7` with the canonical criterion
-- `isRegularLocalRing_iff` on `R`, `S`, and the owner closed fiber `ClosedFiber`. The dimension
-- formula gives `dim S = dim R + dim ClosedFiber`, while generators of `maximalIdeal R` together
-- with lifts of generators of the maximal ideal of `ClosedFiber` generate `maximalIdeal S`;
-- comparing the resulting generator count with the dimension yields regularity.
/-- Lemma 10.112.8: if `R → S` is a flat local homomorphism of local Noetherian rings, `R` is a
regular local ring, and the closed fibre `((maximalIdeal R).Fiber S)`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, is a regular local ring, then `S` is a
regular local ring. -/
theorem isRegularLocalRing_of_flat_localHom_of_regular_closedFiber
    (hclosedFiber : IsRegularLocalRing ClosedFiber) :
    IsRegularLocalRing S := by
  classical
  letI : IsRegularLocalRing ClosedFiber := hclosedFiber
  let hquot : IsRegularLocalRing (S ⧸ 𝔪S) :=
    IsRegularLocalRing.of_ringEquiv closedFiberQuotAlgEquiv.toRingEquiv
  letI : IsRegularLocalRing (S ⧸ 𝔪S) := hquot
  let d : ℕ := (maximalIdeal R).spanFinrank
  let e : ℕ := (maximalIdeal (S ⧸ 𝔪S)).spanFinrank
  have hdimR : ringKrullDim R = d := by
    simpa [d] using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  have hdimQ : ringKrullDim (S ⧸ 𝔪S) = e := by
    simpa [e] using ((isRegularLocalRing_iff (R := S ⧸ 𝔪S)).1 hquot).symm
  -- Choose regular systems of parameters on the source and on the quotient closed fiber.
  obtain ⟨x, hx⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := R) (d := d) hdimR).1
      inferInstance
  obtain ⟨ybar, hybar⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := S ⧸ 𝔪S) (d := e) hdimQ).1
      inferInstance
  have hx_parameter : parameterIdeal x = maximalIdeal R := by
    exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := R) hdimR x).1 hx
  have hybar_parameter : parameterIdeal ybar = maximalIdeal (S ⧸ 𝔪S) := by
    exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := S ⧸ 𝔪S) hdimQ ybar).1 hybar
  have h𝔪S_ne_top : 𝔪S ≠ ⊤ :=
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  have h𝔪S_le : 𝔪S ≤ maximalIdeal S :=
    IsLocalRing.le_maximalIdeal h𝔪S_ne_top
  have hxS_mem :
      ∀ i : Fin d, algebraMap R S ((x i : maximalIdeal R) : R) ∈ maximalIdeal S := by
    intro i
    exact h𝔪S_le (Ideal.mem_map_of_mem _ (x i).2)
  let xS : Fin d → maximalIdeal S :=
    fun i ↦ ⟨algebraMap R S ((x i : maximalIdeal R) : R), hxS_mem i⟩
  have hxS_range :
      Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) =
        (algebraMap R S) '' Set.range (fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨((x i : maximalIdeal R) : R), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hxS_parameter : parameterIdeal xS = 𝔪S := by
    -- Mapping the source parameters into `S` recovers the ideal `𝔪_R S`.
    calc
      parameterIdeal xS = Ideal.span (Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) := by
        rw [parameterIdeal_eq_span]
      _ = Ideal.span ((algebraMap R S) '' Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) := by
        rw [hxS_range]
      _ = Ideal.map (algebraMap R S) (Ideal.span (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R))) := by
        rw [Ideal.map_span]
      _ = Ideal.map (algebraMap R S) (parameterIdeal x) := by
        rw [parameterIdeal_eq_span]
      _ = 𝔪S := by
        rw [hx_parameter]
  have hmaxmap :
      Ideal.map (Ideal.Quotient.mk 𝔪S) (maximalIdeal S) = maximalIdeal (S ⧸ 𝔪S) := by
    -- The quotient map sends the maximal ideal of `S` onto the maximal ideal of the quotient.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔪S)
      Ideal.Quotient.mk_surjective
  choose y hy_mem hy_eq using fun i : Fin e ↦ by
    have hyi :
        ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S) ∈
          Ideal.map (Ideal.Quotient.mk 𝔪S) (maximalIdeal S) := by
      simpa [hmaxmap] using (ybar i).2
    exact (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk 𝔪S)
      (hf := Ideal.Quotient.mk_surjective)
      (I := maximalIdeal S)
      (y := ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S))).1 hyi
  let yLift : Fin e → maximalIdeal S := fun i ↦ ⟨y i, hy_mem i⟩
  have hyLift_parameter_map :
      Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift) = parameterIdeal ybar := by
    -- The chosen lifts project back to the quotient parameters coordinatewise.
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_comap.2 ?_
      change Ideal.Quotient.mk 𝔪S ((yLift i : maximalIdeal S) : S) ∈ parameterIdeal ybar
      rw [show Ideal.Quotient.mk 𝔪S ((yLift i : maximalIdeal S) : S) =
        ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S) by
          simpa [yLift] using hy_eq i]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hyi_mem : ((yLift i : maximalIdeal S) : S) ∈ parameterIdeal yLift := by
        rw [parameterIdeal_eq_span]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hyi_map_mem :
          (((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S)) ∈
            Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift) := by
        refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk 𝔪S)
          (hf := Ideal.Quotient.mk_surjective)
          (I := parameterIdeal yLift)
          (y := ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S))).2 ?_
        refine ⟨((yLift i : maximalIdeal S) : S), hyi_mem, ?_⟩
        simpa [yLift] using hy_eq i
      simpa using hyi_map_mem
  have hyLift_sup : parameterIdeal yLift ⊔ 𝔪S = maximalIdeal S := by
    -- Pulling the quotient maximal ideal back along the quotient map adds back only the kernel.
    calc
      parameterIdeal yLift ⊔ 𝔪S =
          Ideal.comap (Ideal.Quotient.mk 𝔪S)
            (Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift)) := by
              rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔪S)
                Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      _ = Ideal.comap (Ideal.Quotient.mk 𝔪S) (maximalIdeal (S ⧸ 𝔪S)) := by
        rw [hyLift_parameter_map, hybar_parameter]
      _ = maximalIdeal S := by
        rw [← hmaxmap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔪S)
          Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr h𝔪S_le]
  have hgenerator :
      Ideal.span
          (Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ∪
            Set.range (fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S))) =
        maximalIdeal S := by
    -- The source parameters generate `𝔪_R S`, and adjoining lifted quotient parameters generates
    -- the whole maximal ideal of `S`.
    calc
      Ideal.span
          (Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ∪
            Set.range (fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S))) =
          Ideal.span (Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ⊔
            Ideal.span (Set.range fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)) := by
              rw [Ideal.span_union]
      _ = parameterIdeal xS ⊔ parameterIdeal yLift := by
        rw [← parameterIdeal_eq_span, ← parameterIdeal_eq_span]
      _ = maximalIdeal S := by
        rw [hxS_parameter, sup_comm]
        exact hyLift_sup
  let gX : Set S := Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)
  let gY : Set S := Set.range fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)
  have hgX_ncard : gX.ncard ≤ d := by
    let sx : Finset S := Finset.univ.image fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)
    have hsx : gX = (sx : Set S) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        simp [sx]
      · intro hs
        simp only [sx, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hs
        rcases hs with ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hsx, Set.ncard_coe_finset]
    simpa [sx] using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)))
  have hgY_ncard : gY.ncard ≤ e := by
    let sy : Finset S := Finset.univ.image fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)
    have hsy : gY = (sy : Set S) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        simp [sy]
      · intro hs
        simp only [sy, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hs
        rcases hs with ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hsy, Set.ncard_coe_finset]
    simpa [sy] using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin e)))
        (f := fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)))
  have hspan_le : (maximalIdeal S).spanFinrank ≤ d + e := by
    have hgenerator' : Ideal.span (gX ∪ gY) = maximalIdeal S := by
      simpa [gX, gY] using hgenerator
    -- The generating family has at most `d + e` distinct elements.
    calc
      (maximalIdeal S).spanFinrank = (Ideal.span (gX ∪ gY)).spanFinrank := by
        rw [hgenerator']
      _ ≤ (gX ∪ gY).ncard := by
        exact Submodule.spanFinrank_span_le_ncard_of_finite (gX.toFinite.union gY.toFinite)
      _ ≤ gX.ncard + gY.ncard := Set.ncard_union_le gX gY
      _ ≤ d + e := add_le_add hgX_ncard hgY_ncard
  have hdimS : ringKrullDim S = d + e := by
    let q : PrimeSpectrum S := ⟨maximalIdeal S, inferInstance⟩
    let h_unitsR : (maximalIdeal R).primeCompl ≤ IsUnit.submonoid R := by
      intro r hr
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hr
    let h_unitsS : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := by
      intro s hs
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hs
    let pUnder : Ideal R := Ideal.under R (maximalIdeal S)
    letI : pUnder.IsPrime := by
      dsimp [pUnder]
      infer_instance
    have hpUnder : pUnder = maximalIdeal R := by
      simpa [pUnder, Ideal.under_def] using IsLocalRing.maximalIdeal_comap (algebraMap R S)
    have h_unitsP : pUnder.primeCompl ≤ IsUnit.submonoid R := by
      intro r hr
      have hr' : r ∉ maximalIdeal R := by
        simpa [pUnder, hpUnder] using hr
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hr'
    letI : IsLocalization pUnder.primeCompl R := IsLocalization.self h_unitsP
    letI : IsLocalization (maximalIdeal S).primeCompl S := IsLocalization.self h_unitsS
    let eP : Localization.AtPrime pUnder ≃ₐ[R] R :=
      IsLocalization.algEquiv pUnder.primeCompl (Localization.AtPrime pUnder) R
    let eS : Localization.AtPrime (maximalIdeal S) ≃ₐ[S] S :=
      IsLocalization.algEquiv (maximalIdeal S).primeCompl
        (Localization.AtPrime (maximalIdeal S)) S
    let Iunder : Ideal (Localization.AtPrime (maximalIdeal S)) :=
      Ideal.map (algebraMap R (Localization.AtPrime (maximalIdeal S))) pUnder
    have hIunder_map : Ideal.map eS.toRingHom Iunder = 𝔪S := by
      -- Localizing a local ring at its maximal ideal does not change the extended source ideal.
      calc
        Ideal.map eS.toRingHom Iunder =
            Ideal.map
              (eS.toRingHom.comp (algebraMap R (Localization.AtPrime (maximalIdeal S))))
              pUnder := by
                simpa [Iunder] using
                  (Ideal.map_map (I := pUnder)
                    (algebraMap R (Localization.AtPrime (maximalIdeal S))) eS.toRingHom)
        _ = Ideal.map (algebraMap R S) pUnder := by
          congr 1
          ext r
          simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime (maximalIdeal S))] using
            (eS.commutes (algebraMap R S r))
        _ = Ideal.map (algebraMap R S) (maximalIdeal R) := by
          rw [hpUnder]
        _ = 𝔪S := rfl
    have hIunder_comap : Ideal.comap eS.toRingHom 𝔪S = Iunder := by
      rw [← hIunder_map, Ideal.comap_map_of_surjective eS.toRingHom eS.surjective,
        Ideal.comap_bot_of_injective (f := eS.toRingHom) eS.injective, sup_eq_left]
      exact bot_le
    let φ : Localization.AtPrime (maximalIdeal S) →+* S ⧸ 𝔪S :=
      (Ideal.Quotient.mk 𝔪S).comp eS.toRingHom
    have hφ_surj : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp eS.surjective
    have hker_aux :
        RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) =
          Ideal.comap eS.toRingHom 𝔪S := by
      ext z
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hkerφ : RingHom.ker φ = Iunder := by
      change RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) = Iunder
      rw [hker_aux, hIunder_comap]
    let eQ : (Localization.AtPrime (maximalIdeal S)) ⧸ Iunder ≃+* S ⧸ 𝔪S :=
      (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφ_surj)
    have hdimLoc :
        ringKrullDim (Localization.AtPrime (maximalIdeal S)) =
          ringKrullDim (Localization.AtPrime pUnder) +
            ringKrullDim (Localization.AtPrime (maximalIdeal S) ⧸ Iunder) := by
      change
        ringKrullDim (Localization.AtPrime q.asIdeal) =
          ringKrullDim (Localization.AtPrime pUnder) +
            ringKrullDim
              ((Localization.AtPrime q.asIdeal) ⧸
                Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) pUnder)
      simpa [q, pUnder, Iunder] using
        ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
          (R := R) (S := S) q
    -- Rewrite the localized dimension formula back to the original local rings and closed fiber.
    calc
      ringKrullDim S = ringKrullDim (Localization.AtPrime (maximalIdeal S)) := by
        symm
        exact ringKrullDim_eq_of_ringEquiv eS.toRingEquiv
      _ = ringKrullDim (Localization.AtPrime pUnder) + ringKrullDim (Localization.AtPrime (maximalIdeal S) ⧸ Iunder) := by
        exact hdimLoc
      _ = ringKrullDim R + ringKrullDim (S ⧸ 𝔪S) := by
        rw [ringKrullDim_eq_of_ringEquiv eP.toRingEquiv, ringKrullDim_eq_of_ringEquiv eQ]
      _ = d + e := by
        rw [hdimR, hdimQ]
  -- The source-faithful generator count matches the dimension formula, so the regular-local
  -- criterion closes the proof.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := S) ?_
  rw [hdimS]
  exact_mod_cast hspan_le

end

/-! ### Lemma_10_112_9 (from Chap10) -/
universe u v

open RingTheory Sequence
open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R]

/-
Source/core/bridge triage:
* primary domain: Cohen-Macaulay local rings under flat local base change in commutative algebra;
* sampled owner API:
  `Module.CohenMacaulay R R` from Definition `10.104.1`,
  `isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom` from Lemma `10.68.5`,
  `exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq` from
    Lemma `10.104.2`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`;
* source-facing: the four ascent/equality statements of Lemma `10.112.9`;
* core/canonical: `Module.CohenMacaulay`, `ringKrullDim`, and `RingTheory.Sequence.IsRegular`;
* bridge/view: flat local base change of regular sequences and the integral-dimension comparison.

Primitive data are only the source Cohen-Macaulay owner hypothesis on `R`, together with flatness,
finite generation where required, and the Krull-dimension comparison in parts `(3)` and `(4)`.
For part `(1)`, target-side Noetherianity is derived from the owner theorem
`IsNoetherianRing.of_finite` rather than stored as primitive public context. The dimension-equality
claims are derived API from the sampled owner lemmas above, so this file should reuse those owners
directly rather than restating a parallel local dimension wrapper.
-/

/-- Helper for Lemma 10.112.9: a Cohen--Macaulay Noetherian local ring carries a regular sequence
whose length is the Krull dimension. -/
private theorem exists_maximal_regularSequence_self_of_cohenMacaulay
    (hCM : Module.CohenMacaulay R R) :
    ∃ xs : List R, IsRegular R xs ∧ ringKrullDim R = xs.length := by
  letI : Module.CohenMacaulay R R := hCM
  have hxs : ∀ x ∈ ([] : List R), x ∈ maximalIdeal R := by
    simp
  have hquot :
      ringKrullDim (R ⧸ Ideal.ofList ([] : List R)) + ([] : List R).length = ringKrullDim R := by
    -- Rewrite the empty quotient as `R` itself.
    rw [Ideal.ofList_nil]
    simpa using
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R : R ⧸ (⊥ : Ideal R) ≃+* R)
  simpa using
    exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq hxs hquot

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.112.9: flat local base change carries a regular sequence on `R` to the
corresponding regular sequence on `S`. -/
private theorem isRegular_map_self_of_flat_localHom [Module.Flat R S] {xs : List R}
    (hreg : IsRegular R xs) :
    IsRegular S (xs.map (algebraMap R S)) := by
  -- Route correction: Lemma `10.68.5` lands in `S ⊗[R] R`, so we transport across the tensor-unit
  -- equivalence to recover a regular sequence directly on `S`.
  have hregTensor : IsRegular (S ⊗[R] R) (xs.map (algebraMap R S)) :=
    (isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom
      (R := R) (S := S) (M := R) (rs := xs)).mp hreg
  simpa using ((Algebra.TensorProduct.rid R S S).toLinearEquiv.isRegular_congr _).mp hregTensor

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.112.9: a finite flat local homomorphism preserves Krull dimension. -/
private theorem ringKrullDim_eq_of_finiteFlat_localHom_aux [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := by
  -- Faithful flatness gives injectivity of the algebra map, and finiteness gives integrality.
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff : (algebraMap R S).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact ringKrullDim_eq_of_injective_algebraMap_of_isIntegral hff.injective

/-- Helper for Lemma 10.112.9: in a Noetherian local ring, a regular sequence whose length already
equals the Krull dimension forces the ring to be Cohen--Macaulay. -/
private theorem cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim
    [IsNoetherianRing S] {xs : List S} (hreg : IsRegular S xs)
    (hlen : xs.length = ringKrullDim S) :
    Module.CohenMacaulay S S := by
  have hSdim : Module.supportDim S S = xs.length := by
    rw [Module.supportDim_self_eq_ringKrullDim, ← hlen]
  -- Extend the sequence up to module depth and show that no tail can remain.
  obtain ⟨xs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  letI : Nontrivial S := hreg.nontrivial
  have hIneTop : Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S) ≠ ⊤ := by
    simpa [ne_comm] using hreg'.top_ne_smul
  letI : Nontrivial (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) :=
    Submodule.Quotient.nontrivial_iff.2 hIneTop
  have hquot_nonbot :
      Module.supportDim S (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial S _
  have hlen_le :
      (((xs ++ xs').length : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim S S := by
    rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular (M := S) (rs := xs ++ xs') hreg']
    simpa [add_comm] using WithBot.le_add_self hquot_nonbot
      ((((xs ++ xs').length : ℕ∞) : WithBot ℕ∞))
  have htail_len : xs'.length = 0 := by
    have hsum_le :
        (((xs.length + xs'.length : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
          (((xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hSdim, List.length_append] using hlen_le
    have hsum_le_nat : xs.length + xs'.length ≤ xs.length := by
      exact_mod_cast hsum_le
    omega
  have htail : xs' = [] := List.length_eq_zero_iff.mp htail_len
  -- The support-dimension identity is then exactly the Cohen--Macaulay equality.
  refine Module.CohenMacaulay.mk ?_
  rw [hdepth, htail]
  simpa using hSdim

/-- Helper for Lemma 10.112.9: a regular sequence in a Noetherian local ring has length at most
the Krull dimension. -/
private theorem length_le_ringKrullDim_of_isRegular [IsNoetherianRing S] {xs : List S}
    (hreg : IsRegular S xs) :
    xs.length ≤ ringKrullDim S := by
  -- Compare the regular sequence with the canonical dimension formula for quotienting by it.
  have hdimSeq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  have hIneTop : Ideal.ofList xs ≠ ⊤ := by
    simpa [ne_comm] using hreg.top_ne_smul
  letI : Nontrivial (S ⧸ Ideal.ofList xs) := Ideal.Quotient.nontrivial_iff.2 hIneTop
  rw [← hdimSeq]
  exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

-- Proof sketch: choose a regular sequence in `maximalIdeal R` of length `ringKrullDim R` using the
-- Cohen-Macaulay hypothesis on `R`. By Lemma `10.68.5`, its image in `S` is again a regular
-- sequence. In the finite flat case, Lemma `10.112.4` gives `ringKrullDim S = ringKrullDim R`,
-- so this regular sequence has maximal possible length in `S`, which yields the Cohen-Macaulay
-- property for `S`.
/-- Lemma 10.112.9 (1): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, and `S` is finite flat over `R`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_finiteFlat_localHom
    (hCM : Module.CohenMacaulay R R) [Module.Finite R S] [Module.Flat R S] :
    Module.CohenMacaulay S S := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  -- Follow the source proof: transport a full-length regular sequence from `R` to `S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hlenS : (xs.map (algebraMap R S)).length = ringKrullDim S := by
    calc
      (xs.map (algebraMap R S)).length = ringKrullDim R := by
        simpa using hlenR.symm
      _ = ringKrullDim S := ringKrullDim_eq_of_finiteFlat_localHom_aux
  exact cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim hregS hlenS

-- Proof sketch: finite `R`-algebras are integral over `R`, and a flat local homomorphism is
-- faithfully flat. Thus Lemma `10.112.4` applies directly to give equality of Krull dimensions,
-- without any extra Cohen-Macaulay input.
omit [IsNoetherianRing R] in
/-- Lemma 10.112.9 (2): a finite flat local homomorphism of local rings preserves Krull
dimension. This is the dimension-equality input used in part `(1)`. -/
theorem ringKrullDim_eq_of_finiteFlat_localHom [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := by
  -- Reuse the file-local dimension comparison established above.
  exact ringKrullDim_eq_of_finiteFlat_localHom_aux

variable [IsNoetherianRing S]

-- Proof sketch: let `d = ringKrullDim R` and choose a regular sequence in `maximalIdeal R` of
-- length `d` using the Cohen-Macaulay hypothesis on `R`. Lemma `10.68.5` carries this sequence to
-- a regular sequence in `S`. The assumed bound `ringKrullDim S ≤ ringKrullDim R = d` forces this
-- regular sequence to have maximal possible length in `S`, so `S` is Cohen-Macaulay.
/-- Lemma 10.112.9 (3): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_flat_localHom_of_ringKrullDim_le
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    Module.CohenMacaulay S S := by
  -- Transport a maximal regular sequence from `R` and show it already has maximal length in `S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hlenS : (xs.map (algebraMap R S)).length = ringKrullDim S := by
    apply le_antisymm
    · exact length_le_ringKrullDim_of_isRegular hregS
    · calc
        ringKrullDim S ≤ ringKrullDim R := hdim
        _ = (xs.map (algebraMap R S)).length := by
          simpa using hlenR
  exact cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim hregS hlenS

-- Proof sketch: the same regular-sequence transfer as in part (3) gives a regular sequence in `S`
-- of length `ringKrullDim R`, hence `ringKrullDim R ≤ ringKrullDim S` because the length of a
-- regular sequence is bounded above by the Krull dimension. Combine this with the assumed
-- inequality `ringKrullDim S ≤ ringKrullDim R`.
/-- Lemma 10.112.9 (4): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `dim(R) = dim(S)`. -/
theorem ringKrullDim_eq_of_flat_localHom_of_ringKrullDim_le_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    ringKrullDim R = ringKrullDim S := by
  -- The transported regular sequence has length `ringKrullDim R`, so its length bounds
  -- `ringKrullDim R` from above by `ringKrullDim S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hle : ringKrullDim R ≤ ringKrullDim S := by
    calc
      ringKrullDim R = (xs.map (algebraMap R S)).length := by
        simpa using hlenR
      _ ≤ ringKrullDim S := length_le_ringKrullDim_of_isRegular hregS
  exact le_antisymm hle hdim

end
