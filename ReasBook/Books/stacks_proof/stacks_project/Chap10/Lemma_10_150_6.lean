import stacks_proof.stacks_project.Chap10.Lemma_10_150_6.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

namespace RingHom

open scoped BigOperators

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S) (J : Ideal S)
variable (hf : f.FormallyEtale)
variable (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))

/-
Domain-style sampling:
- primary domain: formally étale maps and their effect on nilpotent thickenings and associated
  graded rings;
- sampled owner API:
  `RingHom.FormallyEtale`,
  `Ideal.quotientMap`,
  `idealAssociatedGradedRing`,
  `idealAssociatedGradedRingGrade`,
  `idealAssociatedGradedMap`;
- source-facing: the bijectivity of the induced maps on `R / (comap f J)^n` and on the associated
  graded ring of the `J`-adic filtration, expressed degreewise on the homogeneous pieces;
- core/canonical: formal étaleness is owned by `RingHom.FormallyEtale`, and the associated graded
  ring and its induced comparison maps are owned by `idealAssociatedGradedRing` and
  `idealAssociatedGradedMap`, with `idealAssociatedGradedRingGrade` exposing the owner grading;
- bridge/view: the canonical quotient-thickening maps `R / (comap f J)^n → S / J^n` and the
  induced owner-level degree maps
  `idealAssociatedGradedGradeMap (Ideal.comap f J) J f le_rfl n`.

Primitive data are the ring map `f`, the ideal `J`, and the canonical owner objects
`idealAssociatedGradedRing (Ideal.comap f J)` and `idealAssociatedGradedRing J`, together with the
owner-level comparison map `idealAssociatedGradedMap f le_rfl`.
The quotient-Rees presentation is implementation-level behind that owner abstraction. The
degree-`n` comparison on the associated graded ring is derived API obtained by restricting that
owner map to `idealAssociatedGradedRingGrade` via `idealAssociatedGradedGradeMap`.
-/

local notation "Icomap" => Ideal.comap f J

-- Proof sketch: first identify `R / comap f J ≃ S / J` from the surjectivity of `R → S / J`.
-- Then use the unique lifting property of formal étaleness inductively to produce inverse maps
-- between the higher nilpotent thickenings `R / (comap f J)^n` and `S / J^n`.
/-- Helper for Lemma 10.150.6: the transition ideal `K^n / K^(n + 1)` has square zero in
`A / K^(n + 1)` once `n > 0`. -/
lemma quotient_pow_transition_square_zero
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    (Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n)) ^ 2 = ⊥ := by
  -- The square is the image of `K^(2n)`, and `2n ≥ n + 1` when `n > 0`.
  rw [pow_two, ← Ideal.map_mul, ← pow_add]
  have hle : n + 1 ≤ n + n := by
    omega
  exact eq_bot_mono
    (Ideal.map_mono (Ideal.pow_le_pow_right hle))
    (Ideal.map_quotient_self _)

/-- Helper for Lemma 10.150.6: surjectivity of `R → S / J` identifies the first quotient
`R / comap f J` with `S / J`. -/
lemma formallyEtale_quotientMap_bijective_one :
    Function.Surjective ((Ideal.Quotient.mk J).comp f) →
    Function.Bijective
      ((Ideal.quotientMap J f le_rfl) : R ⧸ Icomap →+* S ⧸ J) := by
  -- The quotient map is injective because the source ideal is exactly the comap, and it is
  -- surjective because `R → S / J` is surjective by hypothesis.
  intro hsurj
  constructor
  · exact Ideal.quotientMap_injective
  · intro x
    rcases hsurj x with ⟨r, rfl⟩
    exact ⟨Ideal.Quotient.mk Icomap r, rfl⟩

/-- Helper for Lemma 10.150.6: the `n = 1` step of the quotient tower is exactly the first
quotient comparison rewritten through `pow_one`. -/
private theorem formallyEtale_quotientMap_pow_one_bijective
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Bijective
      ((Ideal.quotientMap (J ^ 1) f (J.le_comap_pow f 1)) :
        R ⧸ (Icomap ^ 1) →+* S ⧸ (J ^ 1)) := by
  -- Transport the first quotient comparison across `pow_one`.
  constructor
  · have hcomap : Ideal.comap f (J ^ 1) ≤ Icomap ^ 1 := by
      simpa [pow_one]
    exact Ideal.quotientMap_injective' (H := J.le_comap_pow f 1) hcomap
  · intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases hsurj (Ideal.Quotient.mk J s) with ⟨r, hr⟩
    refine ⟨Ideal.Quotient.mk (Icomap ^ 1) r, ?_⟩
    rw [Ideal.quotientMap_mk]
    apply Ideal.Quotient.eq.2
    simpa [pow_one] using Ideal.Quotient.eq.1 hr

/-- Helper for Lemma 10.150.6: any bijective quotient comparison
`R / (comap f J)^n → S / J^n` upgrades to an algebra equivalence over `R`. -/
private noncomputable def quotientMapPowAlgEquiv
    (n : ℕ)
    (hbij : Function.Bijective
      ((Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) :
        R ⧸ (Icomap ^ n) →+* S ⧸ (J ^ n))) :
    letI := f.toAlgebra
    (R ⧸ (Icomap ^ n)) ≃ₐ[R] (S ⧸ (J ^ n)) :=
  -- The quotient comparison is already an `R`-algebra morphism; bijectivity upgrades it to an
  -- equivalence without changing the source-faithful quotient route.
  letI := f.toAlgebra
  { RingEquiv.ofBijective (Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) hbij with
    commutes' := fun _ => rfl }

/-- Helper for Lemma 10.150.6: the kernel of the transition
`R / I^(n + 1) → R / I^n` is exactly the transition ideal `I^n / I^(n + 1)`. -/
private theorem factorPow_kernel_eq_map_pow
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n)) =
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- This is the standard kernel description for quotient transition maps specialized to powers.
  simpa [Ideal.Quotient.factorPow] using
    (Ideal.Quotient.factor_ker (I := K ^ (n + 1)) (J := K ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n)))

/-- Helper for Lemma 10.150.6: the kernel of the transition
`R / I^(n + 1) → R / I^n` is nilpotent as soon as `n > 0`. -/
private theorem factorPow_kernel_isNilpotent
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n))) := by
  -- The transition kernel squares to zero by the quotient-power computation proved above.
  refine ⟨2, ?_⟩
  rw [factorPow_kernel_eq_map_pow]
  exact quotient_pow_transition_square_zero K hn

/-- Helper for Lemma 10.150.6: the quotient maps `R / I^m → S / J^m` commute with the transition
maps `R / I^m → R / I^n` and `S / J^m → S / J^n` in the power towers. -/
private theorem quotientMap_factorPow_commutes
    (m n : ℕ) (hmn : n ≤ m) :
    letI := f.toAlgebra
    let qm : R ⧸ (Icomap ^ m) →ₐ[R] S ⧸ (J ^ m) :=
      Ideal.quotientMapₐ (J ^ m) ({ toRingHom := f, commutes' := fun _ => rfl } : R →ₐ[R] S)
        (J.le_comap_pow f m)
    let qn : R ⧸ (Icomap ^ n) →ₐ[R] S ⧸ (J ^ n) :=
      Ideal.quotientMapₐ (J ^ n) ({ toRingHom := f, commutes' := fun _ => rfl } : R →ₐ[R] S)
        (J.le_comap_pow f n)
    let factorI : R ⧸ (Icomap ^ m) →ₐ[R] R ⧸ (Icomap ^ n) :=
      { Ideal.Quotient.factorPow Icomap hmn with commutes' := fun _ => rfl }
    let factorJ : S ⧸ (J ^ m) →ₐ[R] S ⧸ (J ^ n) :=
      { Ideal.Quotient.factorPow J hmn with commutes' := fun _ => rfl }
    factorJ.comp qm = qn.comp factorI := by
  letI := f.toAlgebra
  intro qm qn factorI factorJ
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- On quotient classes both sides are the same class of `f r` in `S / J^n`.
  simp [qm, qn, factorI, factorJ, Ideal.Quotient.factorPow]

/-- Helper for Lemma 10.150.6: the direct reduction `A / K^(m + 1) → A / K` has kernel equal to
the image of `K` in `A / K^(m + 1)`. -/
private theorem factorPow_to_one_kernel_eq_map
    {A : Type*} [CommRing A] (K : Ideal A) (m : ℕ) :
    RingHom.ker
      (Ideal.Quotient.factorPow K (Nat.succ_le_of_lt (Nat.succ_pos m))) =
        Ideal.map (Ideal.Quotient.mk (K ^ (m + 1))) K := by
  -- This is the power-transition kernel formula specialized to reduction all the way to level `1`.
  rw [RingHom.ker_eq_comap_bot]
  have hmap : Ideal.map (Ideal.Quotient.mk (K ^ 1)) K = ⊥ := by
    rw [pow_one]
    exact Ideal.map_quotient_self K
  rw [← hmap]
  simpa [pow_one] using
    (Ideal.map_mk_comap_factorPow (I := K) (a := 1) (b := m + 1)
      (Nat.succ_pos 0) (Nat.succ_le_of_lt (Nat.succ_pos m)))

/-- Helper for Lemma 10.150.6: an element of `A / K^(m + 1)` that dies modulo `K` is represented
by an element of `K`. -/
private theorem exists_representative_of_factorPow_to_one_eq_zero
    {A : Type*} [CommRing A] (K : Ideal A) (m : ℕ) (x : A ⧸ (K ^ (m + 1)))
    (hx : Ideal.Quotient.factorPow K (Nat.succ_le_of_lt (Nat.succ_pos m)) x = 0) :
    ∃ r ∈ K, Ideal.Quotient.mk (K ^ (m + 1)) r = x := by
  -- The previous kernel computation turns the vanishing statement into ideal membership, and then
  -- quotient surjectivity produces an explicit representative from `K`.
  have hxmem :
      x ∈ RingHom.ker (Ideal.Quotient.factorPow K (Nat.succ_le_of_lt (Nat.succ_pos m))) := by
    rw [RingHom.mem_ker]
    exact hx
  rw [factorPow_to_one_kernel_eq_map (K := K) (m := m)] at hxmem
  exact
    (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (K ^ (m + 1))) Ideal.Quotient.mk_surjective).mp hxmem

/-- Helper for Lemma 10.150.6: if a lift to `R / I^(m + 1)` becomes zero on `J` after reduction to
`R / I`, then the lift sends `J` into the image of `I` inside `R / I^(m + 1)`. -/
private theorem formallyEtale_pow_lift_image_in_map
    (m : ℕ) :
    letI := f.toAlgebra
    ∀ {σ : S →ₐ[R] R ⧸ (Icomap ^ (m + 1))} {g : S →ₐ[R] R ⧸ (Icomap ^ 1)},
      ({ toRingHom := Ideal.Quotient.factorPow Icomap (Nat.succ_le_succ (Nat.zero_le m))
         commutes' := fun _ => rfl } : R ⧸ (Icomap ^ (m + 1)) →ₐ[R] R ⧸ (Icomap ^ 1)).comp σ = g →
      (∀ j ∈ J, g j = 0) →
      J ≤ Ideal.comap σ.toRingHom
        (Ideal.map (Ideal.Quotient.mk (Icomap ^ (m + 1))) Icomap) := by
  letI := f.toAlgebra
  intro σ g hσ hgJ j hj
  -- Evaluate the reduction identity on `j`; by hypothesis the image dies modulo `I`.
  have hj_zero :
      Ideal.Quotient.factorPow Icomap (Nat.succ_le_of_lt (Nat.succ_pos m)) (σ j) = 0 := by
    simpa using (AlgHom.congr_fun hσ j).trans (hgJ j hj)
  -- The kernel computation for the reduction-to-level-1 map identifies the image with `I / I^(m+1)`.
  rw [← factorPow_to_one_kernel_eq_map (K := Icomap) (m := m)]
  exact hj_zero

/-- Helper for Lemma 10.150.6: once a lift sends `J` into the image of `I` inside
`R / I^(m + 1)`, it kills `J^(m + 1)`. -/
private theorem formallyEtale_pow_lift_kills_pow
    (m : ℕ) :
    letI := f.toAlgebra
    ∀ {σ : S →ₐ[R] R ⧸ (Icomap ^ (m + 1))},
      J ≤ Ideal.comap σ.toRingHom
        (Ideal.map (Ideal.Quotient.mk (Icomap ^ (m + 1))) Icomap) →
      J ^ (m + 1) ≤ RingHom.ker σ.toRingHom := by
  letI := f.toAlgebra
  intro σ hσJ
  -- Raise the image containment to the `(m + 1)`-st power and use that
  -- `(I / I^(m + 1))^(m + 1) = 0` in `R / I^(m + 1)`.
  rw [RingHom.ker_eq_comap_bot]
  refine (Ideal.pow_right_mono hσJ (m + 1)).trans ?_
  let K : Ideal (R ⧸ (Icomap ^ (m + 1))) :=
    Ideal.map (Ideal.Quotient.mk (Icomap ^ (m + 1))) Icomap
  have hpow :
      K ^ (m + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  exact (Ideal.le_comap_pow (f := σ.toRingHom) (K := K) (n := m + 1)).trans (by simpa [K, hpow])

/-- Helper for Lemma 10.150.6: the inverse of the quotient equivalence at level `n ≥ 1`
reduces compatibly to the inverse at level `1`. -/
private theorem quotientMapPowAlgEquiv_symm_factor_to_one
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    {n : ℕ} (hn : 1 ≤ n)
    (hbij : Function.Bijective
      ((Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) :
        R ⧸ (Icomap ^ n) →+* S ⧸ (J ^ n))) :
    letI := f.toAlgebra
    let eN : (R ⧸ (Icomap ^ n)) ≃ₐ[R] (S ⧸ (J ^ n)) :=
      quotientMapPowAlgEquiv (f := f) (J := J) n hbij
    let hOneBij :
        Function.Bijective
          ((Ideal.quotientMap (J ^ 1) f (J.le_comap_pow f 1)) :
            R ⧸ (Icomap ^ 1) →+* S ⧸ (J ^ 1)) := by
          constructor
          · have hcomap : Ideal.comap f (J ^ 1) ≤ Icomap ^ 1 := by
              simpa [pow_one]
            exact Ideal.quotientMap_injective' (H := J.le_comap_pow f 1) hcomap
          · intro x
            obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
            rcases hsurj (Ideal.Quotient.mk J s) with ⟨r, hr⟩
            exact ⟨Ideal.Quotient.mk (Icomap ^ 1) r, by
              rw [Ideal.quotientMap_mk]
              rw [show J ^ 1 = J by simp]
              exact hr⟩
    let eOne : (R ⧸ (Icomap ^ 1)) ≃ₐ[R] (S ⧸ (J ^ 1)) :=
      quotientMapPowAlgEquiv (f := f) (J := J) 1 hOneBij
    let factorI : R ⧸ (Icomap ^ n) →ₐ[R] R ⧸ (Icomap ^ 1) :=
      { Ideal.Quotient.factorPow Icomap hn with commutes' := fun _ => rfl }
    let factorJ : S ⧸ (J ^ n) →ₐ[R] S ⧸ (J ^ 1) :=
      { Ideal.Quotient.factorPow J hn with commutes' := fun _ => rfl }
    factorI.comp eN.symm.toAlgHom = eOne.symm.toAlgHom.comp factorJ := by
  letI := f.toAlgebra
  let eN : (R ⧸ (Icomap ^ n)) ≃ₐ[R] (S ⧸ (J ^ n)) :=
    quotientMapPowAlgEquiv (f := f) (J := J) n hbij
  have hOneBij :
      Function.Bijective
        ((Ideal.quotientMap (J ^ 1) f (J.le_comap_pow f 1)) :
          R ⧸ (Icomap ^ 1) →+* S ⧸ (J ^ 1)) :=
    formallyEtale_quotientMap_pow_one_bijective (f := f) (J := J) hsurj
  let eOne : (R ⧸ (Icomap ^ 1)) ≃ₐ[R] (S ⧸ (J ^ 1)) :=
    quotientMapPowAlgEquiv (f := f) (J := J) 1 hOneBij
  let factorI : R ⧸ (Icomap ^ n) →ₐ[R] R ⧸ (Icomap ^ 1) :=
    { Ideal.Quotient.factorPow Icomap hn with commutes' := fun _ => rfl }
  let factorJ : S ⧸ (J ^ n) →ₐ[R] S ⧸ (J ^ 1) :=
    { Ideal.Quotient.factorPow J hn with commutes' := fun _ => rfl }
  -- Compare the two candidate inverses after applying the level-`1` quotient equivalence.
  ext x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply eOne.injective
  have hcomm : factorJ.comp eN.toAlgHom = eOne.toAlgHom.comp factorI := by
    simpa [eN, eOne, factorI, factorJ] using
      (quotientMap_factorPow_commutes (f := f) (J := J) n 1 hn)
  calc
    eOne (factorI (eN.symm (Ideal.Quotient.mk (J ^ n) s)))
        = factorJ (eN (eN.symm (Ideal.Quotient.mk (J ^ n) s))) := by
          exact (AlgHom.congr_fun hcomm (eN.symm (Ideal.Quotient.mk (J ^ n) s))).symm
    _ = factorJ (Ideal.Quotient.mk (J ^ n) s) := by
          rw [AlgEquiv.apply_symm_apply]
    _ = eOne (eOne.symm (factorJ (Ideal.Quotient.mk (J ^ n) s))) := by
          rw [AlgEquiv.apply_symm_apply]

/-- Helper for Lemma 10.150.6: once the quotient comparison is an equivalence at level `n + 1`,
the formally smooth lift to level `n + 2` descends through `J^(n + 2)` and is compatible with
the previous-stage inverse. -/
private theorem formallyEtale_successor_descended_map
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ)
    (hbijPrev : Function.Bijective
      ((Ideal.quotientMap (J ^ (n + 1)) f (J.le_comap_pow f (n + 1))) :
        R ⧸ (Icomap ^ (n + 1)) →+* S ⧸ (J ^ (n + 1)))) :
    letI := f.toAlgebra
    let ePrev : (R ⧸ (Icomap ^ (n + 1))) ≃ₐ[R] (S ⧸ (J ^ (n + 1))) :=
      quotientMapPowAlgEquiv (f := f) (J := J) (n + 1) hbijPrev
    let factorI : R ⧸ (Icomap ^ (n + 2)) →ₐ[R] R ⧸ (Icomap ^ (n + 1)) :=
      { Ideal.Quotient.factorPow Icomap (Nat.le_succ (n + 1)) with commutes' := fun _ => rfl }
    let factorJ : S ⧸ (J ^ (n + 2)) →ₐ[R] S ⧸ (J ^ (n + 1)) :=
      { Ideal.Quotient.factorPow J (Nat.le_succ (n + 1)) with commutes' := fun _ => rfl }
    ∃ τ : S ⧸ (J ^ (n + 2)) →ₐ[R] R ⧸ (Icomap ^ (n + 2)),
      factorI.comp τ = ePrev.symm.toAlgHom.comp factorJ := by
  letI := f.toAlgebra
  intro ePrev factorI factorJ
  have hfAlg : Algebra.FormallyEtale R S := by
    simpa [RingHom.FormallyEtale] using hf
  letI : Algebra.FormallyEtale R S := hfAlg
  have hOneBij :
      Function.Bijective
        ((Ideal.quotientMap (J ^ 1) f (J.le_comap_pow f 1)) :
          R ⧸ (Icomap ^ 1) →+* S ⧸ (J ^ 1)) :=
    formallyEtale_quotientMap_pow_one_bijective (f := f) (J := J) hsurj
  let eOne : (R ⧸ (Icomap ^ 1)) ≃ₐ[R] (S ⧸ (J ^ 1)) :=
    quotientMapPowAlgEquiv (f := f) (J := J) 1 hOneBij
  let factorIToOne : R ⧸ (Icomap ^ (n + 2)) →ₐ[R] R ⧸ (Icomap ^ 1) :=
    { Ideal.Quotient.factorPow Icomap (show 1 ≤ n + 2 by omega) with
      commutes' := fun _ => rfl }
  let factorPrevIToOne : R ⧸ (Icomap ^ (n + 1)) →ₐ[R] R ⧸ (Icomap ^ 1) :=
    { Ideal.Quotient.factorPow Icomap (show 1 ≤ n + 1 by omega) with
      commutes' := fun _ => rfl }
  let factorPrevJToOne : S ⧸ (J ^ (n + 1)) →ₐ[R] S ⧸ (J ^ 1) :=
    { Ideal.Quotient.factorPow J (show 1 ≤ n + 1 by omega) with
      commutes' := fun _ => rfl }
  let mkPrev : S →ₐ[R] S ⧸ (J ^ (n + 1)) := Ideal.Quotient.mkₐ R (J ^ (n + 1))
  let mkNext : S →ₐ[R] S ⧸ (J ^ (n + 2)) := Ideal.Quotient.mkₐ R (J ^ (n + 2))
  let mkOne : S →ₐ[R] S ⧸ (J ^ 1) := Ideal.Quotient.mkₐ R (J ^ 1)
  let σPrev : S →ₐ[R] R ⧸ (Icomap ^ (n + 1)) := ePrev.symm.toAlgHom.comp mkPrev
  have hfactorISurj : Function.Surjective factorI := by
    simpa [factorI, Ideal.Quotient.factorPow] using
      (Ideal.Quotient.factor_surjective
        (S := Icomap ^ (n + 2)) (T := Icomap ^ (n + 1))
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
  let σ : S →ₐ[R] R ⧸ (Icomap ^ (n + 2)) :=
    Algebra.FormallySmooth.liftOfSurjective
      σPrev
      factorI
      hfactorISurj
      (factorPow_kernel_isNilpotent (K := Icomap) (n := n + 1) (hn := Nat.succ_pos n))
  -- First build the formally smooth lift above the previous-stage inverse.
  have hσ : factorI.comp σ = σPrev := by
    simpa [σ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective
        σPrev
        factorI
        hfactorISurj
        (factorPow_kernel_isNilpotent (K := Icomap) (n := n + 1) (hn := Nat.succ_pos n)))
  have hPrevToOne :
      factorPrevIToOne.comp ePrev.symm.toAlgHom = eOne.symm.toAlgHom.comp factorPrevJToOne := by
    simpa [ePrev, eOne, factorPrevIToOne, factorPrevJToOne] using
      (quotientMapPowAlgEquiv_symm_factor_to_one
        (f := f) (J := J) hsurj (n := n + 1) (show 1 ≤ n + 1 by omega) hbijPrev)
  have hmkPrev : factorPrevJToOne.comp mkPrev = mkOne := by
    ext s
    simp [factorPrevJToOne, mkPrev, mkOne, Ideal.Quotient.factorPow]
  have hσToOne : factorIToOne.comp σ = eOne.symm.toAlgHom.comp mkOne := by
    -- Reduce the new lift to level `1`, where the first quotient comparison is already inverted.
    calc
      factorIToOne.comp σ = factorPrevIToOne.comp (factorI.comp σ) := by
        ext s
        simp [factorIToOne, factorPrevIToOne, factorI, Ideal.Quotient.factorPow]
      _ = factorPrevIToOne.comp σPrev := by rw [hσ]
      _ = (factorPrevIToOne.comp ePrev.symm.toAlgHom).comp mkPrev := by
        rfl
      _ = (eOne.symm.toAlgHom.comp factorPrevJToOne).comp mkPrev := by
        rw [hPrevToOne]
      _ = eOne.symm.toAlgHom.comp mkOne := by
        rw [AlgHom.comp_assoc, hmkPrev]
  have hgJ : ∀ j ∈ J, (eOne.symm.toAlgHom.comp mkOne) j = 0 := by
    intro j hj
    have hmj : mkOne j = 0 := by
      change Ideal.Quotient.mk (J ^ 1) j = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa [mkOne, pow_one] using hj
    simpa [AlgHom.comp_apply] using congrArg eOne.symm hmj
  have hσJ :
      J ≤ Ideal.comap σ.toRingHom
        (Ideal.map (Ideal.Quotient.mk (Icomap ^ (n + 2))) Icomap) := by
    -- The reduction-to-level-`1` identity forces the lift to carry `J` into `I / I^(n + 2)`.
    exact
      formallyEtale_pow_lift_image_in_map
        (f := f) (J := J) (m := n + 1) (σ := σ) (g := eOne.symm.toAlgHom.comp mkOne)
        hσToOne hgJ
  have hkill :
      J ^ (n + 2) ≤ RingHom.ker σ.toRingHom := by
    -- Once the image lies in `I / I^(n + 2)`, the `(n + 2)`-nd power dies automatically.
    exact
      formallyEtale_pow_lift_kills_pow
        (f := f) (J := J) (m := n + 1) (σ := σ) hσJ
  let τ : S ⧸ (J ^ (n + 2)) →ₐ[R] R ⧸ (Icomap ^ (n + 2)) :=
    Ideal.Quotient.liftₐ (J ^ (n + 2)) σ fun s hs ↦ RingHom.mem_ker.mp (hkill hs)
  -- Descend the lift through `J^(n + 2)` and record its compatibility with the previous stage.
  have hτ :
      factorI.comp τ = ePrev.symm.toAlgHom.comp factorJ := by
    apply Ideal.Quotient.algHom_ext
    ext s
    simpa [τ, σPrev, factorJ, Ideal.Quotient.factorPow, AlgHom.comp_assoc] using
      AlgHom.congr_fun hσ s
  exact ⟨τ, hτ⟩

/-- Lemma 10.150.6 (1): if `R → S / J` is surjective and `f : R →+* S` is formally étale, then
the induced map `R / (comap f J)^n → S / J^n` is bijective for every `n`. -/
@[stacks 0H1D]
theorem formallyEtale_quotientMap_pow_bijective
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    Function.Bijective
      ((Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) :
        R ⧸ (Icomap ^ n) →+* S ⧸ (J ^ n)) := by
  induction n with
  | zero =>
      -- At level `0`, both quotient rings are the terminal quotient by `⊤`.
      haveI : Subsingleton (R ⧸ (Icomap ^ 0)) := by
        simpa [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      haveI : Subsingleton (S ⧸ (J ^ 0)) := by
        simpa [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (S ⧸ (⊤ : Ideal S)))
      constructor
      · intro x y _
        exact Subsingleton.elim x y
      · intro x
        exact ⟨0, Subsingleton.elim _ _⟩
  | succ n ih =>
      cases n with
      | zero =>
          -- The base case `n = 1` is exactly the surjective quotient comparison `R / I ≃ S / J`.
          exact formallyEtale_quotientMap_pow_one_bijective (f := f) (J := J) hsurj
      | succ n =>
          letI := f.toAlgebra
          have hfAlg : Algebra.FormallyEtale R S := by
            simpa [RingHom.FormallyEtale] using hf
          letI : Algebra.FormallyEtale R S := hfAlg
          let ePrev : (R ⧸ (Icomap ^ (n + 1))) ≃ₐ[R] (S ⧸ (J ^ (n + 1))) :=
            quotientMapPowAlgEquiv (f := f) (J := J) (n + 1) ih
          let factorI : R ⧸ (Icomap ^ (n + 2)) →ₐ[R] R ⧸ (Icomap ^ (n + 1)) :=
            { Ideal.Quotient.factorPow Icomap (Nat.le_succ (n + 1)) with
              commutes' := fun _ => rfl }
          let factorJ : S ⧸ (J ^ (n + 2)) →ₐ[R] S ⧸ (J ^ (n + 1)) :=
            { Ideal.Quotient.factorPow J (Nat.le_succ (n + 1)) with commutes' := fun _ => rfl }
          obtain ⟨τ, hτ⟩ :=
            formallyEtale_successor_descended_map
              (f := f) (J := J) hf hsurj n ih
          let q : R ⧸ (Icomap ^ (n + 2)) →ₐ[R] S ⧸ (J ^ (n + 2)) :=
            Ideal.quotientMapₐ (J ^ (n + 2))
              ({ toRingHom := f, commutes' := fun _ => rfl } : R →ₐ[R] S)
              (J.le_comap_pow f (n + 2))
          have hq :
              factorJ.comp q = ePrev.toAlgHom.comp factorI := by
            simpa [q, ePrev, factorI, factorJ] using
              (quotientMap_factorPow_commutes (f := f) (J := J) (n + 2) (n + 1)
                (Nat.le_succ (n + 1)))
          have hred : factorJ.comp (q.comp τ) = factorJ := by
            -- The descended lift reduces to the previous-stage inverse, so the target composite is
            -- already the identity after passing to level `n + 2`.
            calc
              factorJ.comp (q.comp τ) = (factorJ.comp q).comp τ := by
                simp [AlgHom.comp_assoc]
              _ = (ePrev.toAlgHom.comp factorI).comp τ := by rw [hq]
              _ = ePrev.toAlgHom.comp (factorI.comp τ) := by
                simp [AlgHom.comp_assoc]
              _ = ePrev.toAlgHom.comp (ePrev.symm.toAlgHom.comp factorJ) := by rw [hτ]
              _ = factorJ := by
                ext x
                simp
          have hqτ_mk :
              (q.comp τ).comp (Ideal.Quotient.mkₐ R (J ^ (n + 2))) =
                Ideal.Quotient.mkₐ R (J ^ (n + 2)) := by
            -- Formal unramifiedness gives uniqueness of lifts across the square-zero transition on
            -- the `J`-adic tower.
            apply Algebra.FormallyUnramified.lift_unique'
              factorJ
              (factorPow_kernel_isNilpotent (K := J) (n := n + 1) (hn := Nat.succ_pos n))
            calc
              factorJ.comp ((q.comp τ).comp (Ideal.Quotient.mkₐ R (J ^ (n + 2)))) =
                  (factorJ.comp (q.comp τ)).comp (Ideal.Quotient.mkₐ R (J ^ (n + 2))) := by
                    simp [AlgHom.comp_assoc]
              _ = factorJ.comp (Ideal.Quotient.mkₐ R (J ^ (n + 2))) := by rw [hred]
          have hqτ : q.comp τ = AlgHom.id R (S ⧸ (J ^ (n + 2))) := by
            apply Ideal.Quotient.algHom_ext
            simpa using hqτ_mk
          have hτq : τ.comp q = AlgHom.id R (R ⧸ (Icomap ^ (n + 2))) := by
            -- On quotient generators from `R`, the descended inverse is forced by `R`-linearity.
            apply Ideal.Quotient.algHom_ext
            rw [AlgHom.comp_assoc, Ideal.quotient_map_comp_mkₐ]
            apply AlgHom.ext
            intro r
            change τ (algebraMap R (S ⧸ (J ^ (n + 2))) r) =
              algebraMap R (R ⧸ (Icomap ^ (n + 2))) r
            exact τ.commutes r
          constructor
          · intro x y hxy
            change q x = q y at hxy
            have hxy' := congrArg τ hxy
            have hx : τ (q x) = x := AlgHom.congr_fun hτq x
            have hy : τ (q y) = y := AlgHom.congr_fun hτq y
            rw [hx, hy] at hxy'
            exact hxy'
          · intro y
            exact ⟨τ y, by simpa using AlgHom.congr_fun hqτ y⟩

/-- Helper for Lemma 10.150.6: inside the subtype `I^n M`, the internal denominator `I • ⊤`
is exactly the next filtration step `I^(n + 1) M`. -/
private theorem idealAssociatedGradedInternalDenominator_eq
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    I • (⊤ : Submodule A ↥(RingTheory.Sequence.idealAssociatedGradedStage I M n)) =
      (RingTheory.Sequence.idealAssociatedGradedStage I M (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage I M n) := by
  -- Unpack the internal quotient denominator back to the ambient module.
  ext x
  rw [Submodule.mem_smul_top_iff]
  -- Route correction: use the source filtration identity `I • I^n M = I^(n+1) M` directly
  -- instead of transporting through the older broken associated-graded file.
  change ((x : M) ∈ I • RingTheory.Sequence.idealAssociatedGradedStage I M n) ↔
    ((x : M) ∈ RingTheory.Sequence.idealAssociatedGradedStage I M (n + 1))
  simp [RingTheory.Sequence.idealAssociatedGradedStage, ← mul_smul, Ideal.mul_comm, pow_succ]

/-- Helper for Lemma 10.150.6: the internal quotient `I^n M / I(I^n M)` agrees with the
textbook associated-graded piece `I^n M / I^(n + 1) M`. -/
private noncomputable def idealAssociatedGradedInternalPieceEquiv
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage I M n ⧸
        (I • (⊤ : Submodule A ↥(RingTheory.Sequence.idealAssociatedGradedStage I M n)))) ≃ₗ[A]
      RingTheory.Sequence.idealAssociatedGradedPiece I M n :=
  -- The two quotient models differ only by the denominator description proved just above.
  Submodule.quotEquivOfEq _ _ (idealAssociatedGradedInternalDenominator_eq I n)

/-- Helper for Lemma 10.150.6: an element of the `n`-th stage gives a degree-`n` monomial in the
Rees algebra. -/
private theorem idealAssociatedGradedStage_monomial_mem
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    Polynomial.monomial n (x : A) ∈ reesAlgebra K := by
  -- The stage condition is exactly the coefficient condition needed for a Rees monomial.
  apply reesAlgebra.monomial_mem.mpr
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using x.2

/-- Helper for Lemma 10.150.6: the stage-to-Rees monomial map lands in the degree-`n`
homogeneous piece. -/
private theorem idealAssociatedGradedStageToRees_mem_grade
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    (⟨Polynomial.monomial n (x : A), idealAssociatedGradedStage_monomial_mem K n x⟩ :
      reesAlgebra K) ∈ reesAlgebraGrade K n := by
  -- Rewrite the stage element as an element of `K ^ n`, which is the canonical source of the
  -- degree-`n` Rees grading.
  refine ⟨⟨x, by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using x.2⟩, ?_⟩
  rfl

/-- Helper for Lemma 10.150.6: the degree-`n` monomial construction sends the `n`-th stage into
the Rees algebra. -/
private def idealAssociatedGradedStageToRees
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K A n → reesAlgebra K :=
  fun x ↦ ⟨Polynomial.monomial n (x : A), idealAssociatedGradedStage_monomial_mem K n x⟩

/-- Helper for Lemma 10.150.6: the monomial representative of a stage element has exactly one
possibly nonzero coefficient, in its own degree. -/
private theorem idealAssociatedGradedStageToRees_coeff
    {A : Type*} [CommRing A] (K : Ideal A) (n m : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    (((idealAssociatedGradedStageToRees K n x : reesAlgebra K) : Polynomial A).coeff m) =
      if n = m then (x : A) else 0 := by
  by_cases h : n = m
  · subst h
    simp [idealAssociatedGradedStageToRees]
  · simp [idealAssociatedGradedStageToRees, Polynomial.coeff_monomial, h]

/-- Helper for Lemma 10.150.6: composing the stage-to-Rees monomial map with the quotient map
gives the canonical degree-`n` class in the associated graded ring. -/
private def idealAssociatedGradedStageToOwner
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K A n → idealAssociatedGradedRing K :=
  fun x ↦ Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
    (idealAssociatedGradedStageToRees K n x)

/-- Helper for Lemma 10.150.6: the stage-to-owner map lands in the degree-`n` owner piece. -/
private theorem idealAssociatedGradedStageToOwner_mem_grade
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    idealAssociatedGradedStageToOwner K n x ∈ idealAssociatedGradedRingGrade K n := by
  -- The owner-grade witness is the homogeneous Rees representative constructed above.
  refine ⟨idealAssociatedGradedStageToRees K n x, ?_, rfl⟩
  exact idealAssociatedGradedStageToRees_mem_grade K n x

/-- Helper for Lemma 10.150.6: the stage-to-Rees monomial map is linear. -/
private def idealAssociatedGradedStageToReesLinear
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K A n →ₗ[A] reesAlgebra K :=
  { toFun := fun x ↦ ⟨Polynomial.monomial n (x : A), idealAssociatedGradedStage_monomial_mem K n x⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      exact (Polynomial.monomial n).map_add (x : A) (y : A)
    map_smul' := fun r x ↦ by
      apply Subtype.ext
      exact (Polynomial.monomial n).map_smul r (x : A) }

/-- Helper for Lemma 10.150.6: the linear stage-to-owner map lands in the degree-`n`
owner subtype. -/
private def idealAssociatedGradedStageToOwnerLinear
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K A n →ₗ[A] idealAssociatedGradedRingGrade K n :=
  -- Codomain-restrict the quotient map to the degree-`n` owner piece.
  LinearMap.codRestrict (idealAssociatedGradedRingGrade K n)
    ((Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A (reesAlgebra K)) K)).toLinearMap.comp
      (idealAssociatedGradedStageToReesLinear K n))
    (fun x ↦ idealAssociatedGradedStageToOwner_mem_grade K n x)

/-- Helper for Lemma 10.150.6: the linear stage-to-owner map agrees with the underlying
stage-to-owner function. -/
private theorem idealAssociatedGradedStageToOwnerLinear_apply
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    ((idealAssociatedGradedStageToOwnerLinear K n x :
      idealAssociatedGradedRingGrade K n) : idealAssociatedGradedRing K) =
      idealAssociatedGradedStageToOwner K n x := by
  -- Both constructions are the same quotient class of the degree-`n` monomial representative.
  simp [idealAssociatedGradedStageToOwnerLinear, idealAssociatedGradedStageToOwner,
    idealAssociatedGradedStageToReesLinear, idealAssociatedGradedStageToRees]

/-- Helper for Lemma 10.150.6: taking the `n`-th coefficient sends the denominator ideal of the
quotient-Rees presentation into `K^(n + 1)`. -/
private theorem reesAlgebra_coeff_mem_pow_succ_of_mem_denominator
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    {y : reesAlgebra K}
    (hy : y ∈ Ideal.map (algebraMap A (reesAlgebra K)) K) :
    y.1.coeff n ∈ K ^ (n + 1) := by
  -- Rewrite the denominator ideal as `K • ⊤`, then check the `n`-th coefficient on generators.
  have hy' : y ∈ K • (⊤ : Submodule A (reesAlgebra K)) := by
    simpa [Ideal.smul_top_eq_map] using hy
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr z hz
    -- A scalar from `K` multiplies a coefficient already lying in `K^n`.
    have hzcoeff : z.1.coeff n ∈ K ^ n := z.2 n
    change (r • z.1).coeff n ∈ K ^ (n + 1)
    simpa [Polynomial.coeff_smul, smul_eq_mul, pow_succ', Ideal.mul_comm] using
      Ideal.mul_mem_mul hr hzcoeff
  · intro x y hx hy
    -- The coefficient condition is additive.
    simpa [Polynomial.coeff_add] using Ideal.add_mem (K ^ (n + 1)) hx hy

/-- Helper for Lemma 10.150.6: if a coefficient already lies in `K^(n + 1)`, then the
corresponding degree-`n` monomial belongs to the denominator ideal of the quotient-Rees model. -/
private theorem monomial_mem_denominator_of_mem_pow_succ
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) {a : A}
    (ha : a ∈ K ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
      reesAlgebra K) ∈ Ideal.map (algebraMap A (reesAlgebra K)) K := by
  -- Rewrite denominator membership inside the subtype as an ambient polynomial membership.
  have hsmul :
      (⟨Polynomial.monomial n a,
          reesAlgebra.monomial_mem.mpr
            ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
        reesAlgebra K) ∈ K • (⊤ : Submodule A (reesAlgebra K)) := by
    let x : reesAlgebra K :=
      ⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩
    let φ : A →ₗ[A] Polynomial A := Polynomial.monomial n
    have ha' : a ∈ K • (K ^ n : Submodule A A) := by
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm] using ha
    let RK : Submodule A (Polynomial A) := Subalgebra.toSubmodule (reesAlgebra K)
    have hmap0 :
        (Submodule.map φ (K ^ n : Submodule A A) : Submodule A (Polynomial A)) ≤ RK := by
      intro p hp
      rcases hp with ⟨b, hb, rfl⟩
      exact reesAlgebra.monomial_mem.mpr hb
    have hmap :
        (Submodule.map φ (K • (K ^ n : Submodule A A)) : Submodule A (Polynomial A)) ≤
          (K • RK : Submodule A (Polynomial A)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.mpr ?_
      intro r hr p hp
      exact Submodule.smul_mem_smul hr (hmap0 hp)
    have hambient :
        (x : Polynomial A) ∈ K • RK := by
      have hxmap : φ a ∈ Submodule.map φ (K • (K ^ n : Submodule A A)) := by
        exact Submodule.mem_map_of_mem ha'
      exact hmap <| by simpa [φ, x] using hxmap
    exact
      (Submodule.mem_smul_top_iff (I := K)
        (N := RK) (x := x)).2 hambient
  simpa [Ideal.smul_top_eq_map] using hsmul

/-- Helper for Lemma 10.150.6: a degree-`n` monomial class vanishes in the owner piece exactly
when its coefficient lies in the next filtration step. -/
private theorem idealAssociatedGradedStageToOwner_zero_iff
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    idealAssociatedGradedStageToOwner K n x = 0 ↔
      (x : A) ∈ RingTheory.Sequence.idealAssociatedGradedStage K A (n + 1) := by
  -- A quotient class vanishes exactly when its Rees representative lies in the denominator ideal.
  constructor
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
          (idealAssociatedGradedStageToRees K n x) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    -- The denominator condition forces the degree-`n` coefficient into `K^(n + 1)`.
    simpa [idealAssociatedGradedStageToRees, RingTheory.Sequence.idealAssociatedGradedStage,
      Ideal.smul_eq_mul, Ideal.mul_top]
      using reesAlgebra_coeff_mem_pow_succ_of_mem_denominator K n hx
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
          (idealAssociatedGradedStageToRees K n x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    -- Conversely, a coefficient in `K^(n + 1)` produces a denominator monomial.
    have hx' : (x : A) ∈ K ^ (n + 1) := by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx
    simpa [idealAssociatedGradedStageToRees] using
      monomial_mem_denominator_of_mem_pow_succ K n hx'

/-- Helper for Lemma 10.150.6: every degree-`n` owner class is represented by a stage element. -/
private theorem idealAssociatedGradedStageToOwnerLinear_surjective
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageToOwnerLinear K n) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  rcases hy with ⟨a, rfl⟩
  refine ⟨⟨a.1, ?_⟩, ?_⟩
  · -- A homogeneous Rees generator in degree `n` is exactly an element of `K^n`.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  · -- The representative is already the canonical monomial image of that stage element.
    exact Subtype.ext <| by
      simpa [idealAssociatedGradedStageToOwnerLinear, idealAssociatedGradedStageToReesLinear] using hxy

/-- Helper for Lemma 10.150.6: the kernel of the stage-to-owner map is the next filtration
stage. -/
private theorem idealAssociatedGradedStageToOwnerLinear_ker_eq
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageToOwnerLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K A (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K A n) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (((idealAssociatedGradedStageToOwnerLinear K n x : idealAssociatedGradedRingGrade K n) :
            idealAssociatedGradedRing K)) = 0 := by
      exact congrArg (fun z : idealAssociatedGradedRingGrade K n ↦ (z : idealAssociatedGradedRing K)) hx
    change idealAssociatedGradedStageToOwner K n x = 0 at hx'
    exact (idealAssociatedGradedStageToOwner_zero_iff K n x).1 hx'
  · intro hx
    apply Subtype.ext
    change idealAssociatedGradedStageToOwner K n x = 0
    exact (idealAssociatedGradedStageToOwner_zero_iff K n x).2 hx

/-- Helper for Lemma 10.150.6: the owner map sends a difference of stage representatives to the
difference of their owner classes. -/
private theorem idealAssociatedGradedStageToOwner_sub
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x y : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    idealAssociatedGradedStageToOwner K n (x - y) =
      idealAssociatedGradedStageToOwner K n x - idealAssociatedGradedStageToOwner K n y := by
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
        (idealAssociatedGradedStageToRees K n (x - y)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
          (idealAssociatedGradedStageToRees K n x) -
        Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra K)) K)
          (idealAssociatedGradedStageToRees K n y)
  rw [← RingHom.map_sub]
  congr 1
  apply Subtype.ext
  simp [idealAssociatedGradedStageToRees, Polynomial.monomial_sub]

/-- Helper for Lemma 10.150.6: if two degree-`n` stage representatives define the same owner
class, then their difference lies in the next stage. -/
private theorem idealAssociatedGradedStage_sub_mem_succ_of_owner_eq
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    {x y : RingTheory.Sequence.idealAssociatedGradedStage K A n}
    (hxy : idealAssociatedGradedStageToOwner K n x =
      idealAssociatedGradedStageToOwner K n y) :
    ((x - y : RingTheory.Sequence.idealAssociatedGradedStage K A n) : A) ∈
      RingTheory.Sequence.idealAssociatedGradedStage K A (n + 1) := by
  have hzero :
      idealAssociatedGradedStageToOwner K n (x - y) = 0 := by
    rw [idealAssociatedGradedStageToOwner_sub K n x y, hxy, sub_self]
  exact (idealAssociatedGradedStageToOwner_zero_iff K n (x - y)).1 hzero

/-- Helper for Lemma 10.150.6: the owner degree-`n` homogeneous piece is canonically equivalent to
the textbook quotient `K^n / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_piece
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃ₗ[A] RingTheory.Sequence.idealAssociatedGradedPiece K A n :=
  let φ := idealAssociatedGradedStageToOwnerLinear K n
  -- First identify the owner grade with the stage quotient by the kernel of the stage-to-owner
  -- map, then replace that kernel by the next stage of the filtration.
  ((φ.quotKerEquivOfSurjective
      (idealAssociatedGradedStageToOwnerLinear_surjective K n)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageToOwnerLinear_ker_eq K n)))

/-- Helper for Lemma 10.150.6: the canonical quotient map sends the `n`-th filtration stage
into the image of `K ^ n` inside `A / K^(n + 1)`. -/
private theorem idealAssociatedGradedStageToPowQuotient_mem
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    Ideal.Quotient.mk (K ^ (n + 1)) (x : A) ∈
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- Forgetting the subtype turns the stage condition into membership in `K ^ n`.
  exact Ideal.mem_map_of_mem _ <|
    by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using x.2

/-- Helper for Lemma 10.150.6: the `n`-th stage maps linearly onto the image of `K ^ n`
inside `A / K^(n + 1)`. -/
private def idealAssociatedGradedStageToPowQuotientLinear
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K A n →ₗ[A]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  { toFun := fun x ↦ ⟨Ideal.Quotient.mk (K ^ (n + 1)) (x : A),
      idealAssociatedGradedStageToPowQuotient_mem K n x⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      rfl
    map_smul' := fun r x ↦ by
      apply Subtype.ext
      rfl }

/-- Helper for Lemma 10.150.6: every class in the image of `K ^ n` inside `A / K^(n + 1)` comes
from an element of the `n`-th stage. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_surjective
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageToPowQuotientLinear K n) := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (K ^ (n + 1))) Ideal.Quotient.mk_surjective).mp hy with
    ⟨a, ha, rfl⟩
  refine ⟨⟨a, ?_⟩, ?_⟩
  · -- The witness in `K ^ n` is exactly an element of the `n`-th filtration stage.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using ha
  · -- The codomain representative is built from the same quotient class.
    apply Subtype.ext
    rfl

/-- Helper for Lemma 10.150.6: the kernel of the stage-to-quotient map is the next filtration
step. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_ker_eq
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageToPowQuotientLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K A (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K A n) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hx' : Ideal.Quotient.mk (K ^ (n + 1)) (x : A) = 0 := congrArg Subtype.val hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      by simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx

/-- Helper for Lemma 10.150.6: the quotient `K^n / K^(n + 1)` is canonically equivalent to the
image of `K ^ n` inside `A / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedPiece_equiv_map_pow
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece K A n ≃ₗ[A]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  let φ := idealAssociatedGradedStageToPowQuotientLinear K n
  -- Replace the denominator by the actual kernel, then apply the first isomorphism theorem.
  (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageToPowQuotientLinear_ker_eq K n).symm).trans
    (φ.quotKerEquivOfSurjective
      (idealAssociatedGradedStageToPowQuotientLinear_surjective K n))

/-- Helper for Lemma 10.150.6: the piece-to-quotient identification sends the stage class of
`x` to the quotient class of `x` modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedPiece_equiv_map_pow_apply_stage
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    idealAssociatedGradedPiece_equiv_map_pow K n
      (Submodule.Quotient.mk x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- Both quotient equivalences act trivially on the stage representative `x`.
  simp [idealAssociatedGradedPiece_equiv_map_pow]

/-- Helper for Lemma 10.150.6: the owner degree-`n` piece is canonically equivalent to the image
of `K ^ n` inside `A / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_map_pow
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  (idealAssociatedGradedRingGrade_equiv_piece K n).toEquiv.trans
    (idealAssociatedGradedPiece_equiv_map_pow K n).toEquiv

/-- Helper for Lemma 10.150.6: on stage representatives, the owner-grade equivalence agrees with
the canonical quotient class modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedRingGrade_equiv_map_pow_apply_stage
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K A n) :
    idealAssociatedGradedRingGrade_equiv_map_pow K n
      (idealAssociatedGradedStageToOwnerLinear K n x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- First identify the owner grade with `K^n / K^(n + 1)`, then with the quotient image.
  simpa [idealAssociatedGradedRingGrade_equiv_map_pow, idealAssociatedGradedRingGrade_equiv_piece]
    using idealAssociatedGradedPiece_equiv_map_pow_apply_stage (A := A) K n x

/-- Helper for Lemma 10.150.6: applying `f` to an element of the `n`-th stage lands in the
`n`-th stage for `J`. -/
private theorem idealAssociatedGradedStageMap_mem
    (n : ℕ) :
    letI := f.toAlgebra
    ∀ x : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n,
      f (x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage J S n := by
  letI := f.toAlgebra
  intro x
  -- The stage membership is exactly `I^n`; transport it through `I^n ≤ comap f (J^n)`.
  have hx :
      (x : R) ∈ Icomap ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  have hfx : f (x : R) ∈ J ^ n := Ideal.mem_comap.mp ((J.le_comap_pow f n) hx)
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using hfx

/-- Helper for Lemma 10.150.6: the image of a stage element under `f` as an element of the
corresponding `J`-adic stage. -/
private def idealAssociatedGradedStageMap
    (n : ℕ) :
    letI := f.toAlgebra
    RingTheory.Sequence.idealAssociatedGradedStage Icomap R n →
      RingTheory.Sequence.idealAssociatedGradedStage J S n :=
  letI := f.toAlgebra
  fun x ↦ ⟨f (x : R), idealAssociatedGradedStageMap_mem (f := f) (J := J) n x⟩

/-- Helper for Lemma 10.150.6: on monomial representatives, the owner grade map is induced by
applying `f` to the coefficient. -/
private theorem idealAssociatedGradedGradeMap_apply_stage
    (n : ℕ) :
    letI := f.toAlgebra
    ∀ x : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n,
      idealAssociatedGradedGradeMap Icomap J f le_rfl n
        (idealAssociatedGradedStageToOwnerLinear Icomap n x) =
          idealAssociatedGradedStageToOwnerLinear J n
            (idealAssociatedGradedStageMap (f := f) (J := J) n x) := by
  letI := f.toAlgebra
  intro x
  -- Both sides are the class of the same degree-`n` monomial with coefficient `f x`.
  have hrees :
      reesAlgebraMap f le_rfl (idealAssociatedGradedStageToReesLinear Icomap n x) =
        idealAssociatedGradedStageToReesLinear J n
          (idealAssociatedGradedStageMap (f := f) (J := J) n x) := by
    apply Subtype.ext
    change
      Polynomial.mapRingHom f (Polynomial.monomial n (x : R)) =
        Polynomial.monomial n (f (x : R))
    exact Polynomial.map_monomial (f := f) (n := n) (a := (x : R))
  apply Subtype.ext
  exact congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra J)) J)) hrees

/-- Helper for Lemma 10.150.6: the quotient equivalence at level `n + 1` identifies the source
kernel of `R / I^(n + 1) → R / I^n` with the target kernel of `S / J^(n + 1) → S / J^n`. -/
private theorem factorPow_kernel_comap_quotientMapPowAlgEquiv
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    letI := f.toAlgebra
    let eSucc :
        (R ⧸ (Icomap ^ (n + 1))) ≃ₐ[R] (S ⧸ (J ^ (n + 1))) :=
      quotientMapPowAlgEquiv (f := f) (J := J) (n + 1)
        (formallyEtale_quotientMap_pow_bijective (f := f) (J := J) hf hsurj (n + 1))
    RingHom.ker (Ideal.Quotient.factorPow Icomap (Nat.le_succ n)) =
      (RingHom.ker (Ideal.Quotient.factorPow J (Nat.le_succ n))).comap eSucc.toRingHom := by
  letI := f.toAlgebra
  let eSucc :
      (R ⧸ (Icomap ^ (n + 1))) ≃ₐ[R] (S ⧸ (J ^ (n + 1))) :=
    quotientMapPowAlgEquiv (f := f) (J := J) (n + 1)
      (formallyEtale_quotientMap_pow_bijective (f := f) (J := J) hf hsurj (n + 1))
  let ePrev :
      (R ⧸ (Icomap ^ n)) ≃ₐ[R] (S ⧸ (J ^ n)) :=
    quotientMapPowAlgEquiv (f := f) (J := J) n
      (formallyEtale_quotientMap_pow_bijective (f := f) (J := J) hf hsurj n)
  let factorI : R ⧸ (Icomap ^ (n + 1)) →ₐ[R] R ⧸ (Icomap ^ n) :=
    { Ideal.Quotient.factorPow Icomap (Nat.le_succ n) with commutes' := fun _ => rfl }
  let factorJ : S ⧸ (J ^ (n + 1)) →ₐ[R] S ⧸ (J ^ n) :=
    { Ideal.Quotient.factorPow J (Nat.le_succ n) with commutes' := fun _ => rfl }
  have hcomm : factorJ.comp eSucc.toAlgHom = ePrev.toAlgHom.comp factorI := by
    simpa [eSucc, ePrev, factorI, factorJ] using
      (quotientMap_factorPow_commutes (f := f) (J := J) (n + 1) n (Nat.le_succ n))
  ext x
  constructor
  · intro hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    -- Transport the kernel condition across the commuting square.
    have hcommx : factorJ (eSucc x) = ePrev (factorI x) := AlgHom.congr_fun hcomm x
    have hx' : factorJ (eSucc x) = 0 := by
      have hfactorI : factorI x = 0 := RingHom.mem_ker.mp hx
      rw [hcommx, hfactorI]
      simp
    simpa [factorJ, eSucc] using hx'
  · intro hx
    rw [Ideal.mem_comap, RingHom.mem_ker] at hx
    rw [RingHom.mem_ker]
    have hx' : factorJ (eSucc x) = 0 := by
      simpa [factorJ, eSucc] using hx
    have hcommx : factorJ (eSucc x) = ePrev (factorI x) := AlgHom.congr_fun hcomm x
    have hfactor : ePrev (factorI x) = 0 := by
      rw [← hcommx]
      exact hx'
    exact ePrev.injective <| by simpa [factorI] using hfactor

/-- Helper for Lemma 10.150.6: the quotient equivalence at level `n + 1` induces an equivalence
between the successive quotients `I^n / I^(n + 1)` and `J^n / J^(n + 1)`. -/
private noncomputable def idealAssociatedGradedPowKernelEquiv
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk (Icomap ^ (n + 1))) (Icomap ^ n) ≃
      Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n) :=
  letI := f.toAlgebra
  let eSucc :
      (R ⧸ (Icomap ^ (n + 1))) ≃ₐ[R] (S ⧸ (J ^ (n + 1))) :=
    quotientMapPowAlgEquiv (f := f) (J := J) (n + 1)
      (formallyEtale_quotientMap_pow_bijective (f := f) (J := J) hf hsurj (n + 1))
  -- First rewrite the successive quotients as transition kernels, then restrict the quotient
  -- equivalence to those kernels.
  ((LinearEquiv.ofEq _ _
      (factorPow_kernel_eq_map_pow (K := Icomap) n).symm).toEquiv.trans
    ((LinearEquiv.ofEq _ _
        (factorPow_kernel_comap_quotientMapPowAlgEquiv
          (f := f) (J := J) hf hsurj n)).toEquiv.trans
      (((eSucc.toLinearEquiv.ofSubmodule'
          (Submodule.restrictScalars R
            (RingHom.ker (Ideal.Quotient.factorPow J (Nat.le_succ n))))).toEquiv.trans
        (LinearEquiv.ofEq _ _
          (factorPow_kernel_eq_map_pow (K := J) n)).toEquiv))))

/-- Helper for Lemma 10.150.6: the quotient-kernel equivalence sends the class of `x ∈ I^n`
modulo `I^(n + 1)` to the class of `f x ∈ J^n` modulo `J^(n + 1)`. -/
private theorem idealAssociatedGradedPowKernelEquiv_apply_stage
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    letI := f.toAlgebra
    ∀ x : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n,
      idealAssociatedGradedPowKernelEquiv (f := f) (J := J) hf hsurj n
        (idealAssociatedGradedStageToPowQuotientLinear Icomap n x) =
          idealAssociatedGradedStageToPowQuotientLinear J n
            (idealAssociatedGradedStageMap (f := f) (J := J) n x) := by
  letI := f.toAlgebra
  intro x
  -- Unfold the restricted kernel equivalence and evaluate it on the explicit quotient class.
  rfl

/-- Helper for Lemma 10.150.6: if every coefficient lies one step deeper in the filtration,
then the Rees element belongs to the denominator ideal defining the associated graded ring. -/
private theorem reesAlgebra_mem_denominator_of_coeff_mem_pow_succ
    {A : Type*} [CommRing A] (K : Ideal A) {y : reesAlgebra K}
    (hy : ∀ n, y.1.coeff n ∈ K ^ (n + 1)) :
    y ∈ Ideal.map (algebraMap A (reesAlgebra K)) K := by
  classical
  -- Expand the polynomial as a finite sum of monomials and use the monomial denominator test
  -- termwise.
  let terms : reesAlgebra K :=
    Finset.sum y.1.support fun n ↦
      (⟨Polynomial.monomial n (y.1.coeff n), reesAlgebra.monomial_mem.mpr (y.2 n)⟩ :
        reesAlgebra K)
  have hterms :
      terms ∈ Ideal.map (algebraMap A (reesAlgebra K)) K := by
    exact Ideal.sum_mem _ fun n _ ↦ monomial_mem_denominator_of_mem_pow_succ K n (hy n)
  have hsum : terms = y := by
    apply Subtype.ext
    ext m
    calc
      terms.1.coeff m =
          ∑ n ∈ y.1.support, (Polynomial.monomial n (y.1.coeff n)).coeff m := by
            simp [terms, Polynomial.finset_sum_coeff]
      _ = y.1.coeff m := by
        by_cases hm : m ∈ y.1.support
        · rw [Finset.sum_eq_single_of_mem m hm]
          · simp
          · intro i hi him
            simp [Polynomial.coeff_monomial, him]
        · have hy0 : y.1.coeff m = 0 := by
            simpa [Polynomial.mem_support_iff] using hm
          rw [Finset.sum_eq_zero]
          · simpa [hy0]
          · intro i hi
            have him : i ≠ m := by
              intro hi_eq
              exact hm (hi_eq ▸ hi)
            simp [Polynomial.coeff_monomial, him]
  rw [← hsum]
  exact hterms

/-- Helper for Lemma 10.150.6: denominator membership in the quotient-Rees model is equivalent to
the coefficientwise condition `a_n ∈ K^(n + 1)`. -/
private theorem reesAlgebra_mem_denominator_iff_coeff_mem_pow_succ
    {A : Type*} [CommRing A] (K : Ideal A) {y : reesAlgebra K} :
    y ∈ Ideal.map (algebraMap A (reesAlgebra K)) K ↔
      ∀ n, y.1.coeff n ∈ K ^ (n + 1) := by
  constructor
  · intro hy n
    exact reesAlgebra_coeff_mem_pow_succ_of_mem_denominator K n hy
  · intro hy
    exact reesAlgebra_mem_denominator_of_coeff_mem_pow_succ K hy

-- Proof sketch: apply quotient-thickening bijectivity to the successive quotients defining the
-- associated graded ring to obtain bijectivity of the owner map `idealAssociatedGradedMap f
-- le_rfl`. The degreewise homogeneous-piece statement is then the derived restriction of this
-- owner-level comparison along `idealAssociatedGradedRingGrade`.
-- Route correction: this item no longer depends on the broken tail of `10_69_0_1.lean`; the
-- remaining work is now isolated to the source-faithful owner-grade bridge and the direct-sum
-- packaging of those degreewise comparisons.

/-- Companion: the bijective associated graded ring map restricts to a bijection on each
degree-`n` homogeneous piece. -/
theorem formallyEtale_associatedGradedGradeMap_bijective
    (hf : f.FormallyEtale)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    Function.Bijective (idealAssociatedGradedGradeMap Icomap J f le_rfl n) := by
  -- The degree-preservation part of this restriction is already available via
  -- `idealAssociatedGradedMap_mem_grade`; what remains is the owner-grade/piece identification.
  letI := f.toAlgebra
  let eSrc := idealAssociatedGradedRingGrade_equiv_map_pow (K := Icomap) n
  let eTgt := idealAssociatedGradedRingGrade_equiv_map_pow (K := J) n
  let ePow := idealAssociatedGradedPowKernelEquiv (f := f) (J := J) hf hsurj n
  have hcomm :
      ∀ x : idealAssociatedGradedRingGrade Icomap n,
        eTgt (idealAssociatedGradedGradeMap Icomap J f le_rfl n x) = ePow (eSrc x) := by
    intro x
    rcases idealAssociatedGradedStageToOwnerLinear_surjective Icomap n x with ⟨y, rfl⟩
    -- It suffices to compare the two maps on stage representatives.
    calc
      eTgt
          (idealAssociatedGradedGradeMap Icomap J f le_rfl n
            (idealAssociatedGradedStageToOwnerLinear Icomap n y))
          = eTgt
              (idealAssociatedGradedStageToOwnerLinear J n
                (idealAssociatedGradedStageMap (f := f) (J := J) n y)) := by
                  simpa using idealAssociatedGradedGradeMap_apply_stage (f := f) (J := J) n y
      _ = idealAssociatedGradedStageToPowQuotientLinear J n
            (idealAssociatedGradedStageMap (f := f) (J := J) n y) := by
            exact idealAssociatedGradedRingGrade_equiv_map_pow_apply_stage J n _
      _ = ePow (idealAssociatedGradedStageToPowQuotientLinear Icomap n y) := by
            symm
            exact idealAssociatedGradedPowKernelEquiv_apply_stage (f := f) (J := J) hf hsurj n y
      _ = ePow (eSrc (idealAssociatedGradedStageToOwnerLinear Icomap n y)) := by
            rw [idealAssociatedGradedRingGrade_equiv_map_pow_apply_stage Icomap n y]
  constructor
  · intro x y hxy
    apply eSrc.injective
    apply ePow.injective
    rw [← hcomm x, ← hcomm y, hxy]
  · intro y
    refine ⟨eSrc.symm (ePow.symm (eTgt y)), ?_⟩
    apply eTgt.injective
    rw [hcomm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Lemma 10.150.6 (2): under the same hypotheses, the induced map on associated graded rings
`gr_(comap f J)(R) → gr_J(S)` is bijective. -/
@[stacks 0H1D]
theorem formallyEtale_associatedGradedMap_bijective :
    f.FormallyEtale →
    Function.Surjective ((Ideal.Quotient.mk J).comp f) →
    Function.Bijective
      ((idealAssociatedGradedMap f le_rfl) :
        idealAssociatedGradedRing Icomap →+* idealAssociatedGradedRing J) := by
  -- After proving the homogeneous-piece bijections, package them coefficientwise on
  -- representatives in the quotient-Rees model.
  intro hf hsurj
  let g :
      idealAssociatedGradedRing Icomap →+* idealAssociatedGradedRing J :=
    idealAssociatedGradedMap f le_rfl
  have hker_zero :
      ∀ z : idealAssociatedGradedRing Icomap, g z = 0 → z = 0 := by
    intro z
    refine Quotient.inductionOn z ?_
    intro y hz
    change Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra Icomap)) Icomap) y = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply reesAlgebra_mem_denominator_of_coeff_mem_pow_succ
    intro n
    -- The image class vanishes, so each degree-`n` coefficient class vanishes after applying `f`.
    have hy_zero :
        reesAlgebraMap f le_rfl y ∈ Ideal.map (algebraMap S (reesAlgebra J)) J := by
      simpa [g] using (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    let xStage : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n :=
      ⟨y.1.coeff n, by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using y.2 n⟩
    let yStage : RingTheory.Sequence.idealAssociatedGradedStage J S n :=
      idealAssociatedGradedStageMap (f := f) (J := J) n xStage
    have hyStage_zero :
        idealAssociatedGradedStageToOwner J n yStage = 0 := by
      -- The target coefficient condition is exactly the zero criterion in the owner piece.
      apply (idealAssociatedGradedStageToOwner_zero_iff J n yStage).2
      simpa [yStage, idealAssociatedGradedStageMap, reesAlgebraMap, Polynomial.coeff_map]
        using reesAlgebra_coeff_mem_pow_succ_of_mem_denominator J n hy_zero
    let zeroJ : idealAssociatedGradedRingGrade J n := 0
    let zeroI : idealAssociatedGradedRingGrade Icomap n := 0
    have hgrade_zero :
        idealAssociatedGradedGradeMap Icomap J f le_rfl n
          (idealAssociatedGradedStageToOwnerLinear Icomap n xStage) =
            zeroJ := by
      -- On stage representatives the grade map is coefficientwise application of `f`.
      rw [idealAssociatedGradedGradeMap_apply_stage (f := f) (J := J) n xStage]
      apply Subtype.ext
      change idealAssociatedGradedStageToOwner J n yStage = 0
      simpa [zeroJ] using hyStage_zero
    have hxStage_zero :
        idealAssociatedGradedStageToOwner Icomap n xStage = 0 := by
      -- Injectivity on the `n`-th owner grade forces the source stage class to vanish.
      have hxStage_zero_linear :
          idealAssociatedGradedStageToOwnerLinear Icomap n xStage =
            zeroI := by
        have hmap_zero :
            idealAssociatedGradedGradeMap Icomap J f le_rfl n
                zeroI =
              zeroJ := by
          exact Subtype.ext <| by
            simp [zeroI, zeroJ, idealAssociatedGradedGradeMap, idealAssociatedGradedMap]
        have hgrade_zero' :
            idealAssociatedGradedGradeMap Icomap J f le_rfl n
              (idealAssociatedGradedStageToOwnerLinear Icomap n xStage) =
                idealAssociatedGradedGradeMap Icomap J f le_rfl n
                  zeroI := by
          rw [hmap_zero]
          exact hgrade_zero
        exact
          (formallyEtale_associatedGradedGradeMap_bijective (f := f) (J := J) hf hsurj n).1
            hgrade_zero'
      have hxStage_zero_owner :
          (((idealAssociatedGradedStageToOwnerLinear Icomap n xStage :
              idealAssociatedGradedRingGrade Icomap n) : idealAssociatedGradedRing Icomap)) = 0 := by
        exact congrArg (fun z : idealAssociatedGradedRingGrade Icomap n ↦
          (z : idealAssociatedGradedRing Icomap)) hxStage_zero_linear
      change idealAssociatedGradedStageToOwner Icomap n xStage = 0 at hxStage_zero_owner
      exact hxStage_zero_owner
    -- Translating the source owner vanishing back gives the deeper coefficient condition.
    simpa [xStage] using (idealAssociatedGradedStageToOwner_zero_iff Icomap n xStage).1 hxStage_zero
  constructor
  · intro x y hxy
    -- Trivial kernel implies injectivity by applying it to `x - y`.
    have hsub : g (x - y) = 0 := by
      calc
        g (x - y) = g x - g y := by exact g.map_sub x y
        _ = 0 := by rw [hxy, sub_self]
    have hzero : x - y = 0 := hker_zero (x - y) hsub
    exact sub_eq_zero.mp hzero
  · intro z
    refine Quotient.inductionOn z ?_
    intro y
    classical
    let yStage :
        ∀ n, RingTheory.Sequence.idealAssociatedGradedStage J S n :=
      fun n ↦ ⟨y.1.coeff n, by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using y.2 n⟩
    -- Choose a source stage representative for each target degree appearing in `y`.
    have hpre :
        ∀ n ∈ y.1.support,
          ∃ x : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n,
            idealAssociatedGradedGradeMap Icomap J f le_rfl n
              (idealAssociatedGradedStageToOwnerLinear Icomap n x) =
                idealAssociatedGradedStageToOwnerLinear J n (yStage n) := by
      intro n hn
      rcases
          (formallyEtale_associatedGradedGradeMap_bijective (f := f) (J := J) hf hsurj n).2
            (idealAssociatedGradedStageToOwnerLinear J n (yStage n)) with
        ⟨u, hu⟩
      rcases idealAssociatedGradedStageToOwnerLinear_surjective Icomap n u with ⟨x, rfl⟩
      exact ⟨x, hu⟩
    choose x hx using hpre
    let preimage : reesAlgebra Icomap :=
      Finset.sum y.1.support.attach fun m ↦
        idealAssociatedGradedStageToRees Icomap m.1 (x m.1 m.2)
    refine ⟨Ideal.Quotient.mk _ preimage, ?_⟩
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra J)) J)
          (reesAlgebraMap f le_rfl preimage) =
        Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra J)) J) y
    apply Ideal.Quotient.eq.2
    apply reesAlgebra_mem_denominator_of_coeff_mem_pow_succ
    intro n
    by_cases hn : n ∈ y.1.support
    · let xStage : RingTheory.Sequence.idealAssociatedGradedStage Icomap R n := x n hn
      have hcoeff :
          idealAssociatedGradedStageToOwnerLinear J n
            (idealAssociatedGradedStageMap (f := f) (J := J) n xStage) =
              idealAssociatedGradedStageToOwnerLinear J n (yStage n) := by
        -- The chosen preimage matches the target degree-`n` class.
        have hx' := hx n hn
        rw [idealAssociatedGradedGradeMap_apply_stage (f := f) (J := J) n xStage] at hx'
        exact hx'
      have hpreimage_coeff :
          preimage.1.coeff n = (xStage : R) := by
        let nAttach : {m // m ∈ y.1.support} := ⟨n, hn⟩
        calc
          preimage.1.coeff n =
              ∑ m ∈ y.1.support.attach,
                if m.1 = n then
                  ((x m.1 m.2 :
                    RingTheory.Sequence.idealAssociatedGradedStage Icomap R m.1) : R)
                else 0 := by
                simp [preimage, Polynomial.finset_sum_coeff,
                  idealAssociatedGradedStageToRees_coeff]
          _ = if n = n then (xStage : R) else 0 := by
                refine Finset.sum_eq_single_of_mem nAttach ?_ ?_
                · simp [nAttach]
                · intro m hm hmn
                  have hmn' : m.1 ≠ n := by
                    intro hm_eq
                    exact hmn (Subtype.ext hm_eq)
                  simp [hmn']
          _ = (xStage : R) := by simp
      have hmap_coeff :
          (reesAlgebraMap f le_rfl preimage).1.coeff n = f (xStage : R) := by
        calc
          (reesAlgebraMap f le_rfl preimage).1.coeff n = f (preimage.1.coeff n) := by
            simp [reesAlgebraMap, Polynomial.coeff_map]
          _ = f (xStage : R) := by rw [hpreimage_coeff]
      simpa [Polynomial.coeff_sub, hmap_coeff, idealAssociatedGradedStageMap, yStage] using
        idealAssociatedGradedStage_sub_mem_succ_of_owner_eq (K := J) (n := n)
          (congrArg Subtype.val hcoeff)
    · -- Off the support of `y`, both coefficients are zero, so the difference is trivially deep.
      have hy_coeff : y.1.coeff n = 0 := by
        simpa [Polynomial.mem_support_iff] using hn
      have hpreimage_coeff : preimage.1.coeff n = 0 := by
        calc
          preimage.1.coeff n =
              ∑ m ∈ y.1.support.attach,
                if m.1 = n then
                  ((x m.1 m.2 :
                    RingTheory.Sequence.idealAssociatedGradedStage Icomap R m.1) : R)
                else 0 := by
                simp [preimage, Polynomial.finset_sum_coeff,
                  idealAssociatedGradedStageToRees_coeff]
          _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro m hm
            have hmn : m.1 ≠ n := by
              intro hmn
              exact hn (hmn ▸ m.2)
            simp [hmn]
      have hmap_coeff : (reesAlgebraMap f le_rfl preimage).1.coeff n = 0 := by
        calc
          (reesAlgebraMap f le_rfl preimage).1.coeff n = f (preimage.1.coeff n) := by
            simp [reesAlgebraMap, Polynomial.coeff_map]
          _ = 0 := by rw [hpreimage_coeff, map_zero]
      simpa [Polynomial.coeff_sub, hmap_coeff, hy_coeff] using Ideal.zero_mem (J ^ (n + 1))

end RingHom
