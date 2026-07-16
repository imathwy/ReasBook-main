import Mathlib
import stacks_proof.stacks_project.Chap10.Example_10_136_8.Index

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

/-- Helper for Example 10.136.8: evaluating the normalized successor target at `X = -β`
does recover the quotient-coefficient action after first restricting the successor coefficients
along the predecessor reversed elementary-symmetric map. -/
theorem freeMonic_succ_eval₂RingHom_comp_remainder_coeffs (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    let β : AdjoinRoot (Polynomial.freeMonic ℤ (n + 1)) :=
      AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    RingHom.comp (RingHom.comp ψRing (algebraMap A1 B))
        (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
      RingHom.comp (freeMonic_succ_remainder_coeff_algHom n).toRingHom
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hcoeff :
      RingHom.comp (algebraMap A1 B) (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
        (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- Rewrite the quotient-coefficient action in the normalized target by the predecessor
    -- reversed elementary-symmetric coefficients.
    simpa [A1, B] using freeMonic_succ_remainder_coeff_action_eq_rev n
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun hcoeff x
  -- Apply evaluation to the already-normalized constant-polynomial identity.
  calc
    ψRing ((algebraMap A1 B) ((freeMonic_succ_remainder_coeff_algHom n) x)) =
        ψRing (Polynomial.C
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x)) := by
            exact congrArg ψRing hx
    _ = algebraMap A0 A1
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x) := by
            simpa [A0, A1, B, β, ψRing] using
              freeMonic_succ_eval₂RingHom_C n
                ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x)
    _ = (freeMonic_succ_remainder_coeff_algHom n)
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) x) := by
            rfl

/-- Helper for Example 10.136.8: the evaluation composite sends the universal successor free monic
polynomial to zero at the adjoined root `β`, which is the side condition needed for the corrected
`AdjoinRoot.lift` description. -/
theorem freeMonic_succ_eval₂RingHom_lift_relation (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    (Polynomial.freeMonic ℤ (n + 1)).eval₂
        (RingHom.comp ψRing (algebraMap A B)) β = 0 := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hzero :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂ (algebraMap A B) (-(Polynomial.X : B)) = 0 := by
    -- Reuse the normalized successor root relation before applying evaluation to `A₁`.
    simpa [Polynomial.aeval_def, A, B] using freeMonic_succ_aeval_neg_X_eq_zero n
  have hhom :
      ψRing ((Polynomial.freeMonic ℤ (n + 1)).eval₂ (algebraMap A B) (-(Polynomial.X : B))) =
        (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) (ψRing (-(Polynomial.X : B))) := by
    -- Push evaluation through the ring homomorphism `ψRing`.
    simpa using
      (Polynomial.hom_eval₂ (p := Polynomial.freeMonic ℤ (n + 1))
        (g := ψRing) (f := algebraMap A B) (x := -(Polynomial.X : B)))
  have hmapped :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) (ψRing (-(Polynomial.X : B))) = 0 := by
    -- Apply `ψRing` to the already-known vanishing relation in the normalized target.
    rw [← hhom, hzero]
    simp
  -- Replace the evaluated outer variable by the previously computed root value `β`.
  simpa [A, A0, A1, B, β, ψRing] using hmapped

/-- Helper for Example 10.136.8: the composite `A₁ → Polynomial A₀ → A₁` is the canonical
`AdjoinRoot` endomorphism determined by its induced action on the successor source ring and the
fact that it fixes the adjoined root `β`. -/
theorem freeMonic_succ_eval₂RingHom_section (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    RingHom.comp ψRing (algebraMap A1 B) =
      AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β
        (freeMonic_succ_eval₂RingHom_lift_relation n) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  have hβ :
      (Polynomial.freeMonic ℤ (n + 1)).eval₂
          (RingHom.comp ψRing (algebraMap A B)) β = 0 := by
    -- Freeze the side condition once so the `AdjoinRoot.lift` term stays readable.
    simpa [A, A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_lift_relation n
  -- Route correction: the old claim that `ψRing` is literally a section was too strong. The
  -- corrected statement identifies the composite with the unique `AdjoinRoot` endomorphism that
  -- has the induced source action `ψRing.comp (algebraMap A B)` and still fixes the adjoined root.
  apply AdjoinRoot.ringHom_ext
  · -- Both ring maps restrict to the same action on the successor source ring `A`.
    apply RingHom.ext
    intro a
    have hcomm :
        (algebraMap A1 B) ((AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) a) =
          algebraMap A B a := by
      -- The successor `AdjoinRoot` algebra was defined by a lift extending the normalized
      -- source action, so it commutes with the source coefficients by construction.
      simpa [A, A1, B, AdjoinRoot.algebraMap_eq] using
        (freeMonic_succ_adjoinRoot_to_normalized n).commutes a
    calc
      (((RingHom.comp ψRing (algebraMap A1 B)).comp
          (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1)))) a) =
          ψRing ((algebraMap A1 B) ((AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1))) a)) := by
            rfl
      _ = ψRing (algebraMap A B a) := by
            exact congrArg ψRing hcomm
      _ =
          (((AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β hβ).comp
              (AdjoinRoot.of (Polynomial.freeMonic ℤ (n + 1)))) a) := by
            simp [AdjoinRoot.lift_comp_of]
  · -- Both ring maps send the adjoined root to `β`.
    calc
      (RingHom.comp ψRing (algebraMap A1 B))
          (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) =
          ψRing (-(Polynomial.X : B)) := by
            simpa [RingHom.comp_apply, A, A1, B] using
              congrArg ψRing (freeMonic_succ_adjoinRoot_root_eq_neg_X n)
      _ = β := by
            simpa [A0, A1, B, β, ψRing] using freeMonic_succ_eval₂RingHom_root n
      _ = AdjoinRoot.lift (RingHom.comp ψRing (algebraMap A B)) β hβ
            (AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))) := by
              simp

/-- Helper for Example 10.136.8: evaluating a constant polynomial at `X = -β` just applies the
theorem-local predecessor coefficient map into the one-root stage. -/
theorem freeMonic_succ_eval₂RingHom_C (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
    ∀ a : A0, ψRing (Polynomial.C a) = algebraMap A0 A1 a := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let ψRing : B →+* A1 := Polynomial.eval₂RingHom (algebraMap A0 A1) (-β)
  -- Constants are untouched by polynomial evaluation except for the coefficient map.
  intro a
  simp

/-- Helper for Example 10.136.8: `Polynomial.C` preserves addition for the theorem-local
coefficient-inclusion map. -/
theorem freeMonic_succ_coeff_inclusionLinear_map_add (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let B := Polynomial A0
    ∀ a b : A0, (Polynomial.C (a + b) : B) = Polynomial.C a + Polynomial.C b := by
  let A0 := MvPolynomial (Fin n) ℤ
  let B := Polynomial A0
  intro a b
  simpa using (Polynomial.C_add a b)

/-- Helper for Example 10.136.8: `Polynomial.C` is compatible with the theorem-local twisted
predecessor scalar action induced by the reversed elementary-symmetric map. -/
theorem freeMonic_succ_coeff_inclusionLinear_map_smul (n : ℕ)
    (a b : MvPolynomial (Fin n) ℤ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let B := Polynomial A0
    let revHom : A0 →+* A0 :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
    let coeffHom : A0 →+* B :=
      (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom)
    let algRev : Algebra A0 A0 := revHom.toAlgebra
    let coeffAlg : Algebra A0 B := coeffHom.toAlgebra
    letI : Algebra A0 A0 := algRev
    letI : Module A0 A0 := algRev.toModule
    letI : Algebra A0 B := coeffAlg
    letI : Module A0 B := coeffAlg.toModule
    (Polynomial.C (a • b) : B) = a • (Polynomial.C b : B) := by
  let A0 := MvPolynomial (Fin n) ℤ
  let B := Polynomial A0
  let revHom : A0 →+* A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
  let coeffHom : A0 →+* B :=
    (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom)
  let algRev : Algebra A0 A0 := revHom.toAlgebra
  let coeffAlg : Algebra A0 B := coeffHom.toAlgebra
  letI : Algebra A0 A0 := algRev
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 B := coeffAlg
  letI : Module A0 B := coeffAlg.toModule
  have hcoeff :
      algebraMap A0 B a = Polynomial.C (revHom a) := by
    -- By definition the theorem-local coefficient action is constant inclusion after the twisted
    -- predecessor coefficient map.
    rfl
  -- Rewrite both scalar actions through their concrete coefficient-ring descriptions.
  calc
    (Polynomial.C (a • b) : B) = Polynomial.C (revHom a * b) := by
      -- The source scalar action is multiplication by the reversed coefficient image.
      change Polynomial.C ((algebraMap A0 A0 a) * b) = Polynomial.C (revHom a * b)
      rfl
    _ = Polynomial.C (revHom a) * Polynomial.C b := by
      rw [Polynomial.C_mul]
    _ = algebraMap A0 B a * Polynomial.C b := by
      rw [hcoeff]
    _ = a • (Polynomial.C b : B) := by
      rw [Algebra.smul_def, hcoeff]

/-- Helper for Chap10 Example 10 136 8: constant inclusion is linear for the predecessor
coefficient action after restricting the normalized successor target along `A₀ → A₁ → B`. -/
theorem freeMonic_succ_coeff_inclusion_smul_restrict (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    let algRev : Algebra A0 A0 :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    letI : Algebra A0 A0 := algRev
    letI : SMul A0 A0 := algRev.toSMul
    letI : Module A0 A0 := algRev.toModule
    letI : Algebra A0 A1 := algA01
    letI : SMul A0 A1 := algA01.toSMul
    letI : Algebra A1 B := algA1B
    let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
    letI : SMul A0 B := modA0B.toSMul
    letI : Module A0 B := modA0B
    ∀ a b : A0, (Polynomial.C (a • b) : B) = a • (Polynomial.C b : B) := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  let algRev : Algebra A0 A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  letI : Algebra A0 A0 := algRev
  letI : SMul A0 A0 := algRev.toSMul
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 A1 := algA01
  letI : SMul A0 A1 := algA01.toSMul
  letI : Algebra A1 B := algA1B
  let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
  letI : SMul A0 B := modA0B.toSMul
  letI : Module A0 B := modA0B
  dsimp only
  intro a b
  have hcoeff :
      RingHom.comp (algebraMap A1 B) (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
        (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- The restricted target action is the same coefficient action already normalized in the
    -- theorem-local support API.
    simpa [A0, A1, B, freeMonic_succ_adjoinRootAlgebra] using
      freeMonic_succ_remainder_coeff_action_eq_rev n
  have hcoeff_apply := DFunLike.congr_fun hcoeff a
  have hcoeff_apply' :
      algebraMap A1 B (algebraMap A0 A1 a) =
        Polynomial.C
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) : A0) := by
    -- Put the ring-hom equality in the exact scalar-action shape needed below.
    simpa [algA01, Polynomial.CAlgHom] using hcoeff_apply
  -- Reduce both scalar actions to multiplication by the same reversed elementary-symmetric
  -- coefficient, then use multiplicativity of `Polynomial.C`.
  calc
    (Polynomial.C (a • b) : B) =
        Polynomial.C ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) *
          b) := by
          change Polynomial.C ((algebraMap A0 A0 a) * b) = _
          rfl
    _ = Polynomial.C
          ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) : A0) *
        Polynomial.C b := by
          rw [Polynomial.C_mul]
    _ = algebraMap A1 B (algebraMap A0 A1 a) * Polynomial.C b := by
          rw [hcoeff_apply']
    _ = a • (Polynomial.C b : B) := by
          change algebraMap A1 B (algebraMap A0 A1 a) * Polynomial.C b =
            (algebraMap A0 A1 a) • (Polynomial.C b : B)
          rw [Algebra.smul_def]

/-- Helper for Chap10 Example 10 136 8: successor source coefficients lie in the subalgebra
obtained by adjoining the distinguished root to the predecessor quotient coefficients. -/
theorem freeMonic_succ_source_coeff_mem_remainder_root_adjoin (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    ∀ i : Fin (n + 1),
      algebraMap A A1 (MvPolynomial.X i) ∈ Algebra.adjoin A0 ({β} : Set A1) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A0 A1 := algA01
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let S : Subalgebra A0 A1 := Algebra.adjoin A0 ({β} : Set A1)
  dsimp only
  intro i
  have hlinearCoeff :
      ∀ k : ℕ, ((Polynomial.X - Polynomial.C β : Polynomial A1).coeff k) ∈ S := by
    intro k
    by_cases h0 : k = 0
    · subst k
      -- The constant coefficient of `X - C β` is `-β`, already in the generated subalgebra.
      simpa [Polynomial.coeff_X, Polynomial.coeff_C] using
        S.neg_mem (Algebra.subset_adjoin (by simp : β ∈ ({β} : Set A1)))
    · by_cases h1 : k = 1
      · subst k
        -- The degree-one coefficient is `1`.
        simpa [Polynomial.coeff_X, Polynomial.coeff_C] using (S.one_mem : (1 : A1) ∈ S)
      · -- Every other coefficient of the linear factor is zero.
        have h1' : 1 ≠ k := fun hk ↦ h1 hk.symm
        simpa [Polynomial.coeff_X, Polynomial.coeff_C, h0, h1, h1'] using
          (S.zero_mem : (0 : A1) ∈ S)
  have hquotCoeff : ∀ k : ℕ, (freeMonic_succ_remainder_quotient n).coeff k ∈ S := by
    intro k
    have hcoeff : (freeMonic_succ_remainder_quotient n).coeff k =
        algebraMap A0 A1 ((Polynomial.freeMonic ℤ n).coeff k) := by
      calc
        (freeMonic_succ_remainder_quotient n).coeff k =
            ((Polynomial.freeMonic ℤ n).map
              (freeMonic_succ_remainder_coeff_algHom n).toRingHom).coeff k := by
              rw [freeMonic_succ_remainder_coeff_algHom_spec n]
        _ = algebraMap A0 A1 ((Polynomial.freeMonic ℤ n).coeff k) := by
              rw [Polynomial.coeff_map]
              change (freeMonic_succ_remainder_coeff_algHom n).toRingHom
                  ((Polynomial.freeMonic ℤ n).coeff k) =
                (freeMonic_succ_remainder_coeff_algHom n).toRingHom
                  ((Polynomial.freeMonic ℤ n).coeff k)
              rfl
    -- Quotient coefficients are images of predecessor coefficients, hence already in the base.
    rw [hcoeff]
    exact S.algebraMap_mem ((Polynomial.freeMonic ℤ n).coeff k)
  have hleftMem :
      (((Polynomial.X - Polynomial.C β : Polynomial A1) *
          freeMonic_succ_remainder_quotient n).coeff i.1) ∈ S := by
    -- Coefficients of the product are finite sums of products of coefficients already in `S`.
    rw [Polynomial.coeff_mul]
    exact S.sum_mem (fun jk _ ↦ S.mul_mem (hlinearCoeff jk.1) (hquotCoeff jk.2))
  have hmul :
      (Polynomial.X - Polynomial.C β : Polynomial A1) * freeMonic_succ_remainder_quotient n =
        (Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1) := by
    simpa [A, A1, β] using freeMonic_succ_remainder_quotient_mul n
  have htarget :
      (((Polynomial.X - Polynomial.C β : Polynomial A1) *
          freeMonic_succ_remainder_quotient n).coeff i.1) =
        algebraMap A A1 (MvPolynomial.X i) := by
    -- The `i`th successor source variable is exactly the corresponding low coefficient of
    -- the mapped universal free monic polynomial.
    calc
      (((Polynomial.X - Polynomial.C β : Polynomial A1) *
          freeMonic_succ_remainder_quotient n).coeff i.1) =
          ((Polynomial.freeMonic ℤ (n + 1)).map (algebraMap A A1)).coeff i.1 := by
            rw [hmul]
      _ = algebraMap A A1 (MvPolynomial.X i) := by
            rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic, dif_pos i.2]
  simpa [htarget] using hleftMem

/-- Helper for Chap10 Example 10 136 8: every successor source element maps into the subalgebra
adjoining the root to the predecessor quotient coefficients. -/
theorem freeMonic_succ_source_mem_remainder_root_adjoin (n : ℕ) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    ∀ a : A, algebraMap A A1 a ∈ Algebra.adjoin A0 ({β} : Set A1) := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A0 A1 := algA01
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let S : Subalgebra A0 A1 := Algebra.adjoin A0 ({β} : Set A1)
  dsimp only
  intro a
  induction a using MvPolynomial.induction_on with
  | C z =>
      -- Integer constants come from the predecessor coefficient algebra.
      have hconst : algebraMap A A1 (MvPolynomial.C z) = algebraMap A0 A1 (MvPolynomial.C z) := by
        simp [A, A0, A1]
      rw [hconst]
      exact S.algebraMap_mem (MvPolynomial.C z : A0)
  | add p q hp hq =>
      -- The generated subalgebra is closed under addition.
      simpa using S.add_mem hp hq
  | mul_X p i hp =>
      -- Multiplication by a source variable stays inside by the coefficient-membership lemma.
      have hX := freeMonic_succ_source_coeff_mem_remainder_root_adjoin n i
      simpa [map_mul] using S.mul_mem hp hX

/-- Helper for Chap10 Example 10 136 8: the one-root stage is generated over the predecessor
quotient coefficients by the distinguished root. -/
theorem freeMonic_succ_remainder_root_adjoin_eq_top (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    Algebra.adjoin A0 ({β} : Set A1) = ⊤ := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A0 A1 := algA01
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let S : Subalgebra A0 A1 := Algebra.adjoin A0 ({β} : Set A1)
  dsimp only
  refine Algebra.eq_top_iff.2 ?_
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p =>
      -- Reduce an arbitrary quotient class to polynomial monomials over the successor source.
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          exact S.add_mem hp hq
      | monomial k a =>
          have ha : algebraMap A A1 a ∈ S :=
            freeMonic_succ_source_mem_remainder_root_adjoin n a
          have hβ : β ∈ S := Algebra.subset_adjoin (by simp : β ∈ ({β} : Set A1))
          have hmonomial :
              AdjoinRoot.mk (Polynomial.freeMonic ℤ (n + 1)) (Polynomial.monomial k a) =
                algebraMap A A1 a * β ^ k := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial]
            simp [A, A1, β]
          rw [hmonomial]
          exact S.mul_mem ha (S.pow_mem hβ k)

/-- Helper for Chap10 Example 10 136 8: coefficientwise scalar multiplication on a polynomial
algebra is multiplication by the constant polynomial coming from the algebra map. -/
theorem polynomial_smul_eq_C_algebraMap_mul
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (r : R) (p : Polynomial A) :
    r • p = Polynomial.C (algebraMap R A r) * p := by
  -- Compare coefficients so that scalar multiplication becomes the defining algebra action on
  -- the coefficient ring.
  ext k
  rw [Polynomial.coeff_smul, Polynomial.coeff_C_mul]
  exact Algebra.smul_def r (p.coeff k)

/-- Helper for Chap10 Example 10 136 8: the restricted predecessor action on the normalized
successor target is multiplication by the same constant polynomial as the coefficientwise action. -/
theorem freeMonic_succ_restrict_smul_eq_C_mul (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    let revHom : A0 →+* A0 :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
    let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    letI : Algebra A0 A1 := algA01
    letI : SMul A0 A1 := algA01.toSMul
    letI : Algebra A1 B := algA1B
    let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
    letI : SMul A0 B := modA0B.toSMul
    letI : Module A0 B := modA0B
    ∀ a : A0, ∀ p : B, a • p = Polynomial.C (revHom a) * p := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  let revHom : A0 →+* A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  letI : Algebra A0 A1 := algA01
  letI : SMul A0 A1 := algA01.toSMul
  letI : Algebra A1 B := algA1B
  let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
  letI : SMul A0 B := modA0B.toSMul
  letI : Module A0 B := modA0B
  dsimp only
  intro a p
  have hcoeff :
      RingHom.comp (algebraMap A1 B) (freeMonic_succ_remainder_coeff_algHom n).toRingHom =
        (((Polynomial.CAlgHom (R := ℤ) (A := A0)).comp
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)))).toRingHom) := by
    -- The normalized quotient coefficient map is exactly the reversed coefficient inclusion.
    simpa [A0, A1, B, freeMonic_succ_adjoinRootAlgebra] using
      freeMonic_succ_remainder_coeff_action_eq_rev n
  have hcoeff_apply :
      algebraMap A1 B (algebraMap A0 A1 a) = Polynomial.C (revHom a) := by
    -- Put the ring-hom equality into the scalar-action normal form.
    simpa [algA01, revHom, Polynomial.CAlgHom] using DFunLike.congr_fun hcoeff a
  calc
    a • p = (algebraMap A0 A1 a) • p := by
      rfl
    _ = algebraMap A1 B (algebraMap A0 A1 a) * p := by
      rw [Algebra.smul_def]
    _ = Polynomial.C (revHom a) * p := by
      rw [hcoeff_apply]

/-- Helper for Chap10 Example 10 136 8: adjoining the negated distinguished root gives the same
one-root stage as adjoining the root itself. -/
theorem freeMonic_succ_remainder_neg_root_adjoin_eq_top (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    letI : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    Algebra.adjoin A0 ({-β} : Set A1) = ⊤ := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  letI : Algebra A0 A1 := algA01
  let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
  let Sneg : Subalgebra A0 A1 := Algebra.adjoin A0 ({-β} : Set A1)
  have hβmem : β ∈ Sneg := by
    -- Since `-β` is a generator of `Sneg`, closure under negation puts `β` in the same
    -- subalgebra.
    have hneg : -β ∈ Sneg := Algebra.subset_adjoin (by simp : -β ∈ ({-β} : Set A1))
    have hnegneg : -(-β) = β := neg_neg β
    rw [← hnegneg]
    exact Sneg.neg_mem hneg
  have hle : Algebra.adjoin A0 ({β} : Set A1) ≤ Sneg := by
    -- The adjoin generated by `β` maps into the adjoin generated by `-β`.
    rw [Algebra.adjoin_le_iff]
    intro x hx
    simpa [Set.mem_singleton_iff.mp hx] using hβmem
  rw [freeMonic_succ_remainder_root_adjoin_eq_top n] at hle
  exact top_unique hle

/-- Helper for Chap10 Example 10 136 8: an `R`-linear map commuting with the action of one
algebra generator commutes with the action of every scalar in the algebra it generates. -/
theorem linearMap_of_adjoin_singleton_eq_top_map_smul
    {R S N Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (H : N →ₗ[R] Q) (x : S)
    (hTop : Algebra.adjoin R ({x} : Set S) = ⊤)
    (hx : ∀ n : N, H (x • n) = x • H n) :
    ∀ s : S, ∀ n : N, H (s • n) = s • H n := by
  intro s n
  have hs : s ∈ Algebra.adjoin R ({x} : Set S) := by
    -- The generator hypothesis identifies the adjoin with the whole scalar algebra.
    simpa [hTop]
  -- Induct over the algebra generated by `x`; the algebra-map case is exactly `R`-linearity.
  refine
    (Algebra.adjoin_induction
      (s := ({x} : Set S))
      (p := fun y _ => ∀ n : N, H (y • n) = y • H n)
      ?mem ?algebraMap ?add ?mul hs) n
  · intro y hy n
    have hyx : y = x := by
      simpa using hy
    subst hyx
    exact hx n
  · intro r n
    calc
      H ((algebraMap R S r) • n) = H (r • n) := by
        rw [IsScalarTower.algebraMap_smul S r n]
      _ = r • H n := by
        rw [H.map_smul]
      _ = (algebraMap R S r) • H n := by
        rw [IsScalarTower.algebraMap_smul S r (H n)]
  · intro y z hy hz ihy ihz n
    calc
      H ((y + z) • n) = H (y • n + z • n) := by
        rw [add_smul]
      _ = H (y • n) + H (z • n) := by
        rw [H.map_add]
      _ = y • H n + z • H n := by
        rw [ihy n, ihz n]
      _ = (y + z) • H n := by
        rw [add_smul]
  · intro y z hy hz ihy ihz n
    calc
      H ((y * z) • n) = H (y • z • n) := by
        rw [mul_smul]
      _ = y • H (z • n) := by
        rw [ihy (z • n)]
      _ = y • z • H n := by
        rw [ihz n]
      _ = (y * z) • H n := by
        rw [mul_smul]

/-- Helper for Chap10 Example 10 136 8: an `R`-linear map that commutes with a generator of `S`
upgrades to an `S`-linear map with the same underlying function. -/
noncomputable def linearMap_of_adjoin_singleton_eq_top
    {R S N Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (H : N →ₗ[R] Q) (x : S)
    (hTop : Algebra.adjoin R ({x} : Set S) = ⊤)
    (hx : ∀ n : N, H (x • n) = x • H n) :
    N →ₗ[S] Q :=
  { toFun := H
    map_add' := H.map_add
    map_smul' := linearMap_of_adjoin_singleton_eq_top_map_smul H x hTop hx }

/-- Chap10 Example 10 136 8: the constant-coefficient inclusion is the base-change map
from the predecessor target to the normalized successor target over the one-root stage. -/
theorem freeMonic_succ_exists_coeff_inclusion_isBaseChange (n : ℕ) :
    let A0 := MvPolynomial (Fin n) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial A0
    let algRev : Algebra A0 A0 :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
    let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    letI : Algebra A0 A0 := algRev
    letI : SMul A0 A0 := algRev.toSMul
    letI : Module A0 A0 := algRev.toModule
    letI : Algebra A0 A1 := algA01
    letI : SMul A0 A1 := algA01.toSMul
    letI : Algebra A1 B := algA1B
    let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
    letI : SMul A0 B := modA0B.toSMul
    letI : Module A0 B := modA0B
    letI : IsScalarTower A0 A1 B := IsScalarTower.of_compHom A0 A1 B
    ∃ ε : A0 →ₗ[A0] B, (∀ a : A0, ε a = Polynomial.C a) ∧ IsBaseChange A1 ε := by
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  letI : CommRing A1 := inferInstance
  let B := Polynomial A0
  let algRev : Algebra A0 A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  letI : Algebra A0 A0 := algRev
  letI : SMul A0 A0 := algRev.toSMul
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 A1 := algA01
  letI : SMul A0 A1 := algA01.toSMul
  letI : Algebra A1 B := algA1B
  let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
  letI : SMul A0 B := modA0B.toSMul
  letI : Module A0 B := modA0B
  letI : IsScalarTower A0 A1 B := IsScalarTower.of_compHom A0 A1 B
  dsimp only
  let ε : A0 →ₗ[A0] B :=
    { toFun := Polynomial.C
      map_add' := freeMonic_succ_coeff_inclusionLinear_map_add n
      map_smul' := freeMonic_succ_coeff_inclusion_smul_restrict n }
  refine ⟨ε, ?_, ?_⟩
  · -- The packaged map is definitionally constant-polynomial inclusion.
    intro a
    rfl
  · -- Use the universal-property characterization of base change: every restricted `A₀`-linear
    -- map out of the predecessor target extends uniquely to an `A₁`-linear map from `B`.
    apply IsBaseChange.of_lift_unique ε
    intro Q instQAdd instQA0 instQA1 instTowerQ g
    let β : A1 := AdjoinRoot.root (Polynomial.freeMonic ℤ (n + 1))
    let coeffModuleB : Module A0 B := Polynomial.module
    let coeffSmulB : SMul A0 B := coeffModuleB.toSMul
    letI : SMul A0 B := coeffSmulB
    letI : Module A0 B := coeffModuleB
    let coeffExtension :=
      Polynomial.lsum fun k =>
        (DistribSMul.toLinearMap A0 Q ((-β) ^ k)).comp g
    have hcoeffSmul :
        ∀ a : A0, ∀ p : B,
          coeffExtension (Polynomial.C
              ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) : A0) *
            p) =
            a • coeffExtension p := by
      -- In the coefficientwise polynomial module, scalar multiplication is multiplication by the
      -- same reversed coefficient polynomial, so `Polynomial.lsum` supplies the linearity.
      intro a p
      have hpoly :
          a • p =
            Polynomial.C
              ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) : A0) *
              p := by
        simpa [algRev] using polynomial_smul_eq_C_algebraMap_mul (A := A0) a p
      rw [← hpoly]
      exact coeffExtension.map_smul a p
    have hconstant : ∀ a : A0, coeffExtension (Polynomial.C a : B) = g a := by
      -- Only the degree-zero component of the lsum contributes to a constant polynomial.
      intro a
      simp [coeffExtension]
    have hX :
        algebraMap A1 B (-β) = (Polynomial.X : B) := by
      -- The root acts as `-X`, so the negated root acts as the outer polynomial variable.
      calc
        algebraMap A1 B (-β) = -algebraMap A1 B β := by
          simp
        _ = -(-(Polynomial.X : B)) := by
          rw [freeMonic_succ_adjoinRoot_root_eq_neg_X n]
        _ = (Polynomial.X : B) := by
          rw [neg_neg]
    have hrootAction : ∀ p : B, ((-β) • p : B) = Polynomial.X * p := by
      intro p
      -- Translate the distinguished scalar action on `B` into multiplication by `X`.
      rw [Algebra.smul_def, hX]
    have hcoeffExtension_X :
        ∀ p : B, coeffExtension (Polynomial.X * p) = (-β) • coeffExtension p := by
      -- Prove compatibility with multiplication by `X` on monomials and extend additively.
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simp [mul_add, coeffExtension.map_add, hp, hq, smul_add]
      | monomial k a =>
          calc
            coeffExtension (Polynomial.X * Polynomial.monomial k a) =
                coeffExtension (Polynomial.monomial (k + 1) a : B) := by
              rw [Polynomial.X_mul_monomial]
            _ = ((-β) ^ (k + 1)) • g a := by
              simp [coeffExtension]
            _ = (-β) • (((-β) ^ k) • g a) := by
              rw [pow_succ', smul_smul]
            _ = (-β) • coeffExtension (Polynomial.monomial k a : B) := by
              simp [coeffExtension]
    let coeffFun : B → Q := fun p => coeffExtension p
    have hmapAdd : ∀ p q : B, coeffFun (p + q) = coeffFun p + coeffFun q := by
      -- Additivity comes from the coefficientwise `Polynomial.lsum` before we switch the domain
      -- to the restricted scalar action.
      intro p q
      exact coeffExtension.map_add p q
    letI : SMul A0 B := modA0B.toSMul
    letI : Module A0 B := modA0B
    have hrestrictSmul :
        ∀ a : A0, ∀ p : B,
          a • p =
            Polynomial.C
              ((((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom a) : A0) *
              p := by
      -- Return to the restricted module structure on `B` and use the transport helper.
      simpa using freeMonic_succ_restrict_smul_eq_C_mul n
    have hmapSmul : ∀ a : A0, ∀ p : B, coeffExtension (a • p) = a • coeffExtension p := by
      intro a p
      rw [hrestrictSmul a p]
      exact hcoeffSmul a p
    let restrictedExtension : B →ₗ[A0] Q :=
      { toFun := coeffFun
        map_add' := hmapAdd
        map_smul' := hmapSmul }
    have hrestrictedConstant : ∀ a : A0, restrictedExtension (Polynomial.C a : B) = g a := by
      -- Repackaging the same underlying function preserves its values on constants.
      intro a
      exact hconstant a
    have hrestrictedRoot :
        ∀ p : B, restrictedExtension ((-β) • p) =
          (-β) • restrictedExtension p := by
      -- The root action is multiplication by `X`, and `coeffExtension` was built to shift
      -- coefficients by one power of `-β`.
      intro p
      rw [hrootAction p]
      exact hcoeffExtension_X p
    have hnegTop : Algebra.adjoin A0 ({-β} : Set A1) = ⊤ := by
      -- The one-root stage is generated over the predecessor coefficient ring by `-β`.
      simpa [A0, A1, β] using freeMonic_succ_remainder_neg_root_adjoin_eq_top n
    let lift : B →ₗ[A1] Q :=
      linearMap_of_adjoin_singleton_eq_top restrictedExtension (-β) hnegTop hrestrictedRoot
    refine ⟨lift, ?_, ?_⟩
    · -- The constructed lift extends the original map on constant polynomials.
      ext a
      exact hrestrictedConstant a
    · intro lift' hlift'
      -- Any other `A₁`-linear lift agrees on constants, hence agrees everywhere by the
      -- polynomial-root extensionality lemma.
      apply freeMonic_succ_coeff_inclusion_ext n lift' lift
      intro a
      calc
        lift' (Polynomial.C a : B) =
            (((lift'.restrictScalars A0).comp ε) a) := by
          rfl
        _ = g a := by
          rw [hlift']
        _ = lift (Polynomial.C a : B) := by
          exact (hrestrictedConstant a).symm

/-- Helper for Example 10.136.8: once the normalized successor target is identified with the base
change of the predecessor splitting algebra over `AdjoinRoot (freeMonic)`, the successor free stage
over that one-root extension follows. -/
theorem freeMonic_succ_free_over_adjoinRoot (n : ℕ)
    (hprev :
      letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ)) :
    let A := MvPolynomial (Fin (n + 1)) ℤ
    let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
    let B := Polynomial (MvPolynomial (Fin n) ℤ)
    letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
    letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
    Module.Free A1 B := by
  let A := MvPolynomial (Fin (n + 1)) ℤ
  let A0 := MvPolynomial (Fin n) ℤ
  let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
  let B := Polynomial A0
  letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
  let algRev : Algebra A0 A0 :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let algA01 : Algebra A0 A1 := (freeMonic_succ_remainder_coeff_algHom n).toAlgebra
  let algA1B : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
  letI : Algebra A0 A0 := algRev
  letI : SMul A0 A0 := algRev.toSMul
  letI : Module A0 A0 := algRev.toModule
  letI : Algebra A0 A1 := algA01
  letI : SMul A0 A1 := algA01.toSMul
  letI : Algebra A1 B := algA1B
  let modA0B : Module A0 B := Module.compHom B (algebraMap A0 A1)
  letI : SMul A0 B := modA0B.toSMul
  letI : Module A0 B := modA0B
  letI : IsScalarTower A0 A1 B := IsScalarTower.of_compHom A0 A1 B
  have hprev' : Module.Free A0 A0 := by
    -- Re-express the induction hypothesis in the predecessor coefficient-ring notation.
    simpa [A0, algRev] using hprev
  obtain ⟨ε, _hε, hbase⟩ := freeMonic_succ_exists_coeff_inclusion_isBaseChange n
  letI : Module.Free A0 A0 := hprev'
  -- Route correction: freeness is now delegated to the theorem-local base-change package for
  -- constant inclusion, then transported by the standard `IsBaseChange.free` theorem.
  exact IsBaseChange.free (R := A0) (S := A1) (V := A0) (W := B) (ε := ε) hbase

/-- Helper for Example 10.136.8: if two source algebra structures on the same target differ by a
domain ring equivalence, then finite generation and freeness transport across that equivalence. -/
theorem finite_free_of_domain_equiv
    {A₁ A₂ B : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring B]
    (alg₁ : Algebra A₁ B) (alg₂ : Algebra A₂ B) (e : A₁ ≃+* A₂)
    (hcompat :
      RingHom.comp (@algebraMap A₂ B _ _ alg₂) e.toRingHom =
        @algebraMap A₁ B _ _ alg₁)
    (hfinite : @Module.Finite A₁ B _ _ alg₁.toModule)
    (hfree : @Module.Free A₁ B _ _ alg₁.toModule) :
    @Module.Finite A₂ B _ _ alg₂.toModule ∧ @Module.Free A₂ B _ _ alg₂.toModule := by
  letI : Algebra A₁ B := alg₁
  letI : Algebra A₂ B := alg₂
  letI : Module.Finite A₁ B := hfinite
  letI : Module.Free A₁ B := hfree
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  -- Finite generation is invariant under compatible ring equivalences on source and target.
  have hfinite' : Module.Finite A₂ B := by
    have hcompat' :
        RingHom.comp (algebraMap A₂ B) e.toRingHom =
          RingHom.comp (RingEquiv.refl B) (algebraMap A₁ B) := by
      simpa using hcompat
    exact
      @Module.Finite.of_equiv_equiv A₁ B A₂ B _ _ _ _ alg₁ alg₂ e (RingEquiv.refl B) hcompat'
        hfinite
  -- The identity map on `B` becomes semilinear once the two source actions are matched by `e`.
  have hsemilinear : B ≃ₛₗ[e.toRingHom] B := by
    -- Both semilinear maps are literally the identity on the underlying additive group.
    refine LinearEquiv.ofLinear ?_ ?_ ?_ ?_
    · refine
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }
      intro a b
      have happly := DFunLike.congr_fun hcompat a
      simpa [Algebra.smul_def, RingHom.comp_apply] using
        congrArg (fun x : B ↦ x * b) happly.symm
    · refine
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }
      intro a b
      have happly := DFunLike.congr_fun hcompat (e.symm a)
      simpa [Algebra.smul_def, RingHom.comp_apply] using
        congrArg (fun x : B ↦ x * b) happly
    · ext b
      rfl
    · ext b
      rfl
  -- Freeness transports along semilinear equivalences.
  have hfree' : Module.Free A₂ B := Module.Free.of_equiv hsemilinear
  exact ⟨hfinite', hfree'⟩

/-- Helper for Example 10.136.8: every target root variable is integral over the reversed
elementary-symmetric coefficient ring because the universal monic polynomial splits as a product of
linear factors. -/
theorem isIntegral_X_of_elementary_symmetric_ring_hom_rev (n : ℕ) (i : Fin n) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    IsIntegral (MvPolynomial (Fin n) ℤ) (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let s : Multiset A := Finset.univ.val.map fun j : Fin n => -(MvPolynomial.X j : A)
  have hsplitMap :
      (Polynomial.freeMonic ℤ n).map
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) =
        (s.map fun x : A =>
          (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
    -- Rewrite the source split polynomial in the `X - C r` normal form required by the
    -- standard root-to-integrality API.
    calc
      (Polynomial.freeMonic ℤ n).map
          (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom)
          =
            ∏ j : Fin n,
              ((Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)) +
                Polynomial.C (MvPolynomial.X j : A)) := by
              exact freeMonic_map_elementary_symmetric_ring_hom_rev n
      _ = (s.map fun x : A =>
            (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
            rw [Finset.prod_eq_multiset_prod]
            dsimp [s]
            rw [Multiset.map_map]
            refine congrArg Multiset.prod ?_
            refine Multiset.map_congr rfl ?_
            intro j hj
            change
              ((Polynomial.X : Polynomial (MvPolynomial (Fin n) ℤ)) +
                  Polynomial.C (MvPolynomial.X j : A)) =
                (Polynomial.X - Polynomial.C (-(MvPolynomial.X j : A)) :
                  Polynomial (MvPolynomial (Fin n) ℤ))
            rw [sub_eq_add_neg, Polynomial.C_neg, neg_neg]
  have hsplit :
      (Polynomial.freeMonic ℤ n).mapAlg A A =
        (s.map fun x : A =>
          (Polynomial.X - Polynomial.C x : Polynomial (MvPolynomial (Fin n) ℤ))).prod := by
    simpa [Polynomial.mapAlg_eq_map] using hsplitMap
  have hroot :
      Polynomial.aeval (-(MvPolynomial.X i : A)) (Polynomial.freeMonic ℤ n) = 0 := by
    -- The chosen variable is one of the displayed roots of the split universal polynomial.
    exact Polynomial.aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C
      (R := A) (A := A) (p := Polynomial.freeMonic ℤ n) (s := s)
      (x := -(MvPolynomial.X i : A)) (by simp [s]) hsplit
  have hintNeg' := 
    -- A root of a monic polynomial is integral over the coefficient ring.
    isIntegral_leadingCoeff_smul (R := A) (S := A)
      (p := Polynomial.freeMonic ℤ n) (x := -(MvPolynomial.X i : A)) hroot
  have hlead :
      (Polynomial.freeMonic ℤ n).leadingCoeff • (-(MvPolynomial.X i : A)) =
        -(MvPolynomial.X i : A) := by
    simp [Algebra.smul_def, Polynomial.monic_freeMonic]
  have hintNeg : IsIntegral A (-(MvPolynomial.X i : A)) := hlead ▸ hintNeg'
  -- Negating an integral element preserves integrality, so the variable itself is integral.
  exact IsIntegral.of_neg hintNeg

/-- Helper for Example 10.136.8: for the reversed algebra structure, adjoining the target root
variables already recovers the whole target polynomial ring. -/
  theorem adjoin_root_variables_eq_top_of_elementary_symmetric_ring_hom_rev (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Algebra.adjoin (MvPolynomial (Fin n) ℤ)
      (Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)) = ⊤ := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let S : Subalgebra A A := Algebra.adjoin A (Set.range (MvPolynomial.X : Fin n → A))
  refine top_unique ?_
  intro p hpTop
  clear hpTop
  -- The target ring is generated by integer coefficients and the root variables.
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa [S] using S.algebraMap_mem (MvPolynomial.C r : A)
  | add p q hp hq =>
      exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (by exact ⟨i, rfl⟩))

/-- Helper for Example 10.136.8: finite generation follows because the target polynomial ring is
generated by finitely many integral root variables over the reversed coefficient ring. -/
theorem elementary_symmetric_ring_hom_rev_finite (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  let A := MvPolynomial (Fin n) ℤ
  letI : Algebra A A := (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let s : Set A := Set.range (MvPolynomial.X : Fin n → A)
  have hsIntegral : ∀ x ∈ s, IsIntegral A x := by
    -- Each generator lies among the explicit roots of the universal monic polynomial.
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact isIntegral_X_of_elementary_symmetric_ring_hom_rev n i
  have hfiniteAdjoin : Module.Finite A (Algebra.adjoin A s) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (hf := Set.toFinite s) hsIntegral
  have hsTop : Algebra.adjoin A s = ⊤ := by
    simpa [s] using adjoin_root_variables_eq_top_of_elementary_symmetric_ring_hom_rev n
  let e : Algebra.adjoin A s ≃ₐ[A] A := by
    -- `MvPolynomial` is generated by its variables, so the adjoin is the top subalgebra.
    exact hsTop ▸ (Subalgebra.topEquiv (R := A) (A := A))
  letI : Module.Finite A (Algebra.adjoin A s) := hfiniteAdjoin
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Example 10.136.8: in zero variables, the reversed elementary-symmetric map is the
identity ring endomorphism on `ℤ`. -/
theorem elementary_symmetric_ring_hom_rev_zero_eq_id :
    (((elementary_symmetric_ring_hom 0).comp (rename Fin.revPerm)).toRingHom) =
      RingHom.id (MvPolynomial (Fin 0) ℤ) := by
  apply RingHom.ext
  intro p
  -- Every polynomial in zero variables is constant, so it suffices to check constants.
  have hp : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := MvPolynomial.eq_C_of_isEmpty p
  rw [hp]
  simp [elementary_symmetric_ring_hom]

/-- Helper for Example 10.136.8: after reversing the source coefficient variables, the
elementary-symmetric map is finite free. -/
theorem elementary_symmetric_ring_hom_rev_finite_free (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) ∧
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  induction n with
  | zero =>
      refine ⟨elementary_symmetric_ring_hom_rev_finite 0, ?_⟩
      let A := MvPolynomial (Fin 0) ℤ
      let algId : Algebra A A := (RingHom.id A).toAlgebra
      let algRev : Algebra A A :=
        (((elementary_symmetric_ring_hom 0).comp (rename Fin.revPerm)).toAlgebra)
      -- The zero-variable reversed source action is the identity action.
      have hcompat :
          RingHom.comp (@algebraMap A A _ _ algRev) (RingEquiv.refl A).toRingHom =
            @algebraMap A A _ _ algId := by
        simpa [algId, algRev] using elementary_symmetric_ring_hom_rev_zero_eq_id
      have hfiniteId : @Module.Finite A A _ _ algId.toModule := by
        letI : Algebra A A := algId
        simpa using (Module.Finite.self A)
      have hfreeId : @Module.Free A A _ _ algId.toModule := by
        letI : Algebra A A := algId
        simpa using (Module.Free.self (R := A))
      simpa [A, algRev] using
        (finite_free_of_domain_equiv algId algRev (RingEquiv.refl A) hcompat
          hfiniteId hfreeId).2
  | succ n ih =>
      refine ⟨elementary_symmetric_ring_hom_rev_finite (n + 1), ?_⟩
      let A := MvPolynomial (Fin (n + 1)) ℤ
      let A1 := AdjoinRoot (Polynomial.freeMonic ℤ (n + 1))
      let B := Polynomial (MvPolynomial (Fin n) ℤ)
      letI : Algebra A B := freeMonic_succ_normalizedAlgebra n
      letI : Algebra A1 B := freeMonic_succ_adjoinRootAlgebra n
      have hA1 : Module.Free A A1 := by
        -- The first stage of the successor tower is the standard free one-root extension.
        simpa [A1] using (Polynomial.monic_freeMonic ℤ (n + 1)).free_adjoinRoot
      have hB : Module.Free A1 B := by
        -- The remaining successor-stage freeness is exactly the base-change comparison blocker.
        simpa [A, A1, B] using freeMonic_succ_free_over_adjoinRoot n ih.2
      have hNormalized : Module.Free A B := by
        -- Compose the one-root free stage with the remainder-stage free tower.
        letI : Module.Free A A1 := hA1
        letI : Module.Free A1 B := hB
        exact Module.Free.trans (R := A) (S := A1) (M := B)
      letI : Algebra A (MvPolynomial (Fin (n + 1)) ℤ) :=
        (((elementary_symmetric_ring_hom (n + 1)).comp (rename Fin.revPerm)).toAlgebra)
      -- Transport freeness back across the normalization equivalence `finSuccEquiv`.
      exact Module.Free.of_equiv (freeMonic_succ_normalized_target_algEquiv n).symm.toLinearEquiv

/-- Helper for Example 10.136.8: after restricting scalars along a theorem-local self-action on
`A`, `Polynomial.toFinsupp` still intertwines the induced coefficientwise scalar actions. -/
theorem polynomial_toFinsupp_smul_restrictScalars (A : Type*) [CommSemiring A]
    (alg : Algebra A A) :
    letI : Module A A := alg.toModule
    ∀ a : A, ∀ p : Polynomial A, Polynomial.toFinsupp (a • p) = a • Polynomial.toFinsupp p := by
  letI : Module A A := alg.toModule
  -- Compare both sides coefficientwise: both scalar actions multiply each coefficient by the
  -- theorem-local image of `a` in `A`.
  intro a p
  ext n
  simp [Polynomial.toFinsupp_apply]

/-- Helper for Example 10.136.8: once the predecessor target ring is free over the reversed
coefficient algebra, the coefficientwise polynomial extension remains free over that same source
algebra. -/
theorem polynomial_rev_free_of_rev_free (n : ℕ) :
    let A := MvPolynomial (Fin n) ℤ
    letI : Algebra A A :=
      (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
    Module.Free A (Polynomial A) := by
  let A := MvPolynomial (Fin n) ℤ
  let algRev : Algebra A A :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  letI : Algebra A A := algRev
  letI : Module A A := algRev.toModule
  letI : Module.Free A A := (elementary_symmetric_ring_hom_rev_finite_free n).2
  letI : Module.Free A (ℕ →₀ A) := Module.Free.finsupp (ι := ℕ) (R := A) (M := A)
  let e : Polynomial A ≃ₗ[A] (ℕ →₀ A) :=
    { __ := (Polynomial.toFinsuppIso A).toAddEquiv
      map_smul' := polynomial_toFinsupp_smul_restrictScalars A algRev }
  -- Transport the free finitely-supported-function basis across the theorem-local linear
  -- equivalence from the new helper.
  simpa [algRev] using
    (Module.Free.of_equiv' (P := ℕ →₀ A)
      (inferInstance : Module.Free A (ℕ →₀ A))
      e.symm)

-- Proof sketch: identify `elementary_symmetric_ring_hom n` with the canonical fundamental-theorem
-- owner for symmetric polynomials and use the standard monomial basis to obtain finite generation
-- and freeness over `ℤ[a₁, \ldots, aₙ]`.
/-- Consequence for Chap10 Example 10 136 8: the elementary-symmetric map
`ℤ[a₁, \ldots, aₙ] → ℤ[α₁, \ldots, αₙ]` is finite free. -/
@[stacks 00SR]
theorem elementary_symmetric_ring_hom_finite_free (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
      (elementary_symmetric_ring_hom n).toAlgebra
    Module.Finite (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) ∧
      Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := by
  let revAlg :
      Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toAlgebra)
  let alg :
      Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  let revEquiv :
      MvPolynomial (Fin n) ℤ ≃+* MvPolynomial (Fin n) ℤ :=
    (renameEquiv ℤ (Fin.revPerm : Equiv.Perm (Fin n))).toRingEquiv
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) := revAlg
  have hrev := elementary_symmetric_ring_hom_rev_finite_free n
  -- Route correction: once the reversed theorem is available, the public theorem is only transport
  -- back along the domain automorphism `rename Fin.rev`.
  have hcompat_ring :
      RingHom.comp (elementary_symmetric_ring_hom n).toRingHom revEquiv.toRingHom =
        (((elementary_symmetric_ring_hom n).comp (rename Fin.revPerm)).toRingHom) := by
    rfl
  have hcompat :
      RingHom.comp
          (@algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) _ _ alg)
          revEquiv.toRingHom =
        @algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) _ _ revAlg := by
    simpa [revAlg, alg] using hcompat_ring
  exact finite_free_of_domain_equiv revAlg alg revEquiv hcompat hrev.1 hrev.2

-- Proof sketch: the finite-free statement gives finite generation of the target polynomial ring as
-- a module over the source polynomial ring for the algebra structure induced by
-- `elementary_symmetric_ring_hom n`; this is exactly the ring-hom notion of finiteness.
/-- The elementary-symmetric map is finite. -/
theorem elementary_symmetric_ring_hom_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).Finite := by
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  -- The finite-free theorem already provides the module-finite half of the desired conclusion.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.finite_algebraMap).mpr (elementary_symmetric_ring_hom_finite_free n).1

-- Proof sketch: every finite ring map is quasi-finite in mathlib, so this follows formally from
-- `elementary_symmetric_ring_hom_finite n`.
/-- The elementary-symmetric map is quasi-finite, equivalently its fibers are finite. -/
theorem elementary_symmetric_ring_hom_quasi_finite (n : ℕ) :
    (elementary_symmetric_ring_hom n).QuasiFinite := by
  -- Every finite ring map is quasi-finite.
  exact RingHom.QuasiFinite.of_finite (elementary_symmetric_ring_hom_finite n)

-- Proof sketch: a finite free module is flat, and because its rank is positive the induced map on
-- spectra is surjective; equivalently, the ring map is faithfully flat.
/-- The elementary-symmetric map is faithfully flat. -/
theorem elementary_symmetric_ring_hom_faithfully_flat (n : ℕ) :
    (elementary_symmetric_ring_hom n).FaithfullyFlat := by
  letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom n).toAlgebra
  letI : Module.Free (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ) :=
    (elementary_symmetric_ring_hom_finite_free n).2
  -- A nontrivial free module is faithfully flat, so the ring-hom statement is the algebra-map view.
  simpa [RingHom.algebraMap_toAlgebra] using
    (RingHom.faithfullyFlat_algebraMap_iff).mpr
      (inferInstance :
        Module.FaithfullyFlat (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℤ))
