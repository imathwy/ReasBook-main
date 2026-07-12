import Mathlib
import StacksProject_2024.Chap10.Lemma_10_19_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open scoped Polynomial
open Polynomial

variable {A : Type u} [CommRing A] (I I' : Ideal A)
variable [HenselianRing A I] [HenselianRing A I']

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, compared through the quotient pair
  criterion for a subideal `I ≤ J`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `henselianRing_iff_henselianRing_and_quotient_henselianRing`,
  `Ideal.map_sup`;
- best owner abstraction: the public conclusion is again the canonical owner
  `HenselianRing A (I + I')`; the quotient-pair comparison from Lemma `15.11.9` and the quotient
  transport from Lemma `15.11.8` are derived bridge API, not new local owners;
- primitive data: the ideals `I`, `I'`, the two henselian owner instances on `A`, and the
  canonical quotient map `Ideal.Quotient.mk I : A →+* A ⧸ I`;
- derived API: the quotient henselian structure on `A ⧸ I` coming from `I'`, and the ideal-map
  identity `map (Ideal.Quotient.mk I) (I + I') = map (Ideal.Quotient.mk I) I'`.

Source/core/bridge triage:
- `source-facing`: the henselianity of the sum pair `(A, I + I')`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: Lemma `15.11.9` for the quotient criterion and Lemma `15.11.8` for passing
  henselianity to quotient rings.
-/

-- Proof sketch: write `f(a₀)` as `x + y` with `x ∈ I` and `y ∈ I'`, and first apply henselianity
-- for `(A, I')` to the shifted polynomial `f - x`, obtaining a point `a₁ ≡ a₀ mod I'` with
-- `f(a₁) = x ∈ I`. The derivative remains invertible modulo `I` because its image modulo
-- `I + I'` was invertible and `I' / I` lies in the Jacobson radical of `A / I`. A second Hensel
-- lift for `(A, I)` then produces an actual root congruent to `a₁` modulo `I`, hence to `a₀`
-- modulo `I + I'`.
/-- Helper for Lemma 15.11.10: units lift through quotients by ideals contained in the Jacobson
radical. -/
private theorem isUnit_of_isUnit_quotient_of_le_jacobson
    {R : Type*} [CommRing R] (J : Ideal R) {x : R}
    (hx : IsUnit ((Ideal.Quotient.mk J) x)) (hJ : J ≤ Ring.jacobson R) :
    IsUnit x := by
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    isLocalHom_of_le_jacobson_bot J (by simpa [Ideal.jacobson_bot] using hJ)
  exact (isUnit_map_iff (Ideal.Quotient.mk J) x).mp hx

/-- Helper for Lemma 15.11.10: a surjective image of a Jacobson ideal is again Jacobson. -/
private theorem ideal_map_le_ring_jacobson_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (J : Ideal R) (hJ : J ≤ Ring.jacobson R) :
    Ideal.map f J ≤ Ring.jacobson S := by
  -- Check the Jacobson criterion on `1 + y` after pulling `y` back along surjectivity.
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro y hy
  rcases (Ideal.mem_map_iff_of_surjective f hf).mp hy with ⟨x, hx, rfl⟩
  have hxUnit : IsUnit (1 + x) := by
    exact (ideal_le_ring_jacobson_iff_isUnit_one_add J).mp hJ x hx
  simpa using IsUnit.map f hxUnit

/-- Helper for Lemma 15.11.10: polynomial evaluation respects congruence modulo an ideal. -/
private theorem eval_sub_mem_of_sub_mem_ideal
    {R : Type*} [CommRing R] (J : Ideal R) (p : Polynomial R) {x y : R}
    (hxy : x - y ∈ J) :
    p.eval x - p.eval y ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hq : (Ideal.Quotient.mk J) x = (Ideal.Quotient.mk J) y := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hxy
  calc
    (Ideal.Quotient.mk J) (p.eval x - p.eval y)
        = Polynomial.eval₂ (Ideal.Quotient.mk J) ((Ideal.Quotient.mk J) x) p -
            Polynomial.eval₂ (Ideal.Quotient.mk J) ((Ideal.Quotient.mk J) y) p := by
            rw [map_sub, ← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply]
    _ = 0 := by simpa [hq]

/-- Lemma 15.11.10: if `(A, I)` and `(A, I')` are henselian pairs, then the
pair `(A, I + I')` is henselian. -/
instance ideal_add_henselianRing : HenselianRing A (I + I') := by
  by_cases hA : Subsingleton A
  · letI := hA
    refine ⟨?_, ?_⟩
    · simp
    · intro f hf a0 ha0 hderiv
      refine ⟨a0, ?_, ?_⟩
      · exact Polynomial.IsRoot.def.mpr (Subsingleton.elim _ _)
      · simp
  · letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    refine ⟨?_, ?_⟩
    · -- Proof comment: both ideals already lie in the Jacobson radical, so their sum does as well.
      simpa [Ideal.add_eq_sup] using
        sup_le (HenselianRing.jac (R := A) (I := I)) (HenselianRing.jac (R := A) (I := I'))
    · intro f hf a0 ha0 hderiv
      rcases Submodule.mem_sup.mp ha0 with ⟨x, hx, y, hy, hxy⟩
      let g : A[X] := f - C x
      have hsum_jac : I + I' ≤ Ring.jacobson A := by
        simpa [Ideal.add_eq_sup, Ideal.jacobson_bot] using
          sup_le (HenselianRing.jac (R := A) (I := I)) (HenselianRing.jac (R := A) (I := I'))
      have hsum_ne_top : I + I' ≠ ⊤ := by
        intro htop
        have htop_jac : Ring.jacobson A = ⊤ := by
          exact top_le_iff.mp (htop ▸ hsum_jac)
        exact (Ring.jacobson_lt_top A).ne htop_jac
      letI : Nontrivial (A ⧸ (I + I')) := (Ideal.Quotient.nontrivial_iff).2 hsum_ne_top
      have hnatDegree_f : f.natDegree ≠ 0 := by
        intro hdeg
        have hf_one : f = 1 := hf.natDegree_eq_zero.mp hdeg
        simpa [hf_one] using hderiv.ne_zero
      have hdegree_f : 0 < f.degree := by
        simpa [Polynomial.degree_eq_natDegree hf.ne_zero] using Nat.pos_of_ne_zero hnatDegree_f
      have hdegree_C : (C x : A[X]).degree < f.degree := by
        exact lt_of_le_of_lt Polynomial.degree_C_le hdegree_f
      have hg_monic : g.Monic := by
        simpa [g] using hf.sub_of_left hdegree_C
      have hg_eval : g.eval a0 ∈ I' := by
        -- Proof comment: shifting by the `I`-part of `f(a₀)` leaves the `I'`-part.
        rw [show g.eval a0 = f.eval a0 - x by simp [g]]
        rw [← hxy, add_sub_cancel_left]
        simpa using hy
      let qI' : A →+* A ⧸ I' := Ideal.Quotient.mk I'
      let KI' : Ideal (A ⧸ I') := Ideal.map qI' I
      have hI_jac : I ≤ Ring.jacobson A := by
        simpa [Ideal.jacobson_bot] using
          (show I ≤ Ideal.jacobson (⊥ : Ideal A) from HenselianRing.jac (R := A) (I := I))
      have hKI'_jac : KI' ≤ Ring.jacobson (A ⧸ I') := by
        -- Proof comment: Jacobson containment survives the surjective quotient map to `A ⧸ I'`.
        exact ideal_map_le_ring_jacobson_of_surjective qI' Ideal.Quotient.mk_surjective I hI_jac
      have hderivDoubleI' :
          IsUnit (DoubleQuot.quotQuotMk I' I (g.derivative.eval a0)) := by
        -- Proof comment: pull the unit back across the double-quotient equivalence.
        let e := DoubleQuot.quotQuotEquivQuotSup I' I
        have hMapped :
            IsUnit (e (DoubleQuot.quotQuotMk I' I (g.derivative.eval a0))) := by
          rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
          rw [sup_comm]
          simpa [g, Ideal.add_eq_sup] using hderiv
        simpa [e] using IsUnit.map e.symm.toRingHom hMapped
      have hderivKI' :
          IsUnit ((Ideal.Quotient.mk KI') ((Ideal.Quotient.mk I') (g.derivative.eval a0))) := by
        simpa [KI', qI', DoubleQuot.quotQuotMk] using hderivDoubleI'
      have hderivI' :
          IsUnit ((Ideal.Quotient.mk I') (g.derivative.eval a0)) := by
        exact isUnit_of_isUnit_quotient_of_le_jacobson KI' hderivKI' hKI'_jac
      obtain ⟨a1, ha1_root, ha1_mem⟩ :=
        HenselianRing.is_henselian (R := A) (I := I') g hg_monic a0 hg_eval hderivI'
      have hfa1 : f.eval a1 ∈ I := by
        -- Proof comment: the first lift solves `g = f - x`, so `f(a₁) = x ∈ I`.
        have hg_zero : g.eval a1 = 0 := ha1_root
        have hfa1_eq : f.eval a1 = x := by
          calc
            f.eval a1 = g.eval a1 + x := by simp [g]
            _ = x := by simpa [hg_zero]
        simpa [hfa1_eq] using hx
      let qI : A →+* A ⧸ I := Ideal.Quotient.mk I
      let KI : Ideal (A ⧸ I) := Ideal.map qI I'
      have hI'_jac : I' ≤ Ring.jacobson A := by
        simpa [Ideal.jacobson_bot] using
          (show I' ≤ Ideal.jacobson (⊥ : Ideal A) from HenselianRing.jac (R := A) (I := I'))
      have hKI_jac : KI ≤ Ring.jacobson (A ⧸ I) := by
        -- Proof comment: the same Jacobson-image argument works after quotienting by `I`.
        exact ideal_map_le_ring_jacobson_of_surjective qI Ideal.Quotient.mk_surjective I' hI'_jac
      have hderiv_congr :
          f.derivative.eval a1 - f.derivative.eval a0 ∈ I' := by
        exact eval_sub_mem_of_sub_mem_ideal I' f.derivative ha1_mem
      have hderivSumEq :
          (Ideal.Quotient.mk (I + I')) (f.derivative.eval a1) =
            (Ideal.Quotient.mk (I + I')) (f.derivative.eval a0) := by
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact Submodule.mem_sup.mpr ⟨0, Ideal.zero_mem I, _, hderiv_congr, by simp⟩
      have hderivSumA1 :
          IsUnit ((Ideal.Quotient.mk (I + I')) (f.derivative.eval a1)) := by
        rw [hderivSumEq]
        exact hderiv
      have hderivDoubleI :
          IsUnit (DoubleQuot.quotQuotMk I I' (f.derivative.eval a1)) := by
        -- Proof comment: again pull the derivative unit back through the quotient equivalence.
        let e := DoubleQuot.quotQuotEquivQuotSup I I'
        have hMapped :
            IsUnit (e (DoubleQuot.quotQuotMk I I' (f.derivative.eval a1))) := by
          rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
          simpa [Ideal.add_eq_sup] using hderivSumA1
        simpa [e] using IsUnit.map e.symm.toRingHom hMapped
      have hderivKI :
          IsUnit ((Ideal.Quotient.mk KI) ((Ideal.Quotient.mk I) (f.derivative.eval a1))) := by
        simpa [KI, qI, DoubleQuot.quotQuotMk] using hderivDoubleI
      have hderivI :
          IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval a1)) := by
        exact isUnit_of_isUnit_quotient_of_le_jacobson KI hderivKI hKI_jac
      obtain ⟨a, ha_root, ha_mem⟩ :=
        HenselianRing.is_henselian (R := A) (I := I) f hf a1 hfa1 hderivI
      refine ⟨a, ha_root, ?_⟩
      -- Proof comment: the two successive congruences combine to a congruence modulo `I + I'`.
      have hsum :
          (a - a1) + (a1 - a0) ∈ I + I' := by
        exact Submodule.mem_sup.mpr ⟨a - a1, ha_mem, a1 - a0, ha1_mem, rfl⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

end
