import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function

universe u

section

variable {ι : Type u} [Fintype ι]

/-- Helper for Proposition 1.1.104: solvability of the integer congruence is equivalent to a root
of the coefficientwise-reduced polynomial in `ZMod`. -/
lemma exists_int_root_mod_iff_exists_zmod_root (P : Polynomial ℤ) (m : ℕ) :
    (∃ x : ℤ, P.eval x ≡ 0 [ZMOD (m : ℤ)]) ↔
      ∃ z : ZMod m, Polynomial.eval z (P.map (Int.castRingHom (ZMod m))) = 0 := by
  -- Rewrite `ZMod` roots using integer representatives so the congruence witness stays the same.
  rw [ZMod.exists]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [Polynomial.eval_intCast_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (Int.modEq_zero_iff_dvd.mp hx)
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [Int.modEq_zero_iff_dvd]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 <|
      by simpa [Polynomial.eval_intCast_map] using hx

/-- Helper for Proposition 1.1.104: the Chinese remainder equivalence transports polynomial
evaluation modulo the product to coordinatewise evaluation modulo each factor. -/
lemma prodEquivPi_polynomial_eval (n : ι → ℕ) (P : Polynomial ℤ)
    (hcop : Pairwise (Nat.Coprime on n)) (y : ZMod (∏ i, n i)) :
    ZMod.prodEquivPi n hcop
      (Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ i, n i))))) =
      fun i ↦
        Polynomial.eval ((ZMod.prodEquivPi n hcop y) i)
          (P.map (Int.castRingHom (ZMod (n i)))) := by
  -- Evaluate in the product ring and then project to each coordinate.
  ext i
  let e : ZMod (∏ i, n i) →+* (j : ι) → ZMod (n j) :=
    (ZMod.prodEquivPi n hcop).toRingHom
  let φ : ((j : ι) → ZMod (n j)) →+* ZMod (n i) :=
    Pi.evalRingHom (fun j ↦ ZMod (n j)) i
  have hcomp :
      (φ.comp e).comp (Int.castRingHom (ZMod (∏ j, n j))) =
        Int.castRingHom (ZMod (n i)) := by
    -- Projecting the coefficient ring hom is just the usual cast to the `i`th factor.
    ext x
    simp [e, φ]
  have hh :=
    Polynomial.hom_eval₂ (p := P)
      (f := Int.castRingHom (ZMod (∏ j, n j))) (g := φ.comp e) (x := y)
  change φ (e (Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ j, n j)))))) = _
  rw [Polynomial.eval_map]
  rw [Polynomial.eval_map]
  simpa [hcomp, e, φ] using hh

/-- Helper for Proposition 1.1.104: a reduced polynomial has a root modulo the product exactly
when it has a root modulo each pairwise-coprime factor. -/
lemma exists_zmod_root_product_iff_forall_exists_zmod_root_factor
    (n : ι → ℕ) (P : Polynomial ℤ) (hcop : Pairwise (Nat.Coprime on n)) :
    (∃ y : ZMod (∏ i, n i),
      Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ i, n i)))) = 0) ↔
      ∀ i, ∃ z : ZMod (n i),
        Polynomial.eval z (P.map (Int.castRingHom (ZMod (n i)))) = 0 := by
  constructor
  · rintro ⟨y, hy⟩ i
    -- A root modulo the product projects to a root modulo every factor.
    refine ⟨(ZMod.prodEquivPi n hcop y) i, ?_⟩
    have htransport := congrFun (prodEquivPi_polynomial_eval n P hcop y) i
    simpa [hy] using htransport.symm
  · intro h
    classical
    -- Assemble the chosen factor roots into one point of the product ring.
    choose z hz using h
    let y : ZMod (∏ i, n i) := (ZMod.prodEquivPi n hcop).symm z
    refine ⟨y, ?_⟩
    apply (ZMod.prodEquivPi n hcop).injective
    ext i
    have htransport := congrFun (prodEquivPi_polynomial_eval n P hcop y) i
    simpa [y, hz i] using htransport

/-- Proposition 1.1.104: for a finite family of pairwise coprime natural moduli `n i`, an integer
polynomial congruence `P(X) ≡ 0` modulo the product `∏ i, n i` is solvable if and only if each
factor congruence `P(X) ≡ 0 [ZMOD n i]` is solvable. -/
-- Proof sketch: the forward implication reduces a solution modulo the product to each factor
-- modulus by divisibility. For the reverse implication, transport the chosen roots modulo each
-- `n i` across the canonical Chinese remainder equivalence `ZMod.prodEquivPi`, obtaining one
-- residue class modulo `∏ i, n i`, and then lift it to an integer representative.
theorem polynomial_congruence_solvable_iff_forall_solvable_factor
    (n : ι → ℕ) (P : Polynomial ℤ) (hcop : Pairwise (Nat.Coprime on n)) :
    (∃ x : ℤ, P.eval x ≡ 0 [ZMOD ∏ i, n i]) ↔ ∀ i, ∃ x : ℤ, P.eval x ≡ 0 [ZMOD n i] := by
  constructor
  · rintro ⟨x, hx⟩ i
    -- Any solution modulo the product remains a solution modulo each divisor modulus.
    refine ⟨x, ?_⟩
    exact Int.ModEq.of_dvd
      (Finset.dvd_prod_of_mem (fun j ↦ (n j : ℤ)) (Finset.mem_univ i)) hx
  · intro h
    -- Route correction: use CRT on `ZMod`, then translate the resulting root back to `ℤ`.
    have hfactor :
        ∀ i, ∃ z : ZMod (n i),
          Polynomial.eval z (P.map (Int.castRingHom (ZMod (n i)))) = 0 := by
      intro i
      exact (exists_int_root_mod_iff_exists_zmod_root P (n i)).mp <|
        by simpa using h i
    have hprod :
        ∃ z : ZMod (∏ i, n i),
          Polynomial.eval z (P.map (Int.castRingHom (ZMod (∏ i, n i)))) = 0 :=
      (exists_zmod_root_product_iff_forall_exists_zmod_root_factor n P hcop).2 hfactor
    simpa using (exists_int_root_mod_iff_exists_zmod_root P (∏ i, n i)).mpr hprod

end
