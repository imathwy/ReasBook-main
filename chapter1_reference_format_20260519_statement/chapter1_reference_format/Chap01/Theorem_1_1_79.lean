import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Theorem 1.1.79: reduction modulo `p` keeps the polynomial nonzero when the leading
coefficient is not divisible by `p`. -/
lemma map_ne_zero_of_leadingCoeff_not_dvd (p : ℕ) [Fact p.Prime] (P : Polynomial ℤ)
    (hlead : ¬ (p : ℤ) ∣ P.leadingCoeff) :
    P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  -- The leading coefficient stays nonzero after reduction modulo `p`.
  have hlead_map : (Int.castRingHom (ZMod p)) P.leadingCoeff ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hlead
  have hcoeff : (P.map (Int.castRingHom (ZMod p))).leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead_map]
    exact hlead_map
  -- A polynomial with nonzero leading coefficient cannot be the zero polynomial.
  intro hP
  have hzero : (P.map (Int.castRingHom (ZMod p))).leadingCoeff = 0 := by
    simp [hP]
  exact hcoeff hzero

/-- Helper for Theorem 1.1.79: every canonical representative solving the congruence gives a root
of the reduction of `P` modulo `p`. -/
lemma mem_rootSet_of_eval_modEq_zero (p : ℕ) [Fact p.Prime] (P : Polynomial ℤ) {x : ℕ}
    (hx : x ∈ (Finset.range p).filter fun n : ℕ ↦ P.eval (n : ℤ) ≡ 0 [ZMOD p])
    (hmap_ne : P.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ((x : ℕ) : ZMod p) ∈ P.rootSet (ZMod p) := by
  -- The congruence hypothesis becomes vanishing after reducing coefficients modulo `p`.
  have hxmod : P.eval (x : ℤ) ≡ 0 [ZMOD p] := (Finset.mem_filter.mp hx).2
  have hxeval_cast :
      (P.map (Int.castRingHom (ZMod p))).eval (x : ZMod p) = ((P.eval (x : ℤ) : ℤ) : ZMod p) := by
    convert P.eval_map_apply (Int.castRingHom (ZMod p)) (x : ℤ) using 1
    simp
  have hxeval : (P.map (Int.castRingHom (ZMod p))).eval (x : ZMod p) = 0 := by
    rw [hxeval_cast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 <| Int.modEq_zero_iff_dvd.mp hxmod
  have hroot_eval :
      Polynomial.aeval (x : ZMod p) P = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hxeval
  -- Membership in the root set is exactly the nonvanishing hypothesis together with evaluation at
  -- the candidate root being zero.
  refine (Polynomial.mem_rootSet').2 ?_
  exact ⟨hmap_ne, hroot_eval⟩

/-- Helper for Theorem 1.1.79: natural representatives lying below `p` remain distinct in
`ZMod p`. -/
lemma solution_cast_injective (p : ℕ) [Fact p.Prime] {solutions : Finset ℕ}
    (hsolutions : ∀ {x : ℕ}, x ∈ solutions → x < p) :
    Function.Injective (fun x : solutions ↦ ((x : ℕ) : ZMod p)) := by
  intro x y hxy
  apply Subtype.ext
  -- Equality in `ZMod p` means congruence modulo `p`, and the range bounds force equality.
  have hxy_mod : (x : ℕ) ≡ (y : ℕ) [MOD p] :=
    (ZMod.natCast_eq_natCast_iff (x : ℕ) (y : ℕ) p).mp hxy
  have hxlt : (x : ℕ) < p := hsolutions x.2
  have hylt : (y : ℕ) < p := hsolutions y.2
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hxy_mod

/-- Helper for Theorem 1.1.79: the canonical residue representatives solving the congruence inject
into the root set of the reduced polynomial. -/
lemma solution_card_le_rootSet_ncard (p : ℕ) [Fact p.Prime] (P : Polynomial ℤ)
    (hmap_ne : P.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ((Finset.range p).filter fun x : ℕ ↦ P.eval (x : ℤ) ≡ 0 [ZMOD p]).card ≤
      Set.ncard (P.rootSet (ZMod p)) := by
  let solutions : Finset ℕ :=
    (Finset.range p).filter fun x : ℕ ↦ P.eval (x : ℤ) ≡ 0 [ZMOD p]
  let toRoot : solutions → P.rootSet (ZMod p) := fun x ↦
    ⟨(x : ZMod p), mem_rootSet_of_eval_modEq_zero p P x.2 hmap_ne⟩
  have hsolutions : ∀ {x : ℕ}, x ∈ solutions → x < p := by
    intro x hx
    exact Finset.mem_range.mp ((Finset.mem_filter.mp hx).1)
  have htoRoot : Function.Injective toRoot := by
    -- Two subtype roots are equal only if their underlying representatives agree in `ZMod p`.
    intro x y hxy
    exact solution_cast_injective p hsolutions (congrArg Subtype.val hxy)
  -- Count solutions by transporting them injectively into the finite root set.
  calc
    solutions.card ≤ Fintype.card (P.rootSet (ZMod p)) := by
      simpa using Fintype.card_le_of_injective toRoot htoRoot
    _ = Set.ncard (P.rootSet (ZMod p)) := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

/-- Theorem 1.1.79: if `p` is prime and `P : ℤ[X]` has degree `d` with leading coefficient not
divisible by `p`, then the congruence `P(x) ≡ 0 [ZMOD p]` has at most `P.natDegree` solutions
modulo `p`, counted by their canonical representatives `x ∈ {0, 1, ..., p - 1}`. -/
-- Proof sketch: reduce `P` modulo `p` to a nonzero polynomial over `ZMod p`, identify the
-- filtered residue classes in `Finset.range p` with its roots in `ZMod p`, and apply the standard
-- bound that a nonzero polynomial over an integral domain has at most `natDegree` roots.
theorem card_solutions_modEq_zero_le_natDegree (p : ℕ) (hp : Nat.Prime p) (P : Polynomial ℤ)
    (hlead : ¬ (p : ℤ) ∣ P.leadingCoeff) :
    ((Finset.range p).filter fun x : ℕ ↦ P.eval (x : ℤ) ≡ 0 [ZMOD p]).card ≤ P.natDegree := by
  letI : Fact p.Prime := ⟨hp⟩
  -- Route correction: use the root set of the reduced polynomial, rather than an inductive
  -- argument on representatives, so the textbook idea is packaged by the standard root bound.
  have hmap_ne : P.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_ne_zero_of_leadingCoeff_not_dvd p P hlead
  have hcard :
      ((Finset.range p).filter fun x : ℕ ↦ P.eval (x : ℤ) ≡ 0 [ZMOD p]).card ≤
        Set.ncard (P.rootSet (ZMod p)) :=
    solution_card_le_rootSet_ncard p P hmap_ne
  -- The reduced polynomial over the field `ZMod p` has at most `natDegree` roots.
  exact hcard.trans (Polynomial.ncard_rootSet_le P (ZMod p))
