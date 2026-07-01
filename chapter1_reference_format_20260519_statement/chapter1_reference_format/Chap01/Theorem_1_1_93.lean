import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_91

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

section PowerResidues

variable {n : ℕ} [NeZero n]
variable {a : (ZMod n)ˣ} {k : ℕ}
variable {g : (ZMod n)ˣ}

/-- Helper for Theorem 1.1.93: a power of a primitive root equals `a` exactly when its exponent is
congruent to the bounded discrete logarithm of `a`. -/
theorem primitive_root_pow_eq_iff_log_modEq
    (hg : IsPrimitiveRoot g (φ n)) (m : ℕ) :
    g ^ m = a ↔ m ≡ (hg.log a : ℕ) [MOD φ n] := by
  constructor
  · intro h
    -- Replace `a` by the canonical power `g ^ log_g a` to read the equation on exponents.
    have h' : g ^ m = g ^ (hg.log a : ℕ) := by
      calc
        g ^ m = a := h
        _ = g ^ (hg.log a : ℕ) := hg.pow_log a
    simpa [hg.eq_orderOf] using (pow_eq_pow_iff_modEq.mp h')
  · intro h
    -- Once the exponents are congruent modulo `φ n`, the powers agree.
    have h' : m ≡ (hg.log a : ℕ) [MOD orderOf g] := by
      simpa [hg.eq_orderOf] using h
    exact (pow_eq_pow_iff_modEq.mpr h').trans (hg.pow_log a).symm

/-- Theorem 1.1.93: if `g` is a primitive root modulo `n`, then a unit `a` modulo `n` is a
`k`-th power exactly when the bounded discrete logarithm of `a` with respect to `g` is divisible
by `gcd(k, φ n)`. -/
-- Proof sketch: `hg.log a` is the canonical exponent of `a` with respect to the primitive root
-- `g`. Writing `a = g ^ hg.log a` via `hg.pow_log a`, the equation `x ^ k = a` becomes a linear
-- congruence on exponents modulo `φ n`, so solvability is equivalent to
-- `gcd(k, φ n) ∣ hg.log a`.
theorem zmod_units_exists_pow_eq_iff_gcd_dvd_log
    (hg : IsPrimitiveRoot g (φ n)) :
    (∃ x : (ZMod n)ˣ, x ^ k = a) ↔ Nat.gcd k (φ n) ∣ (hg.log a : ℕ) := by
  constructor
  · intro hsol
    rcases hsol with ⟨x, hx⟩
    -- Convert a solution of `x ^ k = a` into a congruence on discrete logarithms.
    have hklog : (hg.log x : ℕ) * k ≡ (hg.log a : ℕ) [MOD φ n] := by
      apply (primitive_root_pow_eq_iff_log_modEq (a := a) hg ((hg.log x : ℕ) * k)).mp
      calc
        g ^ ((hg.log x : ℕ) * k) = (g ^ (hg.log x : ℕ)) ^ k := by
          rw [pow_mul]
        _ = x ^ k := by
          rw [← hg.pow_log x]
        _ = a := hx
    -- The gcd already divides the left-hand exponent, so it also divides `log_g a`.
    have hdiv : Nat.gcd k (φ n) ∣ (hg.log x : ℕ) * k := by
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left k (φ n)) (hg.log x : ℕ)
    exact (hklog.dvd_iff (Nat.gcd_dvd_right k (φ n))).mp hdiv
  · intro hdiv
    rcases hdiv with ⟨r, hr⟩
    let d := Nat.gcd k (φ n)
    let m := φ n / d
    have hφpos : 0 < φ n := by
      simpa using (Nat.totient_pos (n := n)).2 (NeZero.pos n)
    have hdpos : 0 < d := by
      exact Nat.gcd_pos_of_pos_right k hφpos
    have hm_ne_zero : m ≠ 0 := by
      exact Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.gcd_le_right k hφpos) hdpos)
    have hcop : (k / d).Coprime m := by
      simpa [d, m] using Nat.coprime_div_gcd_div_gcd (m := k) (n := φ n) hdpos
    -- Solve the reduced linear congruence after dividing by the gcd.
    obtain ⟨i, -, hi⟩ := Nat.exists_mul_mod_eq_of_coprime r hcop hm_ne_zero
    have hred : i * (k / d) ≡ r [MOD m] := by
      simpa [Nat.ModEq, m, Nat.mul_comm] using hi
    have hred' : (k / d) * i ≡ r [MOD m] := by
      simpa [Nat.mul_comm] using hred
    have hik : k * i ≡ (hg.log a : ℕ) [MOD φ n] := by
      have hmul := Nat.ModEq.mul_left' d hred'
      have hleft : d * ((k / d) * i) = k * i := by
        calc
          d * ((k / d) * i) = (d * (k / d)) * i := by rw [Nat.mul_assoc]
          _ = ((k / d) * d) * i := by rw [Nat.mul_comm d (k / d)]
          _ = k * i := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left k (φ n))]
      have hright : d * r = (hg.log a : ℕ) := by
        rw [hr]
      have hmodulus : d * m = φ n := by
        change Nat.gcd k (φ n) * (φ n / Nat.gcd k (φ n)) = φ n
        rw [Nat.mul_comm]
        exact Nat.div_mul_cancel (Nat.gcd_dvd_right k (φ n))
      simpa only [hleft, hright, hmodulus] using hmul
    -- Lift the solved congruence back to the witness `g ^ i`.
    refine ⟨g ^ i, ?_⟩
    calc
      (g ^ i) ^ k = g ^ (i * k) := by
        rw [pow_mul]
      _ = a := (primitive_root_pow_eq_iff_log_modEq (a := a) hg (i * k)).2 <| by
        simpa [Nat.mul_comm] using hik

/-- Companion reformulation of `zmod_units_exists_pow_eq_iff_gcd_dvd_log` in terms of powers of a
primitive root. -/
theorem zmod_units_exists_pow_eq_iff_exists_primitiveRoot_pow
    (hg : IsPrimitiveRoot g (φ n)) :
    (∃ x : (ZMod n)ˣ, x ^ k = a) ↔ ∃ m : ℕ, a = g ^ (Nat.gcd k (φ n) * m) := by
  constructor
  · intro hsol
    rcases (zmod_units_exists_pow_eq_iff_gcd_dvd_log (a := a) (k := k) hg).mp hsol with ⟨m, hm⟩
    -- Re-express the divisibility of `log_g a` as an explicit power formula for `a`.
    refine ⟨m, ?_⟩
    calc
      a = g ^ (hg.log a : ℕ) := hg.pow_log a
      _ = g ^ (Nat.gcd k (φ n) * m) := by
        rw [hm]
  · rintro ⟨m, hm⟩
    -- The displayed power already shows the discrete logarithm is a multiple of the gcd.
    apply (zmod_units_exists_pow_eq_iff_gcd_dvd_log (a := a) (k := k) hg).2
    have hmod : Nat.gcd k (φ n) * m ≡ (hg.log a : ℕ) [MOD φ n] := by
      exact (primitive_root_pow_eq_iff_log_modEq (a := a) hg (Nat.gcd k (φ n) * m)).mp hm.symm
    have hdiv : Nat.gcd k (φ n) ∣ Nat.gcd k (φ n) * m := by
      exact dvd_mul_right _ _
    exact (hmod.dvd_iff (Nat.gcd_dvd_right k (φ n))).mp hdiv

/-- A unit modulo `n` is a `k`-th power exactly when its `φ n / gcd(k, φ n)` power is `1`. -/
-- Proof sketch: choose a generator `g` of the cyclic group `(ZMod n)ˣ` from `hc`, apply
-- `zmod_units_exists_pow_eq_iff_gcd_dvd_log` to that primitive root, and then use
-- `IsPrimitiveRoot.pow_eq_one_iff_dvd` to replace the divisibility condition on the discrete
-- logarithm by the generator-free equation `a ^ (φ n / gcd(k, φ n)) = 1`.
theorem zmod_units_exists_pow_eq_iff_pow_totient_div_gcd_eq_one
    (hc : IsCyclic (ZMod n)ˣ) :
    (∃ x : (ZMod n)ˣ, x ^ k = a) ↔ a ^ (φ n / Nat.gcd k (φ n)) = 1 := by
  obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
  have hg : IsPrimitiveRoot u (φ n) := by
    simpa [hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using
      IsPrimitiveRoot.orderOf u
  rw [zmod_units_exists_pow_eq_iff_gcd_dvd_log (a := a) (k := k) hg]
  let d := Nat.gcd k (φ n)
  let m := φ n / d
  have hφpos : 0 < φ n := by
    simpa using (Nat.totient_pos (n := n)).2 (NeZero.pos n)
  constructor
  · rintro ⟨r, hr⟩
    have hphi : u ^ (φ n) = 1 := (hg.pow_eq_one_iff_dvd (φ n)).2 (dvd_rfl)
    -- A multiple of `d` in the discrete log makes the `m`-th power collapse to `1`.
    calc
      a ^ m = (u ^ (hg.log a : ℕ)) ^ m := by
        rw [← hg.pow_log a]
      _ = u ^ ((hg.log a : ℕ) * m) := by
        rw [pow_mul]
      _ = u ^ (r * φ n) := by
        simp [d, m, hr, Nat.mul_left_comm, Nat.mul_comm,
          Nat.div_mul_cancel (Nat.gcd_dvd_right k (φ n))]
      _ = (u ^ (φ n)) ^ r := by
        rw [Nat.mul_comm, pow_mul]
      _ = 1 := by
        rw [hphi, one_pow]
  · intro ha
    -- Conversely, `a ^ m = 1` forces `φ n ∣ log_g(a) * m`, hence `d ∣ log_g(a)`.
    have hpow : u ^ ((hg.log a : ℕ) * m) = 1 := by
      calc
        u ^ ((hg.log a : ℕ) * m) = (u ^ (hg.log a : ℕ)) ^ m := by
          rw [pow_mul]
        _ = a ^ m := by
          rw [← hg.pow_log a]
        _ = 1 := ha
    have hdivphi : φ n ∣ (hg.log a : ℕ) * m := by
      exact (hg.pow_eq_one_iff_dvd ((hg.log a : ℕ) * m)).mp hpow
    have hmpos : 0 < m := by
      exact Nat.div_pos (Nat.gcd_le_right k hφpos) (Nat.gcd_pos_of_pos_right k hφpos)
    have hdm : d * m = φ n := by
      simpa [d, m, Nat.mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_right k (φ n))
    have hmul : d * m ∣ (hg.log a : ℕ) * m := by
      simpa [hdm] using hdivphi
    exact Nat.dvd_of_mul_dvd_mul_right hmpos hmul

/-- If `x ^ k = a` is solvable in the unit group modulo `n`, then it has exactly `gcd(k, φ n)`
solutions. -/
-- Proof sketch: the solutions form a nonempty fiber of `powMonoidHom k`. Every nonempty fiber of a
-- group homomorphism is equivalent to the kernel, and `IsCyclic.card_powMonoidHom_ker` gives the
-- kernel size in a finite cyclic group.
theorem zmod_units_card_pow_eq
    (hc : IsCyclic (ZMod n)ˣ) (hsol : ∃ x : (ZMod n)ˣ, x ^ k = a) :
    Nat.card {x : (ZMod n)ˣ // x ^ k = a} = Nat.gcd k (φ n) := by
  rcases hsol with ⟨x0, hx0⟩
  let e : {x : (ZMod n)ˣ // x ^ k = a} ≃ {y : (ZMod n)ˣ // y ^ k = 1} :=
    { toFun := fun x ↦ ⟨x.1 * x0⁻¹, by
        rw [mul_pow, inv_pow, x.2, hx0]
        simp⟩
      invFun := fun y ↦ ⟨y.1 * x0, by
        rw [mul_pow, y.2, hx0]
        simp⟩
      left_inv := by
        intro x
        ext
        simp [mul_assoc]
      right_inv := by
        intro y
        ext
        simp [mul_assoc] }
  -- Translate the nonempty fiber over `a` to the kernel by dividing by one fixed solution.
  have hfiber : Nat.card {x : (ZMod n)ˣ // x ^ k = a} = Nat.card {y : (ZMod n)ˣ // y ^ k = 1} := by
    exact Nat.card_congr e
  have hker :
      Nat.card {y : (ZMod n)ˣ // y ^ k = 1} =
        Nat.card ((powMonoidHom k : (ZMod n)ˣ →* (ZMod n)ˣ).ker) := by
    simp [MonoidHom.mem_ker]
  have hker_card : Nat.card ((powMonoidHom k : (ZMod n)ˣ →* (ZMod n)ˣ).ker) = Nat.gcd k (φ n) := by
    simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.gcd_comm] using
      (IsCyclic.card_powMonoidHom_ker (G := (ZMod n)ˣ) k)
  exact hfiber.trans (hker.trans hker_card)

/-- In the unit group modulo `n`, the number of distinct `k`-th power residues is
`φ n / gcd(k, φ n)`. -/
-- Proof sketch: the `k`-th power residues are exactly the range of `powMonoidHom k`, and
-- `IsCyclic.card_powMonoidHom_range` computes the cardinality of that range in a finite cyclic
-- group.
theorem zmod_units_card_kth_powers (hc : IsCyclic (ZMod n)ˣ) :
    Nat.card ((powMonoidHom k : (ZMod n)ˣ →* (ZMod n)ˣ).range) =
      φ n / Nat.gcd k (φ n) := by
  -- The cyclic-group range formula gives the exact number of `k`-th powers.
  simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.gcd_comm] using
    (IsCyclic.card_powMonoidHom_range (G := (ZMod n)ˣ) k)

end PowerResidues
