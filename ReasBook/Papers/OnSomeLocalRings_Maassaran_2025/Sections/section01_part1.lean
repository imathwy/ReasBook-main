import Mathlib

namespace SomeLocalRings

open Polynomial
open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜]

/-- Expand `(X + Q)^n` to first order in `Q`, with a remainder divisible by `Q^2`. -/
lemma exists_R_pow_X_add (Q : Polynomial 𝕜) (n : ℕ) :
    ∃ R : Polynomial 𝕜,
      (X + Q) ^ n = X ^ n + (n : Polynomial 𝕜) * X ^ (n - 1) * Q + R * Q ^ 2 := by
  classical
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | succ n =>
      cases n with
      | zero =>
          refine ⟨0, ?_⟩
          simp
      | succ n =>
          -- The binomial expansion, with the `Q^0` and `Q^1` terms separated out.
          let f : ℕ → Polynomial 𝕜 := fun m =>
            X ^ m * Q ^ (n + 2 - m) * ((n + 2).choose m : Polynomial 𝕜)
          let R : Polynomial 𝕜 :=
            ∑ m ∈ Finset.range (n + 1), X ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)
          refine ⟨R, ?_⟩
          have hsplit :
              (∑ m ∈ Finset.range (n + 3), f m) =
                (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := by
            calc
              (∑ m ∈ Finset.range (n + 3), f m) =
                  (∑ m ∈ Finset.range (n + 2), f m) + f (n + 2) := by
                    simpa [Nat.add_assoc] using (Finset.sum_range_succ f (n + 2))
              _ = ((∑ m ∈ Finset.range (n + 1), f m) + f (n + 1)) + f (n + 2) := by
                    simp [Finset.sum_range_succ]
              _ = (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := by
                    ac_rfl
          have htail :
              (∑ m ∈ Finset.range (n + 1), f m) = R * Q ^ 2 := by
            have hterm :
                ∀ m, m ∈ Finset.range (n + 1) →
                  f m = (X ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
              intro m hm
              have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
              have hsub : n + 2 - m = n - m + 2 := Nat.sub_add_comm hmle
              -- Rewrite `Q^(n+2-m)` as `Q^(n-m) * Q^2`.
              simp [f, hsub, pow_add, mul_assoc, mul_left_comm, mul_comm]
            calc
              (∑ m ∈ Finset.range (n + 1), f m) =
                  ∑ m ∈ Finset.range (n + 1),
                    (X ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      simpa using hterm m hm
              _ = (∑ m ∈ Finset.range (n + 1),
                    X ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
                      simpa [R] using
                        (Finset.sum_mul (Finset.range (n + 1))
                          (fun m => X ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜))
                          (Q ^ 2)).symm
          -- Assemble the split binomial expansion.
          have hpow :
              (X + Q) ^ (n + 2) = ∑ m ∈ Finset.range (n + 3), f m := by
            simp [f, Nat.add_left_comm, Nat.add_comm, add_pow]
          -- Simplify the `Q^0` and `Q^1` terms, and package the remainder into `R * Q^2`.
          -- (Note: here `Nat.succ (Nat.succ n) = n + 2` and `(n + 2) - 1 = n + 1`.)
          calc
            (X + Q) ^ (Nat.succ (Nat.succ n)) = (X + Q) ^ (n + 2) := by simp [Nat.add_assoc]
            _ = ∑ m ∈ Finset.range (n + 3), f m := hpow
            _ = (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := hsplit
            _ =
                X ^ (n + 2) + ((n + 2 : ℕ) : Polynomial 𝕜) * X ^ (n + 1) * Q + R * Q ^ 2 := by
              -- rewrite the tail
              rw [htail]
              -- simplify the two explicit terms
              have hlast : f (n + 2) = X ^ (n + 2) := by
                simp [f, mul_left_comm, mul_comm]
              have hlin : f (n + 1) = ((n + 2 : ℕ) : Polynomial 𝕜) * X ^ (n + 1) * Q := by
                have hsub : n + 2 - (n + 1) = 1 := by
                  simp
                have hchoose : (n + 2).choose (n + 1) = n + 2 := by
                  simp
                have hchoose' :
                    ((n + 2).choose (n + 1) : Polynomial 𝕜) = ((n + 2 : ℕ) : Polynomial 𝕜) := by
                  exact congrArg (fun t : ℕ => (t : Polynomial 𝕜)) hchoose
                -- `choose (n+2) (n+1) = n+2` and `n+2-(n+1)=1`.
                dsimp [f]
                rw [hsub, hchoose']
                -- `Q^1 = Q`; rearrange factors.
                simp [pow_one, mul_assoc]
                ac_rfl
              -- finish by rearranging
              simp [hlast, hlin, add_assoc, add_comm, add_left_comm, mul_comm]
            _ = X ^ (Nat.succ (Nat.succ n)) + (Nat.succ (Nat.succ n) : Polynomial 𝕜)
            * X ^ (Nat.succ (Nat.succ n) - 1) * Q + R * Q ^ 2 := by
              simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]

/-- Expand a monomial composed with `X + Q` to first order in `Q`. -/
lemma exists_R_monomial_comp_X_add (Q : Polynomial 𝕜) (a : 𝕜) (n : ℕ) :
    ∃ R : Polynomial 𝕜,
      (monomial n a).comp (X + Q) = monomial n a + (monomial n a).derivative * Q + R * Q ^ 2 := by
  classical
  rcases exists_R_pow_X_add (𝕜 := 𝕜) Q n with ⟨R, hR⟩
  refine ⟨C a * R, ?_⟩
  -- Use `monomial_comp` to reduce to the power expansion, then simplify.
  have hcoeff :
      C a * (n : Polynomial 𝕜) * X ^ (n - 1) =
        (monomial (n - 1) (a * (n : 𝕜)) : Polynomial 𝕜) := by
    have hnat : (n : Polynomial 𝕜) = C (n : 𝕜) :=
      (Polynomial.C_eq_natCast (R := 𝕜) n).symm
    calc
      C a * (n : Polynomial 𝕜) * X ^ (n - 1)
          = (C a * C (n : 𝕜)) * X ^ (n - 1) := by
              rw [hnat]
      _ = C (a * (n : 𝕜)) * X ^ (n - 1) := by
              simp [mul_assoc]
      _ = monomial (n - 1) (a * (n : 𝕜)) := by
              simpa using
                (Polynomial.C_mul_X_pow_eq_monomial (R := 𝕜) (a := a * (n : 𝕜)) (n := n - 1))
  have hder :
      (monomial n a : Polynomial 𝕜).derivative = C a * (n : Polynomial 𝕜) * X ^ (n - 1) := by
    calc
      (monomial n a : Polynomial 𝕜).derivative = monomial (n - 1) (a * (n : 𝕜)) := by
        simp [Polynomial.derivative_monomial]
      _ = C a * (n : Polynomial 𝕜) * X ^ (n - 1) := by
        simpa using hcoeff.symm
  calc
    (monomial n a : Polynomial 𝕜).comp (X + Q) = C a * (X + Q) ^ n := by
      simp [Polynomial.monomial_comp]
    _ = C a * (X ^ n + (n : Polynomial 𝕜) * X ^ (n - 1) * Q + R * Q ^ 2) := by
      simp [hR]
    _ = monomial n a + (monomial n a).derivative * Q + (C a * R) * Q ^ 2 := by
      -- Distribute `C a`, then rewrite the main and derivative terms.
      rw [hder]
      -- Note: `C a * X^n = monomial n a` is a simp lemma.
      -- Avoid using commutativity lemmas with `simp` (they may loop); finish by `ac_rfl`.
      simp [mul_add, mul_assoc, Polynomial.C_mul_X_pow_eq_monomial]

/-- The first-order expansion property is preserved under addition (for fixed `Q`). -/
lemma comp_X_add_taylor1_add
    {Q P₁ P₂ : Polynomial 𝕜}
    (h₁ : ∃ R, P₁.comp (X + Q) = P₁ + P₁.derivative * Q + R * Q ^ 2)
    (h₂ : ∃ R, P₂.comp (X + Q) = P₂ + P₂.derivative * Q + R * Q ^ 2) :
    ∃ R, (P₁ + P₂).comp (X + Q) = (P₁ + P₂) + (P₁ + P₂).derivative * Q + R * Q ^ 2 := by
  classical
  rcases h₁ with ⟨R₁, hR₁⟩
  rcases h₂ with ⟨R₂, hR₂⟩
  refine ⟨R₁ + R₂, ?_⟩
  -- Expand both sides, then use commutativity/associativity of addition to rearrange terms.
  calc
    (P₁ + P₂).comp (X + Q) = P₁.comp (X + Q) + P₂.comp (X + Q) := by
      simp [Polynomial.add_comp]
    _ = (P₁ + P₁.derivative * Q + R₁ * Q ^ 2) + (P₂ + P₂.derivative * Q + R₂ * Q ^ 2) := by
      simp [hR₁, hR₂, add_assoc]
    _ = (P₁ + P₂) + (P₁ + P₂).derivative * Q + (R₁ + R₂) * Q ^ 2 := by
      -- Expand the derivative and remainder terms on the RHS, then close by `ac_rfl`.
      simp [Polynomial.derivative_add, add_mul, add_assoc, add_left_comm, add_comm]

/--
Lemma 1.1.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. For `Q ∈ 𝕜[X]`, we have
`P(X + Q(X)) = P(X) + P'(X) Q(X) + R(X) Q(X)^2` for some `R ∈ 𝕜[X]`.
-/
lemma polynomial_comp_X_add_eq_add_derivative_mul_add_mul_sq
    (P : Polynomial 𝕜) (Q : Polynomial 𝕜) :
    ∃ R : Polynomial 𝕜,
      P.comp (Polynomial.X + Q) = P + P.derivative * Q + R * Q ^ 2 := by
  classical
  -- Reduce to monomials via `Polynomial.induction_on'`, using additivity and the monomial case.
  refine Polynomial.induction_on' (motive := fun P : Polynomial 𝕜 =>
    ∃ R : Polynomial 𝕜, P.comp (X + Q) = P + P.derivative * Q + R * Q ^ 2) P ?_ ?_
  · intro P₁ P₂ h₁ h₂
    simpa [add_assoc] using comp_X_add_taylor1_add (Q := Q) h₁ h₂
  · intro n a
    simpa using exists_R_monomial_comp_X_add (𝕜 := 𝕜) (Q := Q) a n

/-- Expand `(U + Q)^n` to first order in `Q`, with a remainder divisible by `Q^2`. -/
lemma exists_R_pow_add (U Q : Polynomial 𝕜) (n : ℕ) :
    ∃ R : Polynomial 𝕜,
      (U + Q) ^ n = U ^ n + (n : Polynomial 𝕜) * U ^ (n - 1) * Q + R * Q ^ 2 := by
  classical
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | succ n =>
      cases n with
      | zero =>
          refine ⟨0, ?_⟩
          simp
      | succ n =>
          -- The binomial expansion, with the `Q^0` and `Q^1` terms separated out.
          let f : ℕ → Polynomial 𝕜 := fun m =>
            U ^ m * Q ^ (n + 2 - m) * ((n + 2).choose m : Polynomial 𝕜)
          let R : Polynomial 𝕜 :=
            ∑ m ∈ Finset.range (n + 1), U ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)
          refine ⟨R, ?_⟩
          have hsplit :
              (∑ m ∈ Finset.range (n + 3), f m) =
                (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := by
            calc
              (∑ m ∈ Finset.range (n + 3), f m) =
                  (∑ m ∈ Finset.range (n + 2), f m) + f (n + 2) := by
                    simpa [Nat.add_assoc] using (Finset.sum_range_succ f (n + 2))
              _ = ((∑ m ∈ Finset.range (n + 1), f m) + f (n + 1)) + f (n + 2) := by
                    simp [Finset.sum_range_succ]
              _ = (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := by
                    ac_rfl
          have htail :
              (∑ m ∈ Finset.range (n + 1), f m) = R * Q ^ 2 := by
            have hterm :
                ∀ m, m ∈ Finset.range (n + 1) →
                  f m = (U ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
              intro m hm
              have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
              have hsub : n + 2 - m = n - m + 2 := Nat.sub_add_comm hmle
              -- Rewrite `Q^(n+2-m)` as `Q^(n-m) * Q^2`.
              simp [f, hsub, pow_add, mul_assoc, mul_left_comm, mul_comm]
            calc
              (∑ m ∈ Finset.range (n + 1), f m) =
                  ∑ m ∈ Finset.range (n + 1),
                    (U ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      simpa using hterm m hm
              _ = (∑ m ∈ Finset.range (n + 1),
                    U ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜)) * Q ^ 2 := by
                      simpa [R] using
                        (Finset.sum_mul (Finset.range (n + 1))
                          (fun m => U ^ m * Q ^ (n - m) * ((n + 2).choose m : Polynomial 𝕜))
                          (Q ^ 2)).symm
          -- Assemble the split binomial expansion.
          have hpow :
              (U + Q) ^ (n + 2) = ∑ m ∈ Finset.range (n + 3), f m := by
            simp [f, Nat.add_left_comm, Nat.add_comm, add_pow]
          -- Simplify the `Q^0` and `Q^1` terms, and package the remainder into `R * Q^2`.
          calc
            (U + Q) ^ (Nat.succ (Nat.succ n)) = (U + Q) ^ (n + 2) := by simp [Nat.add_assoc]
            _ = ∑ m ∈ Finset.range (n + 3), f m := hpow
            _ = (∑ m ∈ Finset.range (n + 1), f m) + f (n + 1) + f (n + 2) := hsplit
            _ =
                U ^ (n + 2) + ((n + 2 : ℕ) : Polynomial 𝕜) * U ^ (n + 1) * Q + R * Q ^ 2 := by
              rw [htail]
              have hlast : f (n + 2) = U ^ (n + 2) := by
                simp [f]
              have hlin : f (n + 1) = ((n + 2 : ℕ) : Polynomial 𝕜) * U ^ (n + 1) * Q := by
                have hsub : n + 2 - (n + 1) = 1 := by
                  simp
                have hchoose : (n + 2).choose (n + 1) = n + 2 := by
                  simp
                have hchoose' :
                    ((n + 2).choose (n + 1) : Polynomial 𝕜) = ((n + 2 : ℕ) : Polynomial 𝕜) := by
                  exact congrArg (fun t : ℕ => (t : Polynomial 𝕜)) hchoose
                dsimp [f]
                rw [hsub, hchoose']
                simp [pow_one, mul_assoc]
                ac_rfl
              simp [hlast, hlin, add_assoc, add_comm, mul_comm]
            _ = U ^ (Nat.succ (Nat.succ n)) + (Nat.succ (Nat.succ n) : Polynomial 𝕜)
            * U ^ (Nat.succ (Nat.succ n) - 1) * Q + R * Q ^ 2 := by
              simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]

/-- Expand a monomial composed with `U + Q` to first order in `Q`. -/
lemma exists_R_monomial_comp_add (U Q : Polynomial 𝕜) (a : 𝕜) (n : ℕ) :
    ∃ R : Polynomial 𝕜,
      (monomial n a).comp (U + Q) =
        (monomial n a).comp U + ((monomial n a).derivative.comp U) * Q + R * Q ^ 2 := by
  classical
  rcases exists_R_pow_add (𝕜 := 𝕜) (U := U) (Q := Q) n with ⟨R, hR⟩
  refine ⟨C a * R, ?_⟩
  calc
    (monomial n a : Polynomial 𝕜).comp (U + Q) = C a * (U + Q) ^ n := by
      simp [Polynomial.monomial_comp]
    _ = C a * (U ^ n + (n : Polynomial 𝕜) * U ^ (n - 1) * Q + R * Q ^ 2) := by
      simp [hR]
    _ =
        C a * U ^ n + (C a * ((n : Polynomial 𝕜) * U ^ (n - 1))) * Q + (C a * R) * Q ^ 2 := by
      -- Distribute `C a` and reassociate the `Q`-term.
      simp [add_assoc, add_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (monomial n a).comp U + ((monomial n a).derivative.comp U) * Q + (C a * R) * Q ^ 2 := by
      -- Simplify the main and derivative terms.
      simp [Polynomial.monomial_comp, Polynomial.derivative_monomial,
        mul_assoc, mul_left_comm, mul_comm, add_assoc]

/-- The first-order expansion property is preserved under addition (for fixed `U` and `Q`). -/
lemma comp_add_taylor1_add
    {U Q P₁ P₂ : Polynomial 𝕜}
    (h₁ :
      ∃ R, P₁.comp (U + Q) = P₁.comp U + (P₁.derivative.comp U) * Q + R * Q ^ 2)
    (h₂ :
      ∃ R, P₂.comp (U + Q) = P₂.comp U + (P₂.derivative.comp U) * Q + R * Q ^ 2) :
    ∃ R,
      (P₁ + P₂).comp (U + Q) =
        (P₁ + P₂).comp U + ((P₁ + P₂).derivative.comp U) * Q + R * Q ^ 2 := by
  classical
  rcases h₁ with ⟨R₁, hR₁⟩
  rcases h₂ with ⟨R₂, hR₂⟩
  refine ⟨R₁ + R₂, ?_⟩
  calc
    (P₁ + P₂).comp (U + Q) = P₁.comp (U + Q) + P₂.comp (U + Q) := by
      simp [Polynomial.add_comp]
    _ = (P₁.comp U + P₁.derivative.comp U * Q + R₁ * Q ^ 2) +
          (P₂.comp U + P₂.derivative.comp U * Q + R₂ * Q ^ 2) := by
      simp [hR₁, hR₂, add_assoc]
    _ =
        (P₁ + P₂).comp U + ((P₁ + P₂).derivative.comp U) * Q + (R₁ + R₂) * Q ^ 2 := by
      -- Expand the derivative and remainder terms on the RHS, then close by `ac_rfl`.
      simp [Polynomial.derivative_add, Polynomial.add_comp,
        add_mul, add_assoc, add_left_comm, add_comm]

/-- A first-order Taylor expansion of `P.comp` around an arbitrary center `U`. -/
lemma polynomial_comp_add_eq_add_derivative_comp_mul_add_mul_sq (P U Q : Polynomial 𝕜) :
    ∃ R : Polynomial 𝕜,
      P.comp (U + Q) = P.comp U + (P.derivative.comp U) * Q + R * Q ^ 2 := by
  classical
  refine Polynomial.induction_on' (motive := fun P : Polynomial 𝕜 =>
    ∃ R : Polynomial 𝕜,
      P.comp (U + Q) = P.comp U + (P.derivative.comp U) * Q + R * Q ^ 2) P ?_ ?_
  · intro P₁ P₂ h₁ h₂
    simpa [add_assoc] using comp_add_taylor1_add (U := U) (Q := Q) h₁ h₂
  · intro n a
    simpa using exists_R_monomial_comp_add (𝕜 := 𝕜) (U := U) (Q := Q) a n

/-- If `P` is irreducible and `P' ≠ 0`, then the class of `P'` in `𝕜[X]/(P)` is nonzero. -/
lemma mk_derivative_ne_zero_mod_irreducible
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) :
    AdjoinRoot.mk P P.derivative ≠ (0 : AdjoinRoot P) := by
  intro h
  have hdiv : P ∣ P.derivative := (AdjoinRoot.mk_eq_zero).1 (by simpa using h)
  have hdegP : P.natDegree ≠ 0 := by
    intro hdeg
    rcases (Polynomial.natDegree_eq_zero.mp hdeg) with ⟨a, rfl⟩
    have ha : (a : 𝕜) ≠ 0 := by
      simpa [Polynomial.C_ne_zero] using hP.ne_zero
    have : IsUnit (Polynomial.C a : Polynomial 𝕜) := by
      simp [isUnit_iff_ne_zero, ha]
    exact hP.1 this
  have hle : P.natDegree ≤ P.derivative.natDegree := by
    exact Polynomial.natDegree_le_of_dvd hdiv hP'
  have hlt : P.derivative.natDegree < P.natDegree := Polynomial.natDegree_derivative_lt hdegP
  exact (not_lt_of_ge hle) hlt

/-- If `P ∣ U - X`, then composing a polynomial with `U` does not change its class in `𝕜[X]/(P)`. -/
lemma mk_comp_eq_mk_of_dvd_sub
    (P f U : Polynomial 𝕜) (hUX : P ∣ (U - X)) :
    AdjoinRoot.mk P (f.comp U) = AdjoinRoot.mk P f := by
  have hmk : (AdjoinRoot.mk P) U = (AdjoinRoot.mk P) X :=
    (AdjoinRoot.mk_eq_mk).2 (by simpa [sub_eq_add_neg, add_comm] using hUX)
  -- Work in `AdjoinRoot P`, where `mk` is `aeval` at the root.
  calc
    AdjoinRoot.mk P (f.comp U) = (Polynomial.aeval (AdjoinRoot.root P)) (f.comp U) := by
      simp [AdjoinRoot.aeval_eq]
    _ = (Polynomial.aeval ((Polynomial.aeval (AdjoinRoot.root P)) U)) f := by
      simpa using (Polynomial.aeval_comp (p := f) (q := U) (x := AdjoinRoot.root P))
    _ = (Polynomial.aeval ((AdjoinRoot.mk P) U)) f := by
      simp [AdjoinRoot.aeval_eq]
    _ = (Polynomial.aeval ((AdjoinRoot.mk P) X)) f := by
      simp [hmk]
    _ = (Polynomial.aeval (AdjoinRoot.root P)) f := by
      simp [AdjoinRoot.mk_X]
    _ = AdjoinRoot.mk P f := by
      simp [AdjoinRoot.aeval_eq]

/--
Given `U ≡ X (mod P)`, choose `S` so that `Rn + (P' ∘ U) * S ≡ 0 (mod P)`.

This uses that `𝕜[X]/(P)` is a field (since `P` is irreducible) and that `P'` is nonzero mod `P`.
-/
lemma exists_S_kill_Rn_mod_P
    (P U Rn : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) (hUX : P ∣ (U - X)) :
    ∃ S : Polynomial 𝕜, P ∣ (Rn + (P.derivative.comp U) * S) := by
  classical
  letI : Fact (Irreducible P) := ⟨hP⟩
  let a : AdjoinRoot P := AdjoinRoot.mk P (P.derivative.comp U)
  let r : AdjoinRoot P := AdjoinRoot.mk P Rn
  have ha : a ≠ 0 := by
    have ha' : AdjoinRoot.mk P (P.derivative.comp U) = AdjoinRoot.mk P P.derivative := by
      simpa using mk_comp_eq_mk_of_dvd_sub (𝕜 := 𝕜) (P := P) (f := P.derivative) (U := U) hUX
    -- Reduce to `mk P P' ≠ 0`.
    simpa [a, ha'] using mk_derivative_ne_zero_mod_irreducible (𝕜 := 𝕜) P hP hP'
  let sbar : AdjoinRoot P := -(r / a)
  rcases (AdjoinRoot.mk_surjective (g := P) sbar) with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  have hzero : AdjoinRoot.mk P (Rn + (P.derivative.comp U) * S) = (0 : AdjoinRoot P) := by
    -- Compute in the field `AdjoinRoot P`, using `a * (r / a) = r`.
    have hmul : a * (r / a) = r := by
      simpa [a, r] using (mul_div_cancel₀ r ha)
    -- Rewrite `mk P S` as `sbar`.
    have : AdjoinRoot.mk P S = sbar := hS
    -- Now simplify.
    simp [a, r, sbar, this, hmul, mul_comm]
  exact (AdjoinRoot.mk_eq_zero).1 hzero

/--
One Hensel-style lifting step: if `P.comp U` is divisible by `P^(n+1)` and `U ≡ X (mod P)`, then
we can adjust `U` by `S * P^(n+1)` so that `P.comp` becomes divisible by `P^(n+2)`.
-/
lemma hensel_step
    (P U Rn : Polynomial 𝕜) (n : ℕ) (hP : Irreducible P) (hP' : P.derivative ≠ 0)
    (hUX : P ∣ (U - X)) (hcomp : P.comp U = Rn * P ^ (n + 1)) :
    ∃ (S Rn1 : Polynomial 𝕜), P.comp (U + S * P ^ (n + 1)) = Rn1 * P ^ (n + 2) := by
  classical
  rcases exists_S_kill_Rn_mod_P (𝕜 := 𝕜) (P := P) (U := U) (Rn := Rn) hP hP' hUX with ⟨S, hS⟩
  rcases polynomial_comp_add_eq_add_derivative_comp_mul_add_mul_sq (𝕜 := 𝕜) (P := P) (U := U)
      (Q := S * P ^ (n + 1)) with ⟨T, hT⟩
  have hsq : (S * P ^ (n + 1)) ^ 2 = S ^ 2 * P ^ (2 * n + 2) := by
    -- `(S * P^(n+1))^2 = S^2 * (P^(n+1))^2 = S^2 * P^(2n+2)`.
    calc
      (S * P ^ (n + 1)) ^ 2 = S ^ 2 * (P ^ (n + 1)) ^ 2 := by
        simp [mul_pow]
      _ = S ^ 2 * P ^ ((n + 1) * 2) := by
        simp [pow_mul]
      _ = S ^ 2 * P ^ (2 * n + 2) := by
        have hmul : (n + 1) * 2 = 2 * n + 2 := by
          simp [Nat.add_mul, Nat.mul_comm]
        simp [hmul]
  have hrewrite :
      P.comp (U + S * P ^ (n + 1)) =
        (Rn + (P.derivative.comp U) * S) * P ^ (n + 1) + (T * S ^ 2) * P ^ (2 * n + 2) := by
    calc
      P.comp (U + S * P ^ (n + 1)) =
          P.comp U + (P.derivative.comp U) * (S * P ^ (n + 1)) + T * (S * P ^ (n + 1)) ^ 2 := hT
      _ =
          Rn * P ^ (n + 1) + (P.derivative.comp U) * (S * P ^ (n + 1)) +
              T * (S * P ^ (n + 1)) ^ 2 := by
            simp [hcomp, add_assoc]
      _ =
          (Rn + (P.derivative.comp U) * S) * P ^ (n + 1) +
              (T * S ^ 2) * P ^ (2 * n + 2) := by
            -- Factor out `P^(n+1)` and rewrite the remainder using `hsq`.
            simp [hsq, mul_add, mul_assoc, mul_left_comm, mul_comm, add_left_comm,
              add_comm]
  -- The first term is divisible by `P^(n+2)` by construction.
  have hdvd1 : P ^ (n + 2) ∣ (Rn + (P.derivative.comp U) * S) * P ^ (n + 1) := by
    rcases hS with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    calc
      (Rn + (P.derivative.comp U) * S) * P ^ (n + 1) = (P * A) * P ^ (n + 1) := by
        simp [hA]
      _ = P ^ (n + 2) * A := by
        -- Commute and reassociate factors.
        simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  -- The remainder is divisible by `P^(n+2)` since `n+2 ≤ 2n+2`.
  have hdvd2 : P ^ (n + 2) ∣ (T * S ^ 2) * P ^ (2 * n + 2) := by
    have hle : n + 2 ≤ 2 * n + 2 := by
      have hn : n ≤ n + n := Nat.le_add_right n n
      have hn' : n + 2 ≤ (n + n) + 2 := Nat.add_le_add_right hn 2
      simp [two_mul, Nat.add_assoc]
    exact dvd_mul_of_dvd_right (pow_dvd_pow P hle) (T * S ^ 2)
  have hdvd : P ^ (n + 2) ∣ P.comp (U + S * P ^ (n + 1)) := by
    rw [hrewrite]
    exact dvd_add hdvd1 hdvd2
  rcases hdvd with ⟨Rn1, hRn1⟩
  refine ⟨S, Rn1, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using hRn1

/-- State used to build the sequences in Lemma 1.2 by recursion on `n`. -/
structure LiftState (P : Polynomial 𝕜) (n : ℕ) where
  U : Polynomial 𝕜
  R : Polynomial 𝕜
  q : Polynomial 𝕜
  hcomp : P.comp U = R * P ^ (n + 1)
  hmod : P ∣ U - X

/--
Lemma 1.2.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then there exists
an infinite sequence of pairs of polynomials `(Q₀, R₀), (Q₁, R₁), …` such that for all `k ≥ 0`,
`P(X + ∑_{i=1}^k Qᵢ(X) * P(X)^i) = Rₖ(X) * P(X)^(k+1)`.
-/
lemma exists_polynomial_sequences_comp_X_add_sum_mul_pow_eq_mul_pow
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) :
    ∃ (Q R : ℕ → Polynomial 𝕜),
      ∀ k : ℕ,
        P.comp
            (Polynomial.X +
              Finset.sum (Finset.range k) (fun i => Q (i + 1) * P ^ (i + 1))) =
          R k * P ^ (k + 1) := by
  classical
  -- Construct `Uₙ`, `Rₙ`, and `Qₙ` recursively,
  -- lifting the divisibility by one power of `P` at each step.
  let base : LiftState (𝕜 := 𝕜) P 0 :=
    { U := X
      R := 1
      q := 0
      hcomp := by simp
      hmod := by simp }
  let step :
      ∀ n : ℕ,
        LiftState (𝕜 := 𝕜) P n → LiftState (𝕜 := 𝕜) P (n + 1) :=
    fun n st =>
      let hSR :=
        hensel_step (𝕜 := 𝕜) (P := P) (U := st.U) (Rn := st.R) (n := n) hP hP' st.hmod st.hcomp
      let q : Polynomial 𝕜 := Classical.choose hSR
      let hR : ∃ Rn1 : Polynomial 𝕜, P.comp (st.U + q * P ^ (n + 1)) = Rn1 * P ^ (n + 2) :=
        Classical.choose_spec hSR
      let Rn1 : Polynomial 𝕜 := Classical.choose hR
      have hcomp' : P.comp (st.U + q * P ^ (n + 1)) = Rn1 * P ^ (n + 2) :=
        Classical.choose_spec hR
      have h1 : P ∣ st.U - X := st.hmod
      have h2 : P ∣ q * P ^ (n + 1) :=
        dvd_mul_of_dvd_right (dvd_pow_self P (Nat.succ_ne_zero n)) q
      have hsum : P ∣ (st.U - X) + q * P ^ (n + 1) := dvd_add h1 h2
      have hmod' : P ∣ (st.U + q * P ^ (n + 1)) - X := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
      { U := st.U + q * P ^ (n + 1)
        R := Rn1
        q := q
        hcomp := hcomp'
        hmod := hmod' }
  let state : ∀ n : ℕ, LiftState (𝕜 := 𝕜) P n :=
    Nat.rec base (fun n st => step n st)
  have step_U (n : ℕ) (st : LiftState (𝕜 := 𝕜) P n) :
      (step n st).U = st.U + (step n st).q * P ^ (n + 1) := by
    rfl
  refine ⟨(fun n => (state n).q), (fun n => (state n).R), ?_⟩
  intro k
  have hU :
      (state k).U =
        X + Finset.sum (Finset.range k) (fun i => (state (i + 1)).q * P ^ (i + 1)) := by
    induction k with
    | zero =>
        simp [state, base]
    | succ k ih =>
        have hstepU :
            (state (k + 1)).U = (state k).U + (state (k + 1)).q * P ^ (k + 1) := by
          -- Unfold one step of the recursion.
          simpa [state] using (step_U k (state k))
        -- Use `sum_range_succ` to split off the last term.
        calc
          (state (k + 1)).U
              =
              (X + Finset.sum (Finset.range k) (fun i => (state (i + 1)).q * P ^ (i + 1))) +
                (state (k + 1)).q * P ^ (k + 1) := by
                simp [hstepU, ih, add_assoc]
          _ =
              X + Finset.sum (Finset.range (k + 1)) (fun i => (state (i + 1)).q * P ^ (i + 1)) := by
                rw [Finset.sum_range_succ (fun i => (state (i + 1)).q * P ^ (i + 1)) k]
                ac_rfl
  -- Rewrite the argument of `P.comp` using `hU`, then use the stored divisibility equality.
  calc
    P.comp (X + Finset.sum (Finset.range k) (fun i => (state (i + 1)).q * P ^ (i + 1))) =
        P.comp (state k).U := by
          simp [hU]
    _ = (state k).R * P ^ (k + 1) := (state k).hcomp

/--
Evaluating a polynomial `p` at `mk f U` in `AdjoinRoot f`
corresponds to taking `p.comp U` modulo `f`.
-/
lemma aeval_mk_eq_mk_comp (f U p : Polynomial 𝕜) :
    (aeval (AdjoinRoot.mk f U)) p = AdjoinRoot.mk f (p.comp U) := by
  -- Rewrite `mk f U` as `aeval (root f) U`, then use `aeval_comp`.
  rw [show (AdjoinRoot.mk f U : AdjoinRoot f) = (aeval (AdjoinRoot.root f)) U from
    (AdjoinRoot.aeval_eq (f := f) U).symm]
  calc
    (aeval ((aeval (AdjoinRoot.root f)) U)) p = (aeval (AdjoinRoot.root f)) (p.comp U) := by
      simpa using
        (Polynomial.aeval_comp (p := p) (q := U) (x := AdjoinRoot.root f)).symm
    _ = AdjoinRoot.mk f (p.comp U) := by
      simp [AdjoinRoot.aeval_eq]

/--
For `U := X + ∑ i < k - 1, Q (i+1) * P^(i+1)`, Lemma 1.2 gives `P.comp U = R (k-1) * P^k`.
-/
lemma prop1_3_comp_eq_mul_pow (P : Polynomial 𝕜) (Q R : ℕ → Polynomial 𝕜) (k : ℕ) (hk : 1 ≤ k)
    (hQR :
      ∀ n : ℕ,
        P.comp (X + ∑ i ∈ Finset.range n, Q (i + 1) * P ^ (i + 1)) = R n * P ^ (n + 1)) :
    P.comp (X + ∑ i ∈ Finset.range (k - 1), Q (i + 1) * P ^ (i + 1)) = R (k - 1) * P ^ k := by
  simpa [Nat.sub_add_cancel hk] using (hQR (k - 1))

/--
The polynomial `X + ∑ i < n, Q (i+1) * P^(i+1)` is congruent to `X` modulo `P`.
-/
lemma prop1_3_dvd_sub_X (P : Polynomial 𝕜) (Q : ℕ → Polynomial 𝕜) (n : ℕ) :
    P ∣ (X + ∑ i ∈ Finset.range n, Q (i + 1) * P ^ (i + 1)) - X := by
  have hterm :
      ∀ i ∈ Finset.range n, P ∣ Q (i + 1) * P ^ (i + 1) := by
    intro i hi
    exact dvd_mul_of_dvd_right (dvd_pow_self P (Nat.succ_ne_zero i)) (Q (i + 1))
  have hsum : P ∣ ∑ i ∈ Finset.range n, Q (i + 1) * P ^ (i + 1) :=
    Finset.dvd_sum hterm
  simpa [add_sub_cancel_left] using hsum

/--
In `AdjoinRoot P`, the element `root P` is a root of `P^k` for `k ≠ 0`.
-/
lemma prop1_3_aeval_root_pow_eq_zero (P : Polynomial 𝕜) (k : ℕ) (hk : k ≠ 0) :
    (aeval (AdjoinRoot.root P)) (P ^ k) = (0 : AdjoinRoot P) := by
  have hP0 : (aeval (AdjoinRoot.root P)) P = (0 : AdjoinRoot P) := by
    simp [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
  calc
    (aeval (AdjoinRoot.root P)) (P ^ k) = ((aeval (AdjoinRoot.root P)) P) ^ k := by
      simp [map_pow]
    _ = 0 := by
      simp [hP0, hk]

/--
Proposition 1.3.
Let `𝕜` be a field and let `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then for every
`k ≥ 1` there exists an injective `𝕜`-algebra morphism from the field `𝕜[X]⧸(P)` into `𝕜[X]⧸(P^k)`.
-/
theorem exists_injective_algHom_adjoinRoot_to_adjoinRoot_pow
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) :
    ∀ k : ℕ, 1 ≤ k → ∃ f : AdjoinRoot P →ₐ[𝕜] AdjoinRoot (P ^ k), Function.Injective f := by
  classical
  intro k hk
  rcases exists_polynomial_sequences_comp_X_add_sum_mul_pow_eq_mul_pow (𝕜 := 𝕜) (P := P) hP hP' with
    ⟨Q, R, hQR⟩
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  let U : Polynomial 𝕜 :=
    X + ∑ i ∈ Finset.range (k - 1), Q (i + 1) * P ^ (i + 1)
  have hcompU : P.comp U = R (k - 1) * P ^ k := by
    simpa [U] using prop1_3_comp_eq_mul_pow (𝕜 := 𝕜) (P := P) (Q := Q) (R := R) k hk hQR
  have hdvd : P ^ k ∣ P.comp U := by
    refine ⟨R (k - 1), ?_⟩
    -- Commute the factors to match the definition of divisibility.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcompU
  let α : AdjoinRoot (P ^ k) := AdjoinRoot.mk (P ^ k) U
  have haeval : (aeval α) P = 0 := by
    have : (aeval α) P = AdjoinRoot.mk (P ^ k) (P.comp U) := by
      simpa [α, U] using aeval_mk_eq_mk_comp (𝕜 := 𝕜) (f := P ^ k) (U := U) (p := P)
    -- Reduce to the divisibility statement `P^k ∣ P.comp U`.
    simpa [this] using (AdjoinRoot.mk_eq_zero (f := P ^ k) (g := P.comp U)).2 hdvd
  let f : AdjoinRoot P →ₐ[𝕜] AdjoinRoot (P ^ k) :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId 𝕜 (AdjoinRoot (P ^ k))) α (by
      simpa [Polynomial.aeval_def] using haeval)
  let πk : AdjoinRoot (P ^ k) →ₐ[𝕜] AdjoinRoot P :=
    AdjoinRoot.liftAlgHom (P ^ k) (Algebra.ofId 𝕜 (AdjoinRoot P)) (AdjoinRoot.root P) (by
      simpa [Polynomial.aeval_def] using
        (prop1_3_aeval_root_pow_eq_zero (𝕜 := 𝕜) (P := P) k hk0))
  have hπkα : πk α = AdjoinRoot.root P := by
    have hmk :
        (AdjoinRoot.mk (P ^ k) U : AdjoinRoot (P ^ k)) =
          (aeval (AdjoinRoot.root (P ^ k))) U := by
      simp
    calc
      πk α = πk (AdjoinRoot.mk (P ^ k) U) := by simp [α]
      _ = πk ((aeval (AdjoinRoot.root (P ^ k))) U) := by
        simp
      _ = (aeval (πk (AdjoinRoot.root (P ^ k)))) U := by
        simpa using
          (Polynomial.aeval_algHom_apply (f := πk) (x := AdjoinRoot.root (P ^ k)) (p := U)).symm
      _ = (aeval (AdjoinRoot.root P)) U := by
        simp [πk, AdjoinRoot.liftAlgHom_root]
      _ = AdjoinRoot.mk P U := by
        simp [AdjoinRoot.aeval_eq]
      _ = AdjoinRoot.mk P X := by
        refine (AdjoinRoot.mk_eq_mk).2 ?_
        simpa [U] using prop1_3_dvd_sub_X (𝕜 := 𝕜) (P := P) (Q := Q) (n := k - 1)
      _ = AdjoinRoot.root P := by
        simp [AdjoinRoot.mk_X]
  have hcomp : πk.comp f = AlgHom.id 𝕜 (AdjoinRoot P) := by
    apply AdjoinRoot.algHom_ext
    -- It suffices to check the image of `root P`.
    simp [AlgHom.comp_apply, f, πk, AdjoinRoot.liftAlgHom_root, hπkα]
  have hleft : Function.LeftInverse πk f := by
    intro x
    -- Apply the equality `πk.comp f = id` to `x`.
    simpa [AlgHom.comp_apply] using congrArg (fun g => g x) hcomp
  exact ⟨f, hleft.injective⟩

/--
Corollary 1.4.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then for every
`k ≥ 1`, the quotient `𝕜[X]⧸(P ^ k)` contains `𝕜[X]⧸(P)` as a `𝕜`-subalgebra.
-/
theorem exists_residueField_algEquiv_subalgebra_adjoinRoot_pow
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) :
    ∀ k : ℕ,
      1 ≤ k →
        ∃ S : Subalgebra 𝕜 (AdjoinRoot (P ^ k)), Nonempty (AdjoinRoot P ≃ₐ[𝕜] S) := by
  classical
  intro k hk
  rcases
      exists_injective_algHom_adjoinRoot_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P) hP hP' k hk with
    ⟨f, hf⟩
  refine ⟨f.range, ?_⟩
  exact ⟨AlgEquiv.ofInjective f hf⟩

/--
Corollary 1.5.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then for every
`k ≥ 1` the local ring `𝕜[X]⧸(P ^ k)` admits the structure of an algebra over `𝕜[X]⧸(P)`.
-/
theorem nonempty_algebra_adjoinRoot_pow_over_adjoinRoot
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) :
    ∀ k : ℕ, 1 ≤ k → Nonempty (Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))) := by
  intro k hk
  rcases
      exists_injective_algHom_adjoinRoot_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P) hP hP' k hk with
    ⟨f, _⟩
  exact ⟨f.toRingHom.toAlgebra⟩

/-- In `AdjoinRoot (P^k)`, the class of `P^n` is the `n`-th power of the class of `P`. -/
lemma mk_pow_eq_pow_mk (P : Polynomial 𝕜) (k n : ℕ) :
    (AdjoinRoot.mk (P ^ k)) (P ^ n) = ((AdjoinRoot.mk (P ^ k)) P) ^ n := by
  simp

/-- In `AdjoinRoot (P^k)`, the class of `P` is nilpotent of index `k`. -/
lemma beta_pow_k_eq_zero (P : Polynomial 𝕜) (k : ℕ) :
    (((AdjoinRoot.mk (P ^ k)) P) ^ k : AdjoinRoot (P ^ k)) = 0 := by
  have hmk : (AdjoinRoot.mk (P ^ k)) (P ^ k) = (0 : AdjoinRoot (P ^ k)) :=
    (AdjoinRoot.mk_eq_zero (f := P ^ k) (g := P ^ k)).2 dvd_rfl
  calc
    (((AdjoinRoot.mk (P ^ k)) P) ^ k : AdjoinRoot (P ^ k)) =
        (AdjoinRoot.mk (P ^ k)) (P ^ k) := by
          simpa using (mk_pow_eq_pow_mk (P := P) (k := k) (n := k)).symm
    _ = 0 := hmk

/-- In `AdjoinRoot (P^k)`, the class of `P^(k-1)` is nonzero when `P` is irreducible and `k ≥ 1`. -/
lemma beta_pow_pred_ne_zero (P : Polynomial 𝕜) (hP : Irreducible P) (k : ℕ) (hk : 1 ≤ k) :
    (((AdjoinRoot.mk (P ^ k)) P) ^ (k - 1) : AdjoinRoot (P ^ k)) ≠ 0 := by
  intro hzero
  have hmk :
      (AdjoinRoot.mk (P ^ k)) (P ^ (k - 1)) = (0 : AdjoinRoot (P ^ k)) := by
    calc
      (AdjoinRoot.mk (P ^ k)) (P ^ (k - 1)) =
          (((AdjoinRoot.mk (P ^ k)) P) ^ (k - 1) : AdjoinRoot (P ^ k)) := by
            simp
      _ = 0 := hzero
  have hdiv : (P ^ k) ∣ (P ^ (k - 1)) :=
    (AdjoinRoot.mk_eq_zero (f := P ^ k) (g := P ^ (k - 1))).1 hmk
  have hle : k ≤ k - 1 := by
    -- Reduce to an inequality of exponents using `pow_dvd_pow_iff`.
    simpa using
      (pow_dvd_pow_iff (a := P) (m := k - 1) (n := k) hP.ne_zero hP.not_isUnit).1 hdiv
  have hkpos : 0 < k := Nat.succ_le_iff.mp (by simpa using hk)
  have hklt : k - 1 < k := by
    -- `k - 1 = k.pred`, and `k.pred < k` for `k ≠ 0`.
    simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hkpos))
  exact (lt_irrefl k) (lt_of_le_of_lt hle hklt)

/-- Descending elimination for relations among `1, β, …, β^(k-1)` in `AdjoinRoot (P^k)`. -/
lemma coeffs_eq_zero_of_sum_smul_pows_eq_zero
    (P : Polynomial 𝕜) (hP : Irreducible P) (k : ℕ) (hk : 1 ≤ k)
    [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    ∀ g : Fin k → AdjoinRoot P,
      (∑ i : Fin k, g i • (((AdjoinRoot.mk (P ^ k)) P) ^ (i : ℕ)) = (0 : AdjoinRoot (P ^ k))) →
        ∀ j : Fin k, g j = 0 := by
  classical
  letI : Fact (Irreducible P) := ⟨hP⟩
  intro g hsum j
  let β : AdjoinRoot (P ^ k) := (AdjoinRoot.mk (P ^ k)) P
  have hβk : (β ^ k : AdjoinRoot (P ^ k)) = 0 := by
    simpa [β] using (beta_pow_k_eq_zero (P := P) (k := k))
  have hβpred : (β ^ (k - 1) : AdjoinRoot (P ^ k)) ≠ 0 := by
    simpa [β] using (beta_pow_pred_ne_zero (P := P) (hP := hP) (k := k) (hk := hk))
  have hsumβ : (∑ i : Fin k, g i • (β ^ (i : ℕ))) = (0 : AdjoinRoot (P ^ k)) := by
    simpa [β] using hsum
  -- Prove all coefficients vanish by strong induction on their index.
  have hgNat : ∀ n : ℕ, ∀ hn : n < k, g ⟨n, hn⟩ = 0 := by
    intro n hn
    refine Nat.strong_induction_on n (fun n ih hn => ?_) hn
    have hnle : n ≤ k - 1 := Nat.le_pred_of_lt hn
    let m : ℕ := k - 1 - n
    have hmulR :
        (∑ i : Fin k, g i • (β ^ (i : ℕ))) * (β ^ m) = (0 : AdjoinRoot (P ^ k)) := by
      -- Multiply the original relation on the right by `β^m`.
      simpa using congrArg (fun x : AdjoinRoot (P ^ k) => x * (β ^ m)) hsumβ
    have hmul :
        (∑ i : Fin k, g i • (β ^ ((i : ℕ) + m))) = (0 : AdjoinRoot (P ^ k)) := by
      -- Rewrite the multiplied relation as a sum of shifted exponents.
      have hmulR' :
          (∑ i : Fin k, (g i • (β ^ (i : ℕ))) * (β ^ m)) = (0 : AdjoinRoot (P ^ k)) := by
        simpa [Finset.sum_mul] using hmulR
      have hsumEq :
          (∑ i : Fin k, g i • (β ^ ((i : ℕ) + m))) =
            ∑ i : Fin k, (g i • (β ^ (i : ℕ))) * (β ^ m) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- Move the scalar through multiplication and combine the powers.
        have hpow :
            (β ^ (i : ℕ)) * (β ^ m) = β ^ ((i : ℕ) + m) := by
          simpa using (pow_add β (i : ℕ) m).symm
        calc
          g i • (β ^ ((i : ℕ) + m)) = g i • ((β ^ (i : ℕ)) * (β ^ m)) := by
            simp [hpow]
          _ = (g i • (β ^ (i : ℕ))) * (β ^ m) := by
            simp
      exact hsumEq.trans hmulR'
    -- Isolate the `n`-th coefficient after multiplying by `β^(k-1-n)`.
    let i0 : Fin k := ⟨n, hn⟩
    have hsum_single :
        (∑ i : Fin k, g i • (β ^ ((i : ℕ) + m))) = g i0 • (β ^ (n + m)) := by
      -- All other terms vanish: those with smaller indices by IH,
      -- those with larger indices since `β^k = 0`.
      have hsum_single' :
          (∑ i ∈ (Finset.univ : Finset (Fin k)), g i • (β ^ ((i : ℕ) + m))) =
            g i0 • (β ^ (n + m)) := by
        refine Finset.sum_eq_single i0 ?_ ?_
        · intro i hi hne
          by_cases hlt : (i : ℕ) < n
          · have hgi : g i = 0 := by
              have hi' : g ⟨(i : ℕ), i.isLt⟩ = 0 :=
                ih (i : ℕ) hlt i.isLt
              simpa [Fin.eta i i.isLt] using hi'
            simp [hgi]
          · have hneval : (i : ℕ) ≠ n := by
              intro hEq
              apply hne
              apply Fin.ext
              simpa [i0] using hEq
            have hgt : n < (i : ℕ) :=
              lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hneval)
            have hn1le : n + 1 ≤ (i : ℕ) := Nat.succ_le_of_lt hgt
            have hm' : m = k - (n + 1) := by
              dsimp [m]
              simp [Nat.sub_sub, Nat.add_comm]
            have hk_le : k ≤ (i : ℕ) + m := by
              have hk0 : (n + 1) + m = k := by
                simpa [hm'] using (Nat.add_sub_of_le (Nat.succ_le_of_lt hn))
              have := Nat.add_le_add_right hn1le m
              simpa [hk0] using this
            have hpow0 : (β ^ ((i : ℕ) + m) : AdjoinRoot (P ^ k)) = 0 :=
              pow_eq_zero_of_le hk_le hβk
            simp [hpow0]
        · intro hi0
          exact False.elim (by simp at hi0)
      simpa using hsum_single'
    have hgi0 :
        g i0 • (β ^ (k - 1) : AdjoinRoot (P ^ k)) = 0 := by
      have hn_m : n + m = k - 1 := by
        simpa [m] using (Nat.add_sub_of_le hnle)
      -- Rewrite the sum as a single term and use `hmul = 0`.
      have : g i0 • (β ^ (n + m) : AdjoinRoot (P ^ k)) = 0 := by
        have hmul' := hmul
        -- Replace the sum with its single surviving term.
        rw [hsum_single] at hmul'
        simpa using hmul'
      -- Rewrite `n + m` as `k - 1`.
      exact hn_m ▸ this
    -- Cancel the nonzero vector `β^(k-1)` to get `g i0 = 0`.
    by_contra hne0
    have hu : IsUnit (g i0) := (isUnit_iff_ne_zero).2 hne0
    have : (β ^ (k - 1) : AdjoinRoot (P ^ k)) = 0 :=
      (IsUnit.smul_eq_zero hu).1 hgi0
    exact hβpred this
  -- Convert the `ℕ`-indexed statement back to `Fin k`.
  have hj' : g ⟨(j : ℕ), j.isLt⟩ = 0 := hgNat (j : ℕ) j.isLt
  simpa [Fin.eta j j.isLt] using hj'

/--
Lemma 1.6.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then for every
`k ≥ 1`, the family `1, P, P^2, …, P^(k-1)` in `𝕜[X]⧸(P^k)` is linearly independent over
`𝕜[X]⧸(P)`.
-/
lemma linearIndependent_powers_mk_adjoinRoot_pow
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    LinearIndependent (AdjoinRoot P)
      (fun i : Fin k => AdjoinRoot.mk (P ^ k) (P ^ (i : ℕ))) := by
  classical
  -- `hP'` is logically irrelevant here (we assume the `Algebra` structure already),
  -- but is part of the textbook statement.
  by_cases hder0 : P.derivative = 0
  · exact False.elim (hP' hder0)
  -- Reduce to vanishing of coefficients in a finite linear combination.
  refine (Fintype.linearIndependent_iff).2 ?_
  intro g hg j
  have hg' :
      (∑ i : Fin k, g i • (((AdjoinRoot.mk (P ^ k)) P) ^ (i : ℕ)) = (0 : AdjoinRoot (P ^ k))) := by
    simpa [mk_pow_eq_pow_mk (P := P) (k := k)] using hg
  exact
    coeffs_eq_zero_of_sum_smul_pows_eq_zero (P := P) (hP := hP) (k := k) (hk := hk) g hg' j

/-- The algebra map `ψₖ` sending the class of `X` in `AdjoinRoot (X^k)` to the class of `P`. -/
noncomputable def psiK
    (P : Polynomial 𝕜) (k : ℕ) [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k) →ₐ[AdjoinRoot P]
      AdjoinRoot (P ^ k) := by
  classical
  let β : AdjoinRoot (P ^ k) := AdjoinRoot.mk (P ^ k) P
  refine
    AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)
      (Algebra.ofId (AdjoinRoot P) (AdjoinRoot (P ^ k))) β ?_
  have hβk : (β ^ k : AdjoinRoot (P ^ k)) = 0 := by
    simpa [β] using (beta_pow_k_eq_zero (P := P) (k := k))
  -- `X` maps to `β`, hence `X^k` maps to `β^k = 0`.
  simp [β, Polynomial.eval₂_pow, hβk]

lemma psiK_def_and_root
    (P : Polynomial 𝕜) (k : ℕ) [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    psiK (P := P) (k := k) (AdjoinRoot.root ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
      AdjoinRoot.mk (P ^ k) P := by
  classical
  simp [psiK, AdjoinRoot.liftAlgHom_root]

/-- Injectivity of `ψₖ`, deduced from the linear independence of `1, P, …, P^(k-1)` (Lemma 1.6). -/
lemma psiK_injective
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    Function.Injective (psiK (P := P) (k := k)) := by
  classical
  haveI : Fact (Irreducible P) := ⟨hP⟩
  let β : AdjoinRoot (P ^ k) := AdjoinRoot.mk (P ^ k) P
  let f : Polynomial (AdjoinRoot P) := (Polynomial.X : Polynomial (AdjoinRoot P)) ^ k
  have hf : f ≠ 0 := by
    simp [f]
  let pb : PowerBasis (AdjoinRoot P) (AdjoinRoot f) := AdjoinRoot.powerBasis (K := AdjoinRoot P) hf
  have hdim : pb.dim = k := by
    simp [pb, f]
  have hpb_gen : pb.gen = AdjoinRoot.root f := by
    simp [pb]
  have hβ_li :
      LinearIndependent (AdjoinRoot P) (fun i : Fin pb.dim => β ^ (i : ℕ)) := by
    have hβ_li' :
        LinearIndependent (AdjoinRoot P) (fun i : Fin k => β ^ (i : ℕ)) := by
      -- This is exactly Lemma 1.6, rewritten from `mk (P^k) (P^i)` to `β^i`.
      simpa [β, mk_pow_eq_pow_mk (P := P) (k := k)] using
        (linearIndependent_powers_mk_adjoinRoot_pow (P := P) (hP := hP) (hP' := hP') (k := k)
          (hk := hk))
    -- Transport along the index equivalence `Fin pb.dim ≃ Fin k`.
    have hβ_li'' :
        LinearIndependent (AdjoinRoot P)
          (fun i : Fin pb.dim => β ^ ((finCongr hdim i) : ℕ)) := by
      simpa using
        (linearIndependent_equiv (finCongr hdim) (f := fun i : Fin k => β ^ (i : ℕ))).2 hβ_li'
    simpa [finCongr_apply_coe] using hβ_li''
  -- First show that the kernel of `ψₖ` is trivial, using the power basis of `AdjoinRoot (X^k)`.
  have hker : ∀ x : AdjoinRoot f, psiK (P := P) (k := k) x = 0 → x = 0 := by
    intro x hx
    let ψ : AdjoinRoot f →ₐ[AdjoinRoot P] AdjoinRoot (P ^ k) := psiK (P := P) (k := k)
    let φ : AdjoinRoot f →ₗ[AdjoinRoot P] AdjoinRoot (P ^ k) := ψ.toLinearMap
    have hx' : φ x = 0 := by
      simpa [φ] using hx
    have hψ_root : ψ (AdjoinRoot.root f) = β := by
      simpa [ψ, f, β] using (psiK_def_and_root (P := P) (k := k))
    have hφ_gen_pow :
        ∀ i : Fin pb.dim,
          φ (pb.gen ^ (i : ℕ) : AdjoinRoot f) = (β ^ (i : ℕ) : AdjoinRoot (P ^ k)) := by
      intro i
      calc
        φ (pb.gen ^ (i : ℕ) : AdjoinRoot f) = ψ (pb.gen ^ (i : ℕ) : AdjoinRoot f) := by
          rfl
        _ = (ψ pb.gen) ^ (i : ℕ) := by
          simp [map_pow]
        _ = (ψ (AdjoinRoot.root f)) ^ (i : ℕ) := by
          simp [hpb_gen]
        _ = (β : AdjoinRoot (P ^ k)) ^ (i : ℕ) := by
          simp [hψ_root]
    -- Expand `x` in the power basis, apply `φ`, and get a linear relation among the `β^i`.
    have hsum0 :
        (∑ i : Fin pb.dim, (pb.basis.repr x i) • (β ^ (i : ℕ) : AdjoinRoot (P ^ k))) = 0 := by
      have hrepr :
          (∑ i : Fin pb.dim, (pb.basis.repr x i) • (pb.basis i : AdjoinRoot f)) = x := by
        simpa using (pb.basis.sum_repr x)
      have hmap0 : φ (∑ i : Fin pb.dim, (pb.basis.repr x i) • (pb.basis i : AdjoinRoot f)) = 0 := by
        simpa [hx'] using congrArg φ hrepr
      have hsum0' :
          (∑ i : Fin pb.dim, (pb.basis.repr x i) • φ (pb.basis i : AdjoinRoot f)) = 0 := by
        simpa [map_sum, LinearMap.map_smul] using hmap0
      simpa [PowerBasis.coe_basis, hφ_gen_pow] using hsum0'
    -- Linear independence forces all coefficients to vanish.
    have hcoeff : ∀ j : Fin pb.dim, (pb.basis.repr x j) = 0 := by
      have hiff := (Fintype.linearIndependent_iff).1 hβ_li
      exact hiff (fun i => pb.basis.repr x i) hsum0
    have hrepro : pb.basis.repr x = 0 := by
      ext j
      exact hcoeff j
    exact (pb.basis.repr.map_eq_zero_iff).1 hrepro
  -- Conclude injectivity.
  intro x y hxy
  -- Work in the domain `AdjoinRoot f`, rewriting via `hdim`.
  have hsub : psiK (P := P) (k := k) (x - y) = 0 := by
    simp [map_sub, hxy]
  have : (x - y : AdjoinRoot f) = 0 := hker (x - y) hsub
  exact sub_eq_zero.mp this

/-- The `AdjoinRoot P`-dimension of `AdjoinRoot (X^k)` is `k`. -/
lemma finrank_domain_over_adjoinRoot_eq_k (P : Polynomial 𝕜) (hP : Irreducible P) (k : ℕ) :
    Module.finrank (AdjoinRoot P) (AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
      k := by
  classical
  haveI : Fact (Irreducible P) := ⟨hP⟩
  set f : Polynomial (AdjoinRoot P) := (Polynomial.X : Polynomial (AdjoinRoot P)) ^ k
  have hf : f ≠ 0 := by
    simp [f]
  -- Use the standard power basis for `AdjoinRoot f` over a field.
  simpa [f, AdjoinRoot.powerBasis_dim (K := AdjoinRoot P) (f := f) hf,
    Polynomial.natDegree_X_pow] using
    (PowerBasis.finrank (AdjoinRoot.powerBasis (K := AdjoinRoot P) hf))

end SomeLocalRings
