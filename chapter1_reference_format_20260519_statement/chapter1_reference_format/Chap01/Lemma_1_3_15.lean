import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_35

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

section

variable {K : Type*} [Field K]

section

variable {S : Type*} [MonoidWithZero S]

/-- Units and left zero divisors are disjoint in any ring-like object with zero. -/
theorem unit_disjoint_zero_divisor :
    Disjoint {x : S | IsUnit x} {x : S | IsLeftZeroDivisor x} := by
  -- A unit is a non-zero-divisor, so any nontrivial annihilator must vanish.
  rw [Set.disjoint_left]
  intro x hxUnit hxZero
  rcases hxZero with ⟨_, y, hy, hyx⟩
  exact hy ((mul_right_mem_nonZeroDivisors_eq_zero_iff hxUnit.mem_nonZeroDivisors).mp hyx)

end

section IsAdjoinRoot

variable {S : Type*} [CommRing S] [Algebra K S] {f : K[X]}

/-- Owner-level form of Lemma 1.3.15 (1): in any `K`-algebra presented by adjoining a root of
`f`, every nonzero element is either a unit or a zero divisor in the chapter sense. -/
theorem isAdjoinRoot_nonzero_eq_unit_or_zero_divisor (h : IsAdjoinRoot S f) (hf : f ≠ 0) :
    {x : S | x ≠ 0} =
      ({x : S | IsUnit x} \ ({0} : Set S)) ∪ {x : S | IsLeftZeroDivisor x} := by
  -- Route correction: the quotient is finite-dimensional over `K`, not finite as a type in
  -- general, so we use the linear endomorphism `y ↦ x * y` on a finite-dimensional space.
  letI : FiniteDimensional K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf).basis.finiteDimensional_of_finite
  letI : FiniteDimensional K S :=
    FiniteDimensional.of_injective
      (h.adjoinRootAlgEquiv.symm.toLinearMap) h.adjoinRootAlgEquiv.symm.injective
  ext x
  constructor
  · intro hx
    by_cases hunit : IsUnit x
    · -- Units give the first half of the textbook partition immediately.
      exact Or.inl ⟨hunit, hx⟩
    · -- A nonunit gives a noninvertible multiplication endomorphism, hence a nontrivial kernel.
      right
      let lx : Module.End K S := Algebra.lmul K S x
      have hlx_not_unit : ¬ IsUnit lx := by
        rwa [Algebra.lmul_isUnit_iff]
      have hker_ne_bot : LinearMap.ker lx ≠ ⊥ := by
        intro hker
        exact hlx_not_unit ((LinearMap.isUnit_iff_ker_eq_bot lx).2 hker)
      obtain ⟨y, hy_mem, hy_ne⟩ := (LinearMap.ker lx).ne_bot_iff.mp hker_ne_bot
      refine ⟨hx, y, hy_ne, ?_⟩
      -- Kernel membership says `x * y = 0`, and commutativity rewrites this as `y * x = 0`.
      simpa [lx, mul_comm] using hy_mem
  · -- Either side of the partition is visibly nonzero.
    rintro (hxUnit | hxZero)
    · exact hxUnit.2
    · exact hxZero.1

/-- Owner-level form of Lemma 1.3.15 (3): the image of `g` is a zero divisor exactly when it is
nonzero and `g` is not coprime to `f`. -/
theorem isAdjoinRoot_map_isLeftZeroDivisor_iff (h : IsAdjoinRoot S f) (hf : f ≠ 0) (g : K[X]) :
    IsLeftZeroDivisor (h.map g) ↔ h.map g ≠ 0 ∧ ¬ IsCoprime g f := by
  constructor
  · intro hgZero
    refine ⟨hgZero.1, ?_⟩
    intro hgCoprime
    -- The Bézout criterion makes `h.map g` a unit, contradicting disjointness with zero divisors.
    have hgUnit : IsUnit (h.map g) := by
      rcases hgCoprime with ⟨a, b, hab⟩
      have hmul : h.map g * h.map a = 1 := by
        simpa [map_add, map_mul, h.map_self, mul_comm] using congrArg h.map hab
      exact IsUnit.of_mul_eq_one (h.map a) hmul
    have hdisj := Set.disjoint_left.mp
      (unit_disjoint_zero_divisor : Disjoint {x : S | IsUnit x} {x : S | IsLeftZeroDivisor x})
    exact hdisj hgUnit hgZero
  · rintro ⟨hg_ne_zero, hg_not_coprime⟩
    -- The nonzero/unit-or-zero-divisor partition leaves only the zero-divisor branch.
    have hg_split :
        h.map g ∈ ({x : S | IsUnit x} \ ({0} : Set S)) ∪ {x : S | IsLeftZeroDivisor x} := by
      rw [← isAdjoinRoot_nonzero_eq_unit_or_zero_divisor h hf]
      exact hg_ne_zero
    rcases hg_split with hgUnit | hgZero
    · have hgCoprime : IsCoprime g f := by
        rcases hgUnit.1.exists_left_inv with ⟨y, hy⟩
        have hdiv : f ∣ h.repr y * g - 1 := by
          rw [← h.map_eq_zero_iff]
          simp [map_sub, map_mul, h.map_repr, hy]
        rcases hdiv with ⟨q, hq⟩
        refine ⟨h.repr y, -q, ?_⟩
        calc
          h.repr y * g + (-q) * f = (f * q + 1) + (-q) * f := by
            rw [sub_eq_iff_eq_add.mp hq]
          _ = 1 := by ring
      exact False.elim (hg_not_coprime hgCoprime)
    · exact hgZero

section

variable [DecidableEq K]

/-- Companion reformulation of the owner-level zero-divisor criterion via `gcd`. -/
theorem isAdjoinRoot_map_isLeftZeroDivisor_iff_gcd_ne_one
    (h : IsAdjoinRoot S f) (hf : f ≠ 0) (g : K[X]) :
    IsLeftZeroDivisor (h.map g) ↔ h.map g ≠ 0 ∧ gcd g f ≠ 1 := by
  -- Rewrite non-coprimality through the normalized gcd in the PID `K[X]`.
  rw [isAdjoinRoot_map_isLeftZeroDivisor_iff h hf g, ← gcd_isUnit_iff, ← normalize_eq_one,
    normalize_gcd]

end

/-- Owner-level form of Lemma 1.3.15 (4): the image of `g` is a unit exactly when `g` and `f`
are coprime. -/
theorem isAdjoinRoot_map_isUnit_iff (h : IsAdjoinRoot S f) (g : K[X]) :
    IsUnit (h.map g) ↔ IsCoprime g f := by
  constructor
  · intro hgUnit
    rcases hgUnit.exists_left_inv with ⟨y, hy⟩
    have hdiv : f ∣ h.repr y * g - 1 := by
      -- Pull the inverse relation back to a polynomial relation modulo `f`.
      rw [← h.map_eq_zero_iff]
      simp [map_sub, map_mul, h.map_repr, hy]
    rcases hdiv with ⟨q, hq⟩
    refine ⟨h.repr y, -q, ?_⟩
    -- Rearranging the divisibility witness yields the Bézout identity for `g` and `f`.
    calc
      h.repr y * g + (-q) * f = (f * q + 1) + (-q) * f := by rw [sub_eq_iff_eq_add.mp hq]
      _ = 1 := by ring
  · rintro ⟨a, b, hab⟩
    -- Mapping the Bézout identity into `S` shows that `h.map a` is an inverse of `h.map g`.
    have hmul : h.map g * h.map a = 1 := by
      simpa [map_add, map_mul, h.map_self, mul_comm] using congrArg h.map hab
    exact IsUnit.of_mul_eq_one (h.map a) hmul

section

variable [DecidableEq K]

/-- Companion reformulation of the owner-level unit criterion via `gcd`. -/
theorem isAdjoinRoot_map_isUnit_iff_gcd_eq_one (h : IsAdjoinRoot S f) (g : K[X]) :
    IsUnit (h.map g) ↔ gcd g f = 1 := by
  -- Rewrite coprimality through the normalized gcd in the PID `K[X]`.
  rw [isAdjoinRoot_map_isUnit_iff h g, ← gcd_isUnit_iff, ← normalize_eq_one,
    normalize_gcd]

end

end IsAdjoinRoot

/-- Lemma 1.3.15 (1): for a nonzero polynomial `f` over a field `K`, every nonzero class in
`K[X] / (f)` is either a unit or a zero divisor in the chapter sense. -/
theorem polynomial_quotient_nonzero_eq_unit_or_zero_divisor {f : K[X]} (hf : f ≠ 0) :
    {x : AdjoinRoot f | x ≠ 0} =
      ({x : AdjoinRoot f | IsUnit x} \ ({0} : Set (AdjoinRoot f))) ∪
        {x : AdjoinRoot f | IsLeftZeroDivisor x} := by
  simpa using isAdjoinRoot_nonzero_eq_unit_or_zero_divisor (AdjoinRoot.isAdjoinRoot f) hf

/-- Lemma 1.3.15 (2): in the quotient `K[X] / (f)`, the units and the zero divisors are
disjoint. -/
theorem polynomial_quotient_unit_disjoint_zero_divisor (f : K[X]) :
    Disjoint {x : AdjoinRoot f | IsUnit x} {x : AdjoinRoot f | IsLeftZeroDivisor x} := by
  simpa using
    (unit_disjoint_zero_divisor :
      Disjoint {x : AdjoinRoot f | IsUnit x} {x : AdjoinRoot f | IsLeftZeroDivisor x})

/-- Lemma 1.3.15 (3): in `K[X] / (f)` with `f ≠ 0`, the class of `g` is a zero divisor exactly
when it is nonzero and `g` is not coprime to `f`. -/
theorem polynomial_quotient_mk_isLeftZeroDivisor_iff {f : K[X]} (hf : f ≠ 0) (g : K[X]) :
    IsLeftZeroDivisor (AdjoinRoot.mk f g) ↔ AdjoinRoot.mk f g ≠ 0 ∧ ¬ IsCoprime g f := by
  simpa using isAdjoinRoot_map_isLeftZeroDivisor_iff (AdjoinRoot.isAdjoinRoot f) hf g

section

variable [DecidableEq K]

/-- Companion reformulation of Lemma 1.3.15 (3): over `K[X]`, non-coprimality is equivalent to
the monic gcd being different from `1`. -/
theorem polynomial_quotient_mk_isLeftZeroDivisor_iff_gcd_ne_one
    {f : K[X]} (hf : f ≠ 0) (g : K[X]) :
    IsLeftZeroDivisor (AdjoinRoot.mk f g) ↔ AdjoinRoot.mk f g ≠ 0 ∧ gcd g f ≠ 1 := by
  simpa using isAdjoinRoot_map_isLeftZeroDivisor_iff_gcd_ne_one (AdjoinRoot.isAdjoinRoot f) hf g

end

/-- Lemma 1.3.15 (4): the class of `g` in `K[X] / (f)` is a unit exactly when `g` and `f` are
coprime. -/
theorem polynomial_quotient_mk_isUnit_iff {f : K[X]} (g : K[X]) :
    IsUnit (AdjoinRoot.mk f g) ↔ IsCoprime g f := by
  simpa using isAdjoinRoot_map_isUnit_iff (AdjoinRoot.isAdjoinRoot f) g

section

variable [DecidableEq K]

/-- Companion reformulation of Lemma 1.3.15 (4): over `K[X]`, coprimality is equivalent to the
monic gcd being `1`. -/
theorem polynomial_quotient_mk_isUnit_iff_gcd_eq_one {f : K[X]} (g : K[X]) :
    IsUnit (AdjoinRoot.mk f g) ↔ gcd g f = 1 := by
  simpa using isAdjoinRoot_map_isUnit_iff_gcd_eq_one (AdjoinRoot.isAdjoinRoot f) g

end

end
