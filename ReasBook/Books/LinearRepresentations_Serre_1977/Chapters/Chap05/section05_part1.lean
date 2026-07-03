import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_5_1_1 (from Chap05) -/
noncomputable section

open scoped Real

section

variable {n : ℕ}
variable [NeZero n]

/- Source/core/bridge triage:
- `source-facing`: LinearRepresentations_Serre_1977's explicit exponential formula for the cyclic character indexed by `h`;
- `core/canonical`: the upstream Pontryagin-duality owner `AddChar.zmodAddEquiv`, built from
  `AddChar.zmod` and `ZMod.toCircle`;
- `bridge/view`: `AddChar.zmodAddEquiv_apply_eq_exp`, which specializes the owner to the textbook
  formula.

This file therefore keeps no primitive data of its own: it recalls the canonical owner and exposes
only the source-facing evaluation formula. -/

/- The finite Pontryagin duality equivalence identifying `ZMod n` with its complex character
group is `AddChar.zmodAddEquiv`. -/
recall AddChar.zmodAddEquiv

namespace AddChar

/-- The canonical cyclic character indexed by `h` evaluates to the textbook exponential
`e^{2π i hk / n}` on the class `k`. -/
theorem zmodAddEquiv_apply_eq_exp (h k : ZMod n) :
    zmodAddEquiv h k =
      Complex.exp (2 * π * Complex.I * ↑((h * k).val) / ↑n) := by
  simpa using (ZMod.toCircle_apply (h * k : ZMod n))

end AddChar

end

/-! ### Definition_5_5_2_1 (from Chap05) -/
/- Source/core/bridge triage:
- `source-facing`: LinearRepresentations_Serre_1977's continuous rotation group `C_infty`, written via angles modulo `2π`
  together with its invariant measure;
- `core/canonical`: the additive circle owner `Real.Angle = AddCircle (2 * π)`;
- `bridge/view`: `Real.Angle.toCircle` realizes an angle class as the corresponding unit complex
  rotation, while the measure statements are recalled from the generic `AddCircle` API specialized
  at period `2 * π`.

This file therefore introduces no primitive data or parallel wrapper API: it only recalls the
canonical owner and its standard bridge/measure declarations already present in mathlib. -/

/- Definition 5-5.2-1: the group `C_infty` of plane rotations is modeled by the canonical
additive circle `Real.Angle = ℝ / 2πℤ`, so composing rotations corresponds to adding angles
modulo `2π`. -/
recall Real.Angle

/- The rotation `r_α` through angle `α`, with `α` taken modulo `2π`, is represented by the
canonical map `Real.Angle.toCircle : Real.Angle → Circle` to the unit complex numbers. -/
recall Real.Angle.toCircle

/- The canonical normalized Haar measure on `Real.Angle = AddCircle (2 * π)` is
`AddCircle.haarAddCircle`. -/
recall AddCircle.haarAddCircle

/- The standard quotient measure on `Real.Angle = AddCircle (2 * π)` is `2π` times
`AddCircle.haarAddCircle`; equivalently, the normalized invariant measure on `C_infty` is
`(1 / (2 * π)) dα`. -/
recall AddCircle.volume_eq_smul_haarAddCircle

/-! ### Definition_5_5_3_1 (from Chap05) -/
/- Source/core/bridge triage:
- `source-facing`: LinearRepresentations_Serre_1977's presentation of the finite dihedral group by the generators `r` and `s`
  with the relations `r^n = 1`, `s^2 = 1`, and `srs = r⁻¹`;
- `core/canonical`: mathlib's owner `DihedralGroup n`, together with its canonical constructors
  `DihedralGroup.r`, `DihedralGroup.sr` and the upstream formulas for multiplication, inversion,
  normal form, and cardinality;
- `bridge/view`: the single source-facing conjugation theorem below, which packages the primitive
  multiplication rules into the textbook relation `srs = r⁻¹`.

Primitive/derived split:
- primitive data: none is re-owned in this file; all group structure and canonical API come
  directly from `DihedralGroup n`;
- derived API: only the source-facing conjugation relation is stated locally, since mathlib already
  owns the underlying multiplication and inverse formulas. -/

/- Definition 5-5.3-1: for `n ≠ 0`, the dihedral group of the regular `n`-gon is the canonical
mathlib group `DihedralGroup n`, whose elements are the rotations `DihedralGroup.r i` and the
reflections `DihedralGroup.sr i` indexed by `i : ZMod n`. -/
recall DihedralGroup

/- The canonical rotation generator `DihedralGroup.r 1` satisfies the textbook relation
`r ^ n = 1`. -/
recall DihedralGroup.r_one_pow_n

/- Each canonical reflection `DihedralGroup.sr i` has square `1`; in particular the basic
reflection `DihedralGroup.sr 0` satisfies `s ^ 2 = 1`. -/
recall DihedralGroup.sr_mul_self

/- The inverse of the rotation `DihedralGroup.r j` is the rotation `DihedralGroup.r (-j)`. -/
recall DihedralGroup.inv_r

namespace DihedralGroup

-- Proof sketch: combine the canonical multiplication formulas `sr_mul_r` and `sr_mul_sr`, then
-- rewrite the resulting rotation `r (-j)` using the canonical inverse formula `inv_r`.
/-- Conjugating a rotation by a reflection gives the inverse rotation; the textbook relation
`sr 0 * r 1 * sr 0 = (r 1)⁻¹` is the specialization `i = 0`, `j = 1`. -/
theorem sr_mul_r_mul_sr_eq_inv_r (i j : ZMod n) :
    sr i * r j * sr i = (r j)⁻¹ := by
  simp

end DihedralGroup

/- The canonical equivalence `DihedralGroup.equivSum` expresses the unique normal form in which
every element is either a rotation `r^k` or a reflection `sr^k`. -/
recall DihedralGroup.equivSum

/- For `n ≠ 0`, the finite dihedral group has order `2n`. -/
recall DihedralGroup.card

/-! ### Exercise_5_5_3_3 (from Chap05) -/
section

variable (n : ℕ) [NeZero n]

private def halfTurn : ZMod n := (n / 2 : ℕ)

omit [NeZero n] in
private lemma halfTurn_add_self (heven : Even n) : halfTurn n + halfTurn n = (0 : ZMod n) := by
  calc
    halfTurn n + halfTurn n = ((2 * (n / 2) : ℕ) : ZMod n) := by
      simp [halfTurn, two_mul, Nat.cast_add]
    _ = (n : ZMod n) := by rw [Nat.two_mul_div_two_of_even heven]
    _ = 0 := ZMod.natCast_self n

private lemma halfTurn_ne_zero (heven : Even n) : halfTurn n ≠ (0 : ZMod n) := by
  intro hzero
  have hcast : ((n / 2 : ℕ) : ZMod n) = 0 := by
    simpa [halfTurn] using hzero
  have hdiv : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp hcast
  have hhalfpos : 0 < n / 2 := by
    have hn : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
    have hpos : 0 < n := Nat.pos_of_neZero n
    omega
  have hle : n ≤ n / 2 := Nat.le_of_dvd hhalfpos hdiv
  omega

private lemma eq_zero_or_eq_halfTurn (a : ZMod n) (ha : a + a = 0) :
    a = 0 ∨ a = halfTurn n := by
  rcases (ZMod.neg_eq_self_iff a).mp (neg_eq_iff_add_eq_zero.mpr ha) with rfl | hval
  · exact Or.inl rfl
  · right
    rw [← a.natCast_zmod_val]
    have hdiv : a.val = n / 2 := Nat.eq_div_of_mul_eq_right (by decide : 2 ≠ 0) (by omega)
    simp [halfTurn, hdiv]

omit [NeZero n] in
private lemma commute_r_sr_iff (i j : ZMod n) :
    Commute (DihedralGroup.r i) (DihedralGroup.sr j) ↔ i + i = 0 := by
  constructor
  · intro h
    have hs0 : j + -i = j + i := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.eq
    have hs : -i = i := add_left_cancel hs0
    simpa [two_mul] using eq_neg_iff_add_eq_zero.mp hs.symm
  · intro h
    have hs : i = -i := eq_neg_iff_add_eq_zero.mpr (by simpa [two_mul] using h)
    change DihedralGroup.r i * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.r i
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, sub_eq_add_neg, ← hs, add_comm]

omit [NeZero n] in
private lemma commute_sr_r_iff (i j : ZMod n) :
    Commute (DihedralGroup.sr i) (DihedralGroup.r j) ↔ j + j = 0 := by
  constructor
  · intro h
    have hs0 : i + j = i + -j := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.eq
    have hs : j = -j := add_left_cancel hs0
    simpa [two_mul] using eq_neg_iff_add_eq_zero.mp hs
  · intro h
    have hs : j = -j := eq_neg_iff_add_eq_zero.mpr (by simpa [two_mul] using h)
    change DihedralGroup.sr i * DihedralGroup.r j = DihedralGroup.r j * DihedralGroup.sr i
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, ← hs]

omit [NeZero n] in
private lemma commute_sr_sr_iff (i j : ZMod n) :
    Commute (DihedralGroup.sr i) (DihedralGroup.sr j) ↔ (j - i) + (j - i) = 0 := by
  constructor
  · intro h
    have hs0 : j - i = i - j := by simpa using h.eq
    have hs : j - i = -(j - i) := by
      calc
        j - i = i - j := hs0
        _ = -(j - i) := by abel
    simpa using eq_neg_iff_add_eq_zero.mp hs
  · intro h
    have hs : j - i = i - j := by
      have hneg : j - i = -(j - i) := eq_neg_iff_add_eq_zero.mpr h
      calc
        j - i = -(j - i) := hneg
        _ = i - j := by abel
    change DihedralGroup.sr i * DihedralGroup.sr j = DihedralGroup.sr j * DihedralGroup.sr i
    rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr, hs]

private abbrev EvenCommuteCode (n : ℕ) :=
  (ZMod n × ZMod n) ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n

private def evenCommuteEquiv (heven : Even n) :
    { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃ EvenCommuteCode n :=
  { toFun := fun
      | ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, _⟩ => .inl (i, j)
      | ⟨⟨DihedralGroup.r i, DihedralGroup.sr j⟩, _⟩ =>
          if i = 0 then .inr (.inl j) else .inr (.inr (.inl j))
      | ⟨⟨DihedralGroup.sr i, DihedralGroup.r j⟩, _⟩ =>
          if j = 0 then .inr (.inr (.inr (.inl i))) else .inr (.inr (.inr (.inr (.inl i))))
      | ⟨⟨DihedralGroup.sr i, DihedralGroup.sr j⟩, _⟩ =>
          if j - i = 0 then .inr (.inr (.inr (.inr (.inr (.inl i)))))
          else .inr (.inr (.inr (.inr (.inr (.inr i)))))
    invFun := fun
      | .inl (i, j) =>
          ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, by
            change DihedralGroup.r i * DihedralGroup.r j = DihedralGroup.r j * DihedralGroup.r i
            rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]⟩
      | .inr (.inl j) =>
          ⟨⟨DihedralGroup.r 0, DihedralGroup.sr j⟩,
            (commute_r_sr_iff n 0 j).2 (by simp)⟩
      | .inr (.inr (.inl j)) =>
          ⟨⟨DihedralGroup.r (halfTurn n), DihedralGroup.sr j⟩,
            (commute_r_sr_iff n (halfTurn n) j).2 (halfTurn_add_self n heven)⟩
      | .inr (.inr (.inr (.inl i))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.r 0⟩,
            (commute_sr_r_iff n i 0).2 (by simp)⟩
      | .inr (.inr (.inr (.inr (.inl i)))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.r (halfTurn n)⟩,
            (commute_sr_r_iff n i (halfTurn n)).2 (halfTurn_add_self n heven)⟩
      | .inr (.inr (.inr (.inr (.inr (.inl i))))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.sr i⟩,
            (commute_sr_sr_iff n i i).2 (by simp)⟩
      | .inr (.inr (.inr (.inr (.inr (.inr i))))) =>
          ⟨⟨DihedralGroup.sr i, DihedralGroup.sr (i + halfTurn n)⟩,
            (commute_sr_sr_iff n i (i + halfTurn n)).2 (by
              simpa [sub_eq_add_neg, add_assoc] using halfTurn_add_self n heven)⟩
    left_inv := by
      rintro ⟨⟨i | i, j | j⟩, hij⟩
      · rfl
      · dsimp
        split_ifs with hi
        · subst hi
          rfl
        · have hi' := eq_zero_or_eq_halfTurn n i ((commute_r_sr_iff n i j).mp hij)
          rcases hi' with rfl | hi' <;> try contradiction
          subst hi'
          rfl
      · dsimp
        split_ifs with hj
        · subst hj
          rfl
        · have hj' := eq_zero_or_eq_halfTurn n j ((commute_sr_r_iff n i j).mp hij)
          rcases hj' with rfl | hj' <;> try contradiction
          subst hj'
          rfl
      · dsimp
        split_ifs with hji
        · have : j = i := sub_eq_zero.mp hji
          subst this
          rfl
        · have hji' := eq_zero_or_eq_halfTurn n (j - i) ((commute_sr_sr_iff n i j).mp hij)
          rcases hji' with hzero | hhalf
          · contradiction
          · have : j = i + halfTurn n := by
              calc
                j = i + (j - i) := by abel
                _ = i + halfTurn n := by rw [hhalf]
            subst this
            rfl
    right_inv := by
      intro x
      cases x with
      | inl ij =>
          cases ij
          rfl
      | inr x =>
          cases x with
          | inl j => simp
          | inr x =>
              cases x with
              | inl j => simp [halfTurn_ne_zero n heven]
              | inr x =>
                  cases x with
                  | inl i => simp
                  | inr x =>
                      cases x with
                      | inl i => simp [halfTurn_ne_zero n heven]
                      | inr x =>
                          cases x with
                          | inl i => simp
                          | inr i => simp [halfTurn_ne_zero n heven] }

private lemma card_commute_even (heven : Even n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 6) := by
  rw [Nat.card_congr (evenCommuteEquiv n heven)]
  simp_rw [Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

/-
Source/core/bridge triage for Exercise `5-5.3-3`:
* source-facing: the reflections and rotations of `DihedralGroup n` contribute separate
  conjugacy-class counts, and the total number of conjugacy classes matches the number of
  irreducible characters described earlier in Chapter `5`.
* core/canonical: the owner of the total class count is `Nat.card (ConjClasses (DihedralGroup n))`.
* bridge/view: the final comparison theorem rewrites the total class count into the explicit
  Chapter `5` count `2 + (n - 1) / 2` in the odd case and `4 + (n / 2 - 1)` in the even case.

The odd branch of the total count is already owned by mathlib as
`DihedralGroup.card_conjClasses_odd`; this file supplies the missing even branch and keeps the
source-facing rotation/reflection decomposition visible in the public API.
-/
-- Proof sketch: for even `n`, the reflections split into two conjugacy classes while the
-- rotations are indexed by the unordered pairs `{i, -i}`, with fixed points `0` and `n / 2`,
-- giving `n / 2 + 1` rotation classes. Combined with the canonical odd branch from mathlib, this
-- yields the stated parity-dependent formula.
namespace DihedralGroup

/-- Helper for Exercise 5-5.3-3: conjugacy classes with a reflection representative. -/
private abbrev ReflectionConjClasses (n : ℕ) [NeZero n] :=
  { C : ConjClasses (DihedralGroup n) // ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i) }

/-- Helper for Exercise 5-5.3-3: conjugacy classes with a rotation representative. -/
private abbrev RotationConjClasses (n : ℕ) [NeZero n] :=
  { C : ConjClasses (DihedralGroup n) // ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i) }

/-- Helper for Exercise 5-5.3-3: the total number of conjugacy classes is the expected parity
formula. -/
private lemma card_conjClasses_by_parity :
    Nat.card (ConjClasses (DihedralGroup n)) =
      if Even n then n / 2 + 3 else (n + 3) / 2 := by
  by_cases heven : Even n
  · -- The even branch comes from the commuting-pair count already established above.
    rw [if_pos heven]
    have hn : 0 < n := Nat.pos_of_neZero n
    calc
      Nat.card (ConjClasses (DihedralGroup n)) = (n + 6) / 2 := by
        rw [← Nat.mul_div_mul_left (n + 6) 2 hn, ← card_commute_even n heven, mul_comm,
          card_comm_eq_card_conjClasses_mul_card, nat_card,
          Nat.mul_div_left _ (mul_pos two_pos hn)]
      _ = n / 2 + 3 := by
        have htwo : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
        omega
  · -- The odd branch is already available from mathlib.
    rw [if_neg heven]
    exact card_conjClasses_odd (Nat.not_even_iff_odd.mp heven)

/-- Helper for Exercise 5-5.3-3: when `n` is odd, every reflection is conjugate to `sr 0`. -/
private lemma reflection_class_eq_sr_zero_of_odd (hodd : Odd n) (i : ZMod n) :
    ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 0) := by
  -- Odd order makes `2` invertible in `ZMod n`, so a suitable rotation shifts the index to `0`.
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rw [isConj_iff]
  let u : (ZMod n)ˣ :=
    ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat)
  let a : ZMod n := u⁻¹ * i
  refine ⟨DihedralGroup.r a, ?_⟩
  have hu : (2 : ZMod n) * a = i := by
    simpa [u, a, mul_assoc] using u.mul_inv_cancel_left i
  have hdouble : a + a = i := by
    simpa [two_mul, a, add_comm, add_left_comm, add_assoc] using hu
  calc
    DihedralGroup.r a * DihedralGroup.sr i * (DihedralGroup.r a)⁻¹
        = DihedralGroup.sr (i - (a + a)) := by
            simp [sub_eq_add_neg, add_assoc]
    _ = DihedralGroup.sr 0 := by rw [hdouble, sub_self]

/-- Helper for Exercise 5-5.3-3: an even dihedral group has no solution to `2a = 1` in
`ZMod n`. -/
private lemma double_ne_one_of_even (heven : Even n) (a : ZMod n) :
    a + a ≠ (1 : ZMod n) := by
  -- Reduce the equation modulo `2`, where doubling is identically zero.
  intro h
  let f : ZMod n →+* ZMod 2 := ZMod.castHom heven.two_dvd (ZMod 2)
  have hmap := congrArg f h
  rw [map_add] at hmap
  have hone : (ZMod.cast (1 : ZMod n) : ZMod 2) = (1 : ZMod 2) := ZMod.cast_one heven.two_dvd
  have hmap' : (ZMod.cast a : ZMod 2) + ZMod.cast a = (1 : ZMod 2) := by
    simpa [f, hone] using hmap
  have hdouble_zero : (ZMod.cast a : ZMod 2) + ZMod.cast a = (0 : ZMod 2) := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      (ZMod.cast a : ZMod 2) + ZMod.cast a = (2 : ZMod 2) * ZMod.cast a := by ring
      _ = 0 := by rw [htwo, zero_mul]
  exact zero_ne_one (hdouble_zero.symm.trans hmap')

/-- Helper for Exercise 5-5.3-3: when `n` is even, each reflection is conjugate to either `sr 0`
or `sr 1` according to the parity of its index. -/
private lemma reflection_class_eq_sr_zero_or_sr_one_of_even (heven : Even n) (i : ZMod n) :
    ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 0) ∨
      ConjClasses.mk (DihedralGroup.sr i) = ConjClasses.mk (DihedralGroup.sr 1) := by
  -- Splitting the index by parity gives exactly the two reflection orbits.
  have hi : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i
  rcases Nat.even_or_odd i.val with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨DihedralGroup.r k, ?_⟩
    calc
      DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹
          = DihedralGroup.sr (i - ((k : ZMod n) + (k : ZMod n))) := by
              simp [sub_eq_add_neg, add_assoc]
      _ = DihedralGroup.sr (((k + k : ℕ) : ZMod n) - ((k : ZMod n) + (k : ZMod n))) := by
            rw [← hi, hk]
      _ = DihedralGroup.sr 0 := by
            simp [two_mul, Nat.cast_mul]
  · right
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨DihedralGroup.r k, ?_⟩
    calc
      DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹
          = DihedralGroup.sr (i - ((k : ZMod n) + (k : ZMod n))) := by
              simp [sub_eq_add_neg, add_assoc]
      _ = DihedralGroup.sr (((2 * k + 1 : ℕ) : ZMod n) - ((k : ZMod n) + (k : ZMod n))) := by
            rw [← hi, hk]
      _ = DihedralGroup.sr 1 := by
            simp [two_mul, Nat.cast_add, Nat.cast_mul]

/-- Helper for Exercise 5-5.3-3: the two even reflection classes are distinct. -/
private lemma mk_sr_zero_ne_mk_sr_one_of_even (heven : Even n) :
    ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) ≠
      ConjClasses.mk (DihedralGroup.sr (1 : ZMod n)) := by
  intro hclass
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hclass
  rcases hclass with ⟨g, hg⟩
  cases g with
  | r a =>
      have hdouble : (-a) + (-a) = (1 : ZMod n) := by
        apply DihedralGroup.sr.inj
        simpa [sub_eq_add_neg, add_assoc, two_mul] using hg
      exact double_ne_one_of_even n heven (-a) hdouble
  | sr a =>
      have hdouble : a + a = (1 : ZMod n) := by
        apply DihedralGroup.sr.inj
        simpa [sub_eq_add_neg, add_assoc, two_mul] using hg
      exact double_ne_one_of_even n heven a hdouble

/-- Helper for Exercise 5-5.3-3: a rotation is never conjugate to a reflection. -/
private lemma not_isConj_r_sr (i j : ZMod n) :
    ¬ IsConj (DihedralGroup.r i) (DihedralGroup.sr j) := by
  intro hconj
  rw [isConj_iff] at hconj
  rcases hconj with ⟨g, hg⟩
  cases g with
  | r a =>
      have : DihedralGroup.r i = DihedralGroup.sr j := by
        simpa [sub_eq_add_neg, add_assoc] using hg
      cases this
  | sr a =>
      have : DihedralGroup.r (-i) = DihedralGroup.sr j := by
        simpa [sub_eq_add_neg, add_assoc] using hg
      cases this

/-- Helper for Exercise 5-5.3-3: the full set of conjugacy classes splits into the rotation
classes and the reflection classes. -/
private lemma card_conjClasses_eq_rotation_add_reflection :
    Nat.card (ConjClasses (DihedralGroup n)) =
      Nat.card (RotationConjClasses n) + Nat.card (ReflectionConjClasses n) := by
  classical
  let p : ConjClasses (DihedralGroup n) → Prop :=
    fun C => ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i)
  let q : ConjClasses (DihedralGroup n) → Prop :=
    fun C => ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)
  have hcompl : ∀ C : ConjClasses (DihedralGroup n), ¬ p C ↔ q C := by
    intro C
    constructor
    · intro hC
      -- Every class has a representative, so a class outside the rotation side must come from a
      -- reflection representative.
      obtain ⟨g, hg⟩ := ConjClasses.exists_rep C
      cases g with
      | r i =>
          exact False.elim (hC ⟨i, hg.symm⟩)
      | sr i =>
          exact ⟨i, hg.symm⟩
    · rintro ⟨i, hi⟩ ⟨j, hj⟩
      -- Route correction: use the predicate-complement split rather than `Quotient.out`; the
      -- disjointness is exactly the statement that rotations are never conjugate to reflections.
      exact not_isConj_r_sr (n := n) j i <|
        (ConjClasses.mk_eq_mk_iff_isConj).mp (hj.symm.trans hi)
  let e :
      ConjClasses (DihedralGroup n) ≃
        { C : ConjClasses (DihedralGroup n) // p C } ⊕
          { C : ConjClasses (DihedralGroup n) // q C } :=
    (Equiv.sumCompl p).symm.trans
      (Equiv.sumCongr
        (Equiv.subtypeEquivRight fun _ => Iff.rfl)
        (Equiv.subtypeEquivRight hcompl))
  -- Count the two disjoint families using the canonical sum decomposition of all conjugacy
  -- classes.
  rw [Nat.card_congr e, Nat.card_sum]

/-- Exercise 5-5.3-3: the reflection elements of `DihedralGroup n` contribute one conjugacy class
for odd `n` and two conjugacy classes for even `n`. -/
theorem card_reflection_conjClasses :
    Nat.card { C : ConjClasses (DihedralGroup n) //
        ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i) } =
      if Even n then 2 else 1 := by
  change Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1
  classical
  by_cases heven : Even n
  · rw [if_pos heven]
    have hreflect :
        ∀ C : ConjClasses (DihedralGroup n),
          (∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)) ↔
            C = ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) ∨
              C = ConjClasses.mk (DihedralGroup.sr (1 : ZMod n)) := by
      intro C
      constructor
      · rintro ⟨i, rfl⟩
        exact reflection_class_eq_sr_zero_or_sr_one_of_even (n := n) heven i
      · rintro (hC | hC)
        · exact ⟨0, hC⟩
        · exact ⟨1, hC⟩
    -- The even branch reduces to the two distinct classes represented by `sr 0` and `sr 1`.
    rw [Nat.card_congr (Equiv.subtypeEquivRight hreflect), Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_eq_or_eq_of_ne (mk_sr_zero_ne_mk_sr_one_of_even (n := n) heven)
  · rw [if_neg heven]
    rcases Nat.not_even_iff_odd.mp heven with hodd
    have hreflect :
        ∀ C : ConjClasses (DihedralGroup n),
          (∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.sr i)) ↔
            C = ConjClasses.mk (DihedralGroup.sr (0 : ZMod n)) := by
      intro C
      constructor
      · rintro ⟨i, rfl⟩
        exact reflection_class_eq_sr_zero_of_odd (n := n) hodd i
      · intro hC
        exact ⟨0, hC⟩
    -- In the odd branch, all reflections collapse to the single class of `sr 0`.
    rw [Nat.card_congr (Equiv.subtypeEquivRight hreflect), Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_eq _

/-- Exercise 5-5.3-3: the rotation elements of `DihedralGroup n` contribute `(n + 1) / 2`
conjugacy classes for odd `n` and `n / 2 + 1` conjugacy classes for even `n`. -/
theorem card_rotation_conjClasses :
    Nat.card { C : ConjClasses (DihedralGroup n) //
        ∃ i : ZMod n, C = ConjClasses.mk (DihedralGroup.r i) } =
      if Even n then n / 2 + 1 else (n + 1) / 2 := by
  change Nat.card (RotationConjClasses n) = if Even n then n / 2 + 1 else (n + 1) / 2
  by_cases heven : Even n
  · rw [if_pos heven]
    have hsplit := card_conjClasses_eq_rotation_add_reflection (n := n)
    have htotal := card_conjClasses_by_parity (n := n)
    have hreflect : Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1 := by
      simpa [ReflectionConjClasses] using (card_reflection_conjClasses (n := n))
    rw [if_pos heven] at htotal hreflect
    -- Once the total number of classes and the reflection contribution are fixed, the rotation
    -- count is the remaining summand.
    omega
  · rw [if_neg heven]
    have hsplit := card_conjClasses_eq_rotation_add_reflection (n := n)
    have htotal := card_conjClasses_by_parity (n := n)
    have hreflect : Nat.card (ReflectionConjClasses n) = if Even n then 2 else 1 := by
      simpa [ReflectionConjClasses] using (card_reflection_conjClasses (n := n))
    rw [if_neg heven] at htotal hreflect
    -- The odd branch is the same subtraction after rewriting the parity-dependent totals.
    omega

/-- If `n` is even, then `DihedralGroup n` has `n / 2 + 3` conjugacy classes. -/
theorem card_conjClasses_even (heven : Even n) :
    Nat.card (ConjClasses (DihedralGroup n)) = n / 2 + 3 := by
  have hn : 0 < n := Nat.pos_of_neZero n
  calc
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 6) / 2 := by
      rw [← Nat.mul_div_mul_left (n + 6) 2 hn, ← card_commute_even n heven, mul_comm,
        card_comm_eq_card_conjClasses_mul_card, nat_card,
        Nat.mul_div_left _ (mul_pos two_pos hn)]
    _ = n / 2 + 3 := by
      have htwo : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
      omega

/-- Exercise 5-5.3-3: the number of conjugacy classes of `DihedralGroup n` is `n / 2 + 3` for
even `n` and `(n + 3) / 2` for odd `n`, matching the textbook count of irreducible characters. -/
theorem card_conjClasses :
    Nat.card (ConjClasses (DihedralGroup n)) =
      if Even n then n / 2 + 3 else (n + 3) / 2 := by
  by_cases heven : Even n
  · rw [if_pos heven]
    exact card_conjClasses_even n heven
  · rw [if_neg heven]
    exact card_conjClasses_odd (Nat.not_even_iff_odd.mp heven)

/-- Exercise 5-5.3-3: the conjugacy-class count agrees with the Chapter `5` list of irreducible
characters, namely two degree-`1` characters plus `(n - 1) / 2` two-dimensional characters when
`n` is odd, and four degree-`1` characters plus `n / 2 - 1` two-dimensional characters when `n`
is even. -/
theorem card_conjClasses_eq_irreducible_character_count :
    Nat.card (ConjClasses (DihedralGroup n)) =
      (if Even n then 4 else 2) + (if Even n then n / 2 - 1 else (n - 1) / 2) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  rw [card_conjClasses]
  by_cases heven : Even n
  · rw [if_pos heven, if_pos heven, if_pos heven]
    rcases heven with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    omega
  · rw [if_neg heven, if_neg heven, if_neg heven]
    rcases Nat.not_even_iff_odd.mp heven with ⟨k, rfl⟩
    norm_num [Nat.add_assoc]
    omega

end DihedralGroup

end

/-! ### Exercise_5_5_3_4 (from Chap05) -/
open scoped TensorProduct

noncomputable section
open scoped DihedralCharacter

/- Source/core/bridge triage:
- `source-facing`: the Chapter 5 character identities for `χ_h`, `ψ₁`, and `ψ₂`;
- `core/canonical`: the existing owners `ρ[n] ^ h`, `Representation.character`, `Sym²`, `Alt²`,
  and `Representation.char_symmetricSquare_add_char_alternatingSquare`;
- `bridge/view`: this file only identifies the source-facing dihedral characters with the canonical
  symmetric- and alternating-square character owners.

Primitive data already lives in `Proposition_5_5_3_2` and `Proposition_2_2_1_3`. This file should
therefore keep only source-facing consequences and direct reuse of those owners, without adding a
parallel wrapper API. -/

section

variable (n : ℕ) [NeZero n]

-- Proof sketch: evaluate both sides on rotations and reflections using the explicit formulas from
-- Proposition 5-5.3-2 and the multiplicativity relation for the cyclic characters appearing on the
-- rotation subgroup.
/-- Exercise 5-5.3-4: the product of the dihedral characters `χ_h` and `χ_{h'}` is
`χ_{h + h'} + χ_{h - h'}`. -/
theorem dihedralTwoDimensionalCharacter_mul (h h' : ZMod n) :
    χ_ h * χ_ h' = χ_ (h + h') + χ_ (h - h') := by
  ext g
  cases g with
  | r k =>
      -- On rotations, expand every `χ` into the two cyclic characters from Proposition 5-5.3-2.
      simp only [Pi.mul_apply, Pi.add_apply, dihedralTwoDimensionalCharacter_apply_r]
      -- The four target summands are exactly the additive-character products indexed by
      -- `h + h'`, `h - h'`, `-(h + h')`, and `-(h - h')`.
      have hadd :
          AddChar.zmodAddEquiv (h + h') k =
            AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv h' k := by
        simpa using congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h h')
      have hsub :
          AddChar.zmodAddEquiv (h - h') k =
            AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h') k := by
        simpa [sub_eq_add_neg] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h (-h')))
      have hnegadd :
          AddChar.zmodAddEquiv (-(h + h')) k =
            AddChar.zmodAddEquiv (-h) k * AddChar.zmodAddEquiv (-h') k := by
        simpa [add_comm] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv (-h) (-h')))
      have hnegsub :
          AddChar.zmodAddEquiv (-(h - h')) k =
            AddChar.zmodAddEquiv (-h) k * AddChar.zmodAddEquiv h' k := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using
          (congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv (-h) h'))
      rw [hadd, hsub, hnegadd, hnegsub]
      ring
  | sr k =>
      -- On reflections, every two-dimensional dihedral character vanishes.
      simp [Pi.mul_apply, Pi.add_apply, dihedralTwoDimensionalCharacter_apply_sr]

-- Proof sketch: specialize `dihedralTwoDimensionalCharacter_mul` to `h' = h` and simplify the
-- two indices `h + h` and `h - h`.
/-- Squaring `χ_h` gives `χ_{2h} + χ_0` in LinearRepresentations_Serre_1977's notation. -/
theorem dihedralTwoDimensionalCharacter_mul_self (h : ZMod n) :
    χ_ h * χ_ h = χ_ (h + h) + χ_ (0 : ZMod n) := by
  simpa using dihedralTwoDimensionalCharacter_mul n h h

-- Proof sketch: evaluate `χ_0` on rotations and reflections from the explicit formulas in
-- Proposition 5-5.3-2 and compare with the values of the trivial and reflection-sign characters.
/-- The character `χ_0` decomposes as the sum `ψ₁ + ψ₂`. -/
theorem dihedralTwoDimensionalCharacter_zero_eq_trivial_add_reflectionSign :
    χ_ (0 : ZMod n) = ψ₁[n] + ψ₂[n] := by
  ext g
  cases g with
  | r k =>
      -- On rotations, `χ_0` and `ψ₁ + ψ₂` both reduce to `1 + 1`.
      rw [Pi.add_apply, dihedralTwoDimensionalCharacter_apply_r, dihedralTrivialCharacter_apply,
        dihedralReflectionSignCharacter_apply_r]
      simp [AddChar.circleEquivComplex]
  | sr k =>
      -- On reflections, `χ_0` is zero and `ψ₁ + ψ₂` is `1 + (-1)`.
      rw [Pi.add_apply, dihedralTwoDimensionalCharacter_apply_sr, dihedralTrivialCharacter_apply,
        dihedralReflectionSignCharacter_apply_sr]
      norm_num

section SymmetricAlternatingSquareCharacters

variable (h : ZMod n)

-- Proof sketch: apply the alternating-square character formula from Proposition 2-2.1-3 to
-- `ρ^h`, then use the explicit values of `χ_h` on rotations and reflections to identify the
-- resulting one-dimensional character.
/-- The reflection-sign character `ψ₂` is the character of the alternating square of `ρ^h`. -/
theorem dihedralAlternatingSquare_character_eq_reflectionSign :
    (Alt² (ρ[n] ^ h)).character = ψ₂[n] := by
  ext g
  cases g with
  | r k =>
      -- On rotations, the alternating-square character is the half-difference formula from
      -- Proposition 2-2.1-3 applied to the explicit values of `χ_h`.
      rw [Representation.char_alternatingSquare]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      rw [show (DihedralGroup.r k : DihedralGroup n) ^ 2 = DihedralGroup.r (k + k) by
        simp [pow_two]]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      -- The two cyclic summands are inverse to each other, so the half-difference collapses to `1`.
      have hzero :
          AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h) k = 1 := by
        have hsum :
            AddChar.zmodAddEquiv (h + -h) k =
              AddChar.zmodAddEquiv h k * AddChar.zmodAddEquiv (-h) k := by
          simpa using congrArg (fun φ => φ k) (map_add AddChar.zmodAddEquiv h (-h))
        simpa [AddChar.circleEquivComplex] using hsum.symm
      have hsq :
          AddChar.zmodAddEquiv h (k + k) = AddChar.zmodAddEquiv h k ^ 2 := by
        simpa [pow_two] using AddChar.map_add_eq_mul (AddChar.zmodAddEquiv h) k k
      have hsq_neg :
          AddChar.zmodAddEquiv (-h) (k + k) = AddChar.zmodAddEquiv (-h) k ^ 2 := by
        simpa [pow_two] using AddChar.map_add_eq_mul (AddChar.zmodAddEquiv (-h)) k k
      rw [hsq, hsq_neg]
      -- After rewriting `χ_h(r^{2k})` as the sum of squares, the half-difference reduces to `1`.
      field_simp [two_ne_zero]
      ring_nf
      rw [hzero]
      have hψ : ψ₂[n] (DihedralGroup.r k) = 1 := dihedralReflectionSignCharacter_apply_r (n := n) k
      norm_num [hψ]
  | sr k =>
      -- On reflections, the same half-difference formula uses `sr^k * sr^k = 1` and yields `-1`.
      rw [Representation.char_alternatingSquare]
      rw [dihedralTwoDimensionalCharacter_apply_sr]
      rw [show (DihedralGroup.sr k : DihedralGroup n) ^ 2 = DihedralGroup.r 0 by simp [pow_two]]
      rw [dihedralTwoDimensionalCharacter_apply_r]
      norm_num [AddChar.circleEquivComplex]
      simpa using (dihedralReflectionSignCharacter_apply_sr (n := n) k).symm

-- Proof sketch: use the canonical identity
-- `Representation.char_symmetricSquare_add_char_alternatingSquare` and substitute the source-facing
-- Chapter 5 descriptions of `χ_h * χ_h`, `χ_0`, and `Alt²(ρ^h)`.
/-- The character of the symmetric square of `ρ^h` is `χ_{2h} + ψ₁`. -/
theorem dihedralSymmetricSquare_character_eq_double_add_trivial :
    (Sym² (ρ[n] ^ h)).character = χ_ (h + h) + ψ₁[n] := by
  ext g
  have hchar :
      ((Sym² (ρ[n] ^ h)).character + (Alt² (ρ[n] ^ h)).character) g =
        ((ρ[n] ^ h).character * (ρ[n] ^ h).character) g := by
    simpa [pow_two, Pi.add_apply, Pi.mul_apply] using
      congr_fun (Representation.char_symmetricSquare_add_char_alternatingSquare (ρ[n] ^ h)) g
  rw [dihedralAlternatingSquare_character_eq_reflectionSign,
    dihedralTwoDimensionalCharacter_mul_self,
    dihedralTwoDimensionalCharacter_zero_eq_trivial_add_reflectionSign] at hchar
  simp only [Pi.add_apply] at hchar ⊢
  have hchar' :
      ψ₂[n] g + (Sym² (ρ[n] ^ h)).character g = ψ₂[n] g + (χ_ (h + h) g + ψ₁[n] g) := by
    simpa [add_assoc, add_left_comm, add_comm] using hchar
  exact add_left_cancel hchar'

end SymmetricAlternatingSquareCharacters

end

/-! ### Exercise_5_5_3_5 (from Chap05) -/
noncomputable section

open scoped DihedralCharacter

section

variable (n : ℕ) [NeZero n]

/- The `source-facing` owners in this exercise are the two three-dimensional geometric
realizations on `ℂ^3`: the usual rigid-motion realization and the `\mathbf{C}_{nv}` realization.
The `core/canonical` decomposition owner is still `Representation.prod`, and the right
`bridge/view` layer is an explicit `Representation.Equiv` from each geometric realization to the
corresponding product `ρ^1 ⊕ ψ₂` or `ρ^1 ⊕ ψ₁`. -/

private def dihedralThreeDimensionalDecomposition :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) × ℂ :=
  ((LinearEquiv.piCongrLeft ℂ (fun _ : Fin 3 ↦ ℂ) finSuccEquivLast.symm).symm.trans
      (LinearEquiv.piOptionEquivProd ℂ)).trans
    (LinearEquiv.prodComm ℂ ℂ (Fin 2 → ℂ))

private def dihedralThreeDimensionalRealization
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) where
  toFun g :=
    dihedralThreeDimensionalDecomposition.symm.toLinearMap ∘ₗ
      (((ρ[n] ^ (1 : ZMod n)).prod τ) g) ∘ₗ
        dihedralThreeDimensionalDecomposition.toLinearMap
  map_one' := by
    ext v i
    simp [LinearMap.comp_assoc]
  map_mul' g h := by
    ext v i
    simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]

private def dihedralThreeDimensionalRealizationEquivProd
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    (dihedralThreeDimensionalRealization n τ).Equiv ((ρ[n] ^ (1 : ZMod n)).prod τ) :=
  Representation.Equiv.mk dihedralThreeDimensionalDecomposition
    (fun g ↦ by
      apply LinearMap.ext
      intro v
      change dihedralThreeDimensionalDecomposition
          ((dihedralThreeDimensionalRealization n τ) g v) =
        (((ρ[n] ^ (1 : ZMod n)).prod τ) g) (dihedralThreeDimensionalDecomposition v)
      simp [dihedralThreeDimensionalRealization])

/-- Exercise 5-5.3-5: the usual three-dimensional rigid-motion realization of `\mathbf{D}_n`,
written on `ℂ^3` in the basis adapted to the planar `ρ^1`-part and the axial line. -/
def dihedralUsualRigidMotionRepresentation :
    Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) :=
  dihedralThreeDimensionalRealization n
    (dihedralReflectionSignDegreeOneCharacter n).toRepresentation

/-- Exercise 5-5.3-5: the `\mathbf{C}_{nv}` realization of `\mathbf{D}_n`, written on `ℂ^3` in
the same coordinate splitting. -/
def dihedralCnvRepresentation : Representation ℂ (DihedralGroup n) (Fin 3 → ℂ) :=
  dihedralThreeDimensionalRealization n (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- The usual rigid-motion realization is equivariantly isomorphic to the canonical product
`ρ^1 ⊕ ψ₂`. -/
def dihedralUsualRigidMotionRepresentation_equiv_prod :
    (dihedralUsualRigidMotionRepresentation n).Equiv
      ((ρ[n] ^ (1 : ZMod n)).prod
        (dihedralReflectionSignDegreeOneCharacter n).toRepresentation) :=
  dihedralThreeDimensionalRealizationEquivProd n
    (dihedralReflectionSignDegreeOneCharacter n).toRepresentation

/-- The `\mathbf{C}_{nv}` realization is equivariantly isomorphic to the canonical product
`ρ^1 ⊕ ψ₁`. -/
def dihedralCnvRepresentation_equiv_prod :
    (dihedralCnvRepresentation n).Equiv
      ((ρ[n] ^ (1 : ZMod n)).prod
        (Representation.trivial ℂ (DihedralGroup n) ℂ)) :=
  dihedralThreeDimensionalRealizationEquivProd n
    (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- Helper for Exercise 5-5.3-5: the projection from the product model `ρ^1 ⊕ τ` onto its axial
line commutes with the `\mathbf{D}_n`-action. -/
private theorem product_second_projection_isIntertwining
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    ∀ g v,
      LinearMap.snd ℂ (Fin 2 → ℂ) ℂ ((((ρ[n] ^ (1 : ZMod n)).prod τ) g) v) =
        τ g (LinearMap.snd ℂ (Fin 2 → ℂ) ℂ v) := by
  intro g v
  -- In the product representation, the second coordinate is acted on by `τ` alone.
  rcases v with ⟨v₁, v₂⟩
  simp [Representation.prod]

/-- Helper for Exercise 5-5.3-5: the axial projection of the canonical product model is an
equivariant linear map. -/
private noncomputable def product_axis_projection
    (τ : Representation ℂ (DihedralGroup n) ℂ) :
    (((ρ[n] ^ (1 : ZMod n)).prod τ)).IntertwiningMap τ :=
  (LinearMap.snd ℂ (Fin 2 → ℂ) ℂ).intertwiningMap_of_isIntertwiningMap
    (((ρ[n] ^ (1 : ZMod n)).prod τ)) τ
    (product_second_projection_isIntertwining (n := n) τ)

-- Proof sketch: transport reducibility across
-- `dihedralUsualRigidMotionRepresentation_equiv_prod`, then use the canonical direct-sum
-- decomposition to exhibit a proper nontrivial stable summand.
/-- Exercise 5-5.3-5 (1): the usual three-dimensional rigid-motion realization of
`\mathbf{D}_n` is reducible. -/
theorem dihedralUsualRigidMotionRepresentation_not_isIrreducible :
    ¬ (dihedralUsualRigidMotionRepresentation n).IsIrreducible := by
  -- Route correction: instead of building a separate transported subrepresentation lattice, we use
  -- the source-faithful plane/axis decomposition and the axial projection intertwiner directly.
  intro hIrred
  letI : (dihedralUsualRigidMotionRepresentation n).IsIrreducible := hIrred
  let e := dihedralUsualRigidMotionRepresentation_equiv_prod n
  let f : (dihedralUsualRigidMotionRepresentation n).IntertwiningMap
      (dihedralReflectionSignDegreeOneCharacter n).toRepresentation :=
    (product_axis_projection n (dihedralReflectionSignDegreeOneCharacter n).toRepresentation).comp
      e.toIntertwiningMap
  have hplane_vec_ne :
      ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) ≠ 0 := by
    -- The planar summand contains a concrete nonzero vector.
    intro hzero
    have hfst := congrArg Prod.fst hzero
    simp at hfst
  have hplane_preimage_ne :
      e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) ≠ 0 := by
    -- Pulling that planar vector back along the representation equivalence keeps it nonzero.
    intro hx_zero
    apply hplane_vec_ne
    simpa using congrArg e hx_zero
  have hf_not_injective : ¬ Function.Injective f := by
    -- The axial projection kills the planar summand, so its composite with `e` has nontrivial
    -- kernel.
    intro hf_injective
    have hx :
        f (e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ)) = 0 := by
      simp [f, e, product_axis_projection]
    have hzero : f 0 = 0 := by
      simp [f]
    have : e.symm ((Pi.basisFun ℂ (Fin 2) 0, (0 : ℂ)) : (Fin 2 → ℂ) × ℂ) = 0 :=
      hf_injective (by simpa [hzero] using hx)
    exact hplane_preimage_ne this
  have hf_nonzero : f ≠ 0 := by
    -- The axial unit vector survives the projection, so the composite is not the zero map.
    intro hf_zero
    have hvalue : f (e.symm ((0 : Fin 2 → ℂ), (1 : ℂ))) = 1 := by
      simp [f, e, product_axis_projection]
    have hzero_value : f (e.symm ((0 : Fin 2 → ℂ), (1 : ℂ))) = 0 := by
      simp [hf_zero]
    have : (1 : ℂ) = 0 := by
      exact hvalue.symm.trans hzero_value
    norm_num at this
  -- Irreducibility forces every intertwining map out of the source to be injective or zero, but
  -- the axial projection composite is neither.
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf_injective | hf_zero
  · exact hf_not_injective hf_injective
  · exact hf_nonzero hf_zero

-- Proof sketch: apply `Representation.char_iso` to
-- `dihedralUsualRigidMotionRepresentation_equiv_prod`, then use `Representation.char_prod` and the
-- chapter's identifications of the two summand characters with `χ_1` and `ψ₂`.
/-- Exercise 5-5.3-5 (2): the character of the usual rigid-motion realization is
`χ_1 + ψ₂`. -/
theorem dihedralUsualRigidMotionRepresentation_character_eq :
    (dihedralUsualRigidMotionRepresentation n).character = χ_ 1 + ψ₂[n] := by
  calc
    (dihedralUsualRigidMotionRepresentation n).character
      = (((ρ[n] ^ (1 : ZMod n)).prod
            (dihedralReflectionSignDegreeOneCharacter n).toRepresentation)).character := by
          simpa using
            Representation.char_iso (dihedralUsualRigidMotionRepresentation_equiv_prod n)
    _ = (ρ[n] ^ (1 : ZMod n)).character +
          (dihedralReflectionSignDegreeOneCharacter n).toRepresentation.character := by
          exact Representation.char_prod (ρ[n] ^ (1 : ZMod n))
            ((dihedralReflectionSignDegreeOneCharacter n).toRepresentation)
    _ = χ_ 1 + ψ₂[n] := rfl

-- Proof sketch: apply `Representation.char_iso` to `dihedralCnvRepresentation_equiv_prod`, then
-- use `Representation.char_prod` and identify the one-dimensional summand with the trivial
-- character `ψ₁`.
/-- Exercise 5-5.3-5 (3): the character of the `\mathbf{C}_{nv}` realization is
`χ_1 + ψ₁`. -/
theorem dihedralCnvRepresentation_character_eq :
    (dihedralCnvRepresentation n).character = χ_ 1 + ψ₁[n] := by
  calc
    (dihedralCnvRepresentation n).character
      = (((ρ[n] ^ (1 : ZMod n)).prod
            (Representation.trivial ℂ (DihedralGroup n) ℂ))).character := by
          simpa using Representation.char_iso (dihedralCnvRepresentation_equiv_prod n)
    _ = (ρ[n] ^ (1 : ZMod n)).character +
          (Representation.trivial ℂ (DihedralGroup n) ℂ).character := by
          exact Representation.char_prod (ρ[n] ^ (1 : ZMod n))
            (Representation.trivial ℂ (DihedralGroup n) ℂ)
    _ = χ_ 1 + ψ₁[n] := rfl

end
