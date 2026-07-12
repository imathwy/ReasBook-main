import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion

variable (R : Type u) [CommRing R]
variable (I J : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.96.9: a power containment `A ^ k ≤ B` propagates to the cofinal subsequence
`A ^ (k * n) ≤ B ^ n`. -/
private theorem ideal_pow_mul_le_pow_of_pow_le
    {A B : Ideal R} {k : ℕ} (hAB : A ^ k ≤ B) (n : ℕ) :
    A ^ (k * n) ≤ B ^ n := by
  -- Rewrite the left-hand side as `(A ^ k) ^ n`, then apply monotonicity of powers.
  rw [pow_mul]
  exact Ideal.pow_right_mono hAB n

/-- Helper for Lemma 10.96.9: the induced containment on powers gives a containment on the
corresponding submodules `I ^ (k * n) M ⊆ J ^ n M`. -/
private theorem pow_smul_top_le_pow_smul_top_of_pow_le
    {A B : Ideal R} {k n : ℕ} (hAB : A ^ k ≤ B) :
    (A ^ (k * n) • (⊤ : Submodule R M)) ≤ B ^ n • (⊤ : Submodule R M) :=
  Submodule.smul_mono_left (ideal_pow_mul_le_pow_of_pow_le
    (R := R) (A := A) (B := B) (k := k) hAB n)

/-- Helper for Lemma 10.96.9: the quotient map from the `I ^ (c * n)`-quotient to the
`J ^ n`-quotient induced by the containment `I ^ (c * n) M ⊆ J ^ n M`. -/
private noncomputable abbrev adicCompletionRightQuotientMap
    (c : ℕ) (hIJ : I ^ c ≤ J) (n : ℕ) :
    M ⧸ (I ^ (c * n) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (J ^ n • ⊤ : Submodule R M) :=
  Submodule.factor (pow_smul_top_le_pow_smul_top_of_pow_le
    (R := R) (M := M) (A := I) (B := J) (k := c) (n := n) hIJ)

/-- Helper for Lemma 10.96.9: the quotient maps along the cofinal subsequence `n ↦ c * n`
commute with the transition maps. -/
private theorem adicCompletionRightQuotientMap_compatible
    (c : ℕ) (hIJ : I ^ c ≤ J) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap J M hmn ∘ₗ
        adicCompletionRightQuotientMap R I J M c hIJ n =
      adicCompletionRightQuotientMap R I J M c hIJ m ∘ₗ
        AdicCompletion.transitionMap I M (Nat.mul_le_mul_left c hmn) := by
  -- Both composites are the quotient map from the `I ^ (c * n)`-quotient to the `J ^ m`-quotient.
  ext x
  simp [adicCompletionRightQuotientMap, AdicCompletion.transitionMap, Submodule.factorPow]

/-- Helper for Lemma 10.96.9: the `n`th coordinate of the right comparison map is obtained from
the `(c * n)`th `I`-adic coordinate by quotienting further to `M / J ^ n M`. -/
private noncomputable abbrev adicCompletionRightFamily
    (c : ℕ) (hIJ : I ^ c ≤ J) (n : ℕ) :
    AdicCompletion I M →ₗ[R] M ⧸ (J ^ n • ⊤ : Submodule R M) :=
  adicCompletionRightQuotientMap R I J M c hIJ n ∘ₗ AdicCompletion.eval I M (c * n)

/-- Helper for Lemma 10.96.9: the quotient maps defining the right comparison map form a
compatible inverse-system morphism. -/
private theorem adicCompletionRightFamily_compatible
    (c : ℕ) (hIJ : I ^ c ≤ J) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap J M hmn ∘ₗ
        adicCompletionRightFamily R I J M c hIJ n =
      adicCompletionRightFamily R I J M c hIJ m := by
  apply LinearMap.ext
  intro x
  -- Push the `J`-transition past the quotient map, then use compatibility of `I`-adic coordinates.
  calc
    AdicCompletion.transitionMap J M hmn (adicCompletionRightFamily R I J M c hIJ n x) =
        adicCompletionRightQuotientMap R I J M c hIJ m
          (AdicCompletion.transitionMap I M (Nat.mul_le_mul_left c hmn)
            (AdicCompletion.eval I M (c * n) x)) := by
          exact congrArg
            (fun f :
              M ⧸ (I ^ (c * n) • ⊤ : Submodule R M) →ₗ[R]
                M ⧸ (J ^ m • ⊤ : Submodule R M) ↦
              f (AdicCompletion.eval I M (c * n) x))
            (adicCompletionRightQuotientMap_compatible (R := R) (I := I) (J := J) (M := M)
              (c := c) (hIJ := hIJ) hmn)
    _ = adicCompletionRightQuotientMap R I J M c hIJ m
          (AdicCompletion.eval I M (c * m) x) := by
          exact congrArg (adicCompletionRightQuotientMap R I J M c hIJ m)
            (AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := M)
              (m := c * m) (n := c * n) (hmn := Nat.mul_le_mul_left c hmn) x)
    _ = adicCompletionRightFamily R I J M c hIJ m x := rfl

/-- Helper for Lemma 10.96.9: the quotient map from the `J ^ (d * n)`-quotient to the
`I ^ n`-quotient induced by the containment `J ^ (d * n) M ⊆ I ^ n M`. -/
private noncomputable abbrev adicCompletionLeftQuotientMap
    (d : ℕ) (hJI : J ^ d ≤ I) (n : ℕ) :
    M ⧸ (J ^ (d * n) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  Submodule.factor (pow_smul_top_le_pow_smul_top_of_pow_le
    (R := R) (M := M) (A := J) (B := I) (k := d) (n := n) hJI)

/-- Helper for Lemma 10.96.9: the quotient maps along the cofinal subsequence `n ↦ d * n`
commute with the transition maps. -/
private theorem adicCompletionLeftQuotientMap_compatible
    (d : ℕ) (hJI : J ^ d ≤ I) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        adicCompletionLeftQuotientMap R I J M d hJI n =
      adicCompletionLeftQuotientMap R I J M d hJI m ∘ₗ
        AdicCompletion.transitionMap J M (Nat.mul_le_mul_left d hmn) := by
  -- Both composites are the quotient map from the `J ^ (d * n)`-quotient to the `I ^ m`-quotient.
  ext x
  simp [adicCompletionLeftQuotientMap, AdicCompletion.transitionMap, Submodule.factorPow]

/-- Helper for Lemma 10.96.9: the `n`th coordinate of the left comparison map is obtained from
the `(d * n)`th `J`-adic coordinate by quotienting further to `M / I ^ n M`. -/
private noncomputable abbrev adicCompletionLeftFamily
    (d : ℕ) (hJI : J ^ d ≤ I) (n : ℕ) :
    AdicCompletion J M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  adicCompletionLeftQuotientMap R I J M d hJI n ∘ₗ AdicCompletion.eval J M (d * n)

/-- Helper for Lemma 10.96.9: the quotient maps defining the left comparison map form a
compatible inverse-system morphism. -/
private theorem adicCompletionLeftFamily_compatible
    (d : ℕ) (hJI : J ^ d ≤ I) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        adicCompletionLeftFamily R I J M d hJI n =
      adicCompletionLeftFamily R I J M d hJI m := by
  apply LinearMap.ext
  intro x
  -- Push the `I`-transition past the quotient map, then use compatibility of `J`-adic coordinates.
  calc
    AdicCompletion.transitionMap I M hmn (adicCompletionLeftFamily R I J M d hJI n x) =
        adicCompletionLeftQuotientMap R I J M d hJI m
          (AdicCompletion.transitionMap J M (Nat.mul_le_mul_left d hmn)
            (AdicCompletion.eval J M (d * n) x)) := by
          exact congrArg
            (fun f :
              M ⧸ (J ^ (d * n) • ⊤ : Submodule R M) →ₗ[R]
                M ⧸ (I ^ m • ⊤ : Submodule R M) ↦
              f (AdicCompletion.eval J M (d * n) x))
            (adicCompletionLeftQuotientMap_compatible (R := R) (I := I) (J := J) (M := M)
              (d := d) (hJI := hJI) hmn)
    _ = adicCompletionLeftQuotientMap R I J M d hJI m
          (AdicCompletion.eval J M (d * m) x) := by
          exact congrArg (adicCompletionLeftQuotientMap R I J M d hJI m)
            (AdicCompletion.transitionMap_comp_eval_apply (I := J) (M := M)
              (m := d * m) (n := d * n) (hmn := Nat.mul_le_mul_left d hmn) x)
    _ = adicCompletionLeftFamily R I J M d hJI m x := rfl

/-- Helper for Lemma 10.96.9: positivity of `a` and `b` makes the subsequence
`n ↦ a * (b * n)` dominate the identity sequence. -/
private theorem nat_le_mul_mul_of_pos
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    n ≤ a * (b * n) := by
  -- First multiply by `b`, then multiply by `a`.
  have hbn : n ≤ b * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
  have han : b * n ≤ a * (b * n) := by
    simpa [one_mul] using Nat.mul_le_mul_right (b * n) (Nat.succ_le_of_lt ha)
  exact hbn.trans han

/-- Helper for Lemma 10.96.9: the direct right comparison map between the two completions. -/
private noncomputable def adicCompletionToRightOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M →ₗ[R] AdicCompletion J M
  | c, _, _, _, hIJ, _ =>
      AdicCompletion.lift J
        (adicCompletionRightFamily R I J M c hIJ)
        (adicCompletionRightFamily_compatible (R := R) (I := I) (J := J) (M := M) (c := c)
          (hIJ := hIJ))

/-- Helper for Lemma 10.96.9: the direct left comparison map between the two completions. -/
private noncomputable def adicCompletionToLeftOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion J M →ₗ[R] AdicCompletion I M
  | _, d, _, _, _, hJI =>
      AdicCompletion.lift I
        (adicCompletionLeftFamily R I J M d hJI)
        (adicCompletionLeftFamily_compatible (R := R) (I := I) (J := J) (M := M) (d := d)
          (hJI := hJI))

/-- Helper for Lemma 10.96.9: the right comparison map sends the canonical class of `x`
to the canonical class of `x`. -/
@[simp]
private theorem adicCompletionToRightOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  -- Check equality on every quotient coordinate of the inverse limit.
  apply AdicCompletion.ext
  intro n
  simp [adicCompletionToRightOfPowLe, adicCompletionRightFamily, adicCompletionRightQuotientMap]

/-- Helper for Lemma 10.96.9: the left comparison map sends the canonical class of `x`
to the canonical class of `x`. -/
@[simp]
private theorem adicCompletionToLeftOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI (of J M x) = of I M x := by
  -- Check equality on every quotient coordinate of the inverse limit.
  apply AdicCompletion.ext
  intro n
  simp [adicCompletionToLeftOfPowLe, adicCompletionLeftFamily, adicCompletionLeftQuotientMap]

/-- Helper for Lemma 10.96.9: applying the left comparison map after the right one recovers the
original `I`-adic completion element. -/
private theorem adicCompletion_left_right_eq_id
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI).comp
        (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  -- Evaluate the composite at the `n`th quotient level and descend from level `c * (d * n)`.
  have hle : n ≤ c * (d * n) := nat_le_mul_mul_of_pos c d n hc hd
  simpa [adicCompletionToLeftOfPowLe, adicCompletionToRightOfPowLe, adicCompletionLeftFamily,
    adicCompletionRightFamily, adicCompletionLeftQuotientMap, adicCompletionRightQuotientMap,
    AdicCompletion.transitionMap, Submodule.factorPow, Nat.mul_assoc] using x.property hle

/-- Helper for Lemma 10.96.9: applying the right comparison map after the left one recovers the
original `J`-adic completion element. -/
private theorem adicCompletion_right_left_eq_id
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI).comp
        (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  -- Evaluate the composite at the `n`th quotient level and descend from level `d * (c * n)`.
  have hle : n ≤ d * (c * n) := nat_le_mul_mul_of_pos d c n hd hc
  simpa [adicCompletionToLeftOfPowLe, adicCompletionToRightOfPowLe, adicCompletionLeftFamily,
    adicCompletionRightFamily, adicCompletionLeftQuotientMap, adicCompletionRightQuotientMap,
    AdicCompletion.transitionMap, Submodule.factorPow, Nat.mul_assoc, Nat.mul_left_comm] using
    x.property hle

-- Proof sketch: the power containments `I ^ c ≤ J` and `J ^ d ≤ I` make the `I`-adic and
-- `J`-adic filtrations cofinal. The direct quotient maps on the cofinal subsequences therefore
-- induce mutually inverse morphisms between the two inverse-limit completions.
/-- Lemma 10.96.9: if positive powers of `I` and `J` contain one another, then the `I`-adic and
`J`-adic completions of any `R`-module are canonically identified. -/
@[stacks 0319]
noncomputable def adicCompletionLinearEquivOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M ≃ₗ[R] AdicCompletion J M
  | c, d, hc, hd, hIJ, hJI =>
      LinearEquiv.ofLinear
        (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI)
        (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI)
        (adicCompletion_right_left_eq_id (R := R) (I := I) (J := J) (M := M)
          c d hc hd hIJ hJI)
        (adicCompletion_left_right_eq_id (R := R) (I := I) (J := J) (M := M)
          c d hc hd hIJ hJI)

@[simp]
theorem adicCompletionLinearEquivOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  exact adicCompletionToRightOfPowLe_of R I J M c d hc hd hIJ hJI x

-- Proof sketch: transport bijectivity of the canonical map `M → AdicCompletion I M` across the
-- comparison equivalence, using that the equivalence intertwines the two `of` maps.
/-- Under mutual positive-power containments between `I` and `J`, an `R`-module is `I`-adically
complete if and only if it is `J`-adically complete. -/
theorem isAdicComplete_iff_of_pow_le :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      IsAdicComplete I M ↔ IsAdicComplete J M
  | c, d, hc, hd, hIJ, hJI => by
      constructor
      · intro hI
        -- Compose `of I` with the comparison equivalence to recover `of J`.
        rw [← AdicCompletion.of_bijective_iff]
        let e := adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI
        have hcomp :
            of J M = (e : AdicCompletion I M →ₗ[R] AdicCompletion J M).comp (of I M) := by
          apply LinearMap.ext
          intro x
          exact adicCompletionLinearEquivOfPowLe_of R I J M c d hc hd hIJ hJI x
        rw [hcomp]
        exact e.bijective.comp ((AdicCompletion.of_bijective_iff).mpr hI)
      · intro hJ
        -- Apply the same transport argument to the inverse equivalence.
        rw [← AdicCompletion.of_bijective_iff]
        let e := adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI
        have hcomp :
            of I M = ((e.symm : AdicCompletion J M →ₗ[R] AdicCompletion I M)).comp (of J M) := by
          apply LinearMap.ext
          intro x
          exact adicCompletionToLeftOfPowLe_of R I J M c d hc hd hIJ hJI x
        rw [hcomp]
        exact e.symm.bijective.comp ((AdicCompletion.of_bijective_iff).mpr hJ)

end
