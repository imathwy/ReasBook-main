import Mathlib
import stacks_project.Chap10.Lemma_10_32_4
import stacks_project.Chap10.Lemma_10_108_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Ideal.Quotient

variable {R : Type u} [CommRing R]

private theorem exists_pow_eq_iff_exists_pow_eq_unit {A : Type u} [CommRing A]
    {n : ℕ} (hn : 1 ≤ n) {a : A} (ha : IsUnit a) :
    (∃ b : A, b ^ n = a) ↔ ∃ u : Aˣ, u ^ n = ha.unit := by
  constructor
  · rintro ⟨b, hb⟩
    have hb_pow_unit : IsUnit (b ^ n) := by
      simpa [hb] using ha
    have hb_unit : IsUnit b :=
      (isUnit_pow_iff (Nat.one_le_iff_ne_zero.mp hn)).mp hb_pow_unit
    refine ⟨hb_unit.unit, ?_⟩
    apply Units.ext
    change ((hb_unit.unit : A) ^ n) = a
    simp [hb]
  · rintro ⟨u, hu⟩
    refine ⟨(u : A), ?_⟩
    simpa [ha.unit_spec] using congrArg (fun v : Aˣ ↦ (v : A)) hu

private theorem one_add_pow_sub_one_mem (I : Ideal R) (n : ℕ) (x : I) :
    (1 + (x : R)) ^ n - 1 ∈ I := by
  rw [← eq_zero_iff_mem]
  have hx0 : mk I (x : R) = 0 := eq_zero_iff_mem.mpr x.property
  simp [hx0]

/-- Helper for Lemma 10.32.8: if `n` becomes a unit modulo a locally nilpotent ideal, then `n`
is already a unit in the ambient ring. -/
private theorem nat_cast_isUnit_of_isUnit_quotient_nat_cast (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn_unit : IsUnit (n : R ⧸ I)) :
    IsUnit (n : R) :=
  (isUnit_iff_isUnit_quotient_mk_of_isLocallyNilpotent I hI).2 hn_unit

/-- Helper for Lemma 10.32.8: elements of the form `1 + x` with `x ∈ I` lie in `I.oneAdd`. -/
private theorem one_add_mem_oneAdd (I : Ideal R) (x : I) :
    1 + (x : R) ∈ I.oneAdd :=
  (Ideal.mem_oneAdd_iff).2 ⟨x, x.property, rfl⟩

/-- Helper for Lemma 10.32.8: if `u ∈ 1 + I`, then `u - 1` lies in `I`. -/
private theorem sub_one_mem_of_mem_oneAdd (I : Ideal R) {u : R} (hu : u ∈ I.oneAdd) :
    u - 1 ∈ I := by
  rcases (Ideal.mem_oneAdd_iff).1 hu with ⟨x, hx, rfl⟩
  simpa using hx

/-- Helper for Lemma 10.32.8: an element whose difference from `1` lies in `I` belongs to
`I.oneAdd`. -/
private theorem mem_oneAdd_of_sub_one_mem (I : Ideal R) {u : R} (hu : u - 1 ∈ I) :
    u ∈ I.oneAdd := by
  have hu_eq : u = 1 + (u - 1) := by
    ring
  exact (Ideal.mem_oneAdd_iff).2 ⟨u - 1, hu, hu_eq⟩

/-- Helper for Lemma 10.32.8: if the quotient of `u` is `1`, then `u` lies in `1 + I`. -/
private theorem mem_oneAdd_of_quotient_eq_one (I : Ideal R) {u : R}
    (hu : mk I u = 1) : u ∈ I.oneAdd := by
  have hu_sub : u - 1 ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa [map_sub, hu]
  exact mem_oneAdd_of_sub_one_mem I hu_sub

/-- Helper for Lemma 10.32.8: elements of `1 + I` map to `1` in the quotient. -/
private theorem quotient_mk_eq_one_of_mem_oneAdd (I : Ideal R) {u : R} (hu : u ∈ I.oneAdd) :
    mk I u = 1 := by
  rcases (Ideal.mem_oneAdd_iff).1 hu with ⟨x, hx, rfl⟩
  have hx0 : mk I x = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hx
  simp [hx0]

/-- Helper for Lemma 10.32.8: elements of `1 + I` are nilpotently close to `1`. -/
private theorem isNilpotent_one_sub_of_mem_oneAdd (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {u : R} (hu : u ∈ I.oneAdd) :
    IsNilpotent (1 - u) := by
  rcases (Ideal.mem_oneAdd_iff).1 hu with ⟨x, hx, rfl⟩
  have hxnil : IsNilpotent x := (Ideal.isLocallyNilpotent_iff I).1 hI x hx
  simpa using hxnil.neg

/-- Helper for Lemma 10.32.8: in the quotient, an `n`th root of `1` that is nilpotently close to
`1` must equal `1`. -/
private theorem quotient_eq_one_of_pow_eq_one_of_isNilpotent_sub_one (I : Ideal R)
    {n : ℕ} (_hn : 1 ≤ n) (hn_unit : IsUnit (n : R ⧸ I)) {q : R ⧸ I}
    (hqpow : q ^ n = 1) (hqnil : IsNilpotent (1 - q)) :
    q = 1 := by
  let P : Polynomial (R ⧸ I) := Polynomial.X ^ n - Polynomial.C (1 : R ⧸ I)
  -- Apply the Newton uniqueness theorem at the base point `1`.
  have hnil : IsNilpotent ((Polynomial.aeval (1 : R ⧸ I)) P) := by
    simpa [P, Polynomial.aeval_X_pow] using (isNilpotent_zero : IsNilpotent (0 : R ⧸ I))
  have hderiv : IsUnit ((Polynomial.aeval (1 : R ⧸ I)) (Polynomial.derivative P)) := by
    simpa [P, Polynomial.derivative_X_pow, Polynomial.aeval_X_pow] using hn_unit
  obtain ⟨r, hr, huniq⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (x := (1 : R ⧸ I)) (P := P) hnil
      hderiv
  have hqroot : IsNilpotent (1 - q) ∧ Polynomial.aeval q P = 0 := by
    refine ⟨hqnil, ?_⟩
    simpa [P, hqpow] using (sub_eq_zero.mpr hqpow)
  have hone : IsNilpotent (1 - (1 : R ⧸ I)) ∧ Polynomial.aeval (1 : R ⧸ I) P = 0 := by
    refine ⟨?_, ?_⟩
    · simpa using (isNilpotent_zero : IsNilpotent (0 : R ⧸ I))
    · simp [P]
  exact (huniq q hqroot).trans (huniq 1 hone).symm

/-- Helper for Lemma 10.32.8: every element of `1 + I` has a unique `n`th root that still lies in
`1 + I`. -/
private theorem existsUnique_nth_root_mem_oneAdd_of_mem_oneAdd (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) {u : R} (hu : u ∈ I.oneAdd) :
    ∃! v : R, v ^ n = u ∧ v ∈ I.oneAdd := by
  let P : Polynomial R := Polynomial.X ^ n - Polynomial.C u
  have hnR : IsUnit (n : R) :=
    nat_cast_isUnit_of_isUnit_quotient_nat_cast I hI hn_unit
  -- Newton produces a unique root that is nilpotently close to `1`.
  have hnil : IsNilpotent ((Polynomial.aeval (1 : R)) P) := by
    simpa [P, Polynomial.aeval_X_pow] using isNilpotent_one_sub_of_mem_oneAdd I hI hu
  have hderiv : IsUnit ((Polynomial.aeval (1 : R)) (Polynomial.derivative P)) := by
    simpa [P, Polynomial.derivative_X_pow, Polynomial.aeval_X_pow] using hnR
  obtain ⟨r, hr, huniq⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (x := (1 : R)) (P := P) hnil hderiv
  have hrpow : r ^ n = u := by
    exact sub_eq_zero.mp (by simpa [P] using hr.2)
  have hrmem : r ∈ I.oneAdd := by
    -- Route correction: the Newton theorem only gives `r` nilpotently close to `1`; to show
    -- `r ∈ 1 + I`, force its image in the quotient to equal `1` by the same uniqueness argument.
    have hqpow : mk I r ^ n = (1 : R ⧸ I) := by
      rw [← map_pow, hrpow, quotient_mk_eq_one_of_mem_oneAdd I hu]
    have hqnil : IsNilpotent (1 - mk I r) := by
      simpa [map_sub] using hr.1.map (mk I)
    have hqeq : mk I r = 1 :=
      quotient_eq_one_of_pow_eq_one_of_isNilpotent_sub_one I hn hn_unit hqpow hqnil
    exact mem_oneAdd_of_quotient_eq_one I hqeq
  refine ⟨r, ⟨hrpow, hrmem⟩, ?_⟩
  intro v hv
  -- Any competing root in `1 + I` is also nilpotently close to `1`, so Newton uniqueness applies.
  have hvnil : IsNilpotent (1 - v) := isNilpotent_one_sub_of_mem_oneAdd I hI hv.2
  have hvroot : Polynomial.aeval v P = 0 := by
    simpa [P, hv.1]
  exact huniq v ⟨hvnil, hvroot⟩

/-- Helper for Lemma 10.32.8: if a unit of `R` has an `n`th root modulo `I`, then it already has
an `n`th root in `R`. -/
private theorem exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent_aux
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) {a : R} (ha : IsUnit a) :
    (∃ b : R, b ^ n = a) ↔ ∃ bbar : R ⧸ I, bbar ^ n = mk I a := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨mk I b, by simpa [map_pow] using congrArg (mk I) hb⟩
  · rintro ⟨bbar, hbbar⟩
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective bbar
    have hquot_unit : IsUnit (mk I b0) := by
      have hpow_unit : IsUnit ((mk I b0) ^ n) := by
        simpa [hbbar] using ha.map (mk I)
      exact (isUnit_pow_iff (Nat.one_le_iff_ne_zero.mp hn)).1 hpow_unit
    have hb0_unit : IsUnit b0 :=
      (isUnit_iff_isUnit_quotient_mk_of_isLocallyNilpotent I hI).2 hquot_unit
    let b : Rˣ := hb0_unit.unit
    have hb_eq : (b : R) = b0 := hb0_unit.unit_spec
    have hdiff : a - (b : R) ^ n ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa [map_sub, map_pow, hb_eq] using (sub_eq_zero.mpr hbbar.symm)
    let g : R := a * ↑((b⁻¹) ^ n)
    have hcancel_right : (b : R) ^ n * ↑((b⁻¹) ^ n) = 1 := by
      have hbase : (b : R) * ↑(b⁻¹) = 1 := by
        simp
      have hpow_eq : ((b : R) * ↑(b⁻¹)) ^ n = 1 := by
        simpa using congrArg (fun z : R ↦ z ^ n) hbase
      calc
        (b : R) ^ n * ↑((b⁻¹) ^ n) = ((b : R) * ↑(b⁻¹)) ^ n := by
          symm
          rw [mul_pow]
          rfl
        _ = 1 := hpow_eq
    have hcancel_left : ↑((b⁻¹) ^ n) * (b : R) ^ n = 1 := by
      have hbase : ↑(b⁻¹) * (b : R) = 1 := by
        simp
      have hpow_eq : (↑(b⁻¹) * (b : R)) ^ n = 1 := by
        simpa using congrArg (fun z : R ↦ z ^ n) hbase
      calc
        ↑((b⁻¹) ^ n) * (b : R) ^ n = (↑(b⁻¹) * (b : R)) ^ n := by
          symm
          rw [mul_pow]
          rfl
        _ = 1 := hpow_eq
    have hg_sub : g - 1 ∈ I := by
      have hg_eq : g - 1 = (a - (b : R) ^ n) * ↑((b⁻¹) ^ n) := by
        calc
          g - 1 = g - ((b : R) ^ n * ↑((b⁻¹) ^ n)) := by rw [hcancel_right]
          _ = (a - (b : R) ^ n) * ↑((b⁻¹) ^ n) := by
            simp [g]
            ring
      rw [hg_eq]
      exact I.mul_mem_right _ hdiff
    have hg_mem : g ∈ I.oneAdd := mem_oneAdd_of_sub_one_mem I hg_sub
    obtain ⟨c, hc, _⟩ :=
      existsUnique_nth_root_mem_oneAdd_of_mem_oneAdd I hI hn hn_unit hg_mem
    have hcpow : c ^ n = g := hc.1
    refine ⟨c * (b : R), ?_⟩
    -- Reassemble the root using the lifted quotient root and the root in `1 + I`.
    calc
      (c * (b : R)) ^ n = c ^ n * (b : R) ^ n := by
        rw [mul_pow]
      _ = g * (b : R) ^ n := by rw [hcpow]
      _ = a := by
        calc
          g * (b : R) ^ n = (a * ↑((b⁻¹) ^ n)) * (b : R) ^ n := by rfl
          _ = a * (↑((b⁻¹) ^ n) * (b : R) ^ n) := by ring
          _ = a := by rw [hcancel_left, mul_one]

-- Proof sketch: construct the inverse by the truncated binomial series for `(1 + x)^(1 / n)`;
-- local nilpotence makes the series finite, and `n` is invertible in `R` because it is
-- invertible in `R ⧸ I` and units lift across locally nilpotent ideals by Lemma 10.32.4.
/-- Lemma 10.32.8 (1), canonical form: if `I` is locally nilpotent and `n ≥ 1` is invertible in
`R ⧸ I`, then the `n`th-power map on the canonical owner object `1 + I` is bijective. -/
theorem bijective_pow_one_add_of_isLocallyNilpotent (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) :
    Function.Bijective (fun x : Ideal.oneAdd I ↦ x ^ n) := by
  constructor
  · intro x y hxy
    -- Compare two roots of the same element of `1 + I` and use uniqueness.
    have hpow : (x : R) ^ n = (y : R) ^ n := by
      simpa [SubmonoidClass.coe_pow] using congrArg Subtype.val hxy
    have hxpow_mem : (x : R) ^ n ∈ I.oneAdd := by
      simpa [SubmonoidClass.coe_pow] using (x ^ n).2
    obtain ⟨r, hr, huniq⟩ :=
      existsUnique_nth_root_mem_oneAdd_of_mem_oneAdd I hI hn hn_unit hxpow_mem
    have hxroot : (x : R) ^ n = (x : R) ^ n ∧ (x : R) ∈ I.oneAdd := ⟨rfl, x.2⟩
    have hyroot : (y : R) ^ n = (x : R) ^ n ∧ (y : R) ∈ I.oneAdd := ⟨hpow.symm, y.2⟩
    exact Subtype.ext ((huniq x hxroot).trans (huniq y hyroot).symm)
  · intro u
    -- Surjectivity is the existence half of the unique-root statement.
    obtain ⟨v, hv, _⟩ :=
      existsUnique_nth_root_mem_oneAdd_of_mem_oneAdd I hI hn hn_unit u.2
    refine ⟨⟨v, hv.2⟩, ?_⟩
    exact Subtype.ext (by simpa [SubmonoidClass.coe_pow] using hv.1)

/-- Ideal-subtype bridge: under the coordinate identification `x ↦ 1 + x` between `I` and `1 + I`,
the canonical power map on `1 + I` is the textbook map `x ↦ (1 + x)^n - 1` on `I`. -/
theorem bijective_one_add_pow_sub_one_of_isLocallyNilpotent (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) :
    Function.Bijective fun x : I ↦
      show I from ⟨(1 + (x : R)) ^ n - 1, one_add_pow_sub_one_mem I n x⟩ := by
  have hbij := bijective_pow_one_add_of_isLocallyNilpotent I hI hn hn_unit
  constructor
  · intro x y hxy
    -- Translate equality in the textbook coordinates to equality in `1 + I`.
    have hpow : (1 + (x : R)) ^ n = (1 + (y : R)) ^ n := by
      simpa using congrArg (fun z : R ↦ z + 1) (congrArg Subtype.val hxy)
    have hpow_eq :
        (⟨1 + (x : R), one_add_mem_oneAdd I x⟩ : Ideal.oneAdd I) ^ n =
          (⟨1 + (y : R), one_add_mem_oneAdd I y⟩ : Ideal.oneAdd I) ^ n := by
      apply Subtype.ext
      simpa [SubmonoidClass.coe_pow] using hpow
    have hbase :=
      hbij.1 hpow_eq
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hbase)
  · intro y
    -- Solve surjectivity in `1 + I` first, then subtract `1` to return to the ideal.
    let u : Ideal.oneAdd I := ⟨1 + (y : R), one_add_mem_oneAdd I y⟩
    obtain ⟨v, hv⟩ := hbij.2 u
    let x : I := ⟨(v : R) - 1, sub_one_mem_of_mem_oneAdd I v.2⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hvpow : (v : R) ^ n = 1 + (y : R) := by
      simpa [SubmonoidClass.coe_pow] using congrArg Subtype.val hv
    have hx_eq : 1 + (x : R) = (v : R) := by
      change 1 + ((v : R) - 1) = (v : R)
      ring
    calc
      (1 + (x : R)) ^ n - 1 = (v : R) ^ n - 1 := by rw [hx_eq]
      _ = y := by rw [hvpow]; simp

-- Proof sketch: pass between roots in `R` and roots in `R ⧸ I` through the unit groups, then use
-- the owner-level bijectivity statement on `1 + I` from part (1).
/-- Lemma 10.32.8 (2), canonical form: for a locally nilpotent ideal `I`, an `n`th root of a
unit of `R` exists if and only if an `n`th root exists after mapping that unit to `(R ⧸ I)ˣ`. -/
theorem units_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I))
    (a : Rˣ) :
    (∃ b : Rˣ, b ^ n = a) ↔
      ∃ bbar : (R ⧸ I)ˣ, bbar ^ n = Units.map (mk I).toMonoidHom a := by
  have hqa : IsUnit (mk I (a : R)) := a.isUnit.map (mk I)
  have hleft : a.isUnit.unit = a := by
    apply Units.ext
    simp
  have hmap : hqa.unit = Units.map (mk I).toMonoidHom a := by
    apply Units.ext
    simp
  -- Reduce both sides to the ring-level root criterion and reuse the auxiliary theorem.
  calc
    (∃ b : Rˣ, b ^ n = a) ↔ ∃ b : R, b ^ n = (a : R) := by
      simpa [hleft] using (exists_pow_eq_iff_exists_pow_eq_unit hn a.isUnit).symm
    _ ↔ ∃ bbar : R ⧸ I, bbar ^ n = mk I (a : R) :=
      exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent_aux I hI hn hn_unit a.isUnit
    _ ↔ ∃ bbar : (R ⧸ I)ˣ, bbar ^ n = Units.map (mk I).toMonoidHom a := by
      simpa [hmap] using exists_pow_eq_iff_exists_pow_eq_unit hn hqa

-- Proof sketch: if `a = b^n`, then its image in `R ⧸ I` is the `n`th power of the image of `b`.
-- Conversely, if the image of `a` is `b̄^n`, lift `b̄` to `b : R`, use Lemma 10.32.4 to see that
-- `b` is a unit, and then apply part (1) to the element `a * b⁻n` lying in `1 + I`.
/-- Unit-valued bridge: a unit of `R` is an `n`th power if and only if its image in `R ⧸ I` is an
`n`th power. -/
theorem isUnit_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I))
    {a : R} (ha : IsUnit a) :
    (∃ b : R, b ^ n = a) ↔ ∃ bbar : R ⧸ I, bbar ^ n = mk I a := by
  have hqa : IsUnit (mk I a) := ha.map (mk I)
  have hmap : hqa.unit = Units.map (mk I).toMonoidHom ha.unit := by
    apply Units.ext
    simp
  rw [exists_pow_eq_iff_exists_pow_eq_unit hn ha,
    exists_pow_eq_iff_exists_pow_eq_unit hn hqa]
  simpa [hmap] using
    units_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent I hI hn hn_unit ha.unit

end
