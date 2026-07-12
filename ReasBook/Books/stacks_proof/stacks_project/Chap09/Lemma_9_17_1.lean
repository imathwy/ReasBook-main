import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open AddMonoid AddSubgroup

/- Domain-style sampling for Lemma 9.17.1:
- primary domain: finite abelian groups, exponent, and additive torsion subgroups;
- sampled canonical declarations:
  `AddSubgroup.torsionBy`,
  `AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero`,
  `gcd_nsmul_eq_zero`,
  `AddMonoid.addOrder_dvd_exponent`,
  `isAddCyclic_of_card_nsmul_eq_zero_le`,
  `IsAddCyclic.exponent_eq_card`;
- best owner abstraction: the source-facing torsion subgroup `A[d]`, realized canonically by
  `AddSubgroup.torsionBy`, together with the canonical exponent/cyclicity API from mathlib.

Source/core/bridge triage:
- `source-facing`: the textbook equality hypothesis on the canonical torsion groups `A[d]`;
- `core/canonical`: the stronger bounded-cardinality owner theorem
  `isAddCyclic_of_card_nsmul_eq_zero_le`, together with `A[d]`, `AddMonoid.exponent`, and
  `IsAddCyclic`;
- `bridge/view`: the proof-local finiteness of `A` obtained by embedding into `A[n]`, and the
  transport from `d • a = 0` and `n • a = 0` to `(gcd d n) • a = 0` via `gcd_nsmul_eq_zero`.

Primitive data are only the group `A`, the exponent divisibility `hexp : exponent A ∣ n`, and the
cardinality hypothesis on the canonical owner `A[d]`. Finiteness of `A`, the comparison with
`Nat.card A`, and the stronger `≤`-form cyclicity statement are derived consequences, so no extra
wrapper definition is warranted here.
-/

section

variable {A : Type u} [AddCommGroup A] {n : ℕ}

/-- The `gcd`-torsion subgroup still satisfies the source-facing cardinality bound. -/
private theorem natCard_torsionBy_gcd_le [Finite A]
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) (d : ℕ) :
    Nat.card A[d.gcd n] ≤ d.gcd n := by
  have := Cardinal.toNat_le_toNat
    (hcard (d.gcd n) (Nat.gcd_dvd_right d n)) Cardinal.natCast_lt_aleph0
  simpa [Nat.card] using this

/-- The `d`-torsion set is bounded by the corresponding `gcd`-torsion subgroup. -/
private theorem natCard_nsmul_eq_zero_le_of_torsion_cardinal_le [Finite A]
    (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    ∀ d : ℕ, 0 < d → Nat.card {a : A // d • a = 0} ≤ d := by
  intro d hd
  let f : {a : A // d • a = 0} → A[d.gcd n] := fun a ↦
    ⟨a.1, torsionBy.nsmul_iff.mpr (gcd_nsmul_eq_zero.2
      ⟨a.2, (exponent_dvd_iff_forall_nsmul_eq_zero.mp hexp) a.1⟩)⟩
  calc
    Nat.card {a : A // d • a = 0} ≤ Nat.card A[d.gcd n] :=
      Nat.card_le_card_of_injective f fun a b hab ↦
        Subtype.ext (congrArg (fun x : A[d.gcd n] ↦ x.1) hab)
    _ ≤ d.gcd n := natCard_torsionBy_gcd_le hcard d
    _ ≤ d := Nat.gcd_le_left n hd

/-- Stronger companion: the bounded-cardinality torsion hypothesis already forces finiteness. -/
-- Proof sketch: the case `d = n` makes `A[n]` finite, and the exponent hypothesis identifies
-- every element of `A` with an element of `A[n]`.
theorem finite_of_torsion_cardinal_le (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    Finite A := by
  have hfinite_torsion : Finite ↥A[n] := by
    refine Cardinal.lt_aleph0_iff_finite.mp ?_
    exact lt_of_le_of_lt (hcard n dvd_rfl) Cardinal.natCast_lt_aleph0
  letI := hfinite_torsion
  refine Finite.of_injective
      (fun x : A ↦ (⟨x, torsionBy.nsmul_iff.mpr
        ((exponent_dvd_iff_forall_nsmul_eq_zero.mp hexp) x)⟩ : A[n])) ?_
  intro x y hxy
  simpa using hxy

/-- Stronger companion: replacing the textbook equality hypothesis by `≤` still forces cyclicity. -/
-- Proof sketch: once `A` is finite, apply the canonical owner theorem
-- `isAddCyclic_of_card_nsmul_eq_zero_le`; the torsion bound for arbitrary `d > 0` factors through
-- `A[gcd d n]`.
theorem isAddCyclic_of_torsion_cardinal_le (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    IsAddCyclic A := by
  letI := finite_of_torsion_cardinal_le hexp hcard
  classical
  letI := Fintype.ofFinite A
  exact isAddCyclic_of_card_nsmul_eq_zero_le fun d hd ↦ by
    simpa [Fintype.card_subtype, Nat.card_eq_fintype_card] using
      natCard_nsmul_eq_zero_le_of_torsion_cardinal_le hexp hcard d hd

/-- Stronger companion: under the bounded-cardinality torsion hypothesis, the finite order of the
group divides `n`. -/
-- Proof sketch: combine the cyclicity clause with `IsAddCyclic.exponent_eq_card` and the exponent
-- divisibility hypothesis.
theorem natCard_dvd_of_torsion_cardinal_le (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    Nat.card A ∣ n := by
  letI := finite_of_torsion_cardinal_le hexp hcard
  letI := isAddCyclic_of_torsion_cardinal_le hexp hcard
  rw [← IsAddCyclic.exponent_eq_card]
  exact hexp

end

section

variable {A : Type u} [AddCommGroup A] {n : ℕ}

/-- Lemma 9.17.1 (1): if an abelian group of exponent dividing `n` has exactly `d` elements in
`A[d]` for every divisor `d` of `n`, then it is cyclic. -/
@[stacks 09HX]
theorem isAddCyclic_of_torsion_cardinal_eq (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] = d) :
    IsAddCyclic A :=
  isAddCyclic_of_torsion_cardinal_le hexp fun d hd ↦ by
    simpa [torsionBy.nsmul_iff] using (le_of_eq (hcard d hd) : Cardinal.mk A[d] ≤ d)

/-- Lemma 9.17.1 (2): under the source-facing equality hypothesis on the torsion subgroups, the
abelian group is finite. -/
-- Proof sketch: convert each cardinality equality into the corresponding inequality and apply the
-- bounded-cardinality finiteness clause.
@[stacks 09HX]
theorem finite_of_torsion_cardinal_eq (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] = d) :
    Finite A :=
  finite_of_torsion_cardinal_le hexp fun d hd ↦ by
    simpa [torsionBy.nsmul_iff] using (le_of_eq (hcard d hd) : Cardinal.mk A[d] ≤ d)

/-- Lemma 9.17.1 (3): under the source-facing equality hypothesis on the torsion subgroups, the
group order divides `n`. -/
-- Proof sketch: convert each cardinality equality into the corresponding inequality and apply the
-- bounded-cardinality divisibility clause.
@[stacks 09HX]
theorem natCard_dvd_of_torsion_cardinal_eq (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] = d) :
    Nat.card A ∣ n :=
  natCard_dvd_of_torsion_cardinal_le hexp fun d hd ↦ by
    simpa [torsionBy.nsmul_iff] using (le_of_eq (hcard d hd) : Cardinal.mk A[d] ≤ d)

end
