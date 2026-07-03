import Mathlib
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_58_1 (from Chap10) -/
open HomogeneousIdeal

universe u v w

section

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (s : Set S)

/- Domain triage:
* source-facing: a set of positive-degree homogeneous generators.
* core/canonical owners: `HomogeneousIdeal.irrelevant`, `HomogeneousIdeal.irrelevant_eq_span`,
  and `HomogeneousIdeal.toIdeal_irrelevant_le`.
* bridge/view: the inclusion `𝒜₊.toIdeal ≤ Ideal.span s` used by the `Proj` API, and the indexed
  family presentation via `Set.range`.

Primitive data are the set `s : Set S` and the positive-degree homogeneous membership condition on
its elements. The family presentation `f : ι → S` is derived API through `Set.range f` and should
not be the owner-level public input.

Relevant owner declarations sampled for this refinement:
* `HomogeneousIdeal.irrelevant`
* `HomogeneousIdeal.irrelevant_eq_span`
* `HomogeneousIdeal.toIdeal_irrelevant_le`
* `Ideal.homogeneous_span`
-/

/-- A set of positive-degree homogeneous elements always spans an ideal inside the irrelevant
ideal. -/
lemma span_le_irrelevant_of_pos_homogeneous
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Ideal.span s ≤ 𝒜₊.toIdeal := by
  refine Ideal.span_le.2 ?_
  intro x hx
  rcases hs_deg hx with ⟨n, hn, hx_n⟩
  exact mem_irrelevant_of_mem 𝒜 hn hx_n

/-- Library-facing bridge form of Lemma 10.58.1: `Proj`-style arguments naturally use the
inclusion `𝒜₊.toIdeal ≤ Ideal.span s`. -/
theorem homogeneous_adjoin_eq_top_iff_irrelevant_le_span
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ 𝒜₊.toIdeal ≤ Ideal.span s := by
  classical
  let B : Subalgebra (𝒜 0) S := Algebra.adjoin (𝒜 0) s
  constructor
  · intro hs_top
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn x hx
    have hspan_all :
        ∀ ⦃y : S⦄, y ∈ Algebra.adjoin (𝒜 0) s →
          y - GradedRing.projZeroRingHom 𝒜 y ∈ Ideal.span s := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
          rcases hs_deg hy with ⟨m, hm, hym⟩
          have hy_zero : GradedRing.projZeroRingHom 𝒜 y = 0 := by
            rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒜 hym hm.ne']
          simpa [hy_zero] using (Ideal.subset_span hy : y ∈ Ideal.span s)
      | algebraMap r =>
          have hr_proj :
              GradedRing.projZeroRingHom 𝒜 (algebraMap (𝒜 0) S r) = algebraMap (𝒜 0) S r := by
            change GradedRing.projZeroRingHom 𝒜 (r : S) = (r : S)
            exact congrArg ((↑) : 𝒜 0 → S) (GradedRing.projZeroRingHom'_apply_coe 𝒜 r)
          rw [hr_proj, sub_self]
          exact Ideal.zero_mem (Ideal.span s)
      | add a b ha hb ha_span hb_span =>
          simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            Ideal.add_mem (Ideal.span s) ha_span hb_span
      | mul a b ha hb ha_span hb_span =>
          have hmul_left :
              a * (b - GradedRing.projZeroRingHom 𝒜 b) ∈ Ideal.span s :=
            Ideal.mul_mem_left (Ideal.span s) a hb_span
          have hmul_right :
              (a - GradedRing.projZeroRingHom 𝒜 a) * GradedRing.projZeroRingHom 𝒜 b ∈
                Ideal.span s :=
            Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 b) (Ideal.span s) ha_span
          simpa [map_mul, sub_eq_add_neg, left_distrib, right_distrib, mul_add, add_mul,
            add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
            Ideal.add_mem (Ideal.span s) hmul_left hmul_right
    have hx_adjoin : x ∈ Algebra.adjoin (𝒜 0) s := by
      rw [hs_top]
      exact trivial
    have hx_span : x - GradedRing.projZeroRingHom 𝒜 x ∈ Ideal.span s := hspan_all hx_adjoin
    have hx_zero : GradedRing.projZeroRingHom 𝒜 x = 0 := by
      rw [GradedRing.projZeroRingHom_apply]
      exact DirectSum.decompose_of_mem_ne 𝒜 hx (Nat.ne_of_gt hn)
    simpa [hx_zero] using hx_span
  · intro hirr
    have hhom : ∀ n : ℕ, ∀ x : S, x ∈ 𝒜 n → x ∈ B := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih x hx
      cases n with
      | zero =>
          exact B.algebraMap_mem ⟨x, hx⟩
      | succ n =>
          have hx_span : x ∈ Ideal.span s :=
            hirr (mem_irrelevant_of_mem 𝒜 (Nat.succ_pos _) hx)
          rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hx_span
          rw [LinearMap.mem_range] at hx_span
          obtain ⟨l, rfl⟩ := hx_span
          have hproj :
              GradedRing.proj 𝒜 (n + 1)
                  (Finsupp.linearCombination S (fun z : s ↦ (z : S)) l) =
                Finsupp.linearCombination S (fun z : s ↦ (z : S)) l := by
            rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
          rw [← hproj, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
          refine B.sum_mem ?_
          intro z hz
          rcases hs_deg z.2 with ⟨d, hd, hzd⟩
          by_cases hdn : d ≤ n + 1
          · rw [smul_eq_mul, GradedRing.proj_apply,
              DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hzd hdn]
            exact B.mul_mem
              (ih (n + 1 - d) (Nat.sub_lt (Nat.succ_pos _) hd) _
                (DirectSum.decompose 𝒜 (l z) (n + 1 - d)).2)
              (Algebra.subset_adjoin z.2)
          · rw [smul_eq_mul, GradedRing.proj_apply,
              DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 hzd hdn]
            exact B.zero_mem
    change B = ⊤
    rw [← top_le_iff]
    intro x hx
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    exact B.sum_mem fun i hi ↦ hhom i _ (DirectSum.decompose 𝒜 x i).2

/-- Lemma 10.58.1 (Stacks, Tag `07Z4`): a set of positive-degree homogeneous elements generates
the graded ring as an algebra over its degree-zero part if and only if it generates the irrelevant
ideal as an ideal. -/
-- Proof sketch: for the forward implication, every element of the irrelevant ideal is a polynomial
-- in the chosen generators with vanishing constant term, so it lies in the ideal they generate.
-- For the reverse implication, argue by induction on degree for homogeneous elements: write a
-- positive-degree homogeneous element as an ideal combination of the generators and recursively
-- expand the lower-degree coefficients as polynomials over `𝒜 0`.
theorem homogeneous_adjoin_eq_top_iff_span_eq_irrelevant
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ Ideal.span s = 𝒜₊.toIdeal := by
  constructor
  · intro hs_top
    exact le_antisymm
      (span_le_irrelevant_of_pos_homogeneous 𝒜 s hs_deg)
      ((homogeneous_adjoin_eq_top_iff_irrelevant_le_span 𝒜 s hs_deg).1 hs_top)
  · intro hspan
    exact (homogeneous_adjoin_eq_top_iff_irrelevant_le_span 𝒜 s hs_deg).2 hspan.symm.le

end

/-! ### Lemma_10_58_2 (from Chap10) -/
open HomogeneousIdeal

universe u v

section

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage:
* source-facing: the Stacks finite-generation and Noetherian criteria phrased using the irrelevant
  ideal of a nonnegatively graded ring.
* core/canonical owners: `Algebra.FiniteType`, `HomogeneousIdeal.irrelevant`, and
  `GradedRing.GradeZero.isNoetherianRing`.
* bridge/view: `finiteType_iff_irrelevant_fg` converts between the owner finite-type datum and the
  source-facing finite generation of `𝒜₊.toIdeal`.

Primitive data are the graded ring and its canonical owner ideal `𝒜₊`. Finite type over `𝒜 0`,
Noetherianity of `𝒜 0`, and finite generation of `𝒜₊.toIdeal` are derived API and should be proved
from the owner declarations instead of being stored in a parallel wrapper.

Relevant owner declarations sampled for this refinement:
* `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`
* `homogeneous_adjoin_eq_top_iff_span_eq_irrelevant`
* `GradedRing.GradeZero.isNoetherianRing`
-/

/-- Library-facing form of Lemma 10.58.2 (Stacks, Tag `00JW`): a nonnegatively graded ring is of
finite type over its degree-zero part exactly when its irrelevant ideal is finitely generated. -/
-- Proof sketch: if `S` is finite type over `𝒜 0`, choose finitely many algebra generators and
-- decompose them into homogeneous components of positive degree; Lemma `10.58.1` then shows that
-- these homogeneous generators generate the irrelevant ideal. Conversely, if `𝒜₊` is finitely
-- generated, choose finitely many homogeneous generators for it, apply Lemma `10.58.1` to obtain
-- `Algebra.adjoin (𝒜 0) _ = ⊤`, and conclude that `S` is finite type over `𝒜 0`.
theorem finiteType_iff_irrelevant_fg :
    Algebra.FiniteType (𝒜 0) S ↔ 𝒜₊.toIdeal.FG := by
  constructor
  · intro
    classical
    obtain ⟨s, hs, hsdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
    have hs_deg : ∀ ⦃x⦄, x ∈ (s : Set S) → ∃ n > 0, x ∈ 𝒜 n := by
      intro x hx
      rcases hsdeg x hx with ⟨n, hn, hi⟩
      exact ⟨n, Nat.pos_of_ne_zero hn, hi⟩
    have hspan : Ideal.span (s : Set S) = 𝒜₊.toIdeal := by
      exact
        (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant 𝒜 (s : Set S) hs_deg).1
          (by simpa using hs)
    rw [← hspan]
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    classical
    let u : Set S := ⋃ n > 0, (𝒜 n : Set S)
    have hs' : (s : Set S) ⊆ Ideal.span u := by
      intro x hx
      have hx' : x ∈ 𝒜₊.toIdeal := by
        rw [← hs]
        exact Ideal.subset_span hx
      rw [irrelevant_eq_span 𝒜] at hx'
      simpa [u] using hx'
    obtain ⟨t, ht_sub, hs_le⟩ :=
      Submodule.subset_span_finite_of_subset_span hs'
    have ht_deg : ∀ ⦃x⦄, x ∈ (t : Set S) → ∃ n > 0, x ∈ 𝒜 n := by
      intro x hx
      rcases Set.mem_iUnion.mp (ht_sub hx) with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨hn, hi⟩
      exact ⟨n, hn, hi⟩
    have hirr : 𝒜₊.toIdeal ≤ Ideal.span (t : Set S) := by
      rw [← hs]
      refine Ideal.span_le.2 ?_
      exact hs_le
    have hspan : Ideal.span (t : Set S) = 𝒜₊.toIdeal := by
      refine le_antisymm ?_ hirr
      refine Ideal.span_le.2 ?_
      intro x hx
      rcases ht_deg hx with ⟨n, hn, hx_n⟩
      exact mem_irrelevant_of_mem 𝒜 hn hx_n
    exact ⟨⟨t, by
      exact
        (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant 𝒜 (t : Set S) ht_deg).2 hspan⟩⟩

/-- Lemma 10.58.2 (Stacks, Tag `00JW`): an `ℕ`-graded commutative ring `S` is Noetherian if and
only if its degree-zero piece `𝒜 0` is Noetherian and its irrelevant ideal `S₊` is finitely
generated. -/
-- Proof sketch: if `S` is Noetherian, then the degree-zero piece is Noetherian by the existing
-- mathlib instance `GradedRing.GradeZero.isNoetherianRing`, and the irrelevant ideal is finitely
-- generated because every ideal of a Noetherian ring is finitely generated. Conversely, if `𝒜 0`
-- is Noetherian and `𝒜₊` is finitely generated, then `finiteType_iff_irrelevant_fg` makes `S`
-- finite type over `𝒜 0`, so `Algebra.FiniteType.isNoetherianRing` yields that `S` is
-- Noetherian.
lemma isNoetherianRing_iff_degreeZero_isNoetherianRing_and_irrelevant_fg :
    IsNoetherianRing S ↔
      IsNoetherianRing (𝒜 0) ∧ 𝒜₊.toIdeal.FG := by
  constructor
  · intro
    exact ⟨inferInstance, 𝒜₊.toIdeal.fg_of_isNoetherianRing⟩
  · rintro ⟨h0, hfg⟩
    let _ : IsNoetherianRing (𝒜 0) := h0
    let _ : Algebra.FiniteType (𝒜 0) S := (finiteType_iff_irrelevant_fg 𝒜).2 hfg
    exact Algebra.FiniteType.isNoetherianRing (𝒜 0) S

/-- If a graded ring is Noetherian, then it is of finite type over its degree-zero part. -/
instance [IsNoetherianRing S] : Algebra.FiniteType (𝒜 0) S :=
  (finiteType_iff_irrelevant_fg 𝒜).2 (𝒜₊.toIdeal.fg_of_isNoetherianRing)

end

/-! ### Definition_10_58_3 (from Chap10) -/
universe u

open Filter
open scoped BigOperators

section

variable {A : Type u} [AddCommGroup A]

/-- Definition 10.58.3: a function on the integers is a numerical polynomial if, for all
sufficiently large integers `n`, it agrees with a finite sum `∑_{i=0}^r \binom{n}{i} a_i` with
coefficients in the abelian group `A`. In Lean, the source's partial-function wording is modeled
canonically by eventual equality at `atTop` for a total function `ℤ → A`. -/
def IsNumericalPolynomial (f : ℤ → A) : Prop :=
  ∃ (r : ℕ) (a : Fin (r + 1) → A),
    f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

end

/-! ### Lemma_10_58_4 (from Chap10) -/
universe u v

section

variable {A : Type u} [AddCommGroup A]
variable {A' : Type v} [AddCommGroup A']

/-- Lemma 10.58.4: postcomposing a numerical polynomial with a homomorphism of abelian groups
again gives a numerical polynomial. -/
theorem IsNumericalPolynomial.comp {f : ℤ → A} (hf : IsNumericalPolynomial f) (φ : A →+ A') :
    IsNumericalPolynomial (φ ∘ f) := by
  rcases hf with ⟨r, a, ha⟩
  refine ⟨r, φ ∘ a, (ha.fun_comp φ).trans ?_⟩
  exact .of_eq <| by
    funext n
    simp [Function.comp, map_sum, map_zsmul]

end

/-! ### Lemma_10_58_5 (from Chap10) -/
universe u

open Filter
open scoped BigOperators

section

variable {A : Type u} [AddCommGroup A]

private def numericalPolynomialAntiderivativeCoeffs {r : ℕ} (a : Fin (r + 1) → A) :
    Fin (r + 2) → A :=
  Fin.cons (a 0) <|
    Fin.snoc (fun i : Fin r ↦ a i.castSucc + a i.succ) (a <| Fin.last r)

private def numericalPolynomialCoeffsWithConst {m : ℕ} (c : A) (a : Fin (m + 1) → A) :
    Fin (m + 1) → A :=
  Fin.cons (c + a 0) (Fin.tail a)

private theorem numericalPolynomialExpansion_antiderivativeCoeffs {r : ℕ}
    (a : Fin (r + 1) → A) (n : ℤ) :
    (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i) =
      ∑ i : Fin (r + 1), Ring.choose (n + 1) ((i : ℕ) + 1) • a i := by
  rw [Fin.sum_univ_succ]
  simp_rw [numericalPolynomialAntiderivativeCoeffs, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.snoc_castSucc, Fin.snoc_last, smul_add]
  rw [Finset.sum_add_distrib]
  have hcast :
      (∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
          Ring.choose n ↑(Fin.last r).succ • a (Fin.last r) =
        ∑ i : Fin (r + 1), Ring.choose n ↑i.succ • a i := by
    simpa using
      (Fin.sum_univ_castSucc (fun x : Fin (r + 1) ↦ Ring.choose n ↑x.succ • a x)).symm
  rw [show
    (∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
        ∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.succ +
        Ring.choose n ↑(Fin.last r).succ • a (Fin.last r) =
      ((∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.castSucc) +
          Ring.choose n ↑(Fin.last r).succ • a (Fin.last r)) +
        ∑ i : Fin r, Ring.choose n ↑i.castSucc.succ • a i.succ by
      abel]
  rw [hcast]
  rw [Fin.sum_univ_succ]
  simp_rw [Ring.choose_succ_succ]
  rw [Fin.sum_univ_succ]
  simp_rw [add_smul]
  simp [Fin.val_castSucc, add_comm, add_left_comm, add_assoc]
  rw [← Finset.sum_add_distrib]

private theorem numericalPolynomialExpansion_coeffsWithConst {m : ℕ}
    (c : A) (a : Fin (m + 1) → A) (n : ℤ) :
    (∑ i : Fin (m + 1), Ring.choose n (i : ℕ) • numericalPolynomialCoeffsWithConst c a i) =
      c + ∑ i : Fin (m + 1), Ring.choose n (i : ℕ) • a i := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [numericalPolynomialCoeffsWithConst, add_assoc]
  abel

private theorem numericalPolynomialExpansion_antiderivativeCoeffs_sub_pred {r : ℕ}
    (a : Fin (r + 1) → A)
    (n : ℤ) :
    (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i) -
        ∑ i : Fin (r + 2), Ring.choose (n - 1) (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i =
      ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i := by
  rw [numericalPolynomialExpansion_antiderivativeCoeffs,
    numericalPolynomialExpansion_antiderivativeCoeffs, show n - 1 + 1 = n by ring,
    sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← sub_eq_add_neg, ← sub_smul, Ring.choose_succ_succ, add_sub_cancel_right]

private theorem eventuallyEq_const_of_sub_pred_eq_zero (f : ℤ → A)
    (h : ∀ᶠ n : ℤ in atTop, f n - f (n - 1) = 0) :
    ∃ c : A, f =ᶠ[atTop] fun _ ↦ c := by
  rcases Filter.eventually_atTop.mp h with ⟨N, hN⟩
  refine ⟨f (N - 1), Filter.eventually_atTop.mpr ⟨N - 1, ?_⟩⟩
  intro n hn
  induction n, hn using Int.le_induction with
  | base =>
      rfl
  | succ n hn ih =>
      have hstep : f (n + 1) = f n := by
        have hn' : N ≤ n + 1 := by linarith
        simpa using sub_eq_zero.mp (hN (n + 1) hn')
      exact hstep.trans ih

-- Proof sketch: choose a numerical-polynomial description of `n ↦ f n - f (n - 1)`, then
-- antidifferentiate term-by-term using `Δ (choose (n + 1) (i + 1)) = choose n i`. After
-- subtracting this antiderivative from `f`, the resulting function has eventual difference zero,
-- hence is eventually constant, which supplies the missing constant term in the binomial
-- expansion of `f`.
/-- Lemma 10.58.5: if the eventual first difference `n ↦ f(n) - f(n - 1)` is a numerical
polynomial, then `f` itself is a numerical polynomial. -/
theorem IsNumericalPolynomial.of_sub_pred {f : ℤ → A}
    (h : IsNumericalPolynomial (fun n ↦ f n - f (n - 1))) : IsNumericalPolynomial f := by
  rcases h with ⟨r, a, ha⟩
  let g : ℤ → A :=
    fun n ↦ ∑ i : Fin (r + 2), Ring.choose n (i : ℕ) • numericalPolynomialAntiderivativeCoeffs a i
  have hzero : ∀ᶠ n : ℤ in atTop, (f n - g n) - (f (n - 1) - g (n - 1)) = 0 := by
    filter_upwards [ha] with n hn
    have hg :
        g n - g (n - 1) = ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i :=
      by
        simpa [g] using numericalPolynomialExpansion_antiderivativeCoeffs_sub_pred a n
    calc
      (f n - g n) - (f (n - 1) - g (n - 1))
          = (f n - f (n - 1)) - (g n - g (n - 1)) := by
            abel
      _ = (∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i) -
            ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i := by
            rw [hn, hg]
      _ = 0 := sub_self _
  rcases eventuallyEq_const_of_sub_pred_eq_zero (fun n ↦ f n - g n) hzero with ⟨c, hc⟩
  refine ⟨r + 1, numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a), ?_⟩
  filter_upwards [hc] with n hn
  have hg :
      (∑ i : Fin (r + 2), Ring.choose n (i : ℕ) •
          numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) i) =
        c + g n :=
    by
      simpa [g] using
        numericalPolynomialExpansion_coeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) n
  calc
    f n = c + g n := by
      exact sub_eq_iff_eq_add.mp hn
    _ = ∑ i : Fin (r + 2), Ring.choose n (i : ℕ) •
        numericalPolynomialCoeffsWithConst c (numericalPolynomialAntiderivativeCoeffs a) i := by
      symm
      exact hg

end

/-! ### Lemma_10_58_6 (from Chap10) -/
open scoped BigOperators DirectSum

universe u v w

section

local instance instAddActionNatIntLemma10586 : AddAction ℕ ℤ where
  vadd n d := n + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → Submodule R S)
variable (ℳ : ℤ → Submodule S M)
variable [GradedRing 𝒜]
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

local instance : Module (𝒜 0) M := Module.restrictScalars (𝒜 0) S M

/-- Helper for Lemma 10.58.6: the restricted `S₀`-module structure on `M` is compatible with the
ambient `S`-module structure as a scalar tower. -/
local instance graded_zero_piece_isScalarTower : IsScalarTower (𝒜 0) S M :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/- Domain triage:
* `source-facing`: Lemma `10.58.6` asserts that each graded piece `Mₙ` of a finite graded
  `S`-module is finite over the degree-zero ring `S₀ = 𝒜 0`.
* `core/canonical` owners: the ambient graded module is carried by
  `DirectSum.Decomposition ℳ` and `SetLike.GradedSMul 𝒜 ℳ`, ring finiteness over `S₀` is carried
  by `Algebra.FiniteType S₀ S`, and module finiteness is carried by `Module.Finite`.
* `bridge/view`: this theorem passes from the owner-level finiteness of the graded ring/module to
  the individual component `ℳ n`.

Primitive data are the graded ring, the graded module, and the ambient finiteness hypotheses. The
finiteness of each component is derived API; it should not be stored as extra graded-module data.

Relevant owner declarations sampled for this refinement:
* `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`
* `sufficiently_divisible_veronese_generated_in_degree_one`
* `span_eq_top_of_quotient_span_eq_top_of_homogeneous`
-/

variable [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]

/-- Helper for Lemma 10.58.6: a finite graded module admits a finite family of homogeneous
generators indexed by a finite type. -/
lemma exists_finite_homogeneous_module_generators :
    ∃ (κ : Type w) (_ : Fintype κ) (m : κ → M) (η : κ → ℤ),
      (∀ j, m j ∈ ℳ (η j)) ∧ Submodule.span S (Set.range m) = ⊤ := by
  classical
  let hfg : (⊤ : Submodule S M).FG := Module.Finite.fg_top (R := S) (M := M)
  obtain ⟨G, _, g, hg⟩ := (Submodule.fg_iff_exists_finite_generating_family (A := S)
    (M := M) (N := (⊤ : Submodule S M))).mp hfg
  let κ : Type w := Σ j : G, { d // d ∈ (DirectSum.decompose ℳ (g j)).support }
  let m : κ → M := fun j ↦ (DirectSum.decompose ℳ (g j.1) j.2.1 : ℳ j.2.1)
  let η : κ → ℤ := fun j ↦ j.2.1
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype κ := inferInstance
  -- Decompose a finite generating family into all of its homogeneous components.
  refine ⟨κ, inferInstance, m, η, ?_, ?_⟩
  · intro j
    exact (DirectSum.decompose ℳ (g j.1) j.2.1).2
  · rw [← top_le_iff, ← hg, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← DirectSum.sum_support_decompose ℳ (g j)]
    refine Submodule.sum_mem _ ?_
    intro d hd
    exact Submodule.subset_span ⟨⟨j, ⟨d, hd⟩⟩, rfl⟩

/-- Helper for Lemma 10.58.6: a finite-type graded ring admits finitely many positive-degree
homogeneous algebra generators over its degree-zero piece. -/
lemma exists_finite_positive_homogeneous_ring_generators :
    ∃ (ι : Type v) (_ : Fintype ι) (v : ι → S) (δ : ι → ℕ),
      (∀ i, 0 < δ i ∧ v i ∈ 𝒜 (δ i)) ∧
        Algebra.adjoin (𝒜 0) (Set.range v) = ⊤ := by
  classical
  obtain ⟨s, hs, hsdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  let e : s ≃ Fin s.card := Finset.equivFin s
  let v : Fin s.card → S := fun i ↦ ((e.symm i : s) : S)
  choose δ hδ0 hδmem using
    fun i : Fin s.card ↦ hsdeg (v i) ((e.symm i).2)
  have hv_range : Set.range v = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simp [v, e]
  let ι : Type v := ULift.{v} (Fin s.card)
  let v' : ι → S := fun i ↦ v i.down
  let δ' : ι → ℕ := fun i ↦ δ i.down
  have hv'_range : Set.range v' = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i⟩, rfl⟩
  -- Reindex the finite homogeneous algebra generators by the subtype of chosen elements.
  refine ⟨ι, inferInstance, v', δ', ?_, ?_⟩
  · intro i
    exact ⟨Nat.pos_of_ne_zero (hδ0 i.down), hδmem i.down⟩
  · simpa [hv'_range, hv_range] using hs

omit [DirectSum.Decomposition ℳ] [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: a weighted monomial in homogeneous ring generators sends a
homogeneous module generator to the predicted graded piece. -/
lemma weighted_monomial_smul_mem_degree_piece
    {ι : Type*} [Fintype ι]
    (v : ι → S) (δ : ι → ℕ) (m : M) (η : ℤ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i)) (hm : m ∈ ℳ η) (e : ι → ℕ) :
    ((∏ i, v i ^ e i : S) • m) ∈ ℳ ((∑ i, (e i : ℤ) * (δ i : ℤ)) + η) := by
  classical
  have hprod :
      (∏ i, v i ^ e i : S) ∈ 𝒜 (∑ i, e i * δ i) := by
    -- The weighted degree of a product of homogeneous generators is the sum of the weighted
    -- degrees of the factors.
    simpa [nsmul_eq_mul] using
      (SetLike.prod_pow_mem_graded 𝒜 δ v e (fun i _ ↦ hv i))
  have hsmul :
      ((∏ i, v i ^ e i : S) • m) ∈ ℳ ((((∑ i, e i * δ i : ℕ) : ℤ) + η)) := by
    -- The graded action shifts the module degree by the weighted degree of the scalar monomial.
    have hindex : (∑ i, e i * δ i) +ᵥ η = ((((∑ i, e i * δ i : ℕ) : ℤ) + η)) := rfl
    exact hindex ▸ SetLike.GradedSMul.smul_mem hprod hm
  -- Compatibility of the graded ring action with the module grading gives the target degree.
  simpa [Nat.cast_sum, Nat.cast_mul] using hsmul

omit [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: a homogeneous scalar of degree `d` lies in the degree-zero span of
the weighted monomials in the chosen positive-degree homogeneous generators whose total degree is
exactly `d`. -/
lemma homogeneous_scalar_mem_span_weighted_monomials
    {ι : Type*} [Fintype ι]
    (v : ι → S) (δ : ι → ℕ)
    (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    {d : ℕ} {x : S} (hx : x ∈ 𝒜 d) :
    x ∈ Submodule.span (𝒜 0)
      (Set.range fun e : {e : ι → Fin (d + 1) // ∑ i, (e i : ℕ) * δ i = d} ↦
        ∏ i, v i ^ (e.1 i : ℕ)) := by
  classical
  let W : Set S :=
    Set.range fun e : {e : ι → Fin (d + 1) // ∑ i, (e i : ℕ) * δ i = d} ↦
      ∏ i, v i ^ (e.1 i : ℕ)
  have hx_span : x ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    -- Rewrite the algebra-generation hypothesis into the span form used by span induction.
    have hx_adjoin : x ∈ Algebra.adjoin (𝒜 0) (Set.range v) := by
      rw [hgen]
      trivial
    change x ∈ (Algebra.adjoin (𝒜 0) (Set.range v)).toSubmodule at hx_adjoin
    simpa [Algebra.adjoin_eq_span] using hx_adjoin
  have hcomponent : (DirectSum.decompose 𝒜 x d : S) ∈ Submodule.span (𝒜 0) W := by
    clear hx
    induction hx_span using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := Submonoid.exists_of_mem_closure_range v y hy
        by_cases ha : ∑ i, a i * δ i = d
        · have hprod_mem : (∏ i, v i ^ a i : S) ∈ 𝒜 d := by
            have hmem :
                (∏ i, v i ^ a i : S) ∈ 𝒜 (∑ i, a i * δ i) := by
              simpa [nsmul_eq_mul] using
                (SetLike.prod_pow_mem_graded 𝒜 δ v a (fun i _ ↦ hv i))
            simpa [ha] using hmem
          have hbound : ∀ i, a i ≤ d := by
            intro i
            have hi_le_sum : a i * δ i ≤ ∑ j, a j * δ j := by
              simpa using
                (Finset.single_le_sum
                  (fun j _ ↦ Nat.zero_le (a j * δ j)) (Finset.mem_univ i) :
                  a i * δ i ≤ ∑ j, a j * δ j)
            have hone : 1 ≤ δ i := Nat.succ_le_of_lt (hδ i)
            calc
              a i = a i * 1 := by simp
              _ ≤ a i * δ i := by exact Nat.mul_le_mul_left _ hone
              _ ≤ d := by simpa [ha] using hi_le_sum
          let e : ι → Fin (d + 1) := fun i ↦ ⟨a i, Nat.lt_succ_of_le (hbound i)⟩
          have hw : (∏ i, v i ^ a i : S) ∈ Submodule.span (𝒜 0) W := by
            -- Package the exponent vector into the finite admissible family indexed by `Fin`.
            refine Submodule.subset_span ?_
            refine ⟨⟨e, ?_⟩, ?_⟩
            · simpa [e] using ha
            · simp [e]
          simpa [W, DirectSum.decompose_of_mem_same 𝒜 hprod_mem] using hw
        · have hprod_mem :
            (∏ i, v i ^ a i : S) ∈ 𝒜 (∑ i, a i * δ i) := by
            simpa [nsmul_eq_mul] using
              (SetLike.prod_pow_mem_graded 𝒜 δ v a (fun i _ ↦ hv i))
          simpa [W, DirectSum.decompose_of_mem_ne 𝒜 hprod_mem ha] using
            (show (0 : S) ∈ Submodule.span (𝒜 0) W from
              (Submodule.span (𝒜 0) W).zero_mem)
    | zero =>
        simpa [W] using
          (show (0 : S) ∈ Submodule.span (𝒜 0) W from
            (Submodule.span (𝒜 0) W).zero_mem)
    | add y z hy hz hy' hz' =>
        -- The fixed-degree component map is additive.
        simpa [W, DirectSum.decompose_add, AddMemClass.coe_add] using
          (Submodule.span (𝒜 0) W).add_mem hy' hz'
    | smul r y hy hy' =>
        -- Multiplication by a degree-zero scalar keeps the component inside the target span.
        have hdecomp :
            (DirectSum.decompose 𝒜 ((algebraMap (𝒜 0) S r : S) * y) d : S) =
              r • (DirectSum.decompose 𝒜 y d : S) := by
          calc
            (DirectSum.decompose 𝒜 ((algebraMap (𝒜 0) S r : S) * y) d : S) =
                (algebraMap (𝒜 0) S r : S) * (DirectSum.decompose 𝒜 y d : S) := by
                  simpa using
                    (DirectSum.coe_decompose_mul_of_left_mem_zero (𝒜 := 𝒜)
                      (a := (algebraMap (𝒜 0) S r : S)) (b := y) (j := d) (SetLike.coe_mem r))
            _ = r • (DirectSum.decompose 𝒜 y d : S) := by
                  rw [Algebra.smul_def]
        have hdecomp' :
            (DirectSum.decompose 𝒜 (r • y) d : S) =
              r • (DirectSum.decompose 𝒜 y d : S) := by
          simpa [Algebra.smul_def] using hdecomp
        exact hdecomp' ▸ Submodule.smul_mem (Submodule.span (𝒜 0) W) r hy'
  -- The input scalar is already homogeneous of degree `d`, so its `d`-component is itself.
  simpa [W, DirectSum.decompose_of_mem_same 𝒜 hx] using hcomponent

omit [GradedRing 𝒜] [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: a homogeneous scalar term contributes its full ambient scalar action
to the matching graded component. -/
lemma directsum_component_of_homogeneous_scalar_smul_same
    {η n : ℤ} {d : ℕ} {a_d : S} (ha_d : a_d ∈ 𝒜 d)
    {m_eta : M} (hm_eta : m_eta ∈ ℳ η)
    (hnd : (d : ℤ) + η = n) :
    ((DirectSum.decompose ℳ (a_d • m_eta) n : ℳ n) : M) = a_d • m_eta := by
  -- A homogeneous scalar piece sends a homogeneous module generator into one known degree.
  have hsmul : a_d • m_eta ∈ ℳ ((d : ℤ) + η) := SetLike.GradedSMul.smul_mem ha_d hm_eta
  -- Since the target component matches that degree, the projection is the element itself.
  subst n
  simpa using (DirectSum.decompose_of_mem_same ℳ hsmul)

omit [GradedRing 𝒜] [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: a homogeneous scalar term contributes nothing to an off-degree
graded component. -/
lemma directsum_component_of_homogeneous_scalar_smul_ne
    {η n : ℤ} {d : ℕ} {a_d : S} (ha_d : a_d ∈ 𝒜 d)
    {m_eta : M} (hm_eta : m_eta ∈ ℳ η)
    (hnd : (d : ℤ) + η ≠ n) :
    ((DirectSum.decompose ℳ (a_d • m_eta) n : ℳ n) : M) = 0 := by
  -- The homogeneous scalar action still lands in the single degree `(d : ℤ) + η`.
  have hsmul : a_d • m_eta ∈ ℳ ((d : ℤ) + η) := SetLike.GradedSMul.smul_mem ha_d hm_eta
  -- An off-degree projection of a homogeneous element vanishes.
  simpa using (DirectSum.decompose_of_mem_ne ℳ hsmul hnd)

omit [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: for a homogeneous module generator `m ∈ M_η`, only the scalar
component of degree `d` contributes to the degree-`n` component of `a • m` when
`(d : ℤ) + η = n`. -/
lemma decompose_smul_homogeneous_generator_eq
    {η n : ℤ} {d : ℕ} {a : S} {m : M}
    (hm : m ∈ ℳ η) (hnd : (d : ℤ) + η = n) :
    ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
      (((DirectSum.decompose 𝒜 a d : 𝒜 d) : S) • m) := by
  classical
  -- Route correction: first expand `a` into homogeneous pieces, then isolate the unique degree
  -- that can survive in the `n`-component after acting on the homogeneous vector `m`.
  have happly :
      ((((∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m)) n : ℳ n) : M)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n : ℳ n) : M) := by
    -- Evaluate the `n`-coordinate after moving `DirectSum.decompose` through the finite sum.
    simpa using congrArg (fun z : ℳ n ↦ (z : M))
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 a).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m))
        n)
  have hsum :
      ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n : ℳ n) : M) =
        ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) d : 𝒜 d) : S) • m) n : ℳ n) : M) := by
    by_cases hd : d ∈ (DirectSum.decompose 𝒜 a).support
    · rw [Finset.sum_eq_single_of_mem d hd]
      · intro i hi hid
        -- Any scalar piece whose degree is not `d` misses the target component `n`.
        have hi_ne : (i : ℤ) + η ≠ n := by
          intro hi_eq
          have hcast : (i : ℤ) = d := by
            linarith [hi_eq, hnd]
          exact hid (Int.ofNat.inj hcast)
        simpa using
          (directsum_component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ)
            (ha_d := (DirectSum.decompose 𝒜 a i).2)
            (hm_eta := hm) hi_ne)
    · have hsum_zero :
          ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
              ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n : ℳ n) : M) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        -- Without the matching degree `d`, every homogeneous scalar piece lands off degree `n`.
        have hi_ne : (i : ℤ) + η ≠ n := by
          intro hi_eq
          have hcast : (i : ℤ) = d := by
            linarith [hi_eq, hnd]
          exact hd (Int.ofNat.inj hcast ▸ hi)
        simpa using
          (directsum_component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ)
            (ha_d := (DirectSum.decompose 𝒜 a i).2)
            (hm_eta := hm) hi_ne)
      have hdzero : DirectSum.decompose 𝒜 a d = 0 := by
        simpa [DFinsupp.mem_support_iff] using hd
      rw [hsum_zero]
      simp [hdzero]
  have hdecomp :
      ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n : ℳ n) : M) := by
    have h :=
      congrArg (fun z : S ↦ ((DirectSum.decompose ℳ (z • m) n : ℳ n) : M))
        (DirectSum.sum_support_decompose 𝒜 a)
    simpa [Finset.sum_smul, DirectSum.decompose_sum, happly] using h.symm
  calc
    ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n : ℳ n) : M) := hdecomp
    _ = ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) d : 𝒜 d) : S) • m) n : ℳ n) : M) := hsum
    _ = (((DirectSum.decompose 𝒜 a d : 𝒜 d) : S) • m) := by
          simpa using
            (directsum_component_of_homogeneous_scalar_smul_same
              (𝒜 := 𝒜) (ℳ := ℳ)
              (ha_d := (DirectSum.decompose 𝒜 a d).2)
              (hm_eta := hm) hnd)

omit [DirectSum.Decomposition ℳ] [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: each admissible weighted monomial built from the chosen
homogeneous ring and module generators lands in the target homogeneous piece `M_n`. -/
lemma admissible_weighted_module_monomial_mem_degree_piece
    {κ ι : Type*} [Fintype ι]
    (m : κ → M) (η : κ → ℤ)
    (hm : ∀ j, m j ∈ ℳ (η j))
    (v : ι → S) (δ : ι → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    {n : ℤ}
    (t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
      {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1}) :
    ((∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1) ∈ ℳ n := by
  have hmem :=
    weighted_monomial_smul_mem_degree_piece
      (𝒜 := 𝒜) (ℳ := ℳ) v δ (m t.1) (η t.1) hv (hm t.1)
      (fun i ↦ (t.2.2.1 i : ℕ))
  have hdeg : (∑ i, ((t.2.2.1 i : ℕ) : ℤ) * (δ i : ℤ)) = t.2.1.1 := by
    exact_mod_cast t.2.2.2
  have hindex : (∑ i, ((t.2.2.1 i : ℕ) : ℤ) * (δ i : ℤ)) + η t.1 = n := by
    rw [hdeg]
    exact t.2.1.2
  have hmem' :
      ((∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1) ∈
        ℳ ((∑ i, ((t.2.2.1 i : ℕ) : ℤ) * (δ i : ℤ)) + η t.1) := by
    simpa [Nat.cast_mul] using hmem
  simpa [hindex] using hmem'

omit [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: coercing a finite `(𝒜 0)`-linear combination in one graded piece
to the ambient module matches the corresponding ambient linear combination. -/
lemma smul_subtype_sum_coe
    {α : Type*} [Fintype α] {n : ℤ}
    (moduleMon : α → ℳ n) (f : α → M)
    (hmoduleMon : ∀ a, ((moduleMon a : ℳ n) : M) = f a)
    (c : α → 𝒜 0) :
    (((∑ a, c a • moduleMon a : ℳ n) : ℳ n) : M) =
      ∑ a, c a • f a := by
  classical
  -- Coercing the subtype sum just forgets the grading witnesses on each admissible monomial.
  calc
    (((∑ a, c a • moduleMon a : ℳ n) : ℳ n) : M) =
        ∑ a, (((c a • moduleMon a : ℳ n) : ℳ n) : M) := by
          simp
    _ = ∑ a, c a • (((moduleMon a : ℳ n) : M)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rfl
    _ = ∑ a, c a • f a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [hmoduleMon a]

omit [DirectSum.Decomposition ℳ] [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: a homogeneous scalar in the degree-`d` weighted-monomial span
acts on a fixed homogeneous module generator inside the admissible weighted-monomial span of
`Mₙ`. -/
lemma smul_mem_span_admissible_weighted_module_monomials_of_scalar_span
    {κ ι : Type*} [Fintype ι]
    (m : κ → M) (η : κ → ℤ)
    (hm : ∀ j, m j ∈ ℳ (η j))
    (v : ι → S) (δ : ι → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    {n : ℤ} {j : κ} {d : ℕ}
    (hnd : (d : ℤ) + η j = n)
    {a : S} (ha : a ∈ 𝒜 d)
    (ha_span : a ∈ Submodule.span (𝒜 0)
      (Set.range fun e : {e : ι → Fin (d + 1) // ∑ i, (e i : ℕ) * δ i = d} ↦
        ∏ i, v i ^ (e.1 i : ℕ))) :
    (⟨a • m j, by
      have hsmul : a • m j ∈ ℳ ((d : ℤ) + η j) := SetLike.GradedSMul.smul_mem ha (hm j)
      simpa [hnd] using hsmul⟩ : ℳ n) ∈
        Submodule.span (𝒜 0)
          (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
              {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
            ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
              admissible_weighted_module_monomial_mem_degree_piece
                (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) := by
  classical
  let moduleMon :
      {e : ι → Fin (d + 1) // ∑ i, (e i : ℕ) * δ i = d} → ℳ n := fun e ↦
    ⟨(∏ i, v i ^ (e.1 i : ℕ) : S) • m j,
      admissible_weighted_module_monomial_mem_degree_piece
        (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv ⟨j, ⟨⟨d, hnd⟩, e⟩⟩⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝒜 0)).mp ha_span
  -- Multiply the ring-side degree-`d` monomial decomposition by the fixed homogeneous generator.
  have hsmul_eq :
      ∑ e, c e • (((∏ i, v i ^ (e.1 i : ℕ) : S)) • m j) = a • m j := by
    have hmul := congrArg (fun z : S ↦ z • m j) hc
    calc
      ∑ e, c e • (((∏ i, v i ^ (e.1 i : ℕ) : S)) • m j) =
          (∑ e, c e • (∏ i, v i ^ (e.1 i : ℕ) : S)) • m j := by
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl ?_
            intro e he
            rw [smul_assoc]
      _ = a • m j := by
            simpa using hmul
  have hsum_coe :
      (((∑ e, c e • moduleMon e : ℳ n) : ℳ n) : M) =
        ∑ e, c e • (((∏ i, v i ^ (e.1 i : ℕ) : S)) • m j) := by
    -- This isolates the ambient-versus-subtype coercion on the admissible monomial sum.
    refine smul_subtype_sum_coe (𝒜 := 𝒜) (ℳ := ℳ) moduleMon
      (fun e ↦ ((∏ i, v i ^ (e.1 i : ℕ) : S)) • m j) ?_ c
    intro e
    rfl
  have hsubtype_eq :
      (⟨a • m j, by
        have hsmul : a • m j ∈ ℳ ((d : ℤ) + η j) := SetLike.GradedSMul.smul_mem ha (hm j)
        simpa [hnd] using hsmul⟩ : ℳ n) =
        ∑ e, c e • moduleMon e := by
    apply Subtype.ext
    -- Route correction: compare the ambient `M`-valued sums first, then lift back to `ℳ n`.
    calc
      (((⟨a • m j, by
        have hsmul : a • m j ∈ ℳ ((d : ℤ) + η j) := SetLike.GradedSMul.smul_mem ha (hm j)
        simpa [hnd] using hsmul⟩ : ℳ n) : ℳ n) : M) = a • m j := rfl
      _ = ∑ e, c e • (((∏ i, v i ^ (e.1 i : ℕ) : S)) • m j) := by
            simpa using hsmul_eq.symm
      _ = (((∑ e, c e • moduleMon e : ℳ n) : ℳ n) : M) := by
            simpa using hsum_coe.symm
  have hsum_mem :
      (∑ e, c e • moduleMon e : ℳ n) ∈
        Submodule.span (𝒜 0)
          (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
              {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
            ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
              admissible_weighted_module_monomial_mem_degree_piece
                (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) := by
    -- Each admissible monomial term is one of the sigma-indexed generators of the target span.
    refine Submodule.sum_mem _ ?_
    intro e he
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨j, ⟨⟨d, hnd⟩, e⟩⟩, rfl⟩
  exact hsubtype_eq.symm ▸ hsum_mem

/-- Helper for Lemma 10.58.6: for fixed `j` and `n`, the degree fiber
`{d : ℕ // (d : ℤ) + η j = n}` has at most one element. -/
lemma degree_fiber_subsingleton
    {κ : Type*} (η : κ → ℤ) (j : κ) (n : ℤ) :
    Subsingleton {d : ℕ // (d : ℤ) + η j = n} := by
  refine ⟨?_⟩
  intro a b
  apply Subtype.ext
  -- The degree equation determines the natural number `d` uniquely after casting to `ℤ`.
  have hab : (a.1 : ℤ) = b.1 := by
    linarith [a.2, b.2]
  exact Int.ofNat.inj hab

omit [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: after decomposing a scalar into homogeneous pieces, the degree-`n`
component of its action on one homogeneous generator already lies in the admissible weighted
module-monomial span. -/
lemma degree_n_component_smul_generator_mem_span_admissible_weighted_module_monomials
    {κ ι : Type*} [Fintype ι]
    (m : κ → M) (η : κ → ℤ)
    (hm : ∀ j, m j ∈ ℳ (η j))
    (v : ι → S) (δ : ι → ℕ)
    (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    (n : ℤ) (j : κ) (c : S) :
    (DirectSum.decompose ℳ (c • m j) n : ℳ n) ∈
      Submodule.span (𝒜 0)
        (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
            {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
          ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
            admissible_weighted_module_monomial_mem_degree_piece
              (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) := by
  classical
  -- Route correction: decompose the scalar first and keep only the support pieces whose degree
  -- can actually land in `Mₙ` after acting on the fixed homogeneous generator `m j`.
  rw [← DirectSum.sum_support_decompose 𝒜 c, Finset.sum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ i ∈ (DirectSum.decompose 𝒜 c).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m j)) n : ℳ n)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 c).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m j) n : ℳ n) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 c).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m j))
        n)
  rw [happly]
  refine Submodule.sum_mem _ ?_
  intro i hi
  by_cases hnd : (i : ℤ) + η j = n
  · -- The matching homogeneous coefficient is in the ring-side monomial span, so its action on
    -- `m j` lies in the admissible module-monomial span.
    have hi_span :
        (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) ∈
          Submodule.span (𝒜 0)
            (Set.range fun e : {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i} ↦
              ∏ k, v k ^ (e.1 k : ℕ))) :=
      homogeneous_scalar_mem_span_weighted_monomials
        (𝒜 := 𝒜) v δ hδ hv hgen (DirectSum.decompose 𝒜 c i).2
    have hterm_span :
        (⟨(((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m j), by
          have hsmul :
              (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m j) ∈ ℳ ((i : ℤ) + η j) :=
            SetLike.GradedSMul.smul_mem (DirectSum.decompose 𝒜 c i).2 (hm j)
          simpa [hnd] using hsmul⟩ : ℳ n) ∈
          Submodule.span (𝒜 0)
            (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
                {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
              ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
                admissible_weighted_module_monomial_mem_degree_piece
                  (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) :=
      smul_mem_span_admissible_weighted_module_monomials_of_scalar_span
        (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv hnd (DirectSum.decompose 𝒜 c i).2 hi_span
    have hterm_eq :
        (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m j) n : ℳ n) =
          ⟨(((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m j), by
            have hsmul :
                (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m j) ∈ ℳ ((i : ℤ) + η j) :=
              SetLike.GradedSMul.smul_mem (DirectSum.decompose 𝒜 c i).2 (hm j)
            simpa [hnd] using hsmul⟩ := by
      apply Subtype.ext
      simpa using
        (directsum_component_of_homogeneous_scalar_smul_same
          (𝒜 := 𝒜) (ℳ := ℳ)
          (ha_d := (DirectSum.decompose 𝒜 c i).2)
          (hm_eta := hm j) hnd)
    exact hterm_eq ▸ hterm_span
  · -- Every off-degree homogeneous coefficient vanishes after projecting to degree `n`.
    have hterm_zero :
        (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m j) n : ℳ n) = 0 := by
      apply Subtype.ext
      simpa using
        (directsum_component_of_homogeneous_scalar_smul_ne
          (𝒜 := 𝒜) (ℳ := ℳ)
          (ha_d := (DirectSum.decompose 𝒜 c i).2)
          (hm_eta := hm j) hnd)
    have hzero_mem :
        (0 : ℳ n) ∈
          Submodule.span (𝒜 0)
            (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
                {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
              ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
                admissible_weighted_module_monomial_mem_degree_piece
                  (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) :=
      Submodule.zero_mem _
    exact hterm_zero ▸ hzero_mem

omit [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] in
/-- Helper for Lemma 10.58.6: the admissible weighted monomials in the chosen ring and module
generators span the homogeneous piece `M_n` over `S₀`. -/
lemma mem_span_admissible_weighted_module_monomials
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (m : κ → M) (η : κ → ℤ)
    (hm : ∀ j, m j ∈ ℳ (η j))
    (hspan : Submodule.span S (Set.range m) = ⊤)
    (v : ι → S) (δ : ι → ℕ)
    (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    (n : ℤ) :
    ∀ x : ℳ n,
      x ∈ Submodule.span (𝒜 0)
        (Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
            {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
          ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
            admissible_weighted_module_monomial_mem_degree_piece
              (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩) := by
  letI : Fintype κ := Fintype.ofFinite κ
  intro x
  let W :
      Set (ℳ n) :=
        Set.range fun t : Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
            {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1} ↦
          ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
            admissible_weighted_module_monomial_mem_degree_piece
              (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩
  have hx_mem : (x : M) ∈ Submodule.span S (Set.range m) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx_mem
  have hx_decompose :
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) = x := by
    -- Project the finite generator expansion termwise to the fixed degree `n`.
    have hproj := congrArg (fun y : M ↦ DirectSum.decompose ℳ y n) hc
    simpa [DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
      DirectSum.decompose_of_mem_same ℳ x.2] using hproj
  have hsum_mem :
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) ∈ Submodule.span (𝒜 0) W := by
    -- Each generator contribution already lies in the admissible weighted-monomial span.
    refine Submodule.sum_mem _ ?_
    intro j hj
    simpa [W] using
      degree_n_component_smul_generator_mem_span_admissible_weighted_module_monomials
        (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hδ hv hgen n j (c j)
  simpa [W] using hx_decompose ▸ hsum_mem

/-- Lemma 10.58.6: if a finite graded module `M = ⨁_{n ∈ ℤ} Mₙ` over `S` has grading compatible
with a graded ring `S` of finite type over its degree-zero part, then each homogeneous piece `Mₙ`
is a finite `S₀`-module. -/
-- Proof sketch: use the chapter's graded-module owner API from Lemma `10.56.1` to choose a
-- finite homogeneous generating set of `M`, and the mathlib/project finite-type owner API from
-- `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero` and Lemma `10.56.2` to
-- choose homogeneous positive-degree generators of `S` over `S₀`. Then every element of `Mₙ` is
-- an `S₀`-linear combination of finitely many monomials in those generators whose total degree is
-- `n`.
theorem finite_degree_component_of_finiteType (n : ℤ) :
    Module.Finite (𝒜 0) (ℳ n) := by
  classical
  obtain ⟨κ, _, m, η, hm, hspan⟩ :=
    exists_finite_homogeneous_module_generators (ℳ := ℳ)
  obtain ⟨ι, _, v, δ, hposmem, hgen⟩ :=
    exists_finite_positive_homogeneous_ring_generators (𝒜 := 𝒜)
  have hδ : ∀ i, 0 < δ i := fun i ↦ (hposmem i).1
  have hv : ∀ i, v i ∈ 𝒜 (δ i) := fun i ↦ (hposmem i).2
  letI : ∀ j : κ, Subsingleton {d : ℕ // (d : ℤ) + η j = n} :=
    fun j ↦ degree_fiber_subsingleton η j n
  letI : ∀ j : κ, Fintype {d : ℕ // (d : ℤ) + η j = n} :=
    fun j ↦ Fintype.ofFinite _
  let w_n :
      (Σ j : κ, Σ d : {d : ℕ // (d : ℤ) + η j = n},
        {e : ι → Fin (d.1 + 1) // ∑ i, (e i : ℕ) * δ i = d.1}) → ℳ n := fun t ↦
    ⟨(∏ i, v i ^ (t.2.2.1 i : ℕ) : S) • m t.1,
      admissible_weighted_module_monomial_mem_degree_piece
        (𝒜 := 𝒜) (ℳ := ℳ) m η hm v δ hv t⟩
  have htop_le : ⊤ ≤ Submodule.span (𝒜 0) (Set.range w_n) := by
    intro x hx
    -- The textbook monomial argument shows that every `x ∈ Mₙ` lies in the admissible span.
    simpa [w_n] using
      mem_span_admissible_weighted_module_monomials
        (𝒜 := 𝒜) (ℳ := ℳ) m η hm hspan v δ hδ hv hgen n x
  have hspan_top : Submodule.span (𝒜 0) (Set.range w_n) = ⊤ := by
    rw [eq_top_iff]
    exact htop_le
  have hspan_finite :
      Module.Finite (𝒜 0) (Submodule.span (𝒜 0) (Set.range w_n)) :=
    Module.Finite.span_of_finite (𝒜 0) (Set.finite_range w_n)
  have htop_finite : Module.Finite (𝒜 0) (⊤ : Submodule (𝒜 0) (ℳ n)) := by
    exact hspan_top ▸ hspan_finite
  -- Transport finiteness from the spanning top submodule back to the component itself.
  letI : Module.Finite (𝒜 0) (⊤ : Submodule (𝒜 0) (ℳ n)) := htop_finite
  exact Module.Finite.equiv
    (Submodule.topEquiv : (⊤ : Submodule (𝒜 0) (ℳ n)) ≃ₗ[(𝒜 0)] ℳ n)

end
