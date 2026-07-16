import stacks_proof.stacks_project.Chap10.Lemma_10_57_10.ModelPresentation

open scoped BigOperators DirectSum
open HomogeneousLocalization

universe u u' v

section

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R' M]

attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

namespace Lemma_10_57_10

/-- Helper for Lemma 10.57.10: dehomogenize along the extra variable `X 0` by sending `X 0` to
`1` and `X i.succ` back to the original variable `X i`. This is the explicit source-side chart
map before quotienting by the homogenized kernel. -/
noncomputable def coneDehom {n : ℕ} :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval
    (fun i : Fin (n + 1) =>
      Fin.cases (1 : MvPolynomial (Fin n) R) MvPolynomial.X i)

/-- Helper for Lemma 10.57.10: the dehomogenization map sends the extra variable `X 0` to `1`. -/
@[simp] theorem coneDehom_X_zero {n : ℕ} :
    coneDehom (R := R) (n := n) (MvPolynomial.X 0) = 1 := by
  -- This is the defining source substitution `X₀ ↦ 1`.
  simp [coneDehom]

/-- Helper for Lemma 10.57.10: the dehomogenization map sends `X i.succ` back to `X i`. -/
@[simp] theorem coneDehom_X_succ {n : ℕ} (i : Fin n) :
    coneDehom (R := R) (n := n) (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  -- This is the defining source substitution `Xᵢ/X₀ ↦ xᵢ`.
  simp [coneDehom]

/-- Helper for Lemma 10.57.10: re-embedding a polynomial by `rename Fin.succ` and then
dehomogenizing recovers the original polynomial. -/
theorem coneDehom_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    coneDehom (R := R) (n := n) (MvPolynomial.rename Fin.succ p) = p := by
  let φ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R :=
    (coneDehom (R := R) (n := n)).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom
  have hφ : φ = RingHom.id _ := by
    -- The composite fixes coefficients from `R` and sends every affine variable back to itself.
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
    · intro i
      simp [φ]
  exact congrArg (fun f => f p) hφ

/-- Helper for Lemma 10.57.10: homogenize a polynomial to total degree `d` by shifting each
homogeneous piece with the required power of the extra variable `X 0`. This is the source's
positive homogenization operator before quotienting by the cone ideal. -/
noncomputable def coneHomogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R :=
  Finset.sum (Finset.range (d + 1)) fun i =>
    (MvPolynomial.X (0 : Fin (n + 1))) ^ (d - i) *
      MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p)

/-- Helper for Lemma 10.57.10: a homogeneous polynomial is equal to its homogeneous component in
its own degree. -/
theorem homogeneousComponent_eq_self_of_isHomogeneous {σ : Type*} {d : ℕ}
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous d) :
    MvPolynomial.homogeneousComponent d p = p := by
  -- Compare coefficients: the degree-`d` component keeps exactly the coefficients allowed by
  -- homogeneity and kills the others.
  ext m
  by_cases hm : m.degree = d
  · simp [MvPolynomial.coeff_homogeneousComponent, hm]
  · simp [MvPolynomial.coeff_homogeneousComponent, hm, hp.coeff_eq_zero hm]

/-- Helper for Lemma 10.57.10: a homogeneous polynomial has no homogeneous component in any
different degree. -/
theorem homogeneousComponent_eq_zero_of_isHomogeneous_ne {σ : Type*} {d e : ℕ}
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous d) (hde : e ≠ d) :
    MvPolynomial.homogeneousComponent e p = 0 := by
  -- Coefficientwise, the degree-`e` projection can only see monomials of degree `e`, but a
  -- degree-`d` homogeneous polynomial has no such coefficients when `e ≠ d`.
  ext m
  by_cases hm : m.degree = e
  · have hm_ne : m.degree ≠ d := by
      simpa [hm] using hde
    simp [MvPolynomial.coeff_homogeneousComponent, hm, hp.coeff_eq_zero hm_ne]
  · simp [MvPolynomial.coeff_homogeneousComponent, hm]

/-- Helper for Lemma 10.57.10: homogenizing an already degree-`d` homogeneous polynomial simply
renames the original variables into the `succ` coordinates. -/
theorem coneHomogenizeTo_of_isHomogeneous {n : ℕ} {d : ℕ}
    {p : MvPolynomial (Fin n) R} (hp : p.IsHomogeneous d) :
    coneHomogenizeTo (R := R) d p = MvPolynomial.rename Fin.succ p := by
  -- Only the degree-`d` homogeneous component survives in the source-style homogenization sum.
  rw [coneHomogenizeTo, Finset.sum_eq_single d]
  · simp [homogeneousComponent_eq_self_of_isHomogeneous (R := R) hp]
  · intro i hi hid
    simp [homogeneousComponent_eq_zero_of_isHomogeneous_ne (R := R) hp hid]
  · intro hd
    simp at hd

/-- Helper for Lemma 10.57.10: the source homogenization fixes constant affine polynomials. -/
@[simp] theorem coneHomogenizeTo_C {n : ℕ} (r : R) :
    coneHomogenizeTo (R := R) (n := n) 0 (MvPolynomial.C r) = MvPolynomial.C r := by
  -- The degree-zero homogenization of a constant polynomial is just that same constant.
  simpa using
    (coneHomogenizeTo_of_isHomogeneous (R := R) (n := n) (d := 0)
      (p := MvPolynomial.C r) (MvPolynomial.isHomogeneous_C (σ := Fin n) r))

/-- Helper for Lemma 10.57.10: the source-style degree-`d` homogenization is homogeneous of
degree `d`. -/
theorem coneHomogenizeTo_isHomogeneous {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    (coneHomogenizeTo (R := R) d p).IsHomogeneous d := by
  -- Each summand has total degree `d`, so the finite sum stays homogeneous of degree `d`.
  rw [coneHomogenizeTo]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hX :
      (MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i)).IsHomogeneous (d - i) :=
    MvPolynomial.isHomogeneous_X_pow (R := R) (0 : Fin (n + 1)) (d - i)
  have hcomp :
      (MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p)).IsHomogeneous i :=
    (MvPolynomial.homogeneousComponent_isHomogeneous (n := i) (φ := p)).rename_isHomogeneous
  simpa [Nat.sub_add_cancel hi_le] using hX.mul hcomp

/-- Helper for Lemma 10.57.10: dehomogenizing the source-style degree-`d` homogenization recovers
the original polynomial once `d` dominates the total degree. -/
theorem coneDehom_homogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R)
    (hp : p.totalDegree ≤ d) :
    coneDehom (R := R) (n := n) (coneHomogenizeTo (R := R) d p) = p := by
  -- The source proof homogenizes each homogeneous piece separately and then substitutes `X₀ = 1`.
  calc
    coneDehom (R := R) (n := n) (coneHomogenizeTo (R := R) d p) =
        Finset.sum (Finset.range (d + 1)) fun i => MvPolynomial.homogeneousComponent i p := by
      rw [coneHomogenizeTo, map_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- Each inserted factor `X₀^(d-i)` collapses to `1`, and `rename Fin.succ` survives
      -- dehomogenization unchanged.
      rw [map_mul, map_pow, coneDehom_X_zero, one_pow, one_mul, coneDehom_rename_succ]
    _ = p := by
      have hd : p.totalDegree + 1 ≤ d + 1 := Nat.succ_le_succ hp
      rw [← Finset.sum_range_add_sum_Ico _ hd, MvPolynomial.sum_homogeneousComponent]
      have htail :
          Finset.sum (Finset.Ico (p.totalDegree + 1) (d + 1))
            (fun i => MvPolynomial.homogeneousComponent i p) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact MvPolynomial.homogeneousComponent_eq_zero (φ := p) (n := i)
          (Nat.lt_of_succ_le (Finset.mem_Ico.mp hi).1)
      simpa [htail]

/-- Helper for Lemma 10.57.10: if `d` dominates `p.totalDegree`, then the degree-`d`
homogenization differs from the minimal homogenization only by an extra power of `X 0`. This is
the source-side bridge from arbitrary degree shifts back to the canonical cone generators. -/
theorem coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree {n : ℕ} (d : ℕ)
    (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    coneHomogenizeTo (R := R) d p =
      MvPolynomial.X (0 : Fin (n + 1)) ^ (d - p.totalDegree) *
        coneHomogenizeTo (R := R) p.totalDegree p := by
  -- Split the source-style homogenization at `p.totalDegree`; the tail vanishes because all higher
  -- homogeneous components of `p` are zero.
  rw [coneHomogenizeTo]
  have hd : p.totalDegree + 1 ≤ d + 1 := Nat.succ_le_succ hp
  rw [← Finset.sum_range_add_sum_Ico _ hd]
  have htail :
      Finset.sum (Finset.Ico (p.totalDegree + 1) (d + 1)) (fun i =>
        MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i) *
          MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    -- Above `p.totalDegree`, the homogeneous component of `p` vanishes, so the corresponding cone
    -- summand also vanishes.
    have hi_gt : p.totalDegree < i := Nat.lt_of_succ_le (Finset.mem_Ico.mp hi).1
    rw [MvPolynomial.homogeneousComponent_eq_zero (φ := p) (n := i) hi_gt]
    simp
  rw [htail, add_zero]
  -- On the surviving initial segment, factor out the common power `X₀^(d - p.totalDegree)`.
  have hsplit :
      Finset.sum (Finset.range (p.totalDegree + 1)) (fun i =>
        MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i) *
          MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p)) =
        Finset.sum (Finset.range (p.totalDegree + 1)) (fun i =>
          MvPolynomial.X (0 : Fin (n + 1)) ^ (d - p.totalDegree) *
            (MvPolynomial.X (0 : Fin (n + 1)) ^ (p.totalDegree - i) *
              MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : d - i = (d - p.totalDegree) + (p.totalDegree - i) := by
      omega
    rw [hsub, pow_add, mul_assoc]
  rw [hsplit, ← Finset.mul_sum]
  -- What remains is exactly the minimal homogenization of `p`.
  rw [coneHomogenizeTo]

/-- Helper for Lemma 10.57.10: viewing `rename Fin.succ` through `finSuccEquiv` simply turns the
affine polynomial into a constant polynomial in the cone variable. -/
theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
  let φ : MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R) :=
    (MvPolynomial.finSuccEquiv R n).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom
  have hφ : φ = Polynomial.C := by
    -- Both ring maps agree on coefficients from `R` and on every affine variable `X i`.
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [φ, MvPolynomial.finSuccEquiv_apply]
    · intro i
      simp [φ, MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f => f p) hφ

/-- Helper for Lemma 10.57.10: dehomogenization is evaluation at `X 0 = 1` after viewing the cone
polynomial as a polynomial in `X 0` with coefficients in the affine polynomial ring. -/
theorem coneDehom_eq_eval_finSuccEquiv {n : ℕ} (q : MvPolynomial (Fin (n + 1)) R) :
    coneDehom (R := R) (n := n) q =
      Polynomial.eval (1 : MvPolynomial (Fin n) R) (MvPolynomial.finSuccEquiv R n q) := by
  let φ : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
    (Polynomial.evalRingHom (1 : MvPolynomial (Fin n) R)).comp
      (MvPolynomial.finSuccEquiv R n).toRingHom
  have hφ : φ = (coneDehom (R := R) (n := n)).toRingHom := by
    -- Both ring maps send `X 0` to `1` and each `X i.succ` to the corresponding affine variable.
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [φ, coneDehom, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [φ, coneDehom, MvPolynomial.finSuccEquiv_X_zero]
      · intro j
        simp [φ, coneDehom, MvPolynomial.finSuccEquiv_X_succ]
  simpa [φ] using (congrArg (fun f => f q) hφ).symm

/-- Helper for Lemma 10.57.10: for a cone polynomial homogeneous of degree `d`, the `i`-th
coefficient of `finSuccEquiv` is exactly the `(d - i)`-homogeneous component of its
dehomogenization. This is the source-faithful coefficient bridge needed before reconstructing the
homogeneous cone polynomial. -/
theorem coneDehom_eq_sum_finSuccEquiv_coeff_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    coneDehom (R := R) (n := n) q =
      Finset.sum (Finset.range (d + 1)) fun j =>
        (MvPolynomial.finSuccEquiv R n q).coeff j := by
  let P := MvPolynomial.finSuccEquiv R n q
  have hdeg : P.natDegree < d + 1 := by
    -- Homogeneity bounds the `X 0`-degree of the `finSuccEquiv` polynomial by the same source
    -- degree `d`.
    apply Nat.lt_succ_of_le
    dsimp [P]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree q 0).trans hq.totalDegree_le
  -- Evaluate the `X 0`-polynomial at `1` and truncate the sum at degree `d`.
  simpa [P] using
    (show
      coneDehom (R := R) (n := n) q =
        Finset.sum (Finset.range (d + 1)) fun i =>
          P.coeff i * (1 : MvPolynomial (Fin n) R) ^ i by
      rw [coneDehom_eq_eval_finSuccEquiv, Polynomial.eval_eq_sum_range' hdeg])

/-- Helper for Lemma 10.57.10: for a cone polynomial homogeneous of degree `d`, the `i`-th
coefficient of `finSuccEquiv` is exactly the `(d - i)`-homogeneous component of its
dehomogenization. This is the source-faithful coefficient bridge needed before reconstructing the
homogeneous cone polynomial. -/
theorem finSuccEquiv_coeff_eq_homogeneousComponent_coneDehom {n d i : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) (hi : i ≤ d) :
    (MvPolynomial.finSuccEquiv R n q).coeff i =
      MvPolynomial.homogeneousComponent (d - i) (coneDehom (R := R) (n := n) q) := by
  -- Project the source-side dehomogenization formula to degree `d - i`, so only the `i`-th cone
  -- coefficient survives.
  have hproj :
      MvPolynomial.homogeneousComponent (d - i) (coneDehom (R := R) (n := n) q) =
        ∑ j ∈ Finset.range (d + 1),
          MvPolynomial.homogeneousComponent (d - i)
            ((MvPolynomial.finSuccEquiv R n q).coeff j) := by
    simpa [map_sum] using
      congrArg (MvPolynomial.homogeneousComponent (d - i))
        (coneDehom_eq_sum_finSuccEquiv_coeff_of_isHomogeneous
          (R := R) (n := n) (d := d) hq)
  rw [Finset.sum_eq_single i] at hproj
  · -- The surviving summand is already homogeneous of degree `d - i`.
    simpa [homogeneousComponent_eq_self_of_isHomogeneous (R := R)
      (hq.finSuccEquiv_coeff_isHomogeneous i (d - i) (Nat.add_sub_of_le hi))] using hproj.symm
  · intro j hj hji
    have hj_le : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdeg_ne : d - i ≠ d - j := by
      omega
    -- Every off-diagonal cone coefficient has the wrong degree, so the projector kills it.
    simp [homogeneousComponent_eq_zero_of_isHomogeneous_ne (R := R)
      (hq.finSuccEquiv_coeff_isHomogeneous j (d - j) (Nat.add_sub_of_le hj_le)) hdeg_ne]
  · intro hi_not_mem
    exact (hi_not_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).elim

/-- Helper for Lemma 10.57.10: after moving to the single-variable `X 0` picture, the coefficient
of `X^k` in the degree-`d` cone homogenization comes from the `(d - k)`-homogeneous component of
the affine polynomial, and vanishes when `k > d`. -/
theorem finSuccEquiv_coeff_coneHomogenizeTo {n : ℕ} (d k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    (MvPolynomial.finSuccEquiv R n (coneHomogenizeTo (R := R) d p)).coeff k =
      if k ≤ d then MvPolynomial.homogeneousComponent (d - k) p else 0 := by
  by_cases hk : k ≤ d
  · -- Inside the source homogenization sum, only the summand with exponent `d - (d - k) = k`
    -- contributes to the `X^k` coefficient.
    rw [if_pos hk]
    rw [coneHomogenizeTo, map_sum, Polynomial.finset_sum_coeff, Finset.sum_eq_single (d - k)]
    · simp [map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_rename_succ,
        Nat.sub_sub_self hk]
    · intro j hj hj_ne
      have hk_ne : k ≠ d - j := by
        intro hkj
        apply hj_ne
        symm
        apply (Nat.sub_eq_iff_eq_add hk).2
        calc
          d = k + j := by rw [hkj, Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
          _ = j + k := by omega
      -- All remaining summands have the wrong `X`-degree.
      simp [map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_rename_succ, hk_ne]
    · intro hk_not_mem
      exact (hk_not_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)))).elim
  · -- If `k > d`, no source homogenization summand can contribute to the `X^k` coefficient.
    rw [if_neg hk]
    rw [coneHomogenizeTo, map_sum, Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_le : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hk_ne : k ≠ d - j := by
      omega
    simp [map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_rename_succ, hk_ne]

/-- Helper for Lemma 10.57.10: dehomogenizing a degree-`d` homogeneous cone polynomial cannot
increase total degree beyond `d`. -/
theorem coneDehom_totalDegree_le_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    (coneDehom (R := R) (n := n) q).totalDegree ≤ d := by
  -- Rewrite the dehomogenization as a finite sum of homogeneous coefficients of degrees at most
  -- `d`, then bound the total degree termwise.
  rw [coneDehom_eq_sum_finSuccEquiv_coeff_of_isHomogeneous (R := R) (n := n) (d := d) hq]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro i hi
  have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact (hq.finSuccEquiv_coeff_isHomogeneous i (d - i) (Nat.add_sub_of_le hi_le)).totalDegree_le.trans
    (Nat.sub_le _ _)

/-- Helper for Lemma 10.57.10: after moving to the single-variable `X 0` picture, rehomogenizing
the dehomogenization of a degree-`d` homogeneous cone polynomial recovers the original
polynomial. -/
theorem finSuccEquiv_coneHomogenizeTo_coneDehom_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    MvPolynomial.finSuccEquiv R n
        (coneHomogenizeTo (R := R) d (coneDehom (R := R) (n := n) q)) =
      MvPolynomial.finSuccEquiv R n q := by
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ d
  · -- On coefficients up to degree `d`, the source homogenization formula matches the projected
    -- homogeneous component of the dehomogenized polynomial.
    rw [finSuccEquiv_coeff_coneHomogenizeTo (R := R) (n := n) d k]
    simpa [if_pos hk] using
      (finSuccEquiv_coeff_eq_homogeneousComponent_coneDehom
        (R := R) (n := n) (d := d) (i := k) hq hk).symm
  · -- Above degree `d`, both sides vanish: the left by construction, the right by homogeneity.
    rw [finSuccEquiv_coeff_coneHomogenizeTo (R := R) (n := n) d k]
    rw [if_neg hk]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt ?_ (Nat.lt_of_not_ge hk)
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree q 0).trans hq.totalDegree_le

/-- Helper for Lemma 10.57.10: the source-faithful inverse step is obtained by pulling the
polynomial-model reconstruction back through `MvPolynomial.finSuccEquiv`. -/
theorem coneHomogenizeTo_coneDehom_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    coneHomogenizeTo (R := R) d (coneDehom (R := R) (n := n) q) = q := by
  -- Localize the reconstruction under `finSuccEquiv`, then return to cone polynomials in one
  -- injective step.
  apply (MvPolynomial.finSuccEquiv R n).injective
  simpa using
    finSuccEquiv_coneHomogenizeTo_coneDehom_of_isHomogeneous
      (R := R) (n := n) (d := d) hq

/-- Helper for Lemma 10.57.10: any higher-degree shift of a canonical cone generator already lies
in the cone homogenized ideal. -/
theorem coneHomogenizeTo_mem_cone_homogenized_ideal_of_mem {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} (p : I) {d : ℕ} (hp : p.1.totalDegree ≤ d) :
    coneHomogenizeTo (R := R) d p.1 ∈
      Ideal.span (Set.range fun q : I => coneHomogenizeTo (R := R) q.1.totalDegree q.1) := by
  -- Rewrite the shifted homogenization as a power of `X 0` times the canonical generator for
  -- `p`, then use ideal closure under multiplication.
  rw [coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree (R := R) (n := n) d p.1 hp]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

/-- Helper for Lemma 10.57.10: if a degree-`d` homogeneous cone polynomial dehomogenizes into the
affine ideal, then the cone polynomial already lies in the homogenized cone ideal. -/
theorem cone_homogenized_ideal_mem_of_isHomogeneous_of_dehom_mem {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q.IsHomogeneous d) (hdehom : coneDehom (R := R) (n := n) q ∈ I) :
    q ∈ Ideal.span (Set.range fun p : I => coneHomogenizeTo (R := R) p.1.totalDegree p.1) := by
  -- Recover `q` as the degree-`d` homogenization of its affine dehomogenization, then place that
  -- shifted homogenization in the cone ideal using the total-degree bound proved above.
  rw [← coneHomogenizeTo_coneDehom_of_isHomogeneous (R := R) (n := n) (d := d) hq]
  exact coneHomogenizeTo_mem_cone_homogenized_ideal_of_mem
    (R := R) (n := n) (I := I) ⟨_, hdehom⟩
    (coneDehom_totalDegree_le_of_isHomogeneous (R := R) (n := n) (d := d) hq)

/-- Helper for Lemma 10.57.10: the source-side dehomogenization chart is surjective before
passing to the quotient by the homogenized kernel. -/
theorem coneDehom_surjective {n : ℕ} :
    Function.Surjective (coneDehom (R := R) (n := n)) := by
  -- Every polynomial lifts by ignoring the extra variable and renaming the original variables to
  -- `X i.succ`.
  intro p
  exact ⟨MvPolynomial.rename Fin.succ p, coneDehom_rename_succ (R := R) (n := n) p⟩

/-
The source-faithful cone-chart API is now established through the exact cone-ideal kernel
criterion. The remaining unstable block is the final descent from the cone quotient to the
localized affine quotient, together with the module cokernel comparison.
-/

/-- Helper for Lemma 10.57.10: the ideal generated by canonical cone homogenizations of an affine
subset is homogeneous for the standard grading on the cone polynomial ring. -/
theorem cone_homogenized_span_isHomogeneous {n : ℕ}
    (s : Set (MvPolynomial (Fin n) R)) :
    (Ideal.span (Set.range fun p : s =>
      coneHomogenizeTo (R := R) p.1.totalDegree p.1)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  -- Each canonical homogenization is homogeneous in its own total degree, so their span remains
  -- homogeneous.
  apply Ideal.homogeneous_span
  intro q hq
  rcases hq with ⟨p, rfl⟩
  refine ⟨p.1.totalDegree, ?_⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using
    coneHomogenizeTo_isHomogeneous (R := R) (n := n) p.1.totalDegree p.1

/-- Helper for Lemma 10.57.10: the cone homogenized ideal maps into the affine ideal after
dehomogenization along `X 0`. -/
theorem cone_homogenized_span_le_comap_coneDehom_span {n : ℕ}
    (s : Set (MvPolynomial (Fin n) R)) :
    Ideal.span (Set.range fun p : s =>
      coneHomogenizeTo (R := R) p.1.totalDegree p.1) ≤
        Ideal.comap (coneDehom (R := R) (n := n)) (Ideal.span s) := by
  -- Each generator dehomogenizes back to the corresponding affine polynomial, hence lands in the
  -- affine span.
  rw [Ideal.span_le]
  intro q hq
  rcases hq with ⟨p, rfl⟩
  change coneDehom (R := R) (n := n)
      (coneHomogenizeTo (R := R) p.1.totalDegree p.1) ∈ Ideal.span s
  rw [coneDehom_homogenizeTo (R := R) (n := n) p.1.totalDegree p.1 le_rfl]
  exact Ideal.subset_span p.2

end Lemma_10_57_10

end
