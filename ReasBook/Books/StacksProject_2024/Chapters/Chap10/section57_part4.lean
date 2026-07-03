import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_57_10 (from Chap10) -/
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

-- Proof sketch: choose finitely many generators of the finite type algebra `R'`, homogenize the
-- defining ideal inside a polynomial ring with one extra variable of degree `1`, and then
-- homogenize a finite presentation of `M` to obtain a finite graded `S`-module whose localization
-- away from the extra variable recovers `M`.
/- Source-facing existence form of Lemma 10.57.10: keep the chapter’s canonical owner condition
`Algebra.adjoin S₀ S₁ = ⊤` as the main graded-ring conclusion. The explicit finite set of
degree-one generators is derived source-facing API, not primitive owner data. The source equality
`S₀ = R` is identified with the canonical algebra isomorphism `R ≃ₐ[R] S₀`. -/
/-- A graded localization model whose ring is generated in degree `1`, is finite type over its
degree-zero part, and whose graded module is finite over the ring. -/
class IsDegreeOneGeneratedFiniteTypeModel
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N] : Prop where
  degreeOne_adjoin_eq_top : Algebra.adjoin (grading 0) (grading 1 : Set S) = ⊤
  finiteType : Algebra.FiniteType (grading 0) S
  moduleFinite : Module.Finite S N

/-- Helper for Lemma 10.57.10: a finite family of degree-one generators already packages the
source conclusions needed for `IsDegreeOneGeneratedFiniteTypeModel`. -/
private theorem isDegreeOneGeneratedFiniteTypeModel_of_finset
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N]
    [Module.Finite S N] (s : Finset S)
    (hs_top : Algebra.adjoin (grading 0) (s : Set S) = ⊤)
    (hs_deg : ∀ x ∈ s, x ∈ grading 1) :
    IsDegreeOneGeneratedFiniteTypeModel grading N := by
  refine ⟨?_, ?_, inferInstance⟩
  · -- The whole degree-one piece generates once the chosen finite subset already does.
    apply top_le_iff.mp
    rw [← hs_top]
    exact Algebra.adjoin_mono fun x hx => hs_deg x (by simpa using hx)
  · -- Finite generation by a finite family is exactly finite type over the degree-zero piece.
    exact ⟨⟨s, hs_top⟩⟩

/-- Helper for Lemma 10.57.10: an element of `Algebra.adjoin R s` already lies in the adjoin of a
finite subset of `s`. -/
private theorem exists_finset_subset_of_mem_adjoin
    {S : Type _} [CommRing S] [Algebra R S] {s : Set S} {x : S}
    (hx : x ∈ Algebra.adjoin R s) :
    ∃ t : Finset S, (∀ y ∈ t, y ∈ s) ∧ x ∈ Algebra.adjoin R (t : Set S) := by
  classical
  rw [Algebra.mem_adjoin_iff] at hx
  let P : S → Prop := fun y =>
    ∃ t : Finset S, (∀ z ∈ t, z ∈ s) ∧ y ∈ Algebra.adjoin R (t : Set S)
  have hmem :
      ∀ y ∈ Set.range (algebraMap R S) ∪ s, P y := by
    intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨r, rfl⟩
      refine ⟨∅, by simp, ?_⟩
      simpa [Algebra.adjoin_empty] using
        (Subalgebra.algebraMap_mem (⊥ : Subalgebra R S) r)
    · refine ⟨{y}, ?_, ?_⟩
      · intro z hz
        simpa [Finset.mem_singleton.mp hz] using hy
      · exact Algebra.subset_adjoin (by simp)
  have hzero : P 0 := by
    refine ⟨∅, by simp, ?_⟩
    simpa [Algebra.adjoin_empty] using
      (Subalgebra.zero_mem (⊥ : Subalgebra R S))
  have hone : P 1 := by
    refine ⟨∅, by simp, ?_⟩
    simpa [Algebra.adjoin_empty] using
      (Subalgebra.one_mem (⊥ : Subalgebra R S))
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    rcases hx with ⟨tx, htx, hx⟩
    rcases hy with ⟨ty, hty, hy⟩
    refine ⟨tx ∪ ty, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact htx z hz
      · exact hty z hz
    · exact Subalgebra.add_mem _ 
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inl hz)) hx)
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inr hz)) hy)
  have hneg : ∀ x, P x → P (-x) := by
    intro x hx
    rcases hx with ⟨tx, htx, hx⟩
    exact ⟨tx, htx, Subalgebra.neg_mem _ hx⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy
    rcases hx with ⟨tx, htx, hx⟩
    rcases hy with ⟨ty, hty, hy⟩
    refine ⟨tx ∪ ty, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact htx z hz
      · exact hty z hz
    · exact Subalgebra.mul_mem _
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inl hz)) hx)
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inr hz)) hy)
  exact Subring.closure_induction
    (s := Set.range (algebraMap R S) ∪ s)
    (p := fun y _ => P y)
    (fun y hy => hmem y hy)
    hzero
    hone
    (fun x y _ _ hx hy => hadd x y hx hy)
    (fun x _ hx => hneg x hx)
    (fun x y _ _ hx hy => hmul x y hx hy)
    hx

/-- Helper for Lemma 10.57.10: a finite type algebra admits a surjective polynomial presentation
on finitely many variables. This is the source-side starting point `R' = R[x₁, …, xₙ] / I`. -/
private theorem exists_surjective_mvPolynomial_presentation :
    [Algebra.FiniteType R R'] →
    ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] R', Function.Surjective π := by
  -- Unpack the standard finite-type owner theorem into the concrete polynomial presentation used
  -- by the source proof.
  intro _hfinite
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := R')).mp
    inferInstance
  exact ⟨n, π, hπ⟩

/-- Helper for Lemma 10.57.10: the quotient by the kernel of a surjective polynomial presentation
recovers the target algebra. This packages the source identification
`R[x₁, …, xₙ] / I ≃ R'`. -/
private noncomputable def mvPolynomial_quotient_equiv_of_surjective {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π) :
    (MvPolynomial (Fin n) R ⧸ RingHom.ker π) ≃ₐ[R] R' :=
  -- Use the canonical quotient-by-kernel equivalence once, so the main proof can focus on the
  -- cone construction rather than on quotient bookkeeping.
  Ideal.quotientKerAlgEquivOfSurjective hπ

/-- Helper for Lemma 10.57.10: after restricting scalars along an affine presentation
`π : R[x₁, …, xₙ] → R'`, a finite `R'`-module admits a surjective finite free presentation over
the affine polynomial ring. This matches the source proof, where relations are homogenized before
passing to the cone quotient. -/
private theorem exists_surjective_affine_free_module_presentation {n : ℕ}
    (_π : MvPolynomial (Fin n) R →ₐ[R] R')
    [Module (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M] :
    ∃ r : ℕ,
      ∃ τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M,
        Function.Surjective τ := by
  -- Restrict scalars along `π`, then take the canonical finite free cover over the affine ring.
  simpa using (Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M)

/-- Helper for Lemma 10.57.10: the quotient by the relation submodule of a surjective free
presentation recovers the target module. This packages the source identification
`(R')^r / K ≃ M`. -/
private noncomputable def free_module_quotient_equiv_of_surjective {r : ℕ}
    (σ : (Fin r → R') →ₗ[R'] M) (hσ : Function.Surjective σ) :
    ((Fin r → R') ⧸ LinearMap.ker σ) ≃ₗ[R'] M :=
  -- Use the module first isomorphism theorem once, so later work can concentrate on homogenizing
  -- the relation vectors.
  LinearMap.quotKerEquivOfSurjective σ hσ

/-- Helper for Lemma 10.57.10: dehomogenize along the extra variable `X 0` by sending `X 0` to
`1` and `X i.succ` back to the original variable `X i`. This is the explicit source-side chart
map before quotienting by the homogenized kernel. -/
private noncomputable def coneDehom {n : ℕ} :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval
    (fun i : Fin (n + 1) =>
      Fin.cases (1 : MvPolynomial (Fin n) R) MvPolynomial.X i)

/-- Helper for Lemma 10.57.10: the dehomogenization map sends the extra variable `X 0` to `1`. -/
@[simp] private theorem coneDehom_X_zero {n : ℕ} :
    coneDehom (R := R) (n := n) (MvPolynomial.X 0) = 1 := by
  -- This is the defining source substitution `X₀ ↦ 1`.
  simp [coneDehom]

/-- Helper for Lemma 10.57.10: the dehomogenization map sends `X i.succ` back to `X i`. -/
@[simp] private theorem coneDehom_X_succ {n : ℕ} (i : Fin n) :
    coneDehom (R := R) (n := n) (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  -- This is the defining source substitution `Xᵢ/X₀ ↦ xᵢ`.
  simp [coneDehom]

/-- Helper for Lemma 10.57.10: re-embedding a polynomial by `rename Fin.succ` and then
dehomogenizing recovers the original polynomial. -/
private theorem coneDehom_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
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
private noncomputable def coneHomogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R :=
  Finset.sum (Finset.range (d + 1)) fun i =>
    (MvPolynomial.X (0 : Fin (n + 1))) ^ (d - i) *
      MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent i p)

/-- Helper for Lemma 10.57.10: a homogeneous polynomial is equal to its homogeneous component in
its own degree. -/
private theorem homogeneousComponent_eq_self_of_isHomogeneous {σ : Type*} {d : ℕ}
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
private theorem homogeneousComponent_eq_zero_of_isHomogeneous_ne {σ : Type*} {d e : ℕ}
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
private theorem coneHomogenizeTo_of_isHomogeneous {n : ℕ} {d : ℕ}
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
@[simp] private theorem coneHomogenizeTo_C {n : ℕ} (r : R) :
    coneHomogenizeTo (R := R) (n := n) 0 (MvPolynomial.C r) = MvPolynomial.C r := by
  -- The degree-zero homogenization of a constant polynomial is just that same constant.
  simpa using
    (coneHomogenizeTo_of_isHomogeneous (R := R) (n := n) (d := 0)
      (p := MvPolynomial.C r) (MvPolynomial.isHomogeneous_C (σ := Fin n) r))

/-- Helper for Lemma 10.57.10: the source-style degree-`d` homogenization is homogeneous of
degree `d`. -/
private theorem coneHomogenizeTo_isHomogeneous {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
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
private theorem coneDehom_homogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R)
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
private theorem coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree {n : ℕ} (d : ℕ)
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
private theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
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
private theorem coneDehom_eq_eval_finSuccEquiv {n : ℕ} (q : MvPolynomial (Fin (n + 1)) R) :
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
private theorem coneDehom_eq_sum_finSuccEquiv_coeff_of_isHomogeneous {n d : ℕ}
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
private theorem finSuccEquiv_coeff_eq_homogeneousComponent_coneDehom {n d i : ℕ}
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
private theorem finSuccEquiv_coeff_coneHomogenizeTo {n : ℕ} (d k : ℕ)
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
private theorem coneDehom_totalDegree_le_of_isHomogeneous {n d : ℕ}
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
private theorem finSuccEquiv_coneHomogenizeTo_coneDehom_of_isHomogeneous {n d : ℕ}
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
private theorem coneHomogenizeTo_coneDehom_of_isHomogeneous {n d : ℕ}
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
private theorem coneHomogenizeTo_mem_cone_homogenized_ideal_of_mem {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} (p : I) {d : ℕ} (hp : p.1.totalDegree ≤ d) :
    coneHomogenizeTo (R := R) d p.1 ∈
      Ideal.span (Set.range fun q : I => coneHomogenizeTo (R := R) q.1.totalDegree q.1) := by
  -- Rewrite the shifted homogenization as a power of `X 0` times the canonical generator for
  -- `p`, then use ideal closure under multiplication.
  rw [coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree (R := R) (n := n) d p.1 hp]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

/-- Helper for Lemma 10.57.10: if a degree-`d` homogeneous cone polynomial dehomogenizes into the
affine ideal, then the cone polynomial already lies in the homogenized cone ideal. -/
private theorem cone_homogenized_ideal_mem_of_isHomogeneous_of_dehom_mem {n d : ℕ}
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
private theorem coneDehom_surjective {n : ℕ} :
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
private theorem cone_homogenized_span_isHomogeneous {n : ℕ}
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
private theorem cone_homogenized_span_le_comap_coneDehom_span {n : ℕ}
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

/-- Helper for Lemma 10.57.10: once the homogenized cone ideal maps into the affine kernel under
dehomogenization, the source substitution `X₀ ↦ 1` descends to the quotient rings. -/
private noncomputable def coneDehom_quotient_map {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
  Ideal.Quotient.liftₐ J
    ((Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n)))
    (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq))

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization still sends the cone
variable `X 0` to `1`. This is the source computation `X₀/X₀ ↦ 1`. -/
@[simp] private theorem coneDehom_quotient_map_X_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) = 1 := by
  -- Evaluate the descended map on `X₀` by comparing it with its pre-quotient composite.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hX :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (MvPolynomial.X (0 : Fin (n + 1)))) hcomp
  simpa [F, coneDehom]
    using hX

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends `rename Fin.succ p`
to the affine quotient class of `p`. This is the quotient-level surjectivity witness used by the
source ring chart. -/
@[simp] private theorem coneDehom_quotient_map_rename_succ {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I)
    (p : MvPolynomial (Fin n) R) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p)) =
      Ideal.Quotient.mk I p := by
  -- Evaluate the descended map on `rename Fin.succ p` and use the source dehomogenization formula.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hrename :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (MvPolynomial.rename Fin.succ p)) hcomp
  simpa [F, coneDehom_rename_succ]
    using hrename

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends a bounded
homogenization back to the original affine quotient class. This packages the source identity
`\\widetilde g(1, x_1, \\dots, x_n) = g`. -/
@[simp] private theorem coneDehom_quotient_map_homogenizeTo {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I)
    (d : ℕ) (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (coneHomogenizeTo (R := R) d p)) =
      Ideal.Quotient.mk I p := by
  -- Evaluate the descended quotient map on the homogenized polynomial and collapse the inserted
  -- `X₀`-powers via the already-proved dehomogenization formula.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hhomogenize :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (coneHomogenizeTo (R := R) d p)) hcomp
  simpa [F, coneDehom_homogenizeTo, hp]
    using hhomogenize

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization is surjective. This is the
quotient-level source fact that every affine class lifts by ignoring the extra cone variable. -/
private theorem coneDehom_quotient_map_surjective {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    Function.Surjective (coneDehom_quotient_map (R := R) (n := n) I J hJ) := by
  intro pbar
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective pbar
  refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p), ?_⟩
  simpa using coneDehom_quotient_map_rename_succ (R := R) (n := n) I J hJ p

/-- Helper for Lemma 10.57.10: an element of the degree-`d` mapped homogeneous piece of the cone
quotient is represented by a degree-`d` homogeneous cone polynomial upstairs. -/
private theorem homogeneous_quotient_lift_of_mem_grade {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (qbar :
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
        ((Ideal.Quotient.mkₐ R J).toLinearMap)) :
    ∃ q : MvPolynomial (Fin (n + 1)) R,
      q.IsHomogeneous d ∧ Ideal.Quotient.mk J q = qbar.1 := by
  -- Unpack the mapped degree piece directly: membership in the quotient grading is already given
  -- by a homogeneous source representative.
  rcases qbar.2 with ⟨q, hq, hqbar⟩
  refine ⟨q, ?_, hqbar⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using hq

/-- Helper for Lemma 10.57.10: a degree-`d` homogeneous cone polynomial whose dehomogenization
vanishes in the affine quotient already vanishes in the cone quotient. -/
private theorem cone_polynomial_quotient_eq_zero_of_dehom_zero {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d)
    (hdehom : Ideal.Quotient.mk I (coneDehom (R := R) (n := n) q) = 0) :
    Ideal.Quotient.mk
        (Ideal.span (Set.range fun p : I =>
          coneHomogenizeTo (R := R) p.1.totalDegree p.1)) q = 0 := by
  -- Apply the raw cone-kernel lemma upstairs, then translate ideal membership back to the quotient
  -- class of `q`.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact cone_homogenized_ideal_mem_of_isHomogeneous_of_dehom_mem
    (R := R) (n := n) (I := I) hq
    ((Ideal.Quotient.eq_zero_iff_mem).mp hdehom)

/-- Helper for Lemma 10.57.10: the degree-`d` graded piece of the cone quotient is the image of
the degree-`d` homogeneous submodule under the quotient map. -/
private noncomputable def cone_quotient_grading {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
    ((Ideal.Quotient.mkₐ R J).toLinearMap)

/-- Helper for Lemma 10.57.10: each homogeneous cone piece maps linearly to the corresponding
graded piece of the cone quotient. -/
private noncomputable def cone_quotient_component_map {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d →ₗ[R]
      cone_quotient_grading (R := R) (n := n) J d :=
  LinearMap.codRestrict
    (cone_quotient_grading (R := R) (n := n) J d)
    (((Ideal.Quotient.mkₐ R J).toLinearMap).domRestrict
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Helper for Lemma 10.57.10: the direct sum of the source homogeneous cone pieces carries the
canonical graded semiring structure. -/
private noncomputable instance cone_homogeneous_directSum_gSemiring {n : ℕ} :
    DirectSum.GSemiring
      (fun d ↦ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :=
  inferInstance

/-- Helper for Lemma 10.57.10: the quotient images of the homogeneous cone pieces still form a
graded monoid. -/
private instance cone_quotient_setLikeGradedMonoid {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SetLike.GradedMonoid (cone_quotient_grading (R := R) (n := n) J) where
  one_mem := by
    refine ⟨1, SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), ?_⟩
    simp
  mul_mem := by
    intro i j x y hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    refine ⟨x' * y', SetLike.mul_mem_graded hx' hy', ?_⟩
    simp

/-- Helper for Lemma 10.57.10: before descending to the cone quotient, decompose a cone
polynomial into homogeneous pieces and map each piece componentwise to the quotient. -/
private noncomputable def cone_quotient_predecompose {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R]
      DirectSum ℕ (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) :=
  (DirectSum.lmap fun d ↦ cone_quotient_component_map (R := R) (n := n) J d).comp
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toLinearMap

/-- Helper for Lemma 10.57.10: the componentwise quotient predecomposition annihilates every
element of a homogeneous cone ideal. This is the exact descent input needed before building the
quotient grading on the cone quotient ring. -/
private theorem cone_quotient_predecompose_eq_zero_of_mem_J {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q ∈ J) :
    cone_quotient_predecompose (R := R) (n := n) J q = 0 := by
  ext d
  -- Each homogeneous projection of an element of `J` still lies in `J`, so its quotient image
  -- vanishes coordinatewise.
  have hproj_mem :
      GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q ∈ J := by
    exact (Ideal.IsHomogeneous.mem_iff
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) hJ).1 hq d
  have hproj_zero :
      Ideal.Quotient.mk J
        (GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hproj_mem
  -- After rewriting the `d`-th coordinate of `DirectSum.decompose` as `GradedRing.proj`, the
  -- quotient coordinate is exactly the previously established zero class.
  rw [cone_quotient_predecompose, LinearMap.comp_apply, DirectSum.lmap_apply]
  simp [cone_quotient_component_map]
  rw [DirectSum.decomposeLinearEquiv_apply]
  rw [← GradedRing.proj_apply
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q]
  exact hproj_zero

/-- Helper for Lemma 10.57.10: the quotient class of a degree-`d` homogeneous cone polynomial
already lies in the `d`-th graded piece of the cone quotient. -/
private theorem cone_quotient_mk_mem_grade_of_isHomogeneous {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    Ideal.Quotient.mk J q ∈ cone_quotient_grading (R := R) (n := n) J d := by
  -- The quotient grading is defined as the image of the homogeneous source piece, so the source
  -- representative itself gives the required witness.
  refine ⟨q, ?_, rfl⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using hq

/-- Helper for Lemma 10.57.10: on the direct sum of source homogeneous pieces, the componentwise
quotient maps preserve the multiplicative graded generators. -/
private theorem cone_quotient_directSum_component_preserves_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    (DirectSum.lof R ℕ
        (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) 0)
      ((cone_quotient_component_map (R := R) (n := n) J 0)
        ⟨1, SetLike.one_mem_graded
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)⟩) = 1 := by
  -- The quotient component map sends the degree-zero unit to the degree-zero direct-sum unit.
  rw [DirectSum.lof_eq_of]
  rfl

/-- Helper for Lemma 10.57.10: on the direct sum of source homogeneous pieces, the componentwise
quotient maps respect graded multiplication. -/
private theorem cone_quotient_directSum_component_preserves_mul {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) {i j : ℕ}
    (x : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R i)
    (y : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R j) :
      (DirectSum.lof R ℕ
          (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) (i + j))
      ((cone_quotient_component_map (R := R) (n := n) J (i + j))
        ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩) =
      (DirectSum.lof R ℕ
          (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) i)
        ((cone_quotient_component_map (R := R) (n := n) J i) x) *
        (DirectSum.lof R ℕ
            (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) j)
          ((cone_quotient_component_map (R := R) (n := n) J j) y) := by
  -- Multiplication of direct-sum generators matches multiplication of the quotient classes.
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rfl

/-- Helper for Lemma 10.57.10: map the direct sum of homogeneous cone pieces to the direct sum of
their quotient images degreewise. -/
private noncomputable def cone_quotient_directSumAlgHom {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    (⨁ d, MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  DirectSum.toAlgebra (R := R)
    (A := fun d ↦ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d)
    (B := ⨁ d, cone_quotient_grading (R := R) (n := n) J d)
    (fun d ↦
      (DirectSum.lof R ℕ
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d).comp
        (cone_quotient_component_map (R := R) (n := n) J d))
    (cone_quotient_directSum_component_preserves_one (R := R) (n := n) J)
    (fun {_i _j} x y ↦
      cone_quotient_directSum_component_preserves_mul (R := R) (n := n) J x y)

/-- Helper for Lemma 10.57.10: before quotienting by `J`, the algebra decomposition into source
homogeneous pieces can be followed by the componentwise quotient maps. -/
private noncomputable def cone_quotient_predecomposeAlgHom {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  (cone_quotient_directSumAlgHom (R := R) (n := n) J).comp
    (DirectSum.decomposeAlgEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toAlgHom

/-- Helper for Lemma 10.57.10: the algebraic predecomposition agrees with the previously defined
linear predecomposition on cone polynomials. -/
private theorem cone_quotient_predecomposeAlgHom_apply {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (q : MvPolynomial (Fin (n + 1)) R) :
    cone_quotient_predecomposeAlgHom (R := R) (n := n) J q =
      cone_quotient_predecompose (R := R) (n := n) J q := by
  -- The algebraic map and the linear map agree because `DirectSum.toAlgebra` extends the same
  -- degreewise component maps on each direct-sum generator.
  have hlmap :
      (cone_quotient_directSumAlgHom (R := R) (n := n) J).toLinearMap =
        DirectSum.lmap (fun d ↦ cone_quotient_component_map (R := R) (n := n) J d) := by
    apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro x
    simpa [LinearMap.comp_apply, cone_quotient_directSumAlgHom, DirectSum.lof_eq_of,
      DirectSum.lmap_lof] using
      (DirectSum.toSemiring_of
        (f := fun e ↦
          ((DirectSum.lof R ℕ
            (fun f ↦ cone_quotient_grading (R := R) (n := n) J f) e).comp
            (cone_quotient_component_map (R := R) (n := n) J e)).toAddMonoidHom)
        (hone := cone_quotient_directSum_component_preserves_one (R := R) (n := n) J)
        (hmul := fun {_i _j} x y ↦
          cone_quotient_directSum_component_preserves_mul (R := R) (n := n) J x y)
        d x)
  simpa [cone_quotient_predecomposeAlgHom, cone_quotient_predecompose, LinearMap.comp_apply,
    DirectSum.decomposeAlgEquiv_apply, DirectSum.decomposeLinearEquiv_apply] using
    congrArg
      (fun φ :
        (⨁ d, MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) →ₗ[R]
          (⨁ d, cone_quotient_grading (R := R) (n := n) J d) =>
        φ (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) q))
      hlmap

/-- Helper for Lemma 10.57.10: for a homogeneous source polynomial, the quotient predecomposition
is concentrated in the matching degree. -/
private theorem cone_quotient_predecompose_eq_of_isHomogeneous {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    cone_quotient_predecompose (R := R) (n := n) J q =
      DirectSum.of
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
        ⟨Ideal.Quotient.mk J q,
          cone_quotient_mk_mem_grade_of_isHomogeneous
            (R := R) (n := n) (J := J) hq⟩ := by
  -- A homogeneous polynomial has only one nonzero source component, so the quotient
  -- predecomposition is concentrated in the matching direct-sum slot.
  have hq_mem :
      q ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d := by
    simpa [MvPolynomial.mem_homogeneousSubmodule] using hq
  change (DirectSum.lmap fun e ↦ cone_quotient_component_map (R := R) (n := n) J e)
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) q) =
    DirectSum.of
      (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
      ⟨Ideal.Quotient.mk J q,
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J) hq⟩
  rw [DirectSum.decompose_of_mem _ hq_mem]
  rw [DirectSum.lmap_of]
  rfl

/-- Helper for Lemma 10.57.10: the algebraic quotient predecomposition already annihilates the
cone ideal, so it can descend through the quotient. -/
private theorem cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (q : MvPolynomial (Fin (n + 1)) R) (hq : q ∈ J) :
    cone_quotient_predecomposeAlgHom (R := R) (n := n) J q = 0 := by
  -- The algebraic and linear predecompositions agree pointwise, so the earlier vanishing lemma
  -- on `J` is already enough for the quotient lift.
  rw [cone_quotient_predecomposeAlgHom_apply]
  exact cone_quotient_predecompose_eq_zero_of_mem_J
    (R := R) (n := n) hJ hq

/-- Helper for Lemma 10.57.10: if `J` is homogeneous, the source algebraic predecomposition
descends through the quotient by `J`. -/
private noncomputable def cone_quotient_decomposeAlgHom_of_homogeneous_ideal {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  Ideal.Quotient.liftₐ J
    (cone_quotient_predecomposeAlgHom (R := R) (n := n) J)
    (cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J
      (R := R) (n := n) J hJ)

/-- Helper for Lemma 10.57.10: the descended quotient decomposition recovers the source-side
predecomposition after precomposing with the quotient map. -/
private theorem cone_quotient_decomposeAlgHom_comp_mk {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (cone_quotient_decomposeAlgHom_of_homogeneous_ideal
        (R := R) (n := n) J hJ).comp (Ideal.Quotient.mkₐ R J) =
      cone_quotient_predecomposeAlgHom (R := R) (n := n) J := by
  -- The descended map computes by the defining quotient-lift formula.
  simpa [cone_quotient_decomposeAlgHom_of_homogeneous_ideal] using
    (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J)
      (cone_quotient_predecomposeAlgHom (R := R) (n := n) J)
      (cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J
        (R := R) (n := n) J hJ))

/-- Helper for Lemma 10.57.10: the descended quotient decomposition is a right inverse to the
canonical direct-sum algebra map back to the cone quotient ring. -/
private theorem cone_quotient_decomposeAlgHom_right_inv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (DirectSum.coeAlgHom (cone_quotient_grading (R := R) (n := n) J)).comp
        (cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  -- Check the identity after precomposing with the quotient map, then use quotient extensionality.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := J) ?_
  rw [AlgHom.comp_assoc, cone_quotient_decomposeAlgHom_comp_mk]
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, cone_quotient_predecomposeAlgHom_apply]
  rw [cone_quotient_predecompose_eq_of_isHomogeneous (R := R) (n := n) (J := J)
    (d := 1) (q := MvPolynomial.X i) (MvPolynomial.isHomogeneous_X (R := R) i)]
  simp

/-- Helper for Lemma 10.57.10: on a homogeneous quotient class, the descended quotient
decomposition lands in the expected direct-sum slot. -/
private theorem cone_quotient_decomposeAlgHom_left_inv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (d : ℕ) (x : cone_quotient_grading (R := R) (n := n) J d) :
    cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ (x : _) =
      DirectSum.of
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
  -- Lift the quotient class to a homogeneous source representative, then use concentration of the
  -- source predecomposition in its degree.
  rcases homogeneous_quotient_lift_of_mem_grade (R := R) (n := n) (d := d) x with ⟨q, hq, hqx⟩
  have hx :
      (⟨Ideal.Quotient.mk J q,
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J) hq⟩
        : cone_quotient_grading (R := R) (n := n) J d) = x := by
    ext
    exact hqx
  have hcomp :=
    show
      cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ
          (Ideal.Quotient.mk J q) =
        cone_quotient_predecomposeAlgHom (R := R) (n := n) J q by
      simpa [AlgHom.comp_apply] using
        AlgHom.congr_fun
          (cone_quotient_decomposeAlgHom_comp_mk (R := R) (n := n) J hJ) q
  calc
    cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ (x : _) =
        cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ
          (Ideal.Quotient.mk J q) := by rw [hqx]
    _ = DirectSum.of
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
          ⟨Ideal.Quotient.mk J q,
            cone_quotient_mk_mem_grade_of_isHomogeneous
              (R := R) (n := n) (J := J) hq⟩ := by
      rw [hcomp, cone_quotient_predecomposeAlgHom_apply]
      exact cone_quotient_predecompose_eq_of_isHomogeneous
        (R := R) (n := n) (J := J) (d := d) hq
    _ = DirectSum.of
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
      simpa [hx]

/-- Helper for Lemma 10.57.10: a homogeneous cone ideal induces an owner-level graded algebra
structure on the cone quotient ring. -/
private noncomputable def cone_quotient_gradedAlgebra_of_homogeneous_ideal {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    GradedAlgebra (cone_quotient_grading (R := R) (n := n) J) :=
  GradedAlgebra.ofAlgHom (cone_quotient_grading (R := R) (n := n) J)
    (cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ)
    (cone_quotient_decomposeAlgHom_right_inv (R := R) (n := n) J hJ)
    (cone_quotient_decomposeAlgHom_left_inv (R := R) (n := n) J hJ)

/-- Helper for Lemma 10.57.10: the quotient class of `X i.succ` lies in the degree-one cone piece,
so it defines the canonical degree-zero fraction `X(i+1) / X0` in the homogeneous localization. -/
private theorem cone_quotient_X_succ_mem_grade_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin n) :
    Ideal.Quotient.mk J (MvPolynomial.X i.succ) ∈
      cone_quotient_grading (R := R) (n := n) J 1 := by
  -- The source variable `X i.succ` is already homogeneous of degree `1`, so its quotient class
  -- lands in the degree-one cone piece by construction.
  exact cone_quotient_mk_mem_grade_of_isHomogeneous
    (R := R) (n := n) (J := J) (MvPolynomial.isHomogeneous_X (R := R) i.succ)

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends the cone denominator
to a unit, so ordinary away-localization at `X 0` can be evaluated back in the affine quotient. -/
private theorem coneDehom_quotient_map_X_zero_isUnit {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    IsUnit
      (coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))) := by
  -- The quotient-level dehomogenization formula already computes the cone denominator as `1`.
  rw [coneDehom_quotient_map_X_zero (R := R) (n := n) I J hJ]
  exact isUnit_one

/-- Helper for Lemma 10.57.10: after descending dehomogenization to the cone quotient, the
ordinary away-localization at the image of `X 0` maps canonically to the affine quotient because
that denominator already goes to `1`. -/
private noncomputable def cone_ordinary_away_to_affine_quotient {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    Localization.Away (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) →+*
      (MvPolynomial (Fin n) R ⧸ I) :=
  Localization.awayLift
    (coneDehom_quotient_map (R := R) (n := n) I J hJ).toRingHom
    (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))
    (coneDehom_quotient_map_X_zero_isUnit (R := R) (n := n) I J hJ)

/-- Helper for Lemma 10.57.10: shift the cone homogenized affine kernel to positive degree so
degree-zero scalars are not already killed in the cone quotient. -/
private noncomputable def positively_shifted_cone_homogenized_ideal {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (Set.range fun p : I =>
    coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1)

/-- Helper for Lemma 10.57.10: the positively shifted cone kernel remains homogeneous for the
standard grading on the cone polynomial ring. -/
private theorem positively_shifted_cone_homogenized_ideal_isHomogeneous {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  -- The one-step degree shift preserves homogeneity because each chosen generator is still
  -- homogeneous in its declared source degree.
  rw [positively_shifted_cone_homogenized_ideal]
  apply Ideal.homogeneous_span
  intro q hq
  rcases hq with ⟨p, rfl⟩
  refine ⟨max p.1.totalDegree 1, ?_⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using
    coneHomogenizeTo_isHomogeneous (R := R) (n := n) (max p.1.totalDegree 1) p.1

/-- Helper for Lemma 10.57.10: the positively shifted cone kernel still dehomogenizes into the
affine kernel under `X₀ ↦ 1`. -/
private theorem positively_shifted_cone_homogenized_ideal_le_comap_coneDehom {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    positively_shifted_cone_homogenized_ideal (R := R) (n := n) I ≤
      Ideal.comap (coneDehom (R := R) (n := n)) I := by
  -- Each shifted generator dehomogenizes back to the same affine kernel element because the shift
  -- degree still dominates the total degree.
  rw [positively_shifted_cone_homogenized_ideal, Ideal.span_le]
  intro q hq
  rcases hq with ⟨p, rfl⟩
  change
    coneDehom (R := R) (n := n)
        (coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1) ∈ I
  rw [coneDehom_homogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1 (le_max_left _ _)]
  exact p.2

/-- Helper for Lemma 10.57.10: for localization away from a degree-one element, the required
target degree `d • 1` is just the original homogeneous degree `d`. -/
private theorem cone_quotient_mk_mem_grade_of_isHomogeneous_nsmul_one {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    Ideal.Quotient.mk J q ∈ cone_quotient_grading (R := R) (n := n) J (d • 1) := by
  simpa using
    (cone_quotient_mk_mem_grade_of_isHomogeneous
      (R := R) (n := n) (J := J) (d := d) hq)

/-- Helper for Lemma 10.57.10: if a homogeneous cone polynomial dehomogenizes into the affine
kernel, then its normalized fraction vanishes in the ordinary away-localization of the positively
shifted cone quotient. -/
private theorem normalized_homogeneous_fraction_eq_zero_of_dehom_mem {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d)
    (hdehom : coneDehom (R := R) (n := n) q ∈ I) :
    (Localization.mk
      (Ideal.Quotient.mk
        (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) q)
      ⟨(Ideal.Quotient.mk
          (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
          (MvPolynomial.X (0 : Fin (n + 1)))) ^ d, by exact ⟨d, rfl⟩⟩ :
      Localization.Away
        (Ideal.Quotient.mk
          (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
          (MvPolynomial.X (0 : Fin (n + 1))))) = 0 := by
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal (R := R) (n := n) I
  let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
    Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
  have htd :
      (coneDehom (R := R) (n := n) q).totalDegree ≤ d :=
    coneDehom_totalDegree_le_of_isHomogeneous (R := R) (n := n) (d := d) hq
  -- Compare in the ordinary away-localization and then use the shifted cone generators to clear
  -- the numerator by a suitable power of `X₀`.
  by_cases hd0 : d = 0
  · have hp0 : (coneDehom (R := R) (n := n) q).totalDegree = 0 := by
      exact Nat.eq_zero_of_le_zero (hd0 ▸ htd)
    have hqeq :
        coneHomogenizeTo (R := R) (n := n) 0 (coneDehom (R := R) (n := n) q) = q := by
      simpa [hd0] using
        (coneHomogenizeTo_coneDehom_of_isHomogeneous
          (R := R) (n := n) (d := d) hq)
    have hgen_mem :
        coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈ J := by
      exact Ideal.subset_span
        (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
          simp [J, hp0]⟩ :
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈
            Set.range fun p : I =>
              coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
    have hshift :
        MvPolynomial.X (0 : Fin (n + 1)) *
            coneHomogenizeTo (R := R) (n := n) 0 (coneDehom (R := R) (n := n) q) =
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) := by
      simpa [hp0, pow_one] using
        (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
          (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q)
          (by simpa [hp0])).symm
    have hmul_zero : f0 * Ideal.Quotient.mk J q = 0 := by
      change Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)) * q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hqeq, hshift]
      exact hgen_mem
    rw [hd0, Localization.mk_eq_mk']
    change IsLocalization.mk' (Localization.Away f0) (Ideal.Quotient.mk J q)
      (1 : Submonoid.powers f0) = 0
    refine (IsLocalization.mk'_eq_zero_iff
      (S := Localization.Away f0) (Ideal.Quotient.mk J q) (1 : Submonoid.powers f0)).2 ?_
    refine ⟨⟨f0, ⟨1, by simp⟩⟩, ?_⟩
    simpa [f0, J] using hmul_zero
  · rcases d with _ | d
    · contradiction
    have hq_mem : q ∈ J := by
      by_cases hp0 : (coneDehom (R := R) (n := n) q).totalDegree = 0
      · have hgen_mem :
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈ J := by
          exact Ideal.subset_span
            (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
              simp [J, hp0]⟩ :
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈
                Set.range fun p : I =>
                  coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
        have hqeq :
            q = MvPolynomial.X (0 : Fin (n + 1)) ^ d *
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) := by
          have hqeq' :
              coneHomogenizeTo (R := R) (n := n) (d + 1) (coneDehom (R := R) (n := n) q) = q := by
            simpa using
              (coneHomogenizeTo_coneDehom_of_isHomogeneous
                (R := R) (n := n) (d := d + 1) hq)
          have hshift_d :
              coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) =
                MvPolynomial.X (0 : Fin (n + 1)) ^ (d + 1) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := by
            simpa [hp0] using
              (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                (R := R) (n := n) (d + 1) (coneDehom (R := R) (n := n) q)
                (by simpa [hp0]))
          have hshift_one :
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) =
                MvPolynomial.X (0 : Fin (n + 1)) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := by
            simpa [hp0, pow_one] using
              (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q)
                (by simpa [hp0]))
          calc
            q =
                coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) := by
                  symm
                  exact hqeq'
            _ = MvPolynomial.X (0 : Fin (n + 1)) ^ (d + 1) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := hshift_d
            _ = MvPolynomial.X (0 : Fin (n + 1)) ^ d *
                  coneHomogenizeTo (R := R) (n := n) 1
                    (coneDehom (R := R) (n := n) q) := by
                  rw [pow_succ, mul_assoc, hshift_one]
        rw [hqeq]
        exact Ideal.mul_mem_left _ _ hgen_mem
      · have hp1 :
          1 ≤ (coneDehom (R := R) (n := n) q).totalDegree := by
          exact Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hp0)
        have hgen_mem :
            coneHomogenizeTo (R := R) (n := n)
                (coneDehom (R := R) (n := n) q).totalDegree
                (coneDehom (R := R) (n := n) q) ∈ J := by
          exact Ideal.subset_span
            (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
              simp [J, max_eq_left hp1]⟩ :
              coneHomogenizeTo (R := R) (n := n)
                  (coneDehom (R := R) (n := n) q).totalDegree
                  (coneDehom (R := R) (n := n) q) ∈
                Set.range fun p : I =>
                  coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
        have hqeq :
            q =
              MvPolynomial.X (0 : Fin (n + 1)) ^
                ((d + 1) - (coneDehom (R := R) (n := n) q).totalDegree) *
              coneHomogenizeTo (R := R) (n := n)
                (coneDehom (R := R) (n := n) q).totalDegree
                (coneDehom (R := R) (n := n) q) := by
          calc
            q =
                coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) := by
                  symm
                  exact coneHomogenizeTo_coneDehom_of_isHomogeneous
                    (R := R) (n := n) (d := d + 1) hq
            _ =
                MvPolynomial.X (0 : Fin (n + 1)) ^
                  ((d + 1) - (coneDehom (R := R) (n := n) q).totalDegree) *
                coneHomogenizeTo (R := R) (n := n)
                  (coneDehom (R := R) (n := n) q).totalDegree
                  (coneDehom (R := R) (n := n) q) := by
                  exact coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                    (R := R) (n := n) (d + 1)
                    (coneDehom (R := R) (n := n) q) htd
        rw [hqeq]
        exact Ideal.mul_mem_left _ _ hgen_mem
    have hq_zero : Ideal.Quotient.mk J q = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hq_mem
    simp [J, Localization.mk_eq_mk', hq_zero]

/-- Helper for Lemma 10.57.10: every positively shifted cone generator has zero constant
coefficient because it is homogeneous of positive degree. -/
private theorem constantCoeff_coneHomogenizeTo_max_totalDegree_one_eq_zero {n : ℕ}
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.constantCoeff
        (coneHomogenizeTo (R := R) (n := n) (max p.totalDegree 1) p) = 0 := by
  -- The shift to `max totalDegree 1` forces positive total degree, so the degree-zero monomial
  -- cannot appear.
  have hhom :
      (coneHomogenizeTo (R := R) (n := n) (max p.totalDegree 1) p).IsHomogeneous
        (max p.totalDegree 1) :=
    coneHomogenizeTo_isHomogeneous (R := R) (n := n) (max p.totalDegree 1) p
  have hpositive : 0 < max p.totalDegree 1 := by
    exact Nat.succ_le_iff.mp (le_max_right p.totalDegree 1)
  have hdegree_ne : (0 : Fin (n + 1) →₀ ℕ).degree ≠ max p.totalDegree 1 := by
    intro hzero
    exact Nat.ne_of_gt hpositive hzero.symm
  simpa [MvPolynomial.constantCoeff_eq] using hhom.coeff_eq_zero hdegree_ne

/-- Helper for Lemma 10.57.10: every element of the positively shifted cone kernel has zero
constant coefficient. This is the key degree-zero input for the corrected cone quotient. -/
private theorem positively_shifted_cone_homogenized_ideal_constantCoeff_eq_zero {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q ∈ positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) :
    MvPolynomial.constantCoeff q = 0 := by
  -- The property is stable under addition and multiplication by arbitrary cone polynomials, so a
  -- span induction over the shifted generators suffices.
  change q ∈
      Ideal.span (Set.range fun p : I =>
        coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1) at hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · intro x hx
    rcases hx with ⟨p, rfl⟩
    exact constantCoeff_coneHomogenizeTo_max_totalDegree_one_eq_zero
      (R := R) (n := n) p.1
  · simp
  · intro x y _ _ hx hy
    simp [map_add, hx, hy]
  · intro a x _ hx
    simp [smul_eq_mul, map_mul, hx]

/-- Helper for Lemma 10.57.10: a constant polynomial in the positively shifted cone kernel must be
zero, because that kernel has zero constant coefficient. -/
private theorem eq_zero_of_C_mem_positively_shifted_cone_homogenized_ideal {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {r : R}
    (hr :
      MvPolynomial.C r ∈ positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) :
    r = 0 := by
  -- Apply the constant-coefficient vanishing lemma to the constant polynomial representative.
  have hconst :
      MvPolynomial.constantCoeff (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) = 0 :=
    positively_shifted_cone_homogenized_ideal_constantCoeff_eq_zero
      (R := R) (n := n) hr
  simpa using hconst

/-- Helper for Lemma 10.57.10: the quotient class of `X 0` is, tautologically, a power of itself in
the ordinary away-localization denominator submonoid. -/
private theorem cone_quotient_X_zero_mem_powers {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))) ∈
      Submonoid.powers (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) := by
  exact ⟨1, by simp⟩

/-- Helper for Lemma 10.57.10: every cone variable class in the quotient ring is homogeneous of
degree `1`. -/
private theorem cone_quotient_X_mem_grade_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1)) :
    Ideal.Quotient.mk J (MvPolynomial.X i) ∈
      cone_quotient_grading (R := R) (n := n) J 1 := by
  -- Split the cone variable into the denominator variable `X 0` and the shifted affine variables,
  -- then invoke the already established homogeneous-degree-one formulas in each case.
  refine Fin.cases ?_ ?_ i
  · exact cone_quotient_mk_mem_grade_of_isHomogeneous
      (R := R) (n := n) (J := J)
      (MvPolynomial.isHomogeneous_X (R := R) (0 : Fin (n + 1)))
  · intro j
    exact cone_quotient_X_succ_mem_grade_one (R := R) (n := n) J j

/-- Helper for Lemma 10.57.10: the finitely many quotient classes of the cone variables generate
the cone quotient ring over its degree-zero part. -/
private theorem cone_quotient_degree_one_generators_adjoin_top {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)] :
    let S := MvPolynomial (Fin (n + 1)) R ⧸ J
    let grading := cone_quotient_grading (R := R) (n := n) J
    let s : Set S := Set.range fun i : Fin (n + 1) =>
      Ideal.Quotient.mk J (MvPolynomial.X i)
    Algebra.adjoin (grading 0) (s : Set S) = ⊤ := by
  classical
  let S := MvPolynomial (Fin (n + 1)) R ⧸ J
  let grading := cone_quotient_grading (R := R) (n := n) J
  let s : Set S := Set.range fun i : Fin (n + 1) =>
    Ideal.Quotient.mk J (MvPolynomial.X i)
  let B : Subalgebra (grading 0) S := Algebra.adjoin (grading 0) (s : Set S)
  -- The quotient ring is generated by constants and the cone variables, so it suffices to prove
  -- that every quotient polynomial class already lies in the adjoin generated by those variables.
  rw [show B = ⊤ ↔ ⊤ ≤ B by rw [← top_le_iff]]
  intro x _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let P : MvPolynomial (Fin (n + 1)) R → Prop := fun q =>
    (Ideal.Quotient.mk J q : S) ∈ B
  change P p
  refine MvPolynomial.induction_on p ?_ ?_ ?_
  · intro r
    change P (MvPolynomial.C r)
    let r₀ : grading 0 := ⟨Ideal.Quotient.mk J (MvPolynomial.C r), by
      exact cone_quotient_mk_mem_grade_of_isHomogeneous
        (R := R) (n := n) (J := J)
        (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) r)⟩
    -- Constants land in the degree-zero piece, hence already belong to the base subalgebra.
    simpa [B, grading, S] using B.algebraMap_mem r₀
  · intro p q hp hq
    -- The adjoin is closed under addition, so the induction hypothesis is stable under sums.
    change P (p + q)
    simpa [P, map_add] using B.add_mem hp hq
  · intro p i hp
    -- Multiplying by one more cone variable stays inside the adjoin because that variable is one
    -- of the chosen generators.
    have hi : (Ideal.Quotient.mk J (MvPolynomial.X i) : S) ∈ B := by
      exact Algebra.subset_adjoin (by
        refine Set.mem_range.mpr ?_
        exact ⟨i, rfl⟩)
    change P (p * MvPolynomial.X i)
    simpa [P, map_mul] using B.mul_mem hp hi

/-- Helper for Lemma 10.57.10: under the current minimal-degree cone ideal, any scalar whose
constant affine polynomial already lies in `I` is killed in the cone quotient as well. This is the
exact obstruction to obtaining `S₀ ≃ R` from the present cone-kernel choice when the original
structure map `R → R'` has kernel. -/
private theorem cone_quotient_constant_eq_zero_of_mem_affine_kernel {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) {r : R}
    (hr : MvPolynomial.C r ∈ I) :
    Ideal.Quotient.mk
        (Ideal.span (Set.range fun p : I =>
          coneHomogenizeTo (R := R) p.1.totalDegree p.1))
        (MvPolynomial.C r) = 0 := by
  -- The current cone ideal includes the minimal homogenization of every kernel element, and for a
  -- constant kernel element that minimal homogenization is still the same constant polynomial.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span
    (⟨⟨MvPolynomial.C r, hr⟩, by
      simpa using (coneHomogenizeTo_C (R := R) (n := n) r)⟩ :
      (MvPolynomial.C r) ∈ Set.range fun p : I =>
        coneHomogenizeTo (R := R) p.1.totalDegree p.1)

/-- Helper for Lemma 10.57.10: every degree-zero class in the cone quotient is represented by a
constant polynomial. This is the normalized source-faithful form of the corrected `S₀ = R`
statement before packaging it as an algebra isomorphism. -/
private theorem cone_quotient_grade_zero_normal_form {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (x : cone_quotient_grading (R := R) (n := n) J 0) :
    ∃ r : R,
      (⟨Ideal.Quotient.mk J (MvPolynomial.C r),
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J)
          (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) r)⟩ :
        cone_quotient_grading (R := R) (n := n) J 0) = x := by
  -- Lift the quotient class to a homogeneous degree-zero polynomial upstairs.
  rcases homogeneous_quotient_lift_of_mem_grade (R := R) (n := n) (d := 0) x with ⟨q, hq, hq_eq⟩
  have hdeg : q.totalDegree = 0 := by
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := q)).2 hq
  -- Degree-zero homogeneous cone polynomials are exactly constants.
  have hqC : q = MvPolynomial.C (q.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := q)).mp hdeg
  refine ⟨q.coeff 0, ?_⟩
  ext
  rw [hqC] at hq_eq
  exact hq_eq

/-- Helper for Lemma 10.57.10: the corrected shifted cone quotient kills a constant polynomial
exactly when the scalar itself is zero. -/
private theorem cone_quotient_constant_class_eq_zero_iff {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) (r : R) :
    Ideal.Quotient.mk J (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) = 0 ↔ r = 0 := by
  constructor
  · -- Move quotient-zero back to ideal membership, then use the corrected constant-kernel input.
    intro hr
    exact hJ_constant r ((Ideal.Quotient.eq_zero_iff_mem).mp hr)
  · -- The zero scalar gives the zero class tautologically.
    intro hr
    simpa [hr]

/-- Helper for Lemma 10.57.10: the canonical scalar map into the degree-zero cone quotient piece
is injective once constants are not killed by the shifted cone ideal. -/
private theorem cone_quotient_grade_zero_algebraMap_injective {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) :
    Function.Injective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) := by
  intro r s hrs
  have hconst :
      (Ideal.Quotient.mk J (MvPolynomial.C r) :
          MvPolynomial (Fin (n + 1)) R ⧸ J) =
        Ideal.Quotient.mk J (MvPolynomial.C s) := by
    have hconstQ :
        (((Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) r :
            cone_quotient_grading (R := R) (n := n) J 0) :
          MvPolynomial (Fin (n + 1)) R ⧸ J) =
          ((Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0) s :
              cone_quotient_grading (R := R) (n := n) J 0) :
            MvPolynomial (Fin (n + 1)) R ⧸ J) :=
      congrArg (fun x : cone_quotient_grading (R := R) (n := n) J 0 => x.1) hrs
    change
      (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) r =
        (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) s at hconstQ
    change
      (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) r =
        (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) s
    exact hconstQ
  have hsub :
      Ideal.Quotient.mk J (MvPolynomial.C (r - s) : MvPolynomial (Fin (n + 1)) R) = 0 := by
    simpa [MvPolynomial.C_sub] using sub_eq_zero.mpr hconst
  -- Reduce injectivity to the already normalized constant-class criterion.
  exact sub_eq_zero.mp <|
    (cone_quotient_constant_class_eq_zero_iff
      (R := R) (n := n) (J := J) hJ_constant (r - s)).mp hsub

/-- Helper for Lemma 10.57.10: every degree-zero quotient class is reached by the canonical scalar
map from `R`. -/
private theorem cone_quotient_grade_zero_algebraMap_surjective {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    : Function.Surjective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) := by
  intro x
  rcases cone_quotient_grade_zero_normal_form (R := R) (n := n) (J := J) x with ⟨r, rfl⟩
  -- The normalized constant representative is exactly the image of `r`.
  refine ⟨r, ?_⟩
  ext
  rfl

/-- Helper for Lemma 10.57.10: the degree-zero piece of the shifted cone quotient is canonically
the base ring `R`. -/
private noncomputable def cone_quotient_grade_zero_algEquiv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) :
    R ≃ₐ[R] cone_quotient_grading (R := R) (n := n) J 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0))
    ⟨cone_quotient_grade_zero_algebraMap_injective
        (R := R) (n := n) (J := J) hJ_constant,
      cone_quotient_grade_zero_algebraMap_surjective
        (R := R) (n := n) (J := J)⟩

/-- Helper for Lemma 10.57.10: the finite free module on `Fin r` over the cone quotient inherits
the coordinatewise grading from the cone quotient ring. -/
private noncomputable def free_cone_module_grading {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Submodule R (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Submodule.pi Set.univ fun _ : Fin r =>
    cone_quotient_grading (R := R) (n := n) J d

/-- Helper for Lemma 10.57.10: the cone quotient ring acts on itself by multiplication. Making
this owner instance explicit avoids repeated typeclass search through quotient-ring defaults in the
free-module grading API. -/
private noncomputable instance cone_quotient_selfModule {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Module (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  Semiring.toModule

/-- Helper for Lemma 10.57.10: the free cone module on `Fin r` is the standard pointwise module
over the cone quotient ring. This is the owner-level Pi-module API used by the homogeneous-span
arguments below. -/
private noncomputable instance free_cone_module_pointwiseModule {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Module (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Pi.Function.module (I := Fin r)
    (α := MvPolynomial (Fin (n + 1)) R ⧸ J)
    (β := MvPolynomial (Fin (n + 1)) R ⧸ J)

/-- Helper for Lemma 10.57.10: expose the pointwise scalar action on the free cone module
directly, so later graded-module owners do not spend heartbeats rediscovering it through the full
module hierarchy. -/
@[reducible] private noncomputable instance free_cone_module_pointwiseSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SMul (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  (free_cone_module_pointwiseModule (R := R) (n := n) (r := r) J).toSMul

/-- Helper for Lemma 10.57.10: membership in the free cone-module grading is coordinatewise
membership in the corresponding cone quotient piece. -/
private theorem mem_free_cone_module_grading_iff {n r d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)} :
    v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d ↔
      ∀ i, v i ∈ cone_quotient_grading (R := R) (n := n) J d := by
  -- The coordinatewise grading is exactly the product submodule over all coordinates.
  simp [free_cone_module_grading]

/-- Helper for Lemma 10.57.10: insert a homogeneous cone quotient class into a single coordinate
of the free cone module, keeping the same source degree. -/
private noncomputable def free_cone_module_degree_single {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin r) (d : ℕ) :
    cone_quotient_grading (R := R) (n := n) J d →ₗ[R]
      free_cone_module_grading (R := R) (n := n) (r := r) J d :=
  LinearMap.codRestrict
    (free_cone_module_grading (R := R) (n := n) (r := r) J d)
    (((LinearMap.single R (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i).comp
      (cone_quotient_grading (R := R) (n := n) J d).subtype))
    (fun x ↦ by
      -- The inserted vector is zero off the chosen coordinate and equals the given homogeneous
      -- class at that coordinate, so it still lies in the degree-`d` piece coordinatewise.
      rw [mem_free_cone_module_grading_iff]
      intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [LinearMap.single_apply, hji])

/-- Helper for Lemma 10.57.10: the degreewise coordinate insertion is exactly the expected
`Pi.single` on the underlying vector. -/
@[simp] private theorem free_cone_module_degree_single_coe {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin r)
    (x : cone_quotient_grading (R := R) (n := n) J d) :
    ((free_cone_module_degree_single (R := R) (n := n) (r := r) J i d x :
        free_cone_module_grading (R := R) (n := n) (r := r) J d) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      Pi.single i (x : MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  rfl

/-- Helper for Lemma 10.57.10: decompose each coordinate of the free cone module and reinsert the
homogeneous summands into the matching coordinate of the graded direct sum. -/
private noncomputable def free_cone_module_predecomposeLinear {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[R]
      (⨁ d : ℕ, free_cone_module_grading (R := R) (n := n) (r := r) J d) :=
  ∑ i : Fin r,
    (DirectSum.lmap
      (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i d)).comp
      (((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap).comp
        (LinearMap.proj i))

/-- Helper for Lemma 10.57.10: for one fixed coordinate, decomposing and then recomposing the
inserted homogeneous summands recovers the corresponding `Pi.single` vector. -/
private theorem free_cone_module_coordinate_recompose {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    (i : Fin r) :
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) ∘ₗ
      (DirectSum.lmap
        (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i d)) ∘ₗ
      ((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) =
        LinearMap.single R
          (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i := by
  -- Compare both maps on each homogeneous source summand of the cone quotient grading.
  apply DirectSum.decompose_lhom_ext
    (ℳ := cone_quotient_grading (R := R) (n := n) J)
  intro d
  apply LinearMap.ext
  intro x
  -- On a homogeneous source vector, the decomposition is already the single `lof` term.
  change
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J)
        ((DirectSum.lmap
            (fun e ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i e))
          (((DirectSum.decomposeLinearEquiv
              (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) x)) =
      LinearMap.single R
        (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i x
  have hx :
      ((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) x =
        DirectSum.lof R ℕ
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (cone_quotient_grading (R := R) (n := n) J) d x)
  rw [hx, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  ext j
  by_cases hji : j = i
  · subst hji
    simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, hji]

/-- Helper for Lemma 10.57.10: the `e`-component of the free-cone predecomposition is obtained by
decomposing each coordinate in degree `e`. This is the coercion-stable bridge from the direct-sum
object back to the coordinatewise source data. -/
private theorem free_cone_module_predecompose_component_eq_coordinate_decompose {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    (v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) (e : ℕ) :
    (((free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v) e :
        free_cone_module_grading (R := R) (n := n) (r := r) J e) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      fun i ↦
        ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) (v i) e :
            cone_quotient_grading (R := R) (n := n) J e) :
            MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  -- Expand the finite sum defining the predecomposition and read off one coordinate. Only the
  -- `Pi.single` inserted at that coordinate survives.
  ext i
  have hcomponent :
      (((free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v) e :
          free_cone_module_grading (R := R) (n := n) (r := r) J e) :
          Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
        ∑ j : Fin r,
          ((((DirectSum.lmap
                (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J j d))
              (((DirectSum.decomposeLinearEquiv
                  (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) (v j))) e :
              free_cone_module_grading (R := R) (n := n) (r := r) J e) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := by
    -- First project the finite sum to degree `e`, and then coerce that graded piece back to the
    -- underlying coordinatewise function.
    rw [free_cone_module_predecomposeLinear, LinearMap.sum_apply]
    simpa [LinearMap.comp_apply, LinearMap.proj_apply] using
      congrArg
        (fun z :
          free_cone_module_grading (R := R) (n := n) (r := r) J e ↦
            (z : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (DFinsupp.finset_sum_apply Finset.univ
          (fun j : Fin r ↦
            (DirectSum.lmap
              (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J j d))
              (((DirectSum.decomposeLinearEquiv
                  (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) (v j)))
          e)
  rw [hcomponent, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [DirectSum.lmap_apply, free_cone_module_degree_single_coe, Pi.single_apply]
    simpa [DirectSum.decomposeLinearEquiv_apply]
  · intro j hj hji
    have hij : i ≠ j := by
      intro hij
      exact hji hij.symm
    simp [DirectSum.lmap_apply, free_cone_module_degree_single_coe, Pi.single_apply, hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Helper for Lemma 10.57.10: recomposing the coordinatewise free-module predecomposition
recovers the original vector. -/
private theorem free_cone_module_predecomposeLinear_left_inv {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) ∘ₗ
      free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J =
        LinearMap.id := by
  -- Route correction: rewrite the composite at the linear-map level first, so the final
  -- coordinate comparison only sees the finite sum of `Pi.single` vectors.
  apply LinearMap.ext
  intro v
  ext j
  calc
    (DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J)
        (free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v)) j =
      ∑ i : Fin r, (Pi.single i (v i)) j := by
        rw [free_cone_module_predecomposeLinear, LinearMap.sum_apply, map_sum, Finset.sum_apply]
        -- Each summand recomposes one coordinate decomposition back to the corresponding
        -- `Pi.single` vector.
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [LinearMap.comp_apply, LinearMap.proj_apply] using
          congrArg
            (fun f :
              (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₗ[R]
                (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =>
              (f (v i)) j)
            (free_cone_module_coordinate_recompose (R := R) (n := n) (r := r) J i)
    _ = v j := by
      simpa using
        congrArg (fun w : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) => w j)
          (LinearMap.sum_single_apply R (fun i : Fin r ↦ v i))

/-- Helper for Lemma 10.57.10: a degree-`d` cone quotient element has zero decomposition in every
other degree. This isolates the coordinatewise vanishing needed for the free-cone right inverse. -/
private theorem cone_quotient_decompose_eq_zero_of_mem_ne {n d e : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {x : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (hx : x ∈ cone_quotient_grading (R := R) (n := n) J d) (hed : e ≠ d) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) x e :
        cone_quotient_grading (R := R) (n := n) J e) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) = 0 := by
  -- Once the element is known to lie in degree `d`, every off-diagonal direct-sum component
  -- vanishes by the decomposition API.
  simpa using
    (DirectSum.decompose_of_mem_ne
      (cone_quotient_grading (R := R) (n := n) J) hx hed.symm)

/-- Helper for Lemma 10.57.10: a degree-`d` cone quotient element is recovered by its `d`-th
decomposition component. This isolates the matching-degree step for the free-cone right inverse. -/
private theorem cone_quotient_decompose_eq_self_of_mem {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {x : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (hx : x ∈ cone_quotient_grading (R := R) (n := n) J d) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) x d :
        cone_quotient_grading (R := R) (n := n) J d) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) = x := by
  -- The diagonal direct-sum component is exactly the original homogeneous element.
  simpa using
    (DirectSum.decompose_of_mem_same
      (cone_quotient_grading (R := R) (n := n) J) hx)

/-- Helper for Lemma 10.57.10: a homogeneous free-cone vector has each coordinate decomposition
concentrated in the same degree. -/
private theorem free_cone_module_coordinate_decompose_eq_ite {n r d e : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d) (i : Fin r) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) (v i) e :
        cone_quotient_grading (R := R) (n := n) J e) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) =
      if e = d then v i else 0 := by
  have hvi :
      v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
    (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
  by_cases hed : e = d
  · subst e
    -- In the matching degree, the decomposition is the original homogeneous coordinate.
    simpa using
      cone_quotient_decompose_eq_self_of_mem (R := R) (n := n) (d := d) J hvi
  · -- Outside the matching degree, the coordinate decomposition vanishes.
    simpa [hed] using
      cone_quotient_decompose_eq_zero_of_mem_ne
        (R := R) (n := n) (d := d) (e := e) J hvi hed

/-- Helper for Lemma 10.57.10: on a homogeneous free-cone vector, the coordinatewise
predecomposition is concentrated in the matching degree. -/
private theorem free_cone_module_predecompose_eq_lof_of_mem {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d) :
    free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v =
      DirectSum.lof R ℕ
        (fun e ↦ free_cone_module_grading (R := R) (n := n) (r := r) J e) d
        ⟨v, hv⟩ := by
  -- Compare degree components. The new component formula reduces the claim to the already-isolated
  -- statement that each coordinate decomposition is concentrated in degree `d`.
  apply DirectSum.ext
  intro e
  by_cases hed : e = d
  · subst e
    have hsame :
        ((DirectSum.lof R ℕ
            (fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d
            ⟨v, hv⟩) d :
            free_cone_module_grading (R := R) (n := n) (r := r) J d) = ⟨v, hv⟩ := by
      rw [DirectSum.lof_eq_of]
      simpa using DirectSum.of_eq_same
        (β := fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d ⟨v, hv⟩
    rw [hsame]
    apply Subtype.ext
    ext i
    have hvi :
        v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
      (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
    rw [free_cone_module_predecompose_component_eq_coordinate_decompose]
    exact cone_quotient_decompose_eq_self_of_mem (R := R) (n := n) (d := d) J hvi
  · have hzero :
        ((DirectSum.lof R ℕ
            (fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d
            ⟨v, hv⟩) e :
            free_cone_module_grading (R := R) (n := n) (r := r) J e) = 0 := by
      rw [DirectSum.lof_eq_of]
      exact DirectSum.of_eq_of_ne
        (β := fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d e ⟨v, hv⟩ hed
    rw [hzero]
    apply Subtype.ext
    ext i
    have hvi :
        v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
      (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
    rw [free_cone_module_predecompose_component_eq_coordinate_decompose]
    exact cone_quotient_decompose_eq_zero_of_mem_ne
      (R := R) (n := n) (d := d) (e := e) J hvi hed

/-- Helper for Lemma 10.57.10: the coordinatewise predecomposition sends each homogeneous
generator of the free cone module back to the matching direct-sum `lof`. -/
private theorem free_cone_module_predecomposeLinear_right_inv {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J ∘ₗ
      DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) =
        LinearMap.id := by
  -- A direct-sum map is determined by its values on the `lof` generators.
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  -- A homogeneous generator is sent back to the matching direct-sum basis vector.
  simpa [LinearMap.comp_apply, DirectSum.coeLinearMap_lof] using
    (free_cone_module_predecompose_eq_lof_of_mem
      (R := R) (n := n) (r := r) (d := d) J x.2)

/-- Helper for Lemma 10.57.10: package the missing coordinatewise direct-sum decomposition owner
for the graded free cone module on `Fin r`. -/
@[reducible] private noncomputable def free_cone_module_grading_decomposition {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J) :=
  DirectSum.Decomposition.ofLinearMap
    (ℳ := free_cone_module_grading (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear_left_inv
      (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear_right_inv
      (R := R) (n := n) (r := r) J)

/-- Helper for Lemma 10.57.10: coordinatewise multiplication by a homogeneous cone quotient class
preserves the free cone-module grading degree-by-degree. -/
private theorem free_cone_module_grading_mul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J j) :
    (fun k ↦ a * v k) ∈ free_cone_module_grading (R := R) (n := n) (r := r) J (i + j) := by
  -- Read membership coordinatewise: each entry stays homogeneous after multiplication by `a`.
  rw [mem_free_cone_module_grading_iff] at hv ⊢
  intro k
  exact SetLike.mul_mem_graded ha (hv k)

/-- Helper for Lemma 10.57.10: pointwise scalar multiplication by a homogeneous cone quotient
class raises the free cone-module degree by the same amount. -/
private theorem free_cone_module_grading_pointwise_smul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J j) :
    a • v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J (i + j) := by
  -- Read the pointwise scalar action coordinatewise and use graded multiplication in each entry.
  rw [mem_free_cone_module_grading_iff] at hv ⊢
  intro k
  simpa [Pi.smul_apply, smul_eq_mul] using SetLike.mul_mem_graded ha (hv k)

/-- Helper for Lemma 10.57.10: the coordinatewise free cone-module grading is a graded module over
the cone quotient grading. -/
private instance free_cone_module_grading_gradedSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SetLike.GradedSMul
      (cone_quotient_grading (R := R) (n := n) J)
      (free_cone_module_grading (R := R) (n := n) (r := r) J) where
  smul_mem := by
    intro i j a v ha hv
    exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J ha hv

/-- Helper for Lemma 10.57.10: homogenizing an affine relation vector to one common degree yields
a homogeneous vector in the free cone module. -/
private theorem homogenized_affine_relation_mem_free_cone_module_grading {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    (fun i ↦ Ideal.Quotient.mk J (coneHomogenizeTo (R := R) (n := n) d (k i))) ∈
      free_cone_module_grading (R := R) (n := n) (r := r) J d := by
  -- Each coordinate is the quotient class of a degree-`d` homogenized polynomial, so the whole
  -- vector lands in the coordinatewise degree-`d` piece.
  rw [mem_free_cone_module_grading_iff]
  intro i
  exact cone_quotient_mk_mem_grade_of_isHomogeneous
    (R := R) (n := n) (J := J)
    (coneHomogenizeTo_isHomogeneous (R := R) (n := n) d (k i))

/-- Helper for Lemma 10.57.10: the source relation vector is homogenized in the maximum total
degree of its affine coordinates so that all entries land in one graded piece. -/
private noncomputable def affine_relation_common_degree {n r : ℕ}
    (k : Fin r → MvPolynomial (Fin n) R) : ℕ :=
  Finset.sup Finset.univ fun i => (k i).totalDegree

/-- Helper for Lemma 10.57.10: every affine coordinate degree is bounded by the common
homogenization degree chosen for the whole relation vector. -/
private theorem totalDegree_le_affine_relation_common_degree {n r : ℕ}
    (k : Fin r → MvPolynomial (Fin n) R) (i : Fin r) :
    (k i).totalDegree ≤ affine_relation_common_degree (R := R) (n := n) (r := r) k := by
  -- The chosen common degree is the supremum of all coordinate total degrees.
  simpa [affine_relation_common_degree] using
    (Finset.le_sup (f := fun j : Fin r => (k j).totalDegree) (Finset.mem_univ i))

/-- Helper for Lemma 10.57.10: homogenize an affine relation vector coordinatewise in the common
source degree so that it can be inserted into the free cone module. -/
private noncomputable def homogenized_affine_relation {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  fun i =>
    Ideal.Quotient.mk J
      (coneHomogenizeTo (R := R) (n := n)
        (affine_relation_common_degree (R := R) (n := n) (r := r) k) (k i))

/-- Helper for Lemma 10.57.10: the coordinatewise homogenized affine relation vector lies in the
graded free cone module piece indexed by its common source degree. -/
private theorem homogenized_affine_relation_mem_common_degree {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    homogenized_affine_relation (R := R) (n := n) (r := r) J k ∈
      free_cone_module_grading (R := R) (n := n) (r := r) J
        (affine_relation_common_degree (R := R) (n := n) (r := r) k) := by
  -- This is the previous coordinatewise homogeneous-vector lemma specialized to the common degree.
  simpa [homogenized_affine_relation] using
    (homogenized_affine_relation_mem_free_cone_module_grading
      (R := R) (n := n) (r := r)
      (d := affine_relation_common_degree (R := R) (n := n) (r := r) k) J k)

/-- Helper for Lemma 10.57.10: the source module quotient is the span of the homogenized affine
kernel relations inside the free cone module. -/
private noncomputable def homogenized_relation_submodule {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    Submodule (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Submodule.span _ <|
    Set.range fun k : LinearMap.ker τ =>
      homogenized_affine_relation (R := R) (n := n) (r := r) J k.1

/-- Helper for Lemma 10.57.10: in a Nat-graded module, the span of homogeneous elements is a
homogeneous submodule. -/
private theorem span_isHomogeneous_of_isHomogeneousElem_nat
    {A : Type*} [Semiring A]
    {M' : Type*} [AddCommMonoid M'] [Module A M']
    (ℳ : ℕ → Submodule A M')
    [DirectSum.Decomposition ℳ]
    {t : Set M'} (ht : ∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) :
    (Submodule.span A t).IsHomogeneous ℳ := by
  intro i x hx
  -- Keep the target degree fixed and run span induction on the statement that its homogeneous
  -- projection already lies back in the span.
  refine Submodule.span_induction
    (p := fun y _ ↦ ((DirectSum.decompose ℳ y i : ℳ i) : M') ∈ Submodule.span A t) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases ht y hy with ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      simpa [DirectSum.decompose_of_mem_same ℳ hj] using
        (Submodule.subset_span hy : y ∈ Submodule.span A t)
    · simpa [DirectSum.decompose_of_mem_ne ℳ hj hji] using
        (Submodule.zero_mem (Submodule.span A t))
  · simpa using (Submodule.zero_mem (Submodule.span A t))
  · intro y z _ _ hy hz
    simpa [DirectSum.decompose_add] using
      (Submodule.add_mem (Submodule.span A t) hy hz)
  · intro a y _ hy
    simpa [map_smul] using
      (Submodule.smul_mem (Submodule.span A t) a hy)

/-- Helper for Lemma 10.57.10: if a homogeneous free-cone vector already lies in an `Scone`-span,
then every graded component of any pointwise scalar multiple still lies in that same span. -/
private theorem free_cone_module_decompose_sum_component_eval {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {α : Type*} (s : Finset α)
    (f : α → Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) (j : ℕ) :
    ((DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (Finset.sum s f) j :
        free_cone_module_grading (R := R) (n := n) (r := r) J j) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      Finset.sum s fun a =>
        ((DirectSum.decompose
            (free_cone_module_grading (R := R) (n := n) (r := r) J)
            (f a) j :
            free_cone_module_grading (R := R) (n := n) (r := r) J j) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := by
  -- Rewrite `DirectSum.decompose` across the finite sum and then read off the `j`-th coordinate.
  rw [DirectSum.decompose_sum]
  simpa using
    (DFinsupp.finset_sum_apply s
      (fun a ↦ DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (f a))
      j)

/-- Helper for Lemma 10.57.10: if a homogeneous free-cone vector already lies in an `Scone`-span,
then every graded component of any pointwise scalar multiple still lies in that same span. -/
private theorem free_cone_module_component_of_pointwise_smul_mem_span {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {t : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))}
    {x : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hx₁ : SetLike.IsHomogeneousElem
      (free_cone_module_grading (R := R) (n := n) (r := r) J) x)
    (hx₂ : x ∈ Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t)
    (a : MvPolynomial (Fin (n + 1)) R ⧸ J) (j : ℕ) :
    ((DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (a • x) j :
        free_cone_module_grading (R := R) (n := n) (r := r) J j) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ∈
      Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t := by
  classical
  rcases hx₁ with ⟨d, hx₁⟩
  let g : ℕ → Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) := fun i =>
    (((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
        cone_quotient_grading (R := R) (n := n) J i) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) • x)
  let u : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := Set.range g
  have hg_hom : ∀ i, SetLike.IsHomogeneousElem
      (free_cone_module_grading (R := R) (n := n) (r := r) J) (g i) := by
    intro i
    -- Each homogeneous scalar piece of `a` raises the degree of `x` by the same amount.
    refine ⟨i + d, ?_⟩
    exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := d) J
      ((DirectSum.decompose
          (cone_quotient_grading (R := R) (n := n) J) a i :
          cone_quotient_grading (R := R) (n := n) J i).2)
      hx₁
  have hu_hom :
      (Submodule.span R u).IsHomogeneous
        (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
    -- The auxiliary span is generated by homogeneous vectors, so every graded projection stays in
    -- that span.
    refine span_isHomogeneous_of_isHomogeneousElem_nat
      (A := R)
      (ℳ := free_cone_module_grading (R := R) (n := n) (r := r) J)
      (t := u) ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact hg_hom i
  have hu_le :
      (Submodule.span R u) ≤
        (Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t).restrictScalars R := by
    -- Every generator of the auxiliary span already lies in the original `Scone`-span.
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ hx₂
  have hax :
      a • x ∈ Submodule.span R u := by
    -- Decompose `a` into homogeneous scalar pieces and expand the scalar action through the finite
    -- support decomposition.
    let s : Finset ℕ :=
      (DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a).support
    have hsum :
        ((∑ i ∈ s,
            ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
                cone_quotient_grading (R := R) (n := n) J i) :
              MvPolynomial (Fin (n + 1)) R ⧸ J)) : MvPolynomial (Fin (n + 1)) R ⧸ J) = a := by
      simpa [s] using
        (DirectSum.sum_support_decompose (cone_quotient_grading (R := R) (n := n) J) a)
    have hs :
        a • x = ∑ i ∈ s, g i := by
      calc
        a • x =
            ((∑ i ∈ s,
              ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
                  cone_quotient_grading (R := R) (n := n) J i) :
                  MvPolynomial (Fin (n + 1)) R ⧸ J)) : _) • x := by
          rw [hsum]
        _ = ∑ i ∈ s, g i := by
          simp [g, Finset.sum_smul]
    rw [hs]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hgi : g i ∈ u := ⟨i, rfl⟩
    exact Submodule.subset_span hgi
  -- The target component belongs to the auxiliary homogeneous span, hence to the original span.
  exact hu_le (hu_hom j hax)

/-- Helper for Lemma 10.57.10: an `Scone`-span generated by homogeneous free-cone vectors remains
homogeneous after restricting scalars back to `R`. -/
private theorem free_cone_module_span_restrictScalars_is_homogeneous {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {t : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))}
    (ht : ∀ x ∈ t,
      SetLike.IsHomogeneousElem
        (free_cone_module_grading (R := R) (n := n) (r := r) J) x) :
    ((Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t).restrictScalars R).IsHomogeneous
      (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
  admit

/-- Helper for Lemma 10.57.10: once the coordinatewise free-module grading owners are fixed, the
span of the homogenized affine relation vectors is the homogeneous relation submodule from the
source proof. -/
private theorem homogenized_relation_submodule_is_homogeneous {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    ((homogenized_relation_submodule (R := R) (n := n) (r := r) J τ).restrictScalars R).IsHomogeneous
      (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
  classical
  -- The relation submodule is generated by homogeneous homogenized kernel vectors.
  simpa [homogenized_relation_submodule] using
    (free_cone_module_span_restrictScalars_is_homogeneous
      (R := R) (n := n) (r := r) J
      (t := Set.range fun k : LinearMap.ker τ =>
        homogenized_affine_relation (R := R) (n := n) (r := r) J k.1)
      (fun x hx => by
        rcases hx with ⟨k, rfl⟩
        exact ⟨affine_relation_common_degree (R := R) (n := n) (r := r) k.1,
          homogenized_affine_relation_mem_common_degree
            (R := R) (n := n) (r := r) J k.1⟩))

/-- Helper for Lemma 10.57.10: restrict the quotient map to the homogenized relation cokernel
along `R`, so the quotient grading can be expressed as an `R`-graded family. -/
private noncomputable def homogenized_relation_quotient_mkQ {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[R]
      ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) :=
  (((Submodule.mkQ (homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)) :
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[(MvPolynomial (Fin (n + 1)) R ⧸ J)]
        ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)).restrictScalars R)

/-- Helper for Lemma 10.57.10: the homogenized relation cokernel inherits its degree-`d` piece by
mapping the free cone-module degree-`d` part through the quotient map. -/
private noncomputable def homogenized_relation_quotient_grading {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (d : ℕ) :
    Submodule R
      ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) :=
  (free_cone_module_grading (R := R) (n := n) (r := r) J d).map
    (homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ)

/-- Helper for Lemma 10.57.10: membership in the quotient grading means that the class has a
homogeneous lift in the free cone module of the same degree. -/
private theorem mem_homogenized_relation_quotient_grading_iff {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    {x : ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
      homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)} :
    x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ d ↔
      ∃ y ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d,
        homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ y = x := by
  -- Unfold the quotient piece: it is literally the image of the homogeneous free piece.
  rfl

/-- Helper for Lemma 10.57.10: multiplying a homogeneous quotient class in the ring with a
homogeneous quotient class in the module preserves the expected total degree after passing to the
cokernel. -/
private theorem homogenized_relation_quotient_grading_smul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {x : ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
      homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hx : x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ j) :
    a • x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ (i + j) := by
  -- Lift the quotient class to a homogeneous free-cone vector, multiply upstairs, and descend the
  -- result back through the quotient map.
  rcases (mem_homogenized_relation_quotient_grading_iff
      (R := R) (n := n) (r := r) (d := j) J τ).1 hx with ⟨y, hy, rfl⟩
  refine (mem_homogenized_relation_quotient_grading_iff
      (R := R) (n := n) (r := r) (d := i + j) J τ).2 ?_
  refine ⟨a • y, ?_, ?_⟩
  · exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J ha hy
  · -- The quotient map is still `S`-linear before restricting scalars back to `R`.
    change homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ (a • y) =
      a • homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ y
    simp [homogenized_relation_quotient_mkQ]

/-- Helper for Lemma 10.57.10: the quotient grading on the homogenized relation cokernel is a
graded module over the shifted cone quotient ring. -/
private instance homogenized_relation_quotient_grading_gradedSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    SetLike.GradedSMul
      (cone_quotient_grading (R := R) (n := n) J)
      (homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ) where
  smul_mem := by
    intro i j a x ha hx
    exact homogenized_relation_quotient_grading_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J τ ha hx

/-- Helper for Lemma 10.57.10: the finite free cone module on `Fin r` is finite over the cone
quotient ring. This records the finite-basis witness explicitly, avoiding fragile instance
search in the cokernel step. -/
private theorem moduleFinite_free_cone_module {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
    let _ : Module Scone Scone := Semiring.toModule
    let _ : Module Scone (Fin r → Scone) :=
      Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
    Module.Finite Scone (Fin r → Scone) := by
  -- The standard basis on `Fin r → Scone` already gives the finite free presentation needed here.
  let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
  letI : Module Scone Scone := Semiring.toModule
  letI : Module Scone (Fin r → Scone) :=
    Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
  exact (show Module.Finite Scone (Fin r → Scone) from
    Module.Finite.of_basis (Pi.basisFun Scone (Fin r)))

/-- Helper for Lemma 10.57.10: once the homogenized relation span is fixed, the source cokernel
candidate is automatically finite because it is a quotient of a finite free cone module. -/
private theorem moduleFinite_homogenized_relation_quotient {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
    let _ : Module Scone Scone := Semiring.toModule
    let _ : Module Scone (Fin r → Scone) :=
      Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
    Module.Finite Scone
      ((Fin r → Scone) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) := by
  let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
  letI : Module Scone Scone := Semiring.toModule
  letI : Module Scone (Fin r → Scone) :=
    Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
  let _ :
      Module.Finite Scone (Fin r → Scone) := by
    -- Use the explicit finite-basis witness to keep this step stable under elaboration changes.
    simpa [Scone] using moduleFinite_free_cone_module (R := R) (n := n) (r := r) J
  -- The source cokernel is a quotient of that finite free module via the canonical quotient map.
  exact (show
      Module.Finite Scone
        ((Fin r → Scone) ⧸ homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) from
    Module.Finite.of_surjective
      (Submodule.mkQ (homogenized_relation_submodule (R := R) (n := n) (r := r) J τ))
      (Submodule.mkQ_surjective _))

/-- Helper for Lemma 10.57.10: the quotient class of the cone variable `X 0` is degree `1` in the
shifted cone quotient, so it can serve as the source denominator in the homogeneous chart. -/
private theorem shifted_cone_denominator_mem_grade_one {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal.Quotient.mk
        (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
        (MvPolynomial.X (0 : Fin (n + 1))) ∈
      cone_quotient_grading (R := R) (n := n)
        (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) 1 := by
  -- The denominator variable is itself homogeneous of degree `1`.
  exact cone_quotient_mk_mem_grade_of_isHomogeneous
    (R := R) (n := n)
    (J := positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
    (MvPolynomial.isHomogeneous_X (R := R) (0 : Fin (n + 1)))

/-- Helper for Lemma 10.57.10: the shifted cone quotient inherits the canonical graded-algebra
structure from the homogeneous cone ideal. This keeps the dehomogenization chart statements short
and avoids repeating the quotient-grading owner package. -/
@[reducible] private noncomputable instance shifted_cone_gradedAlgebra {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    GradedAlgebra
      (cone_quotient_grading (R := R) (n := n)
        (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)) :=
  cone_quotient_gradedAlgebra_of_homogeneous_ideal
    (R := R) (n := n)
    (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
    (positively_shifted_cone_homogenized_ideal_isHomogeneous (R := R) (n := n) I)

/-- Helper for Lemma 10.57.10: the distinguished degree-one denominator in the shifted cone
quotient. Writing it as a reusable abbreviation keeps the remaining ring-chart statements small and
elaboration-stable. -/
private noncomputable abbrev shifted_cone_denominator {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    cone_quotient_grading (R := R) (n := n)
      (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) 1 :=
  ⟨Ideal.Quotient.mk
      (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
      (MvPolynomial.X (0 : Fin (n + 1))),
    shifted_cone_denominator_mem_grade_one (R := R) (n := n) I⟩


/-- Lemma 10.57.10: if `R'` is a finite type `R`-algebra and `M` is a finite `R'`-module, then
there exist a graded `R`-algebra `S`, a graded `S`-module `N`, and a degree-one homogeneous
element `f` such that `R'` is `R`-algebra isomorphic to `S_(f)`, `M` is semilinearly equivalent
to `N_(f)` over this algebra isomorphism, `R ≃ₐ[R] S₀`, `S` is generated in degree `1` over
`S₀`, `S` is of finite type over `S₀`, and `N` is finite over `S`. The explicit finite set of
degree-one generators from the source is kept below as a companion consequence, while the main
theorem records the chapter-owner finite-type condition `Algebra.FiniteType (S₀) S`. This is the
degree-zero-piece form of the source conditions `S₀ = R` and “`S` is generated over `R` by
finitely many degree-one elements”. -/
@[stacks 052N]
-- Proof sketch: choose finitely many generators of the finite type algebra `R'`, homogenize the
-- defining ideal inside a polynomial ring with one extra variable of degree `1`, and then
-- homogenize a finite presentation of `M` to obtain a finite graded `S`-module whose localization
-- away from the extra variable recovers `M`.
theorem exists_graded_localization_model_of_finite_module
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ (S : Type _) (_ : CommRing S) (_ : Algebra R S)
      (grading : ℕ → Submodule R S) (_ : GradedAlgebra grading)
      (N : Type _) (_ : AddCommGroup N) (_ : Module S N)
      (_ : Module R N) (_ : IsScalarTower R S N)
      (gradingN : ℕ → Submodule R N) (_ : DirectSum.Decomposition gradingN)
      (_ : SetLike.GradedSMul grading gradingN) (f : grading 1),
          ∃ zeroIso : R ≃ₐ[R] grading 0,
          ∃ ringIso : R' ≃ₐ[R] Away grading (f : S),
          ∃ moduleIso :
              M ≃ₛₗ[(ringIso.toRingEquiv : R' →+* Away grading (f : S))]
                awayDegreeZeroPart grading gradingN f,
            IsDegreeOneGeneratedFiniteTypeModel grading N :=
  by
    classical
    -- Start from the verified affine polynomial presentation `R' = P / I`.
    obtain ⟨n, π, hπ⟩ := exists_surjective_mvPolynomial_presentation (R := R) (R' := R')
    let P : Type u := MvPolynomial (Fin n) R
    let I : Ideal P := RingHom.ker π
    let Q : Type u := P ⧸ I
    let eQ : Q ≃ₐ[R] R' := mvPolynomial_quotient_equiv_of_surjective (R := R) π hπ
    let _ : Algebra Q R' := eQ.toRingHom.toAlgebra
    let _ : Module Q M := Module.compHom M (algebraMap Q R')
    let _ : IsScalarTower Q R' M := by
      refine ⟨?_⟩
      intro a b m
      change (((algebraMap Q R') a) * b) • m = ((algebraMap Q R') a) • (b • m)
      exact mul_smul _ _ _
    let _ : Module.Finite Q M := by
      -- The quotient algebra `Q` surjects onto `R'`, so finite generation over `R'` restricts to
      -- finite generation over `Q`.
      refine ⟨by simpa using
        (Submodule.FG.restrictScalars_of_surjective
          (R := Q) (A := R') (M := M) (S := (⊤ : Submodule R' M))
          (Module.Finite.fg_top (R := R') (M := M)) eQ.surjective)⟩
    let _ : Module P M := Module.compHom M (Ideal.Quotient.mkₐ R I).toRingHom
    let _ : IsScalarTower P Q M := by
      refine ⟨?_⟩
      intro a b m
      change (((algebraMap P Q) a) * b) • m = ((algebraMap P Q) a) • (b • m)
      exact mul_smul _ _ _
    let _ : Module.Finite P M := Module.Finite.trans Q M
    -- Use the finite free affine presentation that will later be homogenized.
    obtain ⟨r, τ, hτ⟩ :=
      exists_surjective_affine_free_module_presentation (R := R) (R' := R') (M := M)
        (n := n) π
    -- Build the source-faithful cone quotient ring and the homogenized relation quotient module.
    let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
      positively_shifted_cone_homogenized_ideal (R := R) (n := n) I
    let S : Type _ := MvPolynomial (Fin (n + 1)) R ⧸ J
    let grading : ℕ → Submodule R S := cone_quotient_grading (R := R) (n := n) J
    let _ : CommRing S := inferInstance
    let _ : Algebra R S := inferInstance
    let _ : GradedAlgebra grading := shifted_cone_gradedAlgebra (R := R) (n := n) I
    let K :
        Submodule S (Fin r → S) :=
      homogenized_relation_submodule (R := R) (n := n) (r := r) J τ
    let N : Type _ := (Fin r → S) ⧸ K
    let _ : AddCommGroup N := inferInstance
    let _ : Module S N := inferInstance
    let _ : Module R N := inferInstance
    let _ : IsScalarTower R S N := inferInstance
    let gradingN : ℕ → Submodule R N :=
      homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ
    let _ : SetLike.GradedSMul grading gradingN :=
      homogenized_relation_quotient_grading_gradedSMul (R := R) (n := n) (r := r) J τ
    let _ : Module.Finite S N := by
      -- The homogenized cokernel is finite because it is a quotient of a finite free cone module.
      simpa [N, K, S, J] using
        (moduleFinite_homogenized_relation_quotient
          (R := R) (n := n) (r := r) (M := M) J τ)
    let f : grading 1 := shifted_cone_denominator (R := R) (n := n) I
    let zeroIso : R ≃ₐ[R] grading 0 :=
      cone_quotient_grade_zero_algEquiv (R := R) (n := n) J
        (fun a ha =>
          eq_zero_of_C_mem_positively_shifted_cone_homogenized_ideal
            (R := R) (n := n) (I := I) ha)
    let s : Finset S :=
      Finset.univ.image fun i : Fin (n + 1) =>
        Ideal.Quotient.mk J (MvPolynomial.X i)
    have hs_top : Algebra.adjoin (grading 0) (s : Set S) = ⊤ := by
      -- The cone variables already generate the whole quotient ring over its degree-zero part.
      simpa [s] using
        (cone_quotient_degree_one_generators_adjoin_top (R := R) (n := n) J)
    have hs_deg : ∀ x ∈ s, x ∈ grading 1 := by
      -- Each quotient cone variable is itself homogeneous of degree `1`.
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact cone_quotient_X_mem_grade_one (R := R) (n := n) J i
    have hmodel : IsDegreeOneGeneratedFiniteTypeModel grading N := by
      -- The finite family of cone variables packages the source conclusion that `S` is generated
      -- in degree `1`, while the homogenized cokernel is already finite over `S`.
      exact isDegreeOneGeneratedFiniteTypeModel_of_finset
        (R := R) grading N s hs_top hs_deg
    -- TODO: the remaining source-faithful blocker is exactly the localization comparison.
    -- The ring side still needs the affine chart `Away grading f ≃ (P ⧸ I)`, and the module side
    -- still needs the localized homogenized cokernel identified with `M` through a compatible
    -- graded quotient-module structure on `N`.
    admit

/-- A degree-one generated finite type graded ring admits a finite set of degree-one generators. -/
-- Proof sketch: choose finitely many algebra generators of `S` over `grading 0`, write each one
-- using the degree-one generating hypothesis, and collect the finitely many homogeneous degree-one
-- elements appearing in those expressions into a single finite generating set.
theorem exists_finset_degreeOne_generators_of_model
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N]
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel grading N) :
    ∃ s : Finset S,
      Algebra.adjoin (grading 0) (s : Set S) = ⊤ ∧
        ∀ x ∈ s, x ∈ grading 1 := by
  classical
  let _ : Algebra.FiniteType (grading 0) S := hmodel.finiteType
  -- Start from a finite algebra generating family, then shrink each generator to a finite family
  -- of degree-one elements using `Algebra.adjoin (grading 0) (grading 1) = ⊤`.
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := grading 0) (A := S)
  choose u hu_subset hu_mem using fun x : t ↦
    exists_finset_subset_of_mem_adjoin
      (R := grading 0)
      (s := (grading 1 : Set S))
      (x := x.1)
      (by
        have hx_top : x.1 ∈ (⊤ : Subalgebra (grading 0) S) := by simp
        simpa [hmodel.degreeOne_adjoin_eq_top] using hx_top)
  let s : Finset S := t.attach.biUnion u
  refine ⟨s, ?_, ?_⟩
  · -- The original finite generators are contained in the adjoin of the collected degree-one set.
    have hs :
        Algebra.adjoin (grading 0) (s : Set S) =
          ⨆ x : t, Algebra.adjoin (grading 0) (u x : Set S) := by
      simpa [s] using Algebra.adjoin_attach_biUnion (R := grading 0) (s := t) u
    have ht_le : Algebra.adjoin (grading 0) (t : Set S) ≤ Algebra.adjoin (grading 0) (s : Set S) := by
      rw [hs]
      refine Algebra.adjoin_le_iff.mpr ?_
      intro x hx
      let xt : t := ⟨x, hx⟩
      exact (le_iSup (fun y : t => Algebra.adjoin (grading 0) (u y : Set S)) xt) (hu_mem xt)
    rw [← top_le_iff]
    intro x hx
    exact ht_le (by simpa [ht] using hx)
  · -- Every collected generator was chosen from the degree-one piece.
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, -, hxy⟩
    exact hu_subset y x hxy

end
