import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import StacksProject_2024.Chap10.Lemma_10_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.36.2: the hypothesis `yM ⊆ M` says that `M` is invariant under the
left-multiplication endomorphism by `y`. -/
lemma stable_under_mul_mem_invtSubmodule {y : S} {M : Submodule R S}
    (hy : ∀ m ∈ M, y * m ∈ M) :
    M ∈ (Algebra.lsmul R R S y).invtSubmodule := by
  -- Rewrite the stability hypothesis into the standard invariant-submodule API.
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro m hm
  simpa [Algebra.smul_def] using hy m hm

/-- Helper for Lemma 10.36.2: iterating left multiplication by `y` and then applying to `1`
produces the powers of `y`. -/
lemma lsmul_pow_apply_one (y : S) :
    ∀ n : ℕ, ((Algebra.lsmul R R S y : Module.End R S) ^ n) (1 : S) = y ^ n := by
  intro n
  induction n with
  | zero =>
      -- The zeroth iterate is the identity endomorphism.
      simp
  | succ n ih =>
      -- One more iterate multiplies the previous value by `y`.
      calc
        ((Algebra.lsmul R R S y : Module.End R S) ^ (n + 1)) (1 : S)
            = (Algebra.lsmul R R S y) (((Algebra.lsmul R R S y : Module.End R S) ^ n) (1 : S)) := by
                rw [pow_succ', Module.End.mul_apply]
        _ = y * y ^ n := by
              simpa [Algebra.smul_def] using congrArg (fun z : S ↦ y * z) ih
        _ = y ^ (n + 1) := by
              rw [pow_succ']

/-- Helper for Lemma 10.36.2: evaluating the annihilating polynomial of the restricted
left-multiplication endomorphism at the distinguished element `1 ∈ M` recovers `P(y)` in `S`. -/
lemma aeval_restrict_lsmul_apply_one {y : S} {M : Submodule R S}
    (h1 : (1 : S) ∈ M) (hy : ∀ m ∈ M, y * m ∈ M) (P : Polynomial R) :
    ↑((Polynomial.aeval
        ((Algebra.lsmul R R S y).restrict
          ((Algebra.lsmul R R S y).mem_invtSubmodule_iff_forall_mem_of_mem.mp
            (stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy))) P)
      (⟨1, h1⟩ : M)) =
      Polynomial.aeval y P := by
  let f : Module.End R S := Algebra.lsmul R R S y
  have hstable_invt : M ∈ f.invtSubmodule :=
    stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy
  have hstable : ∀ m ∈ M, f m ∈ M :=
    f.mem_invtSubmodule_iff_forall_mem_of_mem.mp hstable_invt
  let φ : Module.End R M := f.restrict hstable
  let oneM : M := ⟨1, h1⟩
  have hpow_restrict : ∀ n : ℕ, ↑(((f.restrict hstable) ^ n) oneM) = y ^ n := by
    intro n
    -- Replace the restricted iterate by the ambient iterate before evaluating at `1`.
    have hpow_eq :
        (f.restrict hstable) ^ n =
          (f ^ n).restrict (Module.End.pow_apply_mem_of_forall_mem (f' := f) n hstable) := by
      simpa using (Module.End.pow_restrict (f' := f) n hstable)
    calc
      ↑(((f.restrict hstable) ^ n) oneM)
          = ↑(((f ^ n).restrict (Module.End.pow_apply_mem_of_forall_mem (f' := f) n hstable))
              oneM) := by
                rw [hpow_eq]
      _ = (f ^ n) (1 : S) := by
            simp [oneM, LinearMap.restrict_apply]
      _ = y ^ n := by
            simpa [f] using lsmul_pow_apply_one (R := R) (S := S) y n
  -- Compare polynomial evaluation term-by-term on additive generators.
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    -- The claim is additive in the polynomial.
    calc
      ↑((Polynomial.aeval φ (P + Q)) oneM)
          = ↑((Polynomial.aeval φ P) oneM) + ↑((Polynomial.aeval φ Q) oneM) := by
              simp [Polynomial.aeval_add]
      _ = Polynomial.aeval y P + Polynomial.aeval y Q := by
            rw [hP, hQ]
      _ = Polynomial.aeval y (P + Q) := by
            rw [Polynomial.aeval_add]
  · intro n a
    -- On a monomial, the restricted action on `1` is exactly scalar times `y ^ n`.
    calc
      ↑((Polynomial.aeval φ (Polynomial.monomial n a)) oneM)
          = ↑(((algebraMap R (Module.End R M) a * φ ^ n) oneM)) := by
              rw [Polynomial.aeval_monomial]
      _ = (algebraMap R S) a * y ^ n := by
            simp [Module.End.mul_apply, φ, hpow_restrict n, Algebra.smul_def]
      _ = Polynomial.aeval y (Polynomial.monomial n a) := by
            rw [Polynomial.aeval_monomial]

/-- Owner-form criterion for Lemma 10.36.2: if a finitely generated `R`-submodule `M` of `S`
contains `1` and is stable under multiplication by `y`, then `y` is integral over `R`. -/
theorem isIntegral_of_stable_fg_submodule {y : S} {M : Submodule R S}
    (hfg : M.FG) (h1 : (1 : S) ∈ M) (hy : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  haveI : Module.Finite R M := Module.Finite.of_fg hfg
  have hstable_invt : M ∈ (Algebra.lsmul R R S y).invtSubmodule :=
    stable_under_mul_mem_invtSubmodule (R := R) (S := S) hy
  have hstable : ∀ m ∈ M, (Algebra.lsmul R R S y) m ∈ M :=
    (Algebra.lsmul R R S y).mem_invtSubmodule_iff_forall_mem_of_mem.mp hstable_invt
  let φ : Module.End R M := (Algebra.lsmul R R S y).restrict hstable
  let oneM : M := ⟨1, h1⟩
  -- Apply finite-module Cayley-Hamilton to the restricted left-multiplication map.
  obtain ⟨P, hmonic, hP⟩ := LinearMap.exists_monic_and_aeval_eq_zero R φ
  have hP_apply : (Polynomial.aeval φ P) oneM = 0 := by
    -- Evaluate the annihilating endomorphism at the element represented by `1`.
    simpa [hP] using congrArg (fun f : Module.End R M ↦ f oneM) hP
  have hP_apply_coe : ↑((Polynomial.aeval φ P) oneM) = (0 : S) := by
    simpa using congrArg Subtype.val hP_apply
  have hP_y : Polynomial.aeval y P = 0 := by
    -- The restricted polynomial identity at `1` is exactly the polynomial identity for `y`.
    calc
      Polynomial.aeval y P = ↑((Polynomial.aeval φ P) oneM) := by
        symm
        exact aeval_restrict_lsmul_apply_one (R := R) (S := S) (M := M) h1 hy P
      _ = 0 := hP_apply_coe
  exact ⟨P, hmonic, by simpa [Polynomial.aeval_def] using hP_y⟩

/-- Lemma 10.36.2: if there exists a finitely generated `R`-submodule `M` of `S` containing `1`
and stable under multiplication by `y`, then `y` is integral over `R`. This is the thin
source-facing corollary of `isIntegral_of_stable_fg_submodule`. -/
theorem isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem {y : S}
    (hM : ∃ M : Submodule R S, M.FG ∧ (1 : S) ∈ M ∧ ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  rcases hM with ⟨M, hfg, h1, hy⟩
  -- Unpack the witness submodule and invoke the owner-form criterion.
  exact isIntegral_of_stable_fg_submodule hfg h1 hy

end
