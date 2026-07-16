import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_55_1
import stacks_proof.stacks_project.Chap10.Lemma_10_58_4
import stacks_proof.stacks_project.Chap10.Definition_10_58_3
import stacks_proof.stacks_project.Chap10.Lemma_10_58_5
import stacks_proof.stacks_project.Chap10.Example_10_58_9
import stacks_proof.stacks_project.Chap10.Lemma_10_58_10.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open HomogeneousIdeal
open scoped BigOperators DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

/-- Helper for Lemma 10.58.10: the standard nonnegative grading shifts integer degrees by
addition. -/
local instance natVAddInt : AddAction ℕ ℤ where
  vadd n z := (n : ℤ) + z
  zero_vadd := by
    intro z
    change ((0 : ℕ) : ℤ) + z = z
    simp
  add_vadd := by
    intro m n z
    change (((m + n : ℕ) : ℤ) + z) = ((m : ℤ) + ((n : ℤ) + z))
    simp [Nat.cast_add, add_assoc]

noncomputable section

universe u

section

variable {k : Type u} [Field k] {d : ℕ}
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))

local notation "S" => MvPolynomial (Fin d) k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin d) k

/-- Helper for Lemma 10.58.10: eventual equality preserves numerical polynomiality. -/
private theorem IsNumericalPolynomial.congr
    {f g : ℤ → ℤ} (hg : IsNumericalPolynomial g) (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial f := by
  rcases hg with ⟨r, a, ha⟩
  exact ⟨r, a, hfg.trans ha⟩

/-- Helper for Chap10 Lemma 10 58 10: pulling back a module action along a ring map that
respects the base algebra maps produces the expected scalar tower. -/
private theorem isScalarTowerCompHomOfAlgebraMapEq
    {A : Type*} {B : Type*} {C : Type*} {N : Type*}
    [CommSemiring A] [Semiring B] [Semiring C] [Algebra A B] [Algebra A C]
    [AddCommMonoid N] [Module A N] [Module C N] [IsScalarTower A C N]
    (f : B →+* C) (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A C a) :
    letI : Module B N := Module.compHom N f
    IsScalarTower A B N := by
  letI : Module B N := Module.compHom N f
  -- Proof comment: once the pulled-back `B`-action is unfolded, the scalar-tower identity is
  -- exactly the compatibility of `f` with the two algebra maps out of `A`.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a n
  change f (algebraMap A B a) • n = a • n
  rw [hf a, algebraMap_smul C a n]

/-- Helper for Lemma 10.58.10: the degree-`n` exponent vectors in `d` variables are exactly the
elements of the natural `finsuppAntidiag`. -/
private noncomputable def degree_exponent_subtype_equiv_finsuppAntidiag (d n : ℕ) :
    {e : Fin d →₀ ℕ // e.degree = n} ≃
      ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n) where
  toFun e := by
    refine ⟨e.1, ?_⟩
    -- Rewrite the total degree as the univ-sum used by `finsuppAntidiag`.
    refine Finset.mem_finsuppAntidiag'.2 ?_
    refine ⟨?_, by simp⟩
    simpa [Finsupp.degree] using e.2
  invFun e := by
    refine ⟨e.1, ?_⟩
    -- Membership in the antidiagonal records exactly the total-degree condition.
    simpa [Finsupp.degree] using
      (Finset.mem_finsuppAntidiag'.1 e.2).1
  left_inv e := by
    rfl
  right_inv e := by
    rfl

/-- Helper for Lemma 10.58.10: the degree-`n` `finsuppAntidiag` over `Fin d` has cardinality
`d.multichoose n`. -/
private theorem degree_finsuppAntidiag_card_eq_multichoose (d n : ℕ) :
    Fintype.card ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n) = d.multichoose n := by
  simpa [Fintype.card_coe] using
    (Finset.card_finsuppAntidiag_nat_eq_multichoose
      (s := (Finset.univ : Finset (Fin d))) n)

/-- Helper for Lemma 10.58.10: the degree-`n` homogeneous piece of the ambient polynomial ring has
dimension `d.multichoose n`. -/
private theorem ambient_degree_piece_finrank_eq_multichoose (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) = d.multichoose n := by
  classical
  let _ : Fintype {m : Fin d →₀ ℕ // m.degree = n} :=
    Fintype.ofEquiv ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n)
      (degree_exponent_subtype_equiv_finsuppAntidiag d n).symm
  -- Identify the homogeneous piece with finitely supported coefficient functions on degree-`n`
  -- exponent vectors, then count those vectors by `multichoose`.
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let e :
      Finsupp.supported k k {m : Fin d →₀ ℕ | m.degree = n} ≃ₗ[k]
        {m : Fin d →₀ ℕ // m.degree = n} →₀ k :=
    Finsupp.supportedEquivFinsupp (M := k) (R := k) {m : Fin d →₀ ℕ | m.degree = n}
  calc
    Module.finrank k (Finsupp.supported k k {m : Fin d →₀ ℕ | m.degree = n}) =
        Module.finrank k ({m : Fin d →₀ ℕ // m.degree = n} →₀ k) := by
          exact LinearEquiv.finrank_eq e
    _ = Fintype.card {m : Fin d →₀ ℕ // m.degree = n} := by
          simpa using (Module.finrank_finsupp_self (R := k) (ι := {m : Fin d →₀ ℕ // m.degree = n}))
    _ = Fintype.card ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n) := by
          exact Fintype.card_congr (degree_exponent_subtype_equiv_finsuppAntidiag d n)
    _ = d.multichoose n := degree_finsuppAntidiag_card_eq_multichoose d n

/-- Helper for Lemma 10.58.10: the ambient Hilbert function of `k[X₁, …, X_d]`, with the source's
convention that negative degrees are zero. -/
private def ambientHilbertFunction (d : ℕ) : ℤ → ℤ :=
  fun n ↦ if 0 ≤ n then (d.multichoose n.toNat : ℤ) else 0

/-- Helper for Lemma 10.58.10: the forward difference of the ambient Hilbert function in `d + 1`
variables is the ambient Hilbert function in `d` variables. -/
private theorem ambientHilbertFunction_sub_pred (d : ℕ) :
    ∀ᶠ n : ℤ in atTop,
      ambientHilbertFunction (d + 1) n - ambientHilbertFunction (d + 1) (n - 1) =
        ambientHilbertFunction d n := by
  filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn
  have hpos : 0 < n := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hn1 : 0 ≤ n - 1 := by linarith
  have hpred_toNat : (n - 1).toNat = n.toNat - 1 := by
    have hn1_toInt : ((n - 1).toNat : ℤ) = n - 1 := Int.toNat_of_nonneg hn1
    have hpred_cast : ((n.toNat - 1 : ℕ) : ℤ) = n - 1 := by
      simpa using (Int.toNat_pred_coe_of_pos hpos)
    symm
    exact_mod_cast (hpred_cast.trans hn1_toInt.symm)
  have hnat_ge_one : 1 ≤ n.toNat := by
    have hn_toInt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    omega
  have htoNat : n.toNat = (n - 1).toNat + 1 := by
    rw [hpred_toNat]
    omega
  have hrec_nat :
      (d + 1).multichoose n.toNat =
        d.multichoose n.toNat + (d + 1).multichoose (n - 1).toNat := by
    rw [htoNat, Nat.multichoose_succ_succ]
  have hrec_int :
      ((d + 1).multichoose n.toNat : ℤ) =
        (d.multichoose n.toNat : ℤ) + ((d + 1).multichoose (n - 1).toNat : ℤ) := by
    exact_mod_cast hrec_nat
  -- Once both sides are rewritten in nonnegative degrees, the multichoose recursion is the claim.
  rw [ambientHilbertFunction, if_pos hn0, ambientHilbertFunction, if_pos hn1, ambientHilbertFunction,
    if_pos hn0, hpred_toNat]
  apply sub_eq_iff_eq_add.mpr
  simpa [hpred_toNat, add_comm, add_left_comm, add_assoc] using hrec_int

/-- Helper for Lemma 10.58.10: the ambient Hilbert function is a numerical polynomial. -/
private theorem ambientHilbertFunction_isNumericalPolynomial :
    ∀ d : ℕ, IsNumericalPolynomial (ambientHilbertFunction d)
  | 0 => by
      refine ⟨0, fun _ ↦ 0, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn
      have hn0 : 0 ≤ n := by linarith
      have hnat_ge_one : 1 ≤ n.toNat := by
        have hn_toInt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
        omega
      have hnat_ne_zero : n.toNat ≠ 0 := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnat_ne_zero
      simp [ambientHilbertFunction, hn0, hm, Nat.multichoose_zero_succ]
  | d + 1 => by
      have hpred :
          IsNumericalPolynomial
            (fun n ↦ ambientHilbertFunction (d + 1) n - ambientHilbertFunction (d + 1) (n - 1)) := by
        exact
          IsNumericalPolynomial.congr
            (ambientHilbertFunction_isNumericalPolynomial d)
            (ambientHilbertFunction_sub_pred d)
      -- Antidifferentiate the multichoose recursion using the earlier numerical-polynomial API.
      exact IsNumericalPolynomial.of_sub_pred hpred

/-- The image in `k[X₁, …, X_d] ⧸ I` of the homogeneous degree-`n` piece of the standard graded
polynomial ring. -/
private def homogeneousIdealQuotientDegreePiece (n : ℕ) :
    Submodule k (S ⧸ I.toIdeal) :=
  (MvPolynomial.homogeneousSubmodule (Fin d) k n).map (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap

/-- Helper for Lemma 10.58.10: the degree-`n` part `I ∩ Sₙ` of a homogeneous ideal inside the
ambient degree piece. -/
private def homogeneousIdealDegreePiece (n : ℕ) :
    Submodule k (MvPolynomial.homogeneousSubmodule (Fin d) k n) :=
  Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin d) k n).subtype
    (I.toIdeal.restrictScalars k)

/-- Helper for Lemma 10.58.10: membership in the degree-`n` part of `I` is exactly ideal
membership after forgetting the subtype. -/
private theorem mem_homogeneousIdealDegreePiece_iff {n : ℕ}
    {f : MvPolynomial.homogeneousSubmodule (Fin d) k n} :
    f ∈ homogeneousIdealDegreePiece (I := I) n ↔ ((f : 𝒜 n) : S) ∈ I.toIdeal := by
  rfl

/-- The Hilbert function of the homogeneous quotient module `k[X₁, …, X_d] ⧸ I`, computed from
the images of the homogeneous degree pieces in the quotient. The source's partial-function
convention is modeled here by declaring the value to be `0` in negative degrees. -/
def homogeneousIdealQuotientHilbertFunction : ℤ → ℤ :=
  fun n ↦
    if 0 ≤ n then
      Module.finrank k <| homogeneousIdealQuotientDegreePiece I n.toNat
    else 0

-- Proof sketch: for nonnegative `n` this is just the dimension of the image of the degree-`n`
-- homogeneous piece in the quotient module; for negative `n` the function is defined to be `0`.
/-- In nonnegative degree, the Hilbert function is the dimension of the corresponding degree piece
of the quotient module. -/
private theorem homogeneousIdealQuotientHilbertFunction_of_nonneg
    (n : ℤ) (hn : 0 ≤ n) :
    homogeneousIdealQuotientHilbertFunction I n =
      (Module.finrank k <| homogeneousIdealQuotientDegreePiece I n.toNat : ℤ) := by
  rw [homogeneousIdealQuotientHilbertFunction, if_pos hn]

/-- In negative degree, the Hilbert function is `0`. -/
@[simp] private theorem homogeneousIdealQuotientHilbertFunction_of_neg
    {n : ℤ} (hn : n < 0) :
    homogeneousIdealQuotientHilbertFunction I n = 0 := by
  have hnn : ¬ 0 ≤ n := by linarith
  simp [homogeneousIdealQuotientHilbertFunction, hnn]

/-- Helper for Lemma 10.58.10: the file-local `ℤ`-graded model of quotient degree pieces, obtained
by keeping the usual nonnegative pieces and declaring negative pieces to be `⊥`. -/
private def quotientHilbertGrading (n : ℤ) : Submodule k (S ⧸ I.toIdeal) :=
  if 0 ≤ n then homogeneousIdealQuotientDegreePiece I n.toNat else ⊥

/-- Helper for Lemma 10.58.10: quotient grading pieces are free over the coefficient field. -/
private noncomputable instance quotientHilbertGrading_moduleFree (n : ℤ) :
    Module.Free k (quotientHilbertGrading I n) :=
  Module.Free.of_divisionRing k (quotientHilbertGrading I n)

/-- Helper for Lemma 10.58.10: the source proof starts from the integer-lifted standard grading on
`S`, with the negative branch forced to `⊥`. -/
private def ambientIntGrading (n : ℤ) : Submodule k S :=
  if 0 ≤ n then MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat else ⊥

/-- Helper for Lemma 10.58.10: in nonnegative degree, the integer-lifted ambient grading agrees
with the usual homogeneous degree piece. -/
private theorem ambientIntGrading_nonneg_eq
    (n : ℤ) (hn : 0 ≤ n) :
    ambientIntGrading (k := k) (d := d) n =
      MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat := by
  -- Unpack the nonnegative branch of the integer-lifted ambient grading.
  simp [ambientIntGrading, hn]

/-- Helper for Lemma 10.58.10: negative degrees of the integer-lifted ambient grading are
trivial. -/
private theorem ambientIntGrading_neg_eq_bot
    {n : ℤ} (hn : n < 0) :
    ambientIntGrading (k := k) (d := d) n = ⊥ := by
  have hnn : ¬ 0 ≤ n := by
    linarith
  -- Negative degrees are declared to be `⊥` to match the source's partial-function convention.
  simp [ambientIntGrading, hnn]

/-- Helper for Lemma 10.58.10: the nonnegative `ℤ`-piece of the ambient grading is canonically
the usual `ℕ`-graded homogeneous piece. -/
private noncomputable def ambientIntGrading_nat_linearEquiv
    (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin d) k n ≃ₗ[k]
      ambientIntGrading (k := k) (d := d) (n : ℤ) := by
  have hnonneg : 0 ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  -- Replace the integer-indexed piece by the matching nonnegative homogeneous component.
  exact LinearEquiv.ofEq _ _
    (ambientIntGrading_nonneg_eq (k := k) (d := d) (n : ℤ) hnonneg).symm

/-- Helper for Lemma 10.58.10: under the nonnegative `ℤ`-grading, the transported `n`-th ambient
piece still has the same polynomial representative in `S`. -/
private theorem ambientIntGrading_nat_linearEquiv_coe
    (n : ℕ) (x : MvPolynomial.homogeneousSubmodule (Fin d) k n) :
    ((ambientIntGrading_nat_linearEquiv (k := k) (d := d) n x :
      ambientIntGrading (k := k) (d := d) (n : ℤ)) : S) =
      (x : S) := by
  -- The equivalence only repackages the same subtype witness through the equality of pieces.
  simp [ambientIntGrading_nat_linearEquiv]

/-- Helper for Lemma 10.58.10: reindexing the standard `ℕ`-grading of `k[X₁, …, X_d]` by `ℤ`
gives a direct-sum decomposition with negative degrees forced to `⊥`. -/
private noncomputable def ambientIntGrading_decompose :
    S →ₗ[k] DirectSum ℤ (fun n ↦ ↥(ambientIntGrading (k := k) (d := d) n)) :=
  -- Send each ordinary homogeneous summand to the same summand, now viewed in degree `(n : ℤ)`.
  (DirectSum.toModule k ℕ
      (DirectSum ℤ (fun n ↦ ↥(ambientIntGrading (k := k) (d := d) n)))
      (fun n ↦
        (DirectSum.lof k ℤ
          (fun z ↦ ↥(ambientIntGrading (k := k) (d := d) z)) (n : ℤ)).comp
          ((ambientIntGrading_nat_linearEquiv (k := k) (d := d) n).toLinearMap))).comp
    (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin d) k)).toLinearMap

/-- Helper for Lemma 10.58.10: recomposing the reindexed ambient grading recovers the original
polynomial. -/
private theorem ambientIntGrading_decompose_left_inv :
    DirectSum.coeLinearMap (ambientIntGrading (k := k) (d := d)) ∘ₗ
        ambientIntGrading_decompose (k := k) (d := d) =
      LinearMap.id := by
  -- It is enough to compare both maps on the ordinary homogeneous summands of `S`.
  apply DirectSum.decompose_lhom_ext (ℳ := MvPolynomial.homogeneousSubmodule (Fin d) k)
  intro n
  apply LinearMap.ext
  intro x
  change
    DirectSum.coeLinearMap (ambientIntGrading (k := k) (d := d))
        (ambientIntGrading_decompose (k := k) (d := d) (x : S)) =
      (x : S)
  simpa [ambientIntGrading_decompose, LinearMap.comp_apply] using
    ambientIntGrading_nat_linearEquiv_coe (k := k) (d := d) n x

/-- Helper for Lemma 10.58.10: each reindexed ambient summand is recovered by decomposing its
ambient polynomial and reading off the same degree. -/
private theorem ambientIntGrading_decompose_right_inv :
    ambientIntGrading_decompose (k := k) (d := d) ∘ₗ
        DirectSum.coeLinearMap (ambientIntGrading (k := k) (d := d)) =
      LinearMap.id := by
  -- A direct-sum map is determined by its values on the homogeneous `lof` generators.
  apply DirectSum.linearMap_ext
  intro z
  apply LinearMap.ext
  intro xbar
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  by_cases hz : z < 0
  · have hbot :
        ambientIntGrading (k := k) (d := d) z = ⊥ :=
      ambientIntGrading_neg_eq_bot (k := k) (d := d) hz
    haveI : Subsingleton ↥(ambientIntGrading (k := k) (d := d) z) := by
      rw [hbot]
      infer_instance
    -- Negative degrees are trivial, so there is only the zero generator to check.
    have hxbar : xbar = 0 := Subsingleton.elim _ _
    rw [hxbar]
    simp [ambientIntGrading_decompose]
  · have hnonneg : 0 ≤ z := by
      linarith
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    let x :=
      (ambientIntGrading_nat_linearEquiv (k := k) (d := d) n).symm xbar
    have hxbar :
        ambientIntGrading_nat_linearEquiv (k := k) (d := d) n x = xbar := by
      exact LinearEquiv.apply_symm_apply _ _
    -- On nonnegative degrees, the reindexed decomposition is the same `lof` term as before.
    calc
      ambientIntGrading_decompose (k := k) (d := d)
          ((xbar : ambientIntGrading (k := k) (d := d) (n : ℤ)) : S) =
        ambientIntGrading_decompose (k := k) (d := d) ((x : MvPolynomial.homogeneousSubmodule (Fin d) k n) : S) := by
            rw [← hxbar]
            rw [ambientIntGrading_nat_linearEquiv_coe]
      _ = DirectSum.lof k ℤ
            (fun z ↦ ↥(ambientIntGrading (k := k) (d := d) z))
            (n : ℤ)
            (ambientIntGrading_nat_linearEquiv (k := k) (d := d) n x) := by
            simpa [ambientIntGrading_decompose, LinearMap.comp_apply]
      _ = DirectSum.lof k ℤ
            (fun z ↦ ↥(ambientIntGrading (k := k) (d := d) z))
            (n : ℤ) xbar := by
            rw [hxbar]

/-- Helper for Lemma 10.58.10: the integer-lifted ambient grading is a genuine internal direct
sum decomposition of the polynomial ring. -/
private noncomputable instance ambientIntGrading_decomposition :
    DirectSum.Decomposition (ambientIntGrading (k := k) (d := d)) :=
  -- Package the reindexed decomposition map together with its two inverse identities.
  DirectSum.Decomposition.ofLinearMap
    (ℳ := ambientIntGrading (k := k) (d := d))
    (ambientIntGrading_decompose (k := k) (d := d))
    (ambientIntGrading_decompose_left_inv (k := k) (d := d))
    (ambientIntGrading_decompose_right_inv (k := k) (d := d))

/-- Helper for Chap10 Lemma 10 58 10: the standard polynomial grading acts on the integer-lifted
ambient grading by degree addition. -/
private instance ambientIntGrading_setLikeGradedSMul :
    SetLike.GradedSMul
      (MvPolynomial.homogeneousSubmodule (Fin d) k)
      (ambientIntGrading (k := k) (d := d)) where
  smul_mem := by
    intro i j a x ha hx
    by_cases hj : 0 ≤ j
    · have hi_nonneg : 0 ≤ (i : ℤ) := by
        exact_mod_cast Nat.zero_le i
      have hij : 0 ≤ (i : ℤ) + j := add_nonneg hi_nonneg hj
      have htoNat : (((i : ℤ) + j).toNat) = i + j.toNat := by
        omega
      -- On the nonnegative branch, this is the usual homogeneous multiplication rule.
      rw [ambientIntGrading_nonneg_eq (k := k) (d := d) j hj] at hx
      change a • x ∈ ambientIntGrading (k := k) (d := d) ((i : ℤ) + j)
      rw [ambientIntGrading_nonneg_eq (k := k) (d := d) ((i : ℤ) + j) hij]
      simpa [htoNat] using SetLike.mul_mem_graded ha hx
    · have hneg : j < 0 := by
        linarith
      have hx0 : x = 0 := by
        rw [ambientIntGrading_neg_eq_bot (k := k) (d := d) hneg] at hx
        simpa using hx
      -- Negative source degrees are trivial, so only the zero vector needs checking.
      rw [hx0]
      simpa using Submodule.zero_mem (ambientIntGrading (k := k) (d := d) (i +ᵥ j))

/-- Helper for Lemma 10.58.10: in nonnegative degree, the local quotient grading is exactly the
same degree piece used in the Hilbert function definition. -/
private theorem quotientHilbertGrading_nonneg_eq_degreePiece
    (n : ℤ) (hn : 0 ≤ n) :
    quotientHilbertGrading I n = homogeneousIdealQuotientDegreePiece I n.toNat := by
  -- Unpack the nonnegative branch of the local grading.
  simp [quotientHilbertGrading, hn]

/-- Helper for Lemma 10.58.10: negative degrees of the local quotient grading are trivial. -/
private theorem quotientHilbertGrading_neg_eq_bot
    {n : ℤ} (hn : n < 0) :
    quotientHilbertGrading I n = ⊥ := by
  have hnn : ¬ 0 ≤ n := by linarith
  -- Negative degrees are declared to be `⊥` to match the source's partial-function convention.
  simp [quotientHilbertGrading, hnn]

/-- Helper for Chap10 Lemma 10 58 10: the standard polynomial grading acts on the quotient degree
pieces by degree addition. -/
private instance quotientHilbertGrading_setLikeGradedSMul :
    SetLike.GradedSMul
      (MvPolynomial.homogeneousSubmodule (Fin d) k)
      (quotientHilbertGrading I) where
  smul_mem := by
    intro i j a x ha hx
    by_cases hj : 0 ≤ j
    · have hi_nonneg : 0 ≤ (i : ℤ) := by
        exact_mod_cast Nat.zero_le i
      have hij : 0 ≤ (i : ℤ) + j := add_nonneg hi_nonneg hj
      have htoNat : (((i : ℤ) + j).toNat) = i + j.toNat := by
        omega
      -- Rewrite both quotient degrees to the mapped nonnegative homogeneous pieces.
      rw [quotientHilbertGrading_nonneg_eq_degreePiece (I := I) j hj] at hx
      change a • x ∈ quotientHilbertGrading I ((i : ℤ) + j)
      rw [quotientHilbertGrading_nonneg_eq_degreePiece (I := I) ((i : ℤ) + j) hij]
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨(a : S) * y, ?_, ?_⟩
      · -- The representative stays homogeneous in the summed degree.
        simpa [htoNat] using SetLike.mul_mem_graded ha hy
      · -- The quotient action is defined by multiplying the representative before taking classes.
        change (Ideal.Quotient.mkₐ k I.toIdeal) ((a : S) * y) =
          (a : S) • (Ideal.Quotient.mkₐ k I.toIdeal) y
        exact (Ideal.Quotient.mkₐ k I.toIdeal).map_mul (a : S) y
    · have hneg : j < 0 := by
        linarith
      have hx0 : x = 0 := by
        rw [quotientHilbertGrading_neg_eq_bot (I := I) hneg] at hx
        simpa using hx
      -- Negative source degrees are trivial in the quotient grading as well.
      rw [hx0]
      simpa using Submodule.zero_mem (quotientHilbertGrading I (i +ᵥ j))

/-- Helper for Lemma 10.58.10: the Hilbert function is the `k`-dimension of the local quotient
grading piece in every integer degree. -/
private theorem homogeneousIdealQuotientHilbertFunction_eq_quotient_grading_finrank
    (n : ℤ) :
    homogeneousIdealQuotientHilbertFunction I n =
      (Module.finrank k (quotientHilbertGrading I n) : ℤ) := by
  by_cases hn : 0 ≤ n
  · -- On the nonnegative branch both definitions read off the same quotient degree piece.
    rw [homogeneousIdealQuotientHilbertFunction_of_nonneg (I := I) n hn,
      quotientHilbertGrading_nonneg_eq_degreePiece (I := I) n hn]
  · have hneg : n < 0 := by linarith
    -- On the negative branch both sides collapse to zero.
    rw [homogeneousIdealQuotientHilbertFunction_of_neg (I := I) hneg,
      quotientHilbertGrading_neg_eq_bot (I := I) hneg]
    simp

/-- Helper for Lemma 10.58.10: every integer degree piece of the file-local quotient grading is a
finite-dimensional `k`-vector space. -/
private theorem quotientHilbertGrading_moduleFinite
    (n : ℤ) :
    Module.Finite k (quotientHilbertGrading I n) := by
  by_cases hn : 0 ≤ n
  · -- On the nonnegative branch, identify the piece with the quotient-image of the ambient
    -- homogeneous component and use surjectivity of the restricted quotient map.
    rw [quotientHilbertGrading_nonneg_eq_degreePiece (I := I) n hn]
    classical
    let _ : Fintype {m : Fin d →₀ ℕ // m.degree = n.toNat} :=
      Fintype.ofEquiv ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n.toNat)
        (degree_exponent_subtype_equiv_finsuppAntidiag d n.toNat).symm
    let _ : Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat) := by
      rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
      let e :
          Finsupp.supported k k {m : Fin d →₀ ℕ | m.degree = n.toNat} ≃ₗ[k]
            {m : Fin d →₀ ℕ // m.degree = n.toNat} →₀ k :=
        Finsupp.supportedEquivFinsupp (M := k) (R := k) {m : Fin d →₀ ℕ | m.degree = n.toNat}
      exact Module.Finite.equiv e.symm
    let q : MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat →ₗ[k]
        homogeneousIdealQuotientDegreePiece I n.toNat :=
      { toFun := fun x ↦ ⟨(Ideal.Quotient.mkₐ k I.toIdeal) x, ⟨x, x.2, rfl⟩⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          simp
        map_smul' := by
          intro c x
          apply Subtype.ext
          rfl }
    exact Module.Finite.of_surjective q <| by
      intro xbar
      rcases xbar.2 with ⟨x, hx, hxbar⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxbar
  · have hneg : n < 0 := by
      linarith
    -- On the negative branch, the degree piece is `⊥`, hence trivially finite.
    rw [quotientHilbertGrading_neg_eq_bot (I := I) hneg]
    let f : (Fin 0 → k) →ₗ[k] (⊥ : Submodule k (S ⧸ I.toIdeal)) := 0
    exact Module.Finite.of_surjective f <| by
      intro x
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _

/-- Helper for Lemma 10.58.10: quotient grading pieces are registered as finite-dimensional
`k`-vector spaces. -/
private noncomputable instance quotientHilbertGrading_moduleFinite_instance (n : ℤ) :
    Module.Finite k (quotientHilbertGrading I n) :=
  quotientHilbertGrading_moduleFinite (I := I) n

/-- Helper for Chap10 Lemma 10 58 10: the local quotient grading is the image of the
integer-lifted ambient grading under the quotient map. -/
private theorem quotientHilbertGrading_eq_map_ambientIntGrading
    (n : ℤ) :
    quotientHilbertGrading I n =
      (ambientIntGrading (k := k) (d := d) n).map
        (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap := by
  by_cases hn : 0 ≤ n
  · -- In nonnegative degrees both sides are the mapped ordinary homogeneous degree piece.
    rw [quotientHilbertGrading_nonneg_eq_degreePiece (I := I) n hn,
      ambientIntGrading_nonneg_eq (k := k) (d := d) n hn]
    rfl
  · have hneg : n < 0 := by
      linarith
    -- In negative degrees the source piece is `⊥`, so its image and the quotient piece are both
    -- trivial.
    rw [quotientHilbertGrading_neg_eq_bot (I := I) hneg,
      ambientIntGrading_neg_eq_bot (k := k) (d := d) hneg]
    exact (Submodule.map_bot _).symm

/-- Helper for Chap10 Lemma 10 58 10: in nonnegative degrees, the integer-lifted ambient
projection has the same underlying polynomial as the usual natural-degree projection. -/
private theorem ambientIntGrading_decompose_coe_eq_ofNat
    (x : S) (m : ℕ) :
    (((DirectSum.decompose (ambientIntGrading (k := k) (d := d)) x) (m : ℤ) :
        ambientIntGrading (k := k) (d := d) (m : ℤ)) : S) =
      (((DirectSum.decompose 𝒜 x) m : 𝒜 m) : S) := by
  let L : S →ₗ[k] S :=
    (ambientIntGrading (k := k) (d := d) (m : ℤ)).subtype.comp
      ((DirectSum.component k ℤ
          (fun z ↦ ↥(ambientIntGrading (k := k) (d := d) z)) (m : ℤ)).comp
        (ambientIntGrading_decompose (k := k) (d := d)))
  let R : S →ₗ[k] S :=
    (𝒜 m).subtype.comp
      ((DirectSum.component k ℕ (fun n ↦ ↥(𝒜 n)) m).comp
        (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap)
  have hLR : L = R := by
    -- Compare the two projection maps on the ordinary homogeneous summands of `S`.
    apply DirectSum.decompose_lhom_ext (ℳ := 𝒜)
    intro i
    apply LinearMap.ext
    intro y
    by_cases him : i = m
    · subst him
      simp [L, R, ambientIntGrading_decompose, ambientIntGrading_nat_linearEquiv_coe,
        DirectSum.component.lof_self]
    · have hcast : (i : ℤ) ≠ (m : ℤ) := by
        exact_mod_cast him
      simp [L, R, ambientIntGrading_decompose, DirectSum.component.of, him, hcast]
  -- Evaluate the equality of projection maps at `x`.
  exact congrArg (fun f : S →ₗ[k] S ↦ f x) hLR

/-- Helper for Chap10 Lemma 10 58 10: negative integer ambient projections vanish after
forgetting to the polynomial ring. -/
private theorem ambientIntGrading_decompose_coe_eq_zero_of_neg
    (x : S) {n : ℤ} (hn : n < 0) :
    (((DirectSum.decompose (ambientIntGrading (k := k) (d := d)) x) n :
        ambientIntGrading (k := k) (d := d) n) : S) = 0 := by
  have hbot :
      ambientIntGrading (k := k) (d := d) n = ⊥ :=
    ambientIntGrading_neg_eq_bot (k := k) (d := d) hn
  haveI : Subsingleton ↥(ambientIntGrading (k := k) (d := d) n) := by
    rw [hbot]
    infer_instance
  -- Once the negative component is identified with `⊥`, every element of it is zero.
  exact
    congrArg Subtype.val
      (Subsingleton.elim
        (((DirectSum.decompose (ambientIntGrading (k := k) (d := d)) x) n :
          ambientIntGrading (k := k) (d := d) n))
        0)

/-- Helper for Chap10 Lemma 10 58 10: the homogeneous ideal is homogeneous for the
integer-lifted ambient grading after restricting scalars to `k`. -/
private theorem homogeneousIdeal_restrictScalars_isHomogeneous_ambient :
    (I.toIdeal.restrictScalars k).IsHomogeneous (ambientIntGrading (k := k) (d := d)) := by
  intro n x hx
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hxI : x ∈ I.toIdeal := by
      simpa using hx
    -- The nonnegative integer projection is the ordinary homogeneous projection, so
    -- homogeneity of `I` for the standard grading supplies membership.
    rw [ambientIntGrading_decompose_coe_eq_ofNat (k := k) (d := d) x m]
    exact (Ideal.IsHomogeneous.mem_iff 𝒜 I.isHomogeneous).1 hxI m
  · have hneg : n < 0 := by
      linarith
    -- Negative integer components are zero, hence lie in the restricted ideal.
    rw [ambientIntGrading_decompose_coe_eq_zero_of_neg (k := k) (d := d) x hneg]
    exact Submodule.zero_mem _

/-- Helper for Chap10 Lemma 10 58 10: the local quotient grading is a direct-sum decomposition
of the quotient module. -/
private noncomputable instance quotientHilbertGrading_decomposition :
    DirectSum.Decomposition (quotientHilbertGrading I) := by
  let N : Submodule k S := I.toIdeal.restrictScalars k
  have hN : N.IsHomogeneous (ambientIntGrading (k := k) (d := d)) := by
    -- The previous helper supplies the homogeneous-kernel condition needed to descend the ambient
    -- decomposition through the quotient map.
    simpa [N] using
      homogeneousIdeal_restrictScalars_isHomogeneous_ambient (I := I) (k := k) (d := d)
  have hdec :
      DirectSum.Decomposition
        (fun n ↦ quotient_grading (ambientIntGrading (k := k) (d := d)) N n) :=
    @homogeneous_quotient_module_decomposition k _ _ S _ _
      (ambientIntGrading (k := k) (d := d)) _ N hN
  have hpieces :
      quotientHilbertGrading I =
        fun n ↦ quotient_grading (ambientIntGrading (k := k) (d := d)) N n := by
    funext n
    -- Both descriptions are the image of the same ambient component under the quotient map.
    rw [quotientHilbertGrading_eq_map_ambientIntGrading (I := I) (k := k) (d := d) n]
    rfl
  rw [hpieces]
  exact hdec

/-- Helper for Chap10 Lemma 10 58 10: for the standard grading on `MvPolynomial (Fin 0) k`, the
irrelevant ideal is zero. -/
private theorem mvPolynomial_finZero_irrelevant_toIdeal_eq_bot :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 0) k)).toIdeal = ⊥ := by
  let 𝒜₀ := MvPolynomial.homogeneousSubmodule (Fin 0) k
  have hpiece : ∀ i : ℕ, 0 < i → 𝒜₀ i = ⊥ := by
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
    have hfin :
        Module.finrank k (𝒜₀ (j + 1)) = 0 := by
      -- Count monomials in positive degree: there are no exponent vectors in zero variables.
      simpa [𝒜₀, Nat.multichoose_zero_succ] using
        ambient_degree_piece_finrank_eq_multichoose (k := k) (d := 0) (j + 1)
    -- A finite-dimensional subspace of dimension zero is the bottom subspace.
    exact Submodule.finrank_eq_zero.mp hfin
  rw [HomogeneousIdeal.irrelevant_eq_span]
  rw [Ideal.span_eq_bot]
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hi, hxpiece⟩
  -- Every positive homogeneous piece is zero, so the span of all positive pieces is zero.
  have hbot : 𝒜₀ i = ⊥ := hpiece i hi
  change x ∈ 𝒜₀ i at hxpiece
  rw [hbot] at hxpiece
  simpa using hxpiece

/-- Helper for Chap10 Lemma 10 58 10: under `MvPolynomial.finSuccEquiv`, the ideal generated by
the first variable maps to the ideal generated by `Polynomial.X - Polynomial.C 0`. -/
private theorem mvPolynomial_firstVariable_span_map (d : ℕ) :
    Ideal.span
        ({(Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin d) k) :
          Polynomial (MvPolynomial (Fin d) k))} : Set _) =
      Ideal.map (MvPolynomial.finSuccEquiv k d)
        (Ideal.span ({(MvPolynomial.X 0 : MvPolynomial (Fin (d + 1)) k)} : Set _)) := by
  -- The quotient bridge is paid for once by mapping the principal ideal across `finSuccEquiv`.
  rw [Ideal.map_span]
  simp [MvPolynomial.finSuccEquiv_X_zero]

/-- Helper for Chap10 Lemma 10 58 10: quotienting `MvPolynomial (Fin (d + 1)) k` by the first
coordinate gives the smaller standard polynomial ring. -/
private noncomputable def mvPolynomialQuotientFirstVariableAlgEquiv (d : ℕ) :
    (MvPolynomial (Fin (d + 1)) k ⧸
        Ideal.span ({(MvPolynomial.X 0 : MvPolynomial (Fin (d + 1)) k)} : Set _)) ≃ₐ[k]
      MvPolynomial (Fin d) k :=
  (Ideal.quotientEquivAlg
      (Ideal.span ({(MvPolynomial.X 0 : MvPolynomial (Fin (d + 1)) k)} : Set _))
      (Ideal.span
        ({(Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin d) k) :
          Polynomial (MvPolynomial (Fin d) k))} : Set _))
      (MvPolynomial.finSuccEquiv k d)
      (mvPolynomial_firstVariable_span_map (k := k) d)).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv (R := MvPolynomial (Fin d) k) 0).restrictScalars k)

/-- Helper for Chap10 Lemma 10 58 10: `finSuccEquiv` sends renamed smaller-variable
polynomials to constant polynomials in the split-off variable. -/
private theorem finSuccEquiv_rename_succ (d : ℕ) (p : MvPolynomial (Fin d) k) :
    (MvPolynomial.finSuccEquiv k d)
        (MvPolynomial.rename Fin.succ p : MvPolynomial (Fin (d + 1)) k) =
      Polynomial.C p := by
  -- Prove the computation on the polynomial generators and extend by the polynomial induction API.
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
      simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp [map_mul, hp, MvPolynomial.finSuccEquiv_X_succ]

/-- Helper for Chap10 Lemma 10 58 10: the first-coordinate quotient equivalence sends the class
of a renamed smaller-variable polynomial to that polynomial. -/
private theorem mvPolynomialQuotientFirstVariableAlgEquiv_mk_rename_succ
    (d : ℕ) (p : MvPolynomial (Fin d) k) :
    (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d)
      (Ideal.Quotient.mk _
        (MvPolynomial.rename Fin.succ p : MvPolynomial (Fin (d + 1)) k)) = p := by
  -- This is the main computation needed when transporting killed-coordinate quotients downward.
  simp [mvPolynomialQuotientFirstVariableAlgEquiv, finSuccEquiv_rename_succ]

/-- Helper for Chap10 Lemma 10 58 10: the inverse first-coordinate quotient equivalence is
represented by the class of `rename Fin.succ`. -/
private theorem mvPolynomialQuotientFirstVariableAlgEquiv_symm_rename_succ
    (d : ℕ) (p : MvPolynomial (Fin d) k) :
    (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm p =
      Ideal.Quotient.mk _
        (MvPolynomial.rename Fin.succ p : MvPolynomial (Fin (d + 1)) k) := by
  -- Push the candidate representative forward and use injectivity of the quotient equivalence.
  apply (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).injective
  simpa using
    mvPolynomialQuotientFirstVariableAlgEquiv_mk_rename_succ (k := k) d p
      |>.symm

/-- Helper for Chap10 Lemma 10 58 10: the first coordinate itself becomes zero in the smaller
polynomial ring quotient. -/
private theorem mvPolynomialQuotientFirstVariableAlgEquiv_mk_X_zero (d : ℕ) :
    (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d)
      (Ideal.Quotient.mk _
        (MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)) = 0 := by
  -- The univariate quotient equivalence evaluates the split-off variable at zero.
  simp [mvPolynomialQuotientFirstVariableAlgEquiv]

/-- Helper for Chap10 Lemma 10 58 10: renaming the surviving variables preserves homogeneous
degree. -/
private theorem mvPolynomial_rename_succ_mem_homogeneousSubmodule
    (d n : ℕ) {p : MvPolynomial (Fin d) k}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin d) k n) :
    (MvPolynomial.rename Fin.succ p : MvPolynomial (Fin (d + 1)) k) ∈
      MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k n := by
  -- The renaming map only relabels variables, so homogeneous degree is unchanged.
  refine (MvPolynomial.mem_homogeneousSubmodule n _).2 ?_
  simpa using
    (MvPolynomial.mem_homogeneousSubmodule n p).1 hp |>.rename_isHomogeneous

/-- Helper for Chap10 Lemma 10 58 10: a scalar homogeneous submodule and its quotient assemble
the numerical-polynomiality of the original scalar Hilbert function. -/
private theorem scalarHomogeneousSubmodule_finrank_isNumericalPolynomial_of_parts
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) (K : Submodule S M)
    (hfinite : ∀ n, Module.Finite k (ℳ n))
    (hkernel :
      IsNumericalPolynomial
        (fun n ↦
          (Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) : ℤ)))
    (hquotient :
      IsNumericalPolynomial
        (fun n ↦ (Module.finrank k (scalarQuotientGrading ℳ K n) : ℤ))) :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (ℳ n) : ℤ)) := by
  -- The existing scalar splitting gives a pointwise sum formula for dimensions; numerical
  -- polynomiality is closed under that sum and under pointwise equality.
  refine IsNumericalPolynomial.congr (IsNumericalPolynomial.add hkernel hquotient) ?_
  exact Filter.EventuallyEq.of_eq <| by
    ext n
    exact scalarHomogeneousSubmodule_finrank_add (ℳ := ℳ) K hfinite n

/-- Helper for Chap10 Lemma 10 58 10: package the ambient homogeneous components of
`x : K` as an element of the inherited scalar direct sum. -/
private noncomputable def scalarSubmoduleGrading_ambientWitness
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) (x : K) :
    DirectSum ℤ (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype)) := by
  classical
  -- Use the ambient decomposition support and package each ambient coordinate back into `K`.
  refine DFinsupp.mk (DirectSum.decompose ℳ (x : M)).support fun n ↦ ?_
  refine ⟨⟨((DirectSum.decompose ℳ (x : M) n.1 : ℳ n.1) : M), ?_⟩, ?_⟩
  · exact hK n.1 x.2
  · exact (DirectSum.decompose ℳ (x : M) n.1).2

/-- Helper for Chap10 Lemma 10 58 10: recomposing the ambient witness recovers the original
submodule element. -/
private theorem scalarSubmoduleGrading_ambientWitness_recompose
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) (x : K) :
    DirectSum.coeAddMonoidHom
      (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))
      (scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x) = x := by
  classical
  apply Subtype.ext
  -- Rewrite the inherited recomposition as the ambient finite sum of homogeneous coordinates.
  let w :=
    scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x
  have hsupp :
      w.support = (DirectSum.decompose ℳ (x : M)).support := by
    ext n
    by_cases hn : n ∈ (DirectSum.decompose ℳ (x : M)).support
    · constructor
      · intro _
        exact hn
      · have hcomp_ne : (DirectSum.decompose ℳ (x : M) n : ℳ n) ≠ 0 :=
          DFinsupp.mem_support_iff.mp hn
        intro _
        apply DFinsupp.mem_support_iff.mpr
        intro hw_zero
        apply hcomp_ne
        apply Subtype.ext
        have hcoerced :=
          congrArg
            (fun y : (ℳ n).comap ((K.restrictScalars k).subtype) ↦ (((y.1 : K) : M)))
            hw_zero
        simpa [w, scalarSubmoduleGrading_ambientWitness, hn] using hcoerced
    · constructor
      · intro hw
        have hw_ne : w n ≠ 0 := DFinsupp.mem_support_iff.mp hw
        have hw_zero : w n = 0 := by
          simp [w, scalarSubmoduleGrading_ambientWitness, hn]
        exact False.elim (hw_ne hw_zero)
      · intro hfalse
        exact False.elim (hn hfalse)
  have hsumWitness :
      ((DirectSum.coeAddMonoidHom
          (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))
          w : K) : M) =
        ∑ n ∈ w.support, (((w n).1 : K) : M) := by
    have hdfinsupp :=
      congrArg (fun y : K ↦ (y : M))
        (DirectSum.coeAddMonoidHom_eq_dfinsuppSum
          (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))
          w)
    simpa [DFinsupp.sum] using hdfinsupp
  have hsum :
      ((DirectSum.coeAddMonoidHom
          (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))
          w : K) : M) =
        ∑ n ∈ (DirectSum.decompose ℳ (x : M)).support,
          ((DirectSum.decompose ℳ (x : M) n : ℳ n) : M) := by
    rw [hsumWitness, hsupp]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [w, scalarSubmoduleGrading_ambientWitness, hi]
  -- The ambient direct-sum decomposition recomposes exactly to `x`.
  exact hsum.trans (DirectSum.sum_support_decompose ℳ (x : M))

/-- Helper for Chap10 Lemma 10 58 10: the scalar degree pieces inside a homogeneous
`S`-submodule span that submodule. -/
private theorem scalarSubmoduleGrading_coeAddMonoidHom_surjective
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) :
    Function.Surjective
      (DirectSum.coeAddMonoidHom
        (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))) := by
  intro x
  refine ⟨scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x, ?_⟩
  -- The explicit witness was designed so that recomposition is immediate.
  exact scalarSubmoduleGrading_ambientWitness_recompose (ℳ := ℳ) (K := K) hK x

/-- Helper for Chap10 Lemma 10 58 10: ambient degree projection after recomposing inherited
scalar pieces recovers the original coordinate. -/
private theorem scalarSubmoduleGrading_ambientDecompose_recompose_apply
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M)
    (z : DirectSum ℤ (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))) (n : ℤ) :
    let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
    ((DirectSum.decompose ℳ ((DirectSum.coeAddMonoidHom 𝒦 z : K) : M) n : ℳ n) : M) =
      (((z n).1 : K) : M) := by
  classical
  let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
  let g : ℤ → M := fun i ↦
    ((DirectSum.decompose ℳ (((z i).1 : K) : M) n : ℳ n) : M)
  have hrecompose :
      ((DirectSum.coeAddMonoidHom 𝒦 z : K) : M) =
        ∑ i ∈ z.support, (((z i).1 : K) : M) := by
    have hdfinsupp :=
      congrArg (fun y : K ↦ (y : M)) (DirectSum.coeAddMonoidHom_eq_dfinsuppSum 𝒦 z)
    simpa [DFinsupp.sum, 𝒦] using hdfinsupp
  have hdecomp :
      ((DirectSum.decompose ℳ ((DirectSum.coeAddMonoidHom 𝒦 z : K) : M) n : ℳ n) : M) =
        ∑ i ∈ z.support, g i := by
    -- Project the ambient finite recomposition termwise to degree `n`.
    have hproj :=
      congrArg (fun y : M ↦ ((DirectSum.decompose ℳ y n : ℳ n) : M)) hrecompose
    simpa [g, DirectSum.decompose_sum] using hproj
  have hsum :
      ∑ i ∈ z.support, g i = g n := by
    by_cases hn : n ∈ z.support
    · rw [Finset.sum_eq_single_of_mem n hn]
      intro i hi hin
      have hi_ne : i ≠ n := hin
      simpa [g, hi_ne] using
        (DirectSum.decompose_of_mem_ne ℳ
          (show (((z i).1 : K) : M) ∈ ℳ i from (z i).2) hi_ne)
    · have hsum_zero :
          ∑ i ∈ z.support, g i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi_ne : i ≠ n := by
          intro hi_eq
          exact hn (hi_eq ▸ hi)
        simpa [g, hi_ne] using
          (DirectSum.decompose_of_mem_ne ℳ
            (show (((z i).1 : K) : M) ∈ ℳ i from (z i).2) hi_ne)
      have hn_zero : z n = 0 := DFinsupp.notMem_support_iff.mp hn
      have hg_zero : g n = 0 := by
        simp [g, hn_zero]
      rw [hsum_zero, hg_zero]
  -- Only the degree-`n` coordinate survives the projection.
  calc
    ((DirectSum.decompose ℳ ((DirectSum.coeAddMonoidHom 𝒦 z : K) : M) n : ℳ n) : M) =
        ∑ i ∈ z.support, g i := hdecomp
    _ = g n := hsum
    _ = (((z n).1 : K) : M) := by
          simpa [g] using
            (DirectSum.decompose_of_mem_same ℳ
              (show (((z n).1 : K) : M) ∈ ℳ n from (z n).2))

/-- Helper for Chap10 Lemma 10 58 10: the scalar degree pieces inside a homogeneous
`S`-submodule are independent. -/
private theorem scalarSubmoduleGrading_coeAddMonoidHom_injective
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) :
    Function.Injective
      (DirectSum.coeAddMonoidHom
        (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))) := by
  classical
  let 𝒦 : ℤ → Submodule k K :=
    fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype)
  intro x y hxy
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  apply Subtype.ext
  have hM :
      ((DirectSum.coeAddMonoidHom 𝒦 x : K) : M) =
        ((DirectSum.coeAddMonoidHom 𝒦 y : K) : M) := by
    exact congrArg (fun z : K ↦ (z : M)) hxy
  have hxproj :
      ((DirectSum.decompose ℳ ((DirectSum.coeAddMonoidHom 𝒦 x : K) : M) n : ℳ n) : M) =
        (((x n).1 : K) : M) := by
    -- Project the recomposed `x` back to degree `n`.
    simpa [𝒦] using
      scalarSubmoduleGrading_ambientDecompose_recompose_apply (ℳ := ℳ) (K := K) x n
  have hyproj :
      ((DirectSum.decompose ℳ ((DirectSum.coeAddMonoidHom 𝒦 y : K) : M) n : ℳ n) : M) =
        (((y n).1 : K) : M) := by
    -- Apply the same projector formula to `y`.
    simpa [𝒦] using
      scalarSubmoduleGrading_ambientDecompose_recompose_apply (ℳ := ℳ) (K := K) y n
  -- Ambient projection in degree `n` reads off the scalar submodule coordinate on both sides.
  have hproj :=
    congrArg
      (fun z : M ↦ ((DirectSum.decompose ℳ z n : ℳ n) : M)) hM
  exact hxproj.symm.trans (hproj.trans hyproj)

/-- Helper for Chap10 Lemma 10 58 10: the scalar degree pieces inside a homogeneous
`S`-submodule form an internal direct sum. -/
private theorem scalarSubmoduleGrading_isInternal
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) :
    DirectSum.IsInternal
      (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype)) := by
  -- The previous two helpers identify the recomposition map as bijective.
  exact
    ⟨scalarSubmoduleGrading_coeAddMonoidHom_injective (ℳ := ℳ) K,
      scalarSubmoduleGrading_coeAddMonoidHom_surjective (ℳ := ℳ) K hK⟩

/-- Helper for Chap10 Lemma 10 58 10: a homogeneous `S`-submodule inherits the scalar
direct-sum decomposition from the ambient scalar graded module. -/
@[reducible]
private noncomputable def scalarSubmoduleGrading_decomposition
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) :
    DirectSum.Decomposition
      (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype)) :=
  DirectSum.IsInternal.chooseDecomposition
    (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype))
    (scalarSubmoduleGrading_isInternal (ℳ := ℳ) K hK)

/-- Helper for Chap10 Lemma 10 58 10: evaluating the ambient witness in degree `n` recovers the
ambient degree-`n` component of `x`. -/
private theorem scalarSubmoduleGrading_ambientWitness_apply
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ)
    (x : K) (n : ℤ) :
    (((scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x n).1 : K) : M) =
      ((DirectSum.decompose ℳ (x : M) n : ℳ n) : M) := by
  classical
  by_cases hn : n ∈ (DirectSum.decompose ℳ (x : M)).support
  · -- On the ambient support, the witness was defined to be exactly that component.
    simp [scalarSubmoduleGrading_ambientWitness, hn]
  · -- Off the ambient support, both the witness coordinate and the ambient coordinate vanish.
    have hzero : DirectSum.decompose ℳ (x : M) n = 0 := DFinsupp.notMem_support_iff.mp hn
    simpa [scalarSubmoduleGrading_ambientWitness, DFinsupp.mk_of_notMem, hn] using
      (congrArg (fun y : ℳ n ↦ (y : M)) hzero).symm

/-- Helper for Chap10 Lemma 10 58 10: the chosen decomposition on the inherited grading equals
the explicit ambient witness. -/
private theorem scalarSubmoduleGrading_decompose_eq_ambientWitness
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ)
    (x : K) :
    let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
    letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) K hK
    DirectSum.decompose 𝒦 x = scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x :=
  by
    classical
    let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
    letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) K hK
    apply scalarSubmoduleGrading_coeAddMonoidHom_injective (ℳ := ℳ) (K := K)
    have hleft : DirectSum.coeAddMonoidHom 𝒦 (DirectSum.decompose 𝒦 x) = x :=
      (DirectSum.decompose 𝒦).left_inv x
    exact hleft.trans (scalarSubmoduleGrading_ambientWitness_recompose (ℳ := ℳ) (K := K) hK x).symm

/-- Helper for Chap10 Lemma 10 58 10: the inherited scalar decomposition on a homogeneous
`S`-submodule is computed by the ambient scalar decomposition after coercing back to `M`. -/
private theorem scalarSubmoduleGrading_decompose_coe_eq
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ)
    (x : K) (n : ℤ) :
    let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
    letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) K hK
    (((DirectSum.decompose 𝒦 x n).1 : K) : M) =
      ((DirectSum.decompose ℳ (x : M) n : ℳ n) : M) := by
  classical
  let 𝒦 : ℤ → Submodule k K := fun m ↦ (ℳ m).comap ((K.restrictScalars k).subtype)
  letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) K hK
  have hcoord :
      DirectSum.decompose 𝒦 x n =
        scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x n :=
    congrArg (fun z : ⨁ m, 𝒦 m ↦ z n)
      (scalarSubmoduleGrading_decompose_eq_ambientWitness
        (ℳ := ℳ) (K := K) (hK := hK) x)
  have hcoord_coe :
      (((DirectSum.decompose 𝒦 x n).1 : K) : M) =
        (((scalarSubmoduleGrading_ambientWitness (ℳ := ℳ) (K := K) hK x n).1 : K) : M) := by
    exact congrArg (fun y : 𝒦 n ↦ (((y.1 : K) : M))) hcoord
  exact hcoord_coe.trans (scalarSubmoduleGrading_ambientWitness_apply (ℳ := ℳ) (K := K) hK x n)

/-- Helper for Chap10 Lemma 10 58 10: a homogeneous scalar quotient grading inherits the ambient
direct-sum decomposition on the quotient module. -/
@[reducible]
private noncomputable def scalarQuotientGrading_decomposition
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (K : Submodule S M) (hK : (K.restrictScalars k).IsHomogeneous ℳ) :
    DirectSum.Decomposition (scalarQuotientGrading ℳ K) := by
  let hdec :
      DirectSum.Decomposition
        (fun n ↦ quotient_grading ℳ (K.restrictScalars k) n) :=
    @homogeneous_quotient_module_decomposition k _ _ M _ _
      ℳ _ (K.restrictScalars k) hK
  have hpieces :
      scalarQuotientGrading ℳ K =
        fun n ↦ quotient_grading ℳ (K.restrictScalars k) n := by
    -- The scalar quotient grading is definitionally the componentwise quotient grading after
    -- restricting the `S`-submodule to a `k`-submodule.
    funext n
    rfl
  -- Reuse the owner-level homogeneous quotient decomposition on the scalar quotient spelling.
  simpa [hpieces] using hdec

/-- Helper for Chap10 Lemma 10 58 10: every homogeneous scalar element of `(a)Q` has a
homogeneous scalar preimage one degree lower. -/
private theorem exists_scalarHomogeneous_preimage_of_mem_smul_top
    {Q : Type u} [AddCommGroup Q] [Module k Q] [Module S Q] [IsScalarTower k S Q]
    (Qgr : ℤ → Submodule k Q)
    [DirectSum.Decomposition Qgr] [SetLike.GradedSMul 𝒜 Qgr]
    {a : S} (ha_deg : a ∈ 𝒜 1)
    {e : ℤ} {z : Q} (hz_deg : z ∈ Qgr e)
    (hzN : z ∈ ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q))) :
    ∃ y : Qgr (e - 1), a • (y : Q) = z := by
  rw [Submodule.ideal_span_singleton_smul] at hzN
  rw [Submodule.mem_smul_pointwise_iff_exists] at hzN
  rcases hzN with ⟨m, -, rfl⟩
  refine ⟨DirectSum.decompose Qgr m (e - 1), ?_⟩
  -- Project the representative to degree `e - 1`, then reinsert the degree-one scalar.
  calc
    a • ((DirectSum.decompose Qgr m (e - 1) : Qgr (e - 1)) : Q) =
        ((DirectSum.decompose Qgr (a • m) ((e - 1) + 1) : Qgr ((e - 1) + 1)) : Q) := by
          symm
          exact scalar_decompose_degree_succ_smul_eq (ℳ := Qgr) ha_deg m (e - 1)
    _ = ((DirectSum.decompose Qgr (a • m) e : Qgr e) : Q) := by
          have he_shift : (e - 1) + 1 = e := by
            linarith
          rw [he_shift]
    _ = a • m := by
          simpa using (DirectSum.decompose_of_mem_same Qgr hz_deg)

/-- Helper for Chap10 Lemma 10 58 10: the principal image `(a)Q` is homogeneous for scalar
graded pieces when `a` has degree `1`. -/
private theorem scalarDegreeOneSmulTop_isHomogeneous
    {Q : Type u} [AddCommGroup Q] [Module k Q] [Module S Q] [IsScalarTower k S Q]
    (Qgr : ℤ → Submodule k Q)
    [DirectSum.Decomposition Qgr] [SetLike.GradedSMul 𝒜 Qgr]
    {a : S} (ha_deg : a ∈ 𝒜 1) :
    (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q)) : Submodule S Q).restrictScalars k
      |>.IsHomogeneous Qgr := by
  intro n z hzN
  change z ∈ (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q)) : Submodule S Q) at hzN
  change
    (((DirectSum.decompose Qgr z n : Qgr n) : Q)) ∈
      (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q)) : Submodule S Q)
  rw [Submodule.ideal_span_singleton_smul] at hzN ⊢
  rw [Submodule.mem_smul_pointwise_iff_exists] at hzN ⊢
  rcases hzN with ⟨m, -, rfl⟩
  refine ⟨((DirectSum.decompose Qgr m (n - 1) : Qgr (n - 1)) : Q), by simp, ?_⟩
  -- Project the representative to degree `n - 1`, then reinsert the degree-one scalar `a`.
  calc
    a • ((DirectSum.decompose Qgr m (n - 1) : Qgr (n - 1)) : Q) =
        ((DirectSum.decompose Qgr (a • m) ((n - 1) + 1) : Qgr ((n - 1) + 1)) : Q) := by
          symm
          exact scalar_decompose_degree_succ_smul_eq (ℳ := Qgr) ha_deg m (n - 1)
    _ = ((DirectSum.decompose Qgr (a • m) n : Qgr n) : Q) := by
          have hn_shift : (n - 1) + 1 = n := by
            linarith
          rw [hn_shift]

/-- Helper for Chap10 Lemma 10 58 10: in degree `n`, the scalar piece of `(a)Q` has the same
`k`-dimension as the range of multiplication by `a`. -/
private theorem scalarDegreeOneImagePiece_finrank_eq
    {Q : Type u} [AddCommGroup Q] [Module k Q] [Module S Q] [IsScalarTower k S Q]
    (Qgr : ℤ → Submodule k Q)
  [DirectSum.Decomposition Qgr] [SetLike.GradedSMul 𝒜 Qgr]
  {a : S} (ha_deg : a ∈ 𝒜 1) (n : ℤ) :
    Module.finrank k
        ((Qgr n).comap
          (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q)).restrictScalars k).subtype) =
      Module.finrank k (LinearMap.range (scalarDegreeOneMulMap (ℳ := Qgr) ha_deg n)) := by
  let N : Submodule S Q := ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q))
  let μ : Qgr (n - 1) →ₗ[k] Qgr n := scalarDegreeOneMulMap (ℳ := Qgr) ha_deg n
  have hmaps :
      ((Qgr n).comap (N.restrictScalars k).subtype).map ((N.restrictScalars k).subtype) =
        (LinearMap.range μ).map (Qgr n).subtype := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      -- Every degree-`n` vector in `(a)Q` comes from a homogeneous vector of degree `n - 1`.
      obtain ⟨y, hy⟩ :=
        exists_scalarHomogeneous_preimage_of_mem_smul_top
          (Qgr := Qgr) (ha_deg := ha_deg) (e := n) (z := (y : Q)) hy (by
            simpa [N] using y.2)
      refine ⟨μ y, ⟨y, rfl⟩, ?_⟩
      simpa [μ] using hy
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, rfl⟩
      -- A point in the range is visibly an element of the principal image `(a)Q`.
      refine ⟨⟨a • (z : Q), ?_⟩, ?_, rfl⟩
      · change a • (z : Q) ∈ N
        change a • (z : Q) ∈ (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S Q)) : Submodule S Q)
        rw [Submodule.ideal_span_singleton_smul]
        rw [Submodule.mem_smul_pointwise_iff_exists]
        exact ⟨(z : Q), by simp, rfl⟩
      · change a • (z : Q) ∈ Qgr n
        exact (μ z).2
  let eD :=
    (N.restrictScalars k).equivSubtypeMap ((Qgr n).comap (N.restrictScalars k).subtype)
  let eR := (Qgr n).equivSubtypeMap (LinearMap.range μ)
  -- Compare both owners after mapping them into the same ambient submodule of `Q`.
  calc
    Module.finrank k ((Qgr n).comap (N.restrictScalars k).subtype) =
        Module.finrank k (((Qgr n).comap (N.restrictScalars k).subtype).map
          ((N.restrictScalars k).subtype)) := by
          exact LinearEquiv.finrank_eq eD
    _ = Module.finrank k ((LinearMap.range μ).map (Qgr n).subtype) := by
          rw [hmaps]
    _ = Module.finrank k (LinearMap.range μ) := by
          exact (LinearEquiv.finrank_eq eR).symm

/-- Helper for Chap10 Lemma 10 58 10: if the first variable acts trivially, then the scalar
grading can be viewed as a grading over the quotient ring and hence over the smaller polynomial
ring obtained by deleting that variable. -/
private theorem descendedGradedSmulOfFirstVariableAnnihilated
    {Q : Type u} [AddCommGroup Q] [Module k Q]
    [Module (MvPolynomial (Fin (d + 1)) k) Q]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) Q]
    (Qgr : ℤ → Submodule k Q)
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) Qgr]
    (hann :
      Ideal.span
          ({(MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)} : Set _) ≤
        Module.annihilator (MvPolynomial (Fin (d + 1)) k) Q) :
    let I : Ideal (MvPolynomial (Fin (d + 1)) k) :=
      Ideal.span
        ({(MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)} : Set _)
    let hTors :
        Module.IsTorsionBySet (MvPolynomial (Fin (d + 1)) k) Q (I : Set _) :=
      (Module.isTorsionBySet_iff_subset_annihilator
        (MvPolynomial (Fin (d + 1)) k) Q).2 hann
    letI : Module ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q :=
      Module.IsTorsionBySet.module hTors
    letI : Algebra (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
      RingHom.toAlgebra
        (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm.toRingHom
    letI : Module (MvPolynomial (Fin d) k) Q :=
      Module.compHom Q (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm.toRingHom
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr := by
  let I : Ideal (MvPolynomial (Fin (d + 1)) k) :=
    Ideal.span
      ({(MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)} : Set _)
  let hTors :
      Module.IsTorsionBySet (MvPolynomial (Fin (d + 1)) k) Q (I : Set _) :=
    (Module.isTorsionBySet_iff_subset_annihilator
      (MvPolynomial (Fin (d + 1)) k) Q).2 hann
  letI : Module ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q :=
    Module.IsTorsionBySet.module hTors
  letI : Algebra (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    RingHom.toAlgebra
      (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm.toRingHom
  letI : Module (MvPolynomial (Fin d) k) Q :=
    Module.compHom Q (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm.toRingHom
  refine
    { smul_mem := ?_ }
  intro i j p x hp hx
  -- Rewrite the descended smaller-ring action through the quotient-by-`X 0` description.
  change
    (((mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d).symm p) • (x : Q)) ∈
      Qgr ((i : ℕ) +ᵥ j)
  rw [mvPolynomialQuotientFirstVariableAlgEquiv_symm_rename_succ (k := k) d p]
  -- The quotient scalar class acts by its chosen representative, and `rename Fin.succ`
  -- preserves homogeneous degree.
  simpa [Module.IsTorsionBySet.mk_smul hTors (MvPolynomial.rename Fin.succ p) (x : Q)] using
    (SetLike.GradedSMul.smul_mem
      (mvPolynomial_rename_succ_mem_homogeneousSubmodule (k := k) (d := d) i hp)
      hx)

/-- Helper for Chap10 Lemma 10 58 10: if `X 0` annihilates a scalar graded module over
`k[X₀, …, X_d]`, then the grading descends to the smaller polynomial ring
`k[X₁, …, X_d]` and the induction hypothesis applies. -/
private theorem scalarAnnihilatedByFirstVariable_finrank_isNumericalPolynomial_standard
    (hind :
      ∀ {Q : Type u} [AddCommGroup Q] [Module k Q]
        [Module (MvPolynomial (Fin d) k) Q]
        [IsScalarTower k (MvPolynomial (Fin d) k) Q]
        [Module.Finite (MvPolynomial (Fin d) k) Q]
        (Qgr : ℤ → Submodule k Q), [DirectSum.Decomposition Qgr] →
        [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr] →
        (∀ n, Module.Finite k (Qgr n)) →
        IsNumericalPolynomial (fun n ↦ (Module.finrank k (Qgr n) : ℤ)))
    {Q : Type u} [AddCommGroup Q] [Module k Q]
    [Module (MvPolynomial (Fin (d + 1)) k) Q]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) Q]
    [Module.Finite (MvPolynomial (Fin (d + 1)) k) Q]
    (Qgr : ℤ → Submodule k Q) [DirectSum.Decomposition Qgr]
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) Qgr]
    (hfinite : ∀ n, Module.Finite k (Qgr n))
    (hX0 : ∀ q : Q,
      ((MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)) • q = 0) :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (Qgr n) : ℤ)) := by
  let I : Ideal (MvPolynomial (Fin (d + 1)) k) :=
    Ideal.span ({(MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)} : Set _)
  have hann : I ≤ Module.annihilator (MvPolynomial (Fin (d + 1)) k) Q := by
    refine Ideal.span_le.2 ?_
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    -- Spell out ideal membership as pointwise annihilation on `Q`.
    simpa [Module.mem_annihilator] using hX0
  let hTors :
      Module.IsTorsionBySet (MvPolynomial (Fin (d + 1)) k) Q (I : Set _) :=
    (Module.isTorsionBySet_iff_subset_annihilator
      (MvPolynomial (Fin (d + 1)) k) Q).2 hann
  letI : Module ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q :=
    Module.IsTorsionBySet.module hTors
  letI : Module.Finite ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin (d + 1)) k)
      ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q
  let e : ((MvPolynomial (Fin (d + 1)) k) ⧸ I) ≃ₐ[k] MvPolynomial (Fin d) k := by
    simpa [I] using (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d)
  let quotientSelfModule :
      Module ((MvPolynomial (Fin (d + 1)) k) ⧸ I) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    Semiring.toModule
  letI : SMul ((MvPolynomial (Fin (d + 1)) k) ⧸ I) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    quotientSelfModule.toSMul
  letI :
      Module ((MvPolynomial (Fin (d + 1)) k) ⧸ I) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    quotientSelfModule
  let smallerRingOnQuotient :
      Module (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    Module.compHom ((MvPolynomial (Fin (d + 1)) k) ⧸ I) e.symm.toRingHom
  letI : SMul (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    smallerRingOnQuotient.toSMul
  letI : Module (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    smallerRingOnQuotient
  letI : Module (MvPolynomial (Fin d) k) Q :=
    Module.compHom Q e.symm.toRingHom
  letI : IsScalarTower k (MvPolynomial (Fin d) k) Q :=
    isScalarTowerCompHomOfAlgebraMapEq
      (A := k) (B := MvPolynomial (Fin d) k)
      (C := (MvPolynomial (Fin (d + 1)) k) ⧸ I) (N := Q)
      e.symm.toRingHom
      (by
        intro c
        -- Constants survive unchanged under the first-variable quotient equivalence.
        simpa using e.symm.commutes c)
  letI :
      IsScalarTower (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q :=
    by
      -- Pin the scalar-action roles explicitly so Lean reuses the pulled-back smaller-ring action.
      exact
        (SMul.comp.isScalarTower
          (M := (MvPolynomial (Fin (d + 1)) k) ⧸ I)
          (N := MvPolynomial (Fin d) k)
          (α := (MvPolynomial (Fin (d + 1)) k) ⧸ I)
          (β := Q)
          e.symm.toRingHom)
  letI : Module.Finite (MvPolynomial (Fin d) k) ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
    by
      let eLinear :
          MvPolynomial (Fin d) k ≃ₗ[MvPolynomial (Fin d) k]
            ((MvPolynomial (Fin (d + 1)) k) ⧸ I) :=
        Module.compHom.toLinearEquiv e.symm.toRingEquiv
      -- Transport finiteness along the explicit smaller-ring linear equivalence of the quotient.
      exact Module.Finite.equiv eLinear
  letI : Module.Finite (MvPolynomial (Fin d) k) Q :=
    Module.Finite.trans ((MvPolynomial (Fin (d + 1)) k) ⧸ I) Q
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr :=
    descendedGradedSmulOfFirstVariableAnnihilated (k := k) (d := d) (Qgr := Qgr) hann
  -- After factoring the action through the quotient by `X 0`, the induction hypothesis applies.
  exact hind (Q := Q) Qgr hfinite

/-- Helper for Chap10 Lemma 10 58 10: the quotient
`ker ((a • id)^(i + 1)) / ker ((a • id)^i)` is annihilated by `a`. -/
private theorem kernelPowStageQuotient_smul_eq_zero
    {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin (d + 1)) k) M]
    {a : MvPolynomial (Fin (d + 1)) k} (i : ℕ) :
    let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
      fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
    let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (i + 1)
    let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow i).comap H.subtype
    ∀ q : H ⧸ L', a • q = 0 := by
  dsimp
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  -- Represent the quotient class by `x ∈ ker ((a • id)^(i + 1))` and show `a • x`
  -- lands in the previous kernel stage.
  apply (Submodule.Quotient.mk_eq_zero _).2
  change a • (x : M) ∈ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ i)
  change
    ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ i) (a • (x : M)) = 0
  simpa [pow_succ, LinearMap.comp_apply] using x.2

/-- Helper for Chap10 Lemma 10 58 10: the successive quotient
`ker ((X 0 • id)^(i + 1)) / ker ((X 0 • id)^i)` has numerical-polynomial scalar degree
dimensions because `X 0` kills it. -/
private theorem kernelPowSuccQuotient_finrank_isNumericalPolynomial
    (hind :
      ∀ {Q : Type u} [AddCommGroup Q] [Module k Q]
        [Module (MvPolynomial (Fin d) k) Q]
        [IsScalarTower k (MvPolynomial (Fin d) k) Q]
        [Module.Finite (MvPolynomial (Fin d) k) Q]
        (Qgr : ℤ → Submodule k Q), [DirectSum.Decomposition Qgr] →
        [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr] →
        (∀ n, Module.Finite k (Qgr n)) →
        IsNumericalPolynomial (fun n ↦ (Module.finrank k (Qgr n) : ℤ)))
    {M : Type u} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (d + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) M]
    [Module.Finite (MvPolynomial (Fin (d + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ℳ]
    (hfinite : ∀ n, Module.Finite k (ℳ n))
    {a : MvPolynomial (Fin (d + 1)) k}
    (ha_eq_X0 : a = MvPolynomial.X 0)
    (ha_deg : a ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 1)
    (i : ℕ) :
    let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
      fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
    let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (i + 1)
    let 𝒦 : ℤ → Submodule k H := fun n ↦ (ℳ n).comap ((H.restrictScalars k).subtype)
    let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow i).comap H.subtype
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (scalarQuotientGrading 𝒦 L' n) : ℤ)) :=
    by
  classical
  dsimp
  let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
    fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
  let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (i + 1)
  let 𝒦 : ℤ → Submodule k H := fun n ↦ (ℳ n).comap ((H.restrictScalars k).subtype)
  let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow i).comap H.subtype
  let hH_hom : (H.restrictScalars k).IsHomogeneous ℳ :=
    scalar_degree_one_mul_kernel_pow_isHomogeneous (ℳ := ℳ) ha_deg (i + 1)
  letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) H hH_hom
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) 𝒦 :=
    scalarSubmoduleGrading_setLikeGradedSMul (ℳ := ℳ) H
  have hL'_hom : (L'.restrictScalars k).IsHomogeneous 𝒦 := by
    intro n x hx
    -- Compare the inherited `H`-decomposition with the ambient decomposition on `M`.
    change ((((DirectSum.decompose 𝒦 x n : 𝒦 n) : H) : M)) ∈ Kpow i
    have hambient :
        (((DirectSum.decompose ℳ (x : M) n : ℳ n) : M)) ∈ Kpow i :=
      (scalar_degree_one_mul_kernel_pow_isHomogeneous (ℳ := ℳ) ha_deg i) n hx
    have hdecomp_eq :
        ((((DirectSum.decompose 𝒦 x n : 𝒦 n) : H) : M)) =
          (((DirectSum.decompose ℳ (x : M) n : ℳ n) : M)) := by
      simpa using
        (scalarSubmoduleGrading_decompose_coe_eq (ℳ := ℳ) (K := H) (hK := hH_hom) (x := x) (n := n))
    rw [hdecomp_eq]
    exact hambient
  letI : DirectSum.Decomposition (scalarQuotientGrading 𝒦 L') :=
    scalarQuotientGrading_decomposition (ℳ := 𝒦) L' hL'_hom
  letI :
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)
        (scalarQuotientGrading 𝒦 L') :=
    scalarQuotientGrading_setLikeGradedSMul (ℳ := 𝒦) L'
  have h𝒦finite : ∀ n, Module.Finite k (𝒦 n) := by
    intro n
    -- Each inherited degree piece stays finite-dimensional over `k`.
    simpa [𝒦] using scalarSubmoduleGrading_moduleFinite (ℳ := ℳ) H hfinite n
  have hX0 :
      ∀ q : H ⧸ L',
        ((MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)) • q =
          (0 : H ⧸ L') := by
    intro q
    have ha_zero : a • q = 0 := by
      simpa [Kpow, H, L'] using
        (kernelPowStageQuotient_smul_eq_zero (k := k) (d := d) (M := M) (a := a) i q)
    -- Rewrite the annihilator from `a` to the fixed first variable.
    simpa [ha_eq_X0] using ha_zero
  -- Route correction: descend the successor quotient only after proving that `X 0`
  -- annihilates it, then reuse the smaller-variable theorem on the quotient grading.
  exact
    scalarAnnihilatedByFirstVariable_finrank_isNumericalPolynomial_standard
      (k := k) (d := d) hind
      (Qgr := scalarQuotientGrading 𝒦 L')
      (fun n ↦ scalarQuotientGrading_moduleFinite (ℳ := 𝒦) L' h𝒦finite n)
      hX0

/-- Helper for Chap10 Lemma 10 58 10: the nested kernel degree piece inside the successor stage
has the same `k`-dimension as the ambient stage-`r` degree piece. -/
private theorem kernelPowNestedDegreePiece_finrank_eq
    {M : Type u} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (d + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) M]
    {a : MvPolynomial (Fin (d + 1)) k} (ℳ : ℤ → Submodule k M)
    (r : ℕ) (n : ℤ) :
    let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
      fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
    let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (r + 1)
    let 𝒦 : ℤ → Submodule k H := fun m ↦ (ℳ m).comap ((H.restrictScalars k).subtype)
    let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow r).comap H.subtype
    Module.finrank k ((𝒦 n).comap ((L'.restrictScalars k).subtype)) =
      Module.finrank k ((ℳ n).comap (((Kpow r).restrictScalars k).subtype)) := by
  classical
  dsimp
  let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
    fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
  let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (r + 1)
  let 𝒦 : ℤ → Submodule k H := fun m ↦ (ℳ m).comap ((H.restrictScalars k).subtype)
  let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow r).comap H.subtype
  have hKpow_le_H : Kpow r ≤ H := by
    intro x hx
    -- One more multiplication by `a` still kills anything already in the `r`-th kernel.
    change
      ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ (r + 1)) x = 0
    rw [pow_succ, Module.End.mul_apply]
    simpa using congrArg (fun y : M ↦ a • y) hx
  let f : (L'.restrictScalars k) →ₗ[k] ((Kpow r).restrictScalars k) :=
    { toFun := fun x ↦ ⟨(x : M), x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ((Kpow r).restrictScalars k) ↦ (z : M)) hxy
  have hmap :
      ((𝒦 n).comap ((L'.restrictScalars k).subtype)).map f =
        ((ℳ n).comap (((Kpow r).restrictScalars k).subtype)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨⟨⟨(y : M), hKpow_le_H y.2⟩, y.2⟩, ?_⟩
      exact ⟨hy, rfl⟩
  -- Transport the nested subtype owner along the canonical inclusion `Kpow r ≤ Kpow (r + 1)`.
  calc
    Module.finrank k ((𝒦 n).comap ((L'.restrictScalars k).subtype)) =
        Module.finrank k (((𝒦 n).comap ((L'.restrictScalars k).subtype)).map
          f) := by
          exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf _)
    _ = Module.finrank k ((ℳ n).comap (((Kpow r).restrictScalars k).subtype)) := by
          rw [hmap]

/-- Helper for Chap10 Lemma 10 58 10: each stage of the kernel filtration of multiplication by a
degree-one scalar has a numerical-polynomial scalar Hilbert function. -/
private theorem kernelPowStage_finrank_isNumericalPolynomial
    (hind :
      ∀ {Q : Type u} [AddCommGroup Q] [Module k Q]
        [Module (MvPolynomial (Fin d) k) Q]
        [IsScalarTower k (MvPolynomial (Fin d) k) Q]
        [Module.Finite (MvPolynomial (Fin d) k) Q]
        (Qgr : ℤ → Submodule k Q), [DirectSum.Decomposition Qgr] →
        [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr] →
        (∀ n, Module.Finite k (Qgr n)) →
        IsNumericalPolynomial (fun n ↦ (Module.finrank k (Qgr n) : ℤ)))
    {M : Type u} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (d + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) M]
    [Module.Finite (MvPolynomial (Fin (d + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ℳ]
    (hfinite : ∀ n, Module.Finite k (ℳ n))
    {a : MvPolynomial (Fin (d + 1)) k}
    (ha_eq_X0 : a = MvPolynomial.X 0)
    (ha_deg : a ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 1)
    (r : ℕ) :
    IsNumericalPolynomial
      (fun n ↦
        (Module.finrank k
          ((ℳ n).comap
            (((LinearMap.ker
              ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ r)).restrictScalars
                k).subtype)) : ℤ)) := by
  induction r with
  | zero =>
      refine ⟨0, fun _ ↦ 0, Filter.EventuallyEq.of_eq ?_⟩
      funext n
      -- The zeroth kernel is `⊥`, so every scalar degree piece has dimension zero.
      have hker0 :
          LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ 0) = ⊥ := by
        ext x
        simp [pow_zero]
      rw [hker0]
      simp
  | succ r ihr =>
      classical
      let Kpow : ℕ → Submodule (MvPolynomial (Fin (d + 1)) k) M :=
        fun j ↦ LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ j)
      let H : Submodule (MvPolynomial (Fin (d + 1)) k) M := Kpow (r + 1)
      let 𝒦 : ℤ → Submodule k H := fun n ↦ (ℳ n).comap ((H.restrictScalars k).subtype)
      let L' : Submodule (MvPolynomial (Fin (d + 1)) k) H := (Kpow r).comap H.subtype
      let hH_hom : (H.restrictScalars k).IsHomogeneous ℳ :=
        scalar_degree_one_mul_kernel_pow_isHomogeneous (ℳ := ℳ) ha_deg (r + 1)
      letI : DirectSum.Decomposition 𝒦 := scalarSubmoduleGrading_decomposition (ℳ := ℳ) H hH_hom
      letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) 𝒦 :=
        scalarSubmoduleGrading_setLikeGradedSMul (ℳ := ℳ) H
      have hL'_hom : (L'.restrictScalars k).IsHomogeneous 𝒦 := by
        intro n x hx
        -- Compare the inherited `H`-decomposition with the ambient decomposition on `M`.
        change ((((DirectSum.decompose 𝒦 x n : 𝒦 n) : H) : M)) ∈ Kpow r
        have hambient :
            (((DirectSum.decompose ℳ (x : M) n : ℳ n) : M)) ∈ Kpow r :=
          (scalar_degree_one_mul_kernel_pow_isHomogeneous (ℳ := ℳ) ha_deg r) n hx
        have hdecomp_eq :
            ((((DirectSum.decompose 𝒦 x n : 𝒦 n) : H) : M)) =
              (((DirectSum.decompose ℳ (x : M) n : ℳ n) : M)) := by
          simpa using
            (scalarSubmoduleGrading_decompose_coe_eq
              (ℳ := ℳ) (K := H) (hK := hH_hom) (x := x) (n := n))
        rw [hdecomp_eq]
        exact hambient
      letI : DirectSum.Decomposition (scalarQuotientGrading 𝒦 L') :=
        scalarQuotientGrading_decomposition (ℳ := 𝒦) L' hL'_hom
      letI :
          SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)
            (scalarQuotientGrading 𝒦 L') :=
        scalarQuotientGrading_setLikeGradedSMul (ℳ := 𝒦) L'
      have h𝒦finite : ∀ n, Module.Finite k (𝒦 n) := by
        intro n
        -- Each inherited kernel-stage degree piece stays finite-dimensional over `k`.
        simpa [𝒦] using scalarSubmoduleGrading_moduleFinite (ℳ := ℳ) H hfinite n
      have hkernel :
          IsNumericalPolynomial
            (fun n ↦
              (Module.finrank k ((𝒦 n).comap ((L'.restrictScalars k).subtype)) : ℤ)) := by
        refine IsNumericalPolynomial.congr ihr ?_
        exact Filter.EventuallyEq.of_eq <| by
          ext n
          simpa [Kpow, H, 𝒦, L'] using
            (kernelPowNestedDegreePiece_finrank_eq
              (k := k) (d := d) (M := M) (a := a) (ℳ := ℳ) r n)
      have hquotient :
          IsNumericalPolynomial
            (fun n ↦ (Module.finrank k (scalarQuotientGrading 𝒦 L' n) : ℤ)) := by
        -- The successive quotient is killed by `X 0`, so the descended induction closes it.
        simpa [Kpow, H, 𝒦, L'] using
          (kernelPowSuccQuotient_finrank_isNumericalPolynomial
            (k := k) (d := d) hind (ℳ := ℳ) hfinite (a := a) ha_eq_X0 (ha_deg := ha_deg) r)
      have hparts :
          IsNumericalPolynomial (fun n ↦ (Module.finrank k (𝒦 n) : ℤ)) :=
        scalarHomogeneousSubmodule_finrank_isNumericalPolynomial_of_parts
          (ℳ := 𝒦) L' h𝒦finite hkernel hquotient
      -- Assemble the successor stage from the nested kernel branch and the quotient branch.
      refine IsNumericalPolynomial.congr hparts ?_
      exact Filter.EventuallyEq.of_eq <| by
        funext n
        rfl

/-- Helper for Chap10 Lemma 10 58 10: once multiplication by a degree-one scalar is injective on
`M ⧸ K`, the scalar quotient Hilbert function is numerical polynomial via the first-difference
formula. -/
private theorem successorQuotient_finrank_isNumericalPolynomial
    (hind :
      ∀ {Q : Type u} [AddCommGroup Q] [Module k Q]
        [Module (MvPolynomial (Fin d) k) Q]
        [IsScalarTower k (MvPolynomial (Fin d) k) Q]
        [Module.Finite (MvPolynomial (Fin d) k) Q]
        (Qgr : ℤ → Submodule k Q), [DirectSum.Decomposition Qgr] →
        [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) Qgr] →
        (∀ n, Module.Finite k (Qgr n)) →
        IsNumericalPolynomial (fun n ↦ (Module.finrank k (Qgr n) : ℤ)))
    {M : Type u} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (d + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (d + 1)) k) M]
    [Module.Finite (MvPolynomial (Fin (d + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ℳ]
    (hfinite : ∀ n, Module.Finite k (ℳ n))
    (K : Submodule (MvPolynomial (Fin (d + 1)) k) M)
    (hK : (K.restrictScalars k).IsHomogeneous ℳ)
    {a : MvPolynomial (Fin (d + 1)) k}
    (ha_eq_X0 : a = MvPolynomial.X 0)
    (ha_deg : a ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 1)
    (hinj :
      Function.Injective
        ((a • LinearMap.id :
          M ⧸ K →ₗ[MvPolynomial (Fin (d + 1)) k] M ⧸ K))) :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (scalarQuotientGrading ℳ K n) : ℤ)) := by
  let Qgr : ℤ → Submodule k (M ⧸ K) := scalarQuotientGrading ℳ K
  let N : Submodule (MvPolynomial (Fin (d + 1)) k) (M ⧸ K) :=
    (Ideal.span ({a} : Set (MvPolynomial (Fin (d + 1)) k))) •
      (⊤ : Submodule (MvPolynomial (Fin (d + 1)) k) (M ⧸ K))
  letI : DirectSum.Decomposition Qgr :=
    scalarQuotientGrading_decomposition (ℳ := ℳ) K hK
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) Qgr :=
    scalarQuotientGrading_setLikeGradedSMul (ℳ := ℳ) K
  have hQfinite : ∀ n, Module.Finite k (Qgr n) := by
    intro n
    -- The stabilized quotient still has finite-dimensional scalar degree pieces.
    simpa [Qgr] using scalarQuotientGrading_moduleFinite (ℳ := ℳ) K hfinite n
  have hN_hom : (N.restrictScalars k).IsHomogeneous Qgr := by
    -- The principal image `(a)(M/K)` is homogeneous because `a` has degree one.
    simpa [Qgr, N] using scalarDegreeOneSmulTop_isHomogeneous (Qgr := Qgr) (ha_deg := ha_deg)
  letI : DirectSum.Decomposition (scalarQuotientGrading Qgr N) :=
    scalarQuotientGrading_decomposition (ℳ := Qgr) N hN_hom
  letI :
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)
        (scalarQuotientGrading Qgr N) :=
    scalarQuotientGrading_setLikeGradedSMul (ℳ := Qgr) N
  have hdouble :
      IsNumericalPolynomial
        (fun n ↦ (Module.finrank k (scalarQuotientGrading Qgr N n) : ℤ)) := by
    have hX0 : ∀ q : (M ⧸ K) ⧸ N, a • q = 0 := by
      intro q
      -- The double quotient is the quotient by the principal image `(a)(M / K)`.
      simpa [N] using quotient_smul_eq_zero_of_span_singleton_smul_top a q
    -- After quotienting by `(a)(M / K)`, the first variable acts trivially and we descend.
    exact
      scalarAnnihilatedByFirstVariable_finrank_isNumericalPolynomial_standard
        (k := k) (d := d) hind
        (Qgr := scalarQuotientGrading Qgr N)
        (fun n ↦ scalarQuotientGrading_moduleFinite (ℳ := Qgr) N hQfinite n)
        (by simpa [ha_eq_X0] using hX0)
  have hpred :
      IsNumericalPolynomial
        (fun n ↦
          (Module.finrank k (Qgr n) : ℤ) -
            (Module.finrank k (Qgr (n - 1)) : ℤ)) := by
    refine IsNumericalPolynomial.congr hdouble ?_
    exact Filter.EventuallyEq.of_eq <| by
      ext n
      let μ : Qgr (n - 1) →ₗ[k] Qgr n := scalarDegreeOneMulMap (ℳ := Qgr) ha_deg n
      have hμ_inj : Function.Injective μ := by
        intro x y hxy
        apply Subtype.ext
        apply hinj
        exact congrArg (fun z : Qgr n ↦ (z : M ⧸ K)) hxy
      have hker_zero : Module.finrank k (LinearMap.ker μ) = 0 := by
        have hker_bot : LinearMap.ker μ = ⊥ := LinearMap.ker_eq_bot.mpr hμ_inj
        simpa [hker_bot]
      have hrange_shift :
          Module.finrank k (LinearMap.range μ) = Module.finrank k (Qgr (n - 1)) := by
        simpa [μ, hker_zero] using
          scalarDegreeOneMulMap_finrankExact (ℳ := Qgr) hQfinite ha_deg n
      have hpieceNat :
          Module.finrank k ((Qgr n).comap ((N.restrictScalars k).subtype)) =
            Module.finrank k (Qgr (n - 1)) := by
        rw [scalarDegreeOneImagePiece_finrank_eq (Qgr := Qgr) (ha_deg := ha_deg) n]
        exact hrange_shift
      have hpiece :
          (Module.finrank k ((Qgr n).comap ((N.restrictScalars k).subtype)) : ℤ) =
            (Module.finrank k (Qgr (n - 1)) : ℤ) := by
        exact_mod_cast hpieceNat
      have hadd := scalarHomogeneousSubmodule_finrank_add (ℳ := Qgr) N hQfinite n
      -- Rewrite the principal image term as the previous degree and solve the first difference.
      linarith
  -- The first-difference identity upgrades the descended double quotient theorem to `Qgr`.
  exact IsNumericalPolynomial.of_sub_pred hpred

/-- Helper for Chap10 Lemma 10 58 10: scalar Hilbert-Serre for standard polynomial modules whose
graded pieces are `k`-submodules. -/
private theorem baseSubmoduleGradedPiece_finrank_isNumericalPolynomial_standard
    {M : Type u} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    [Module.Finite S M] (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (hfinite : ∀ n, Module.Finite k (ℳ n)) :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (ℳ n) : ℤ)) := by
  induction d generalizing M with
  | zero =>
      -- The zero-variable standard polynomial ring has no positive homogeneous scalars, so the
      -- scalar Hilbert function is eventually zero by the established base-case helper.
      exact
        scalarGradedPiece_finrank_isNumericalPolynomial_of_irrelevant_eq_bot
          (k := k) (d := 0) (ℳ := ℳ)
          (mvPolynomial_finZero_irrelevant_toIdeal_eq_bot (k := k))
  | succ d ih =>
      -- Route correction: the owner-valued Proposition `10.58.7` applies to `Submodule S M`,
      -- while this theorem needs scalar `k`-submodule pieces. The zero-variable base case above is
      -- now closed. The successor route is deliberately fixed at the first coordinate `X 0`, so
      -- the quotient is the standard `d`-variable polynomial ring by
      -- `mvPolynomialQuotientFirstVariableAlgEquiv`; this avoids the previous arbitrary-generator
      -- transport problem.
      let a : MvPolynomial (Fin (d + 1)) k := MvPolynomial.X 0
      have ha_deg : a ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 1 := by
        -- The chosen coordinate is homogeneous of degree one.
        exact mvPolynomial_X_mem_degree_one (k := k) (d := d + 1) 0
      have hquot_zero :
          (mvPolynomialQuotientFirstVariableAlgEquiv (k := k) d)
            (Ideal.Quotient.mk _
              (MvPolynomial.X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) k)) = 0 := by
        -- The coordinate quotient bridge has been normalized to the univariate quotient by `X`.
        exact mvPolynomialQuotientFirstVariableAlgEquiv_mk_X_zero (k := k) d
      obtain ⟨r, hker_hom, hquot_inj⟩ :=
        scalar_degree_one_stable_kernel_package
          (k := k) (d := d + 1) (M := M) (ℳ := ℳ) ha_deg
      let K : Submodule (MvPolynomial (Fin (d + 1)) k) M :=
        LinearMap.ker ((a • LinearMap.id : M →ₗ[MvPolynomial (Fin (d + 1)) k] M) ^ r)
      have hkernel :
          IsNumericalPolynomial
            (fun n ↦
              (Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) : ℤ)) := by
        -- The kernel branch is the generic kernel-filtration induction specialized to the
        -- stabilized kernel stage.
        simpa [K] using
          kernelPowStage_finrank_isNumericalPolynomial
            (k := k) (d := d) ih (ℳ := ℳ) hfinite rfl (ha_deg := ha_deg) r
      have hquotient :
          IsNumericalPolynomial
            (fun n ↦ (Module.finrank k (scalarQuotientGrading ℳ K n) : ℤ)) := by
        -- The quotient branch uses the descended double quotient and the first-difference formula.
        exact
          successorQuotient_finrank_isNumericalPolynomial
            (k := k) (d := d) ih (ℳ := ℳ) hfinite K hker_hom rfl
            (ha_deg := ha_deg) hquot_inj
      -- The verified assembly step reduces the successor case to the kernel and quotient halves.
      exact
        scalarHomogeneousSubmodule_finrank_isNumericalPolynomial_of_parts
          (ℳ := ℳ) K hfinite hkernel hquotient

/-- Helper for Chap10 Lemma 10 58 10: the quotient degree piece in degree `n`, viewed as a
generator class in `K'_0(k)`. -/
private noncomputable def quotientHilbertGrading_k0Class (n : ℤ) :
    finiteGrothendieckGroup k :=
  let _ : Module.Finite k (quotientHilbertGrading I n) :=
    quotientHilbertGrading_moduleFinite (I := I) (k := k) (d := d) n
  finiteGrothendieckGroupOf k (FGModuleCat.of k (quotientHilbertGrading I n))

/-- Helper for Chap10 Lemma 10 58 10: the field-length map evaluates the quotient
degree-piece class as its `k`-dimension. -/
private theorem quotientHilbertGrading_k0Class_length_eq_finrank
    (n : ℤ) :
    finiteGrothendieckGroup_lengthMap k
        (quotientHilbertGrading_k0Class (I := I) (k := k) (d := d) n) =
      (Module.finrank k (quotientHilbertGrading I n) : ℤ) := by
  let _ : Module.Finite k (quotientHilbertGrading I n) :=
    quotientHilbertGrading_moduleFinite (I := I) (k := k) (d := d) n
  -- Evaluate the canonical length map on the generator and identify field length with finrank.
  rw [quotientHilbertGrading_k0Class, finiteGrothendieckGroup_lengthMap_apply_of]
  simpa [Module.length_eq_finrank]

/-- Helper for Lemma 10.58.10: the remaining Hilbert-Serre bridge should give numerical
polynomiality for the degreewise `k`-dimensions of the quotient grading. -/
private theorem quotientHilbertGrading_finrank_isNumericalPolynomial :
    IsNumericalPolynomial
      (fun n ↦ (Module.finrank k (quotientHilbertGrading I n) : ℤ)) := by
  -- Route correction: the old `K'_0(k)` route reproduced the same owner-valued Hilbert-Serre
  -- blocker. Work directly with the scalar finrank theorem for `k`-submodule graded pieces.
  let _ : Module.Finite S (S ⧸ I.toIdeal) := by
    exact Module.Finite.of_surjective (Submodule.mkQ I.toIdeal) (Submodule.mkQ_surjective _)
  exact
    baseSubmoduleGradedPiece_finrank_isNumericalPolynomial_standard
      (k := k) (d := d) (M := S ⧸ I.toIdeal) (ℳ := quotientHilbertGrading I)
      (fun n ↦ quotientHilbertGrading_moduleFinite (I := I) (k := k) (d := d) n)

/-- Helper for Lemma 10.58.10: postcomposing the `K'_0(k)`-valued quotient Hilbert function with
the field-length map gives the usual numerical Hilbert function. -/
private theorem homogeneousIdealQuotientHilbertFunction_isNumericalPolynomial_aux :
    IsNumericalPolynomial (homogeneousIdealQuotientHilbertFunction I) := by
  -- Rewrite the direct scalar-valued quotient-grading theorem to the file-local Hilbert function.
  exact
    IsNumericalPolynomial.congr
      (quotientHilbertGrading_finrank_isNumericalPolynomial (I := I) (k := k) (d := d))
      (Filter.EventuallyEq.of_eq <| by
        ext n
        exact
          (homogeneousIdealQuotientHilbertFunction_eq_quotient_grading_finrank
            (I := I) (k := k) n))

/-- Helper for Lemma 10.58.10: when `I = ⊥`, the quotient Hilbert function is the ambient Hilbert
function of the polynomial ring. -/
private theorem homogeneousIdealQuotientHilbertFunction_eq_ambient_of_bot
    (hI : I = ⊥) :
    homogeneousIdealQuotientHilbertFunction I = ambientHilbertFunction d := by
  ext n
  by_cases hn : 0 ≤ n
  · -- In nonnegative degree, quotienting by `⊥` is the identity on the ambient homogeneous piece.
    rw [homogeneousIdealQuotientHilbertFunction_of_nonneg (I := I) n hn, ambientHilbertFunction,
      if_pos hn]
    subst hI
    have hmap :
        Module.finrank k
            (homogeneousIdealQuotientDegreePiece
              (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
              n.toNat) =
          Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat) := by
      let e : S ≃ₗ[k] S ⧸ (⊥ : Ideal S) := (AlgEquiv.quotientBot k S).symm.toLinearEquiv
      -- Replace the mapped submodule by its image under the quotient-by-`⊥` linear equivalence.
      simpa [e, homogeneousIdealQuotientDegreePiece] using
        (LinearEquiv.finrank_eq (e.submoduleMap (MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat))).symm
    calc
      (Module.finrank k
          (homogeneousIdealQuotientDegreePiece
            (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
            n.toNat) : ℤ) =
          Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat) := by
            exact_mod_cast hmap
      _ = d.multichoose n.toNat := by
            exact_mod_cast ambient_degree_piece_finrank_eq_multichoose (k := k) (d := d) n.toNat
  · -- Negative degrees are zero on both sides by definition.
    have hneg : n < 0 := by linarith
    rw [homogeneousIdealQuotientHilbertFunction_of_neg (I := I) hneg, ambientHilbertFunction, if_neg hn]

/-- Helper for Lemma 10.58.10: if the homogeneous ideal is all of `S`, then every quotient degree
piece vanishes. -/
private theorem homogeneousIdealQuotientHilbertFunction_eq_zero_of_top
    (hI : I = ⊤) :
    homogeneousIdealQuotientHilbertFunction I = fun _ ↦ (0 : ℤ) := by
  ext n
  by_cases hn : 0 ≤ n
  · rw [homogeneousIdealQuotientHilbertFunction_of_nonneg (I := I) n hn]
    subst hI
    -- After quotienting by `⊤`, the codomain is subsingleton, so every degree piece has dimension
    -- zero.
    have hfin :
        Module.finrank k
            (homogeneousIdealQuotientDegreePiece
              (⊤ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
              n.toNat) = 0 := by
      have hbot :
          homogeneousIdealQuotientDegreePiece
              (⊤ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin d) k))
              n.toNat =
            ⊥ := by
        -- Unpack the mapped degree piece: every quotient class modulo `⊤` is zero.
        rw [homogeneousIdealQuotientDegreePiece, Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨y, -, rfl⟩
        change (Ideal.Quotient.mk (⊤ : Ideal S)) (y : S) = 0
        exact (Ideal.Quotient.eq_zero_iff_mem).2 (by simp)
      rw [hbot]
      let _ :
          Module.Free k ↥(⊥ : Submodule k (S ⧸ (⊤ : Ideal S))) :=
        Module.Free.of_subsingleton k _
      simpa using
        (Module.finrank_eq_zero_of_subsingleton k
          ↥(⊥ : Submodule k (S ⧸ (⊤ : Ideal S))))
    exact_mod_cast hfin
  · have hneg : n < 0 := by linarith
    rw [homogeneousIdealQuotientHilbertFunction_of_neg (I := I) hneg]

/-- Helper for Lemma 10.58.10: a nonzero proper homogeneous ideal of `k[X₁, …, X_d]` contains a
nonzero homogeneous element of positive degree. -/
private theorem exists_nonzero_positive_degree_homogeneous_mem_of_nonbot_ne_top
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ (e : ℕ) (f : S),
      0 < e ∧ f ≠ 0 ∧ f ∈ I.toIdeal ∧ f ∈ 𝒜 e := by
  classical
  have hnonzero : ∃ z : S, z ∈ I.toIdeal ∧ z ≠ 0 := by
    by_contra h
    have hbotIdeal : I.toIdeal = ⊥ := by
      apply le_antisymm
      · intro z hz
        by_contra hz0
        exact h ⟨z, hz, hz0⟩
      · exact bot_le
    exact hI0 ((HomogeneousIdeal.eq_bot_iff I).2 hbotIdeal)
  obtain ⟨z, hzI, hz0⟩ := hnonzero
  have hz_components : ∀ n, (DirectSum.decompose 𝒜 z n : S) ∈ I := by
    exact (Ideal.IsHomogeneous.mem_iff 𝒜 I.isHomogeneous).1 hzI
  have hnot_all_zero : ¬ ∀ n, (DirectSum.decompose 𝒜 z n : S) = 0 := by
    intro hzall
    apply hz0
    simpa [hzall] using (DirectSum.sum_support_decompose 𝒜 z).symm
  obtain ⟨e, he⟩ := not_forall.mp hnot_all_zero
  let f : S := DirectSum.decompose 𝒜 z e
  have hf_ne : f ≠ 0 := he
  have hf_mem : f ∈ I.toIdeal := by
    exact hz_components e
  have hf_hom : f ∈ 𝒜 e := SetLike.coe_mem (DirectSum.decompose 𝒜 z e)
  have he_pos : 0 < e := by
    by_contra hepos
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hepos
    have hf_deg0 : f ∈ 𝒜 0 := by simpa [f, he0] using hf_hom
    have hf_const : f ∈ (1 : Submodule k S) := by
      simpa [MvPolynomial.homogeneousSubmodule_zero] using hf_deg0
    rw [Submodule.one_eq_range] at hf_const
    obtain ⟨c, hc⟩ := hf_const
    have hc_poly : MvPolynomial.C c = f := by
      simpa [f] using hc
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hf_ne
      rw [← hc_poly, hc0]
      simp
    have hunit_mem : (1 : S) ∈ I.toIdeal := by
      have hmul_mem : MvPolynomial.C c⁻¹ * MvPolynomial.C c ∈ I.toIdeal := by
        exact Ideal.mul_mem_left I.toIdeal (MvPolynomial.C c⁻¹) (hc_poly ▸ hf_mem)
      have hprod_eq : MvPolynomial.C c⁻¹ * MvPolynomial.C c = (1 : S) := by
        calc
          MvPolynomial.C c⁻¹ * MvPolynomial.C c = MvPolynomial.C (c⁻¹ * c) := by
            symm
            exact map_mul (MvPolynomial.C : k →+* S) c⁻¹ c
          _ = 1 := by
            simp [hc_ne]
      exact hprod_eq ▸ hmul_mem
    exact hItop ((HomogeneousIdeal.eq_top_iff I).2 ((Ideal.eq_top_iff_one I.toIdeal).2 hunit_mem))
  exact ⟨e, f, he_pos, hf_ne, hf_mem, hf_hom⟩

/-- Helper for Lemma 10.58.10: each ambient degree piece `S_n` is finite-dimensional over `k`. -/
private theorem ambient_degree_piece_moduleFinite (n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin d) k n) := by
  classical
  let _ : Fintype {m : Fin d →₀ ℕ // m.degree = n} :=
    Fintype.ofEquiv ↥((Finset.univ : Finset (Fin d)).finsuppAntidiag n)
      (degree_exponent_subtype_equiv_finsuppAntidiag d n).symm
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let e :
      Finsupp.supported k k {m : Fin d →₀ ℕ | m.degree = n} ≃ₗ[k]
        {m : Fin d →₀ ℕ // m.degree = n} →₀ k :=
    Finsupp.supportedEquivFinsupp (M := k) (R := k) {m : Fin d →₀ ℕ | m.degree = n}
  exact Module.Finite.equiv e.symm

/-- Helper for Lemma 10.58.10: the degree-`n` part `I_n = I ∩ S_n` is finite-dimensional. -/
private theorem homogeneousIdealDegreePiece_moduleFinite (n : ℕ) :
    Module.Finite k (homogeneousIdealDegreePiece I n) := by
  let _ : Module.Finite k (𝒜 n) := ambient_degree_piece_moduleFinite (k := k) (d := d) n
  exact Module.Finite.of_injective (homogeneousIdealDegreePiece I n).subtype
    (Submodule.injective_subtype _)

/-- Helper for Lemma 10.58.10: the quotient degree piece `(S / I)_n` is finite-dimensional as the
image of the ambient degree-`n` piece under the quotient map. -/
private theorem homogeneousIdealQuotientDegreePiece_moduleFinite (n : ℕ) :
    Module.Finite k (homogeneousIdealQuotientDegreePiece I n) := by
  let _ : Module.Finite k (𝒜 n) := ambient_degree_piece_moduleFinite (k := k) (d := d) n
  let q : 𝒜 n →ₗ[k] homogeneousIdealQuotientDegreePiece I n :=
    { toFun := fun x ↦ ⟨(Ideal.Quotient.mkₐ k I.toIdeal) x, ⟨x, x.2, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  refine Module.Finite.of_surjective q ?_
  intro xbar
  rcases xbar.2 with ⟨x, hx, hxbar⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxbar

/-- Helper for Lemma 10.58.10: restricting the quotient map to the ambient degree-`n` piece and
applying rank-nullity gives
`dim_k((S / I)_n) + dim_k(I_n) = dim_k(S_n)`. -/
private theorem homogeneous_ideal_quotient_degree_piece_finrank_add_degreePiece (n : ℕ) :
    Module.finrank k (homogeneousIdealQuotientDegreePiece I n) +
      Module.finrank k (homogeneousIdealDegreePiece I n) =
        Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) := by
  let qn : 𝒜 n →ₗ[k] S ⧸ I.toIdeal :=
    ((Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap).domRestrict (𝒜 n)
  have hrange : LinearMap.range qn = homogeneousIdealQuotientDegreePiece I n := by
    -- The range of the restricted quotient map is exactly the mapped degree-`n` piece.
    simpa [qn, homogeneousIdealQuotientDegreePiece] using LinearMap.range_eq_map qn
  have hker : LinearMap.ker qn = homogeneousIdealDegreePiece I n := by
    -- Kernel elements are precisely the homogeneous degree-`n` elements landing in `I`.
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      exact (mem_homogeneousIdealDegreePiece_iff (I := I) (f := x)).2
        ((Ideal.Quotient.eq_zero_iff_mem).1 hx)
    · intro hx
      rw [LinearMap.mem_ker]
      exact (Ideal.Quotient.eq_zero_iff_mem).2
        ((mem_homogeneousIdealDegreePiece_iff (I := I) (f := x)).1 hx)
  -- With the kernel and range identified, the source proof's exact sequence becomes
  -- the usual finite-dimensional rank-nullity formula.
  calc
    Module.finrank k (homogeneousIdealQuotientDegreePiece I n) +
        Module.finrank k (homogeneousIdealDegreePiece I n) =
      Module.finrank k (LinearMap.range qn) + Module.finrank k (LinearMap.ker qn) := by
        rw [hrange, hker]
    _ = Module.finrank k (𝒜 n) := by
        -- Use `quotKerEquivRange` plus the finrank version of rank-nullity to avoid a
        -- separate finite-dimensional instance search.
        let _ : Module.Finite k (𝒜 n) := ambient_degree_piece_moduleFinite (k := k) (d := d) n
        let _ : Module.Finite k (LinearMap.ker qn) := by
          rw [hker]
          exact homogeneousIdealDegreePiece_moduleFinite (I := I) (k := k) (d := d) n
        rw [← LinearEquiv.finrank_eq qn.quotKerEquivRange]
        exact (LinearMap.ker qn).finrank_quotient_add_finrank

/-- Helper for Lemma 10.58.10: multiplication by one fixed nonzero homogeneous
`f ∈ I ∩ S_e` injects `S_{n-e}` into `I_n`. -/
private theorem homogeneousIdealDegreePiece_finrank_ge_shift_of_homogeneous_mem
    {e n : ℕ} {f : S}
    (hf_ne : f ≠ 0) (hf_mem : f ∈ I.toIdeal) (hf_hom : f ∈ 𝒜 e) (hen : e ≤ n) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k (n - e)) ≤
      Module.finrank k (homogeneousIdealDegreePiece I n) := by
  let μ : 𝒜 (n - e) →ₗ[k] homogeneousIdealDegreePiece I n :=
    { toFun := fun g ↦
        let fg : 𝒜 n := ⟨f * (g : S), by
          simpa [Nat.add_sub_of_le hen] using SetLike.mul_mem_graded hf_hom g.2⟩
        ⟨fg, (mem_homogeneousIdealDegreePiece_iff (I := I) (f := fg)).2 <| by
          simpa [fg, mul_comm] using Ideal.mul_mem_left I.toIdeal (g : S) hf_mem⟩
      map_add' := by
        intro g h
        ext
        simp [mul_add]
      map_smul' := by
        intro c g
        ext
        simp }
  have hμ_injective : Function.Injective μ := by
    intro g h hgh
    apply Subtype.ext
    have hmul :
        f * (g : S) = f * (h : S) := by
      exact congrArg (fun x : homogeneousIdealDegreePiece I n ↦ (((x : _) : 𝒜 n) : S)) hgh
    have hzero : f * ((g : S) - (h : S)) = 0 := by
      rw [mul_sub, hmul, sub_self]
    have hdiff_zero : ((g : S) - (h : S)) = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hf_ne
    exact sub_eq_zero.mp hdiff_zero
  -- The injective multiplication map gives the desired finrank lower bound for `I_n`.
  let _ : Module.Finite k (𝒜 (n - e)) :=
    ambient_degree_piece_moduleFinite (k := k) (d := d) (n - e)
  let _ : Module.Finite k (homogeneousIdealDegreePiece I n) :=
    homogeneousIdealDegreePiece_moduleFinite (I := I) (k := k) (d := d) n
  exact μ.finrank_le_finrank_of_injective hμ_injective

/-- Helper for Lemma 10.58.10: combining the degreewise exact sequence with multiplication by
`f ∈ I ∩ S_e` yields the source inequality
`dim_k((S / I)_n) ≤ dim_k(S_n) - dim_k(S_{n-e})`. -/
private theorem homogeneous_ideal_quotient_degree_piece_finrank_le_ambient_sub_shift
    {e n : ℕ} {f : S}
    (hf_ne : f ≠ 0) (hf_mem : f ∈ I.toIdeal) (hf_hom : f ∈ 𝒜 e) (hen : e ≤ n) :
    Module.finrank k (homogeneousIdealQuotientDegreePiece I n) ≤
      Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) -
        Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k (n - e)) := by
  have hsum := homogeneous_ideal_quotient_degree_piece_finrank_add_degreePiece (I := I) n
  have hshift :=
    homogeneousIdealDegreePiece_finrank_ge_shift_of_homogeneous_mem (I := I) hf_ne hf_mem hf_hom hen
  omega

/-- Helper for Lemma 10.58.10: once a positive-degree homogeneous witness `f ∈ I` is fixed, the
quotient Hilbert function is eventually bounded above by the expected multichoose difference from
the source proof. -/
private theorem homogeneousIdealQuotientHilbertFunction_eventually_le_multichoose_difference
    {e : ℕ} {f : S}
    (hf_ne : f ≠ 0) (hf_mem : f ∈ I.toIdeal) (hf_hom : f ∈ 𝒜 e) :
    ∀ᶠ n : ℤ in atTop,
      0 ≤ homogeneousIdealQuotientHilbertFunction I n ∧
        homogeneousIdealQuotientHilbertFunction I n ≤
          ((d.multichoose n.toNat : ℤ) - (d.multichoose (n.toNat - e) : ℤ)) := by
  filter_upwards [eventually_ge_atTop (e : ℤ)] with n hn
  have hnn : 0 ≤ n := by linarith
  have hen : e ≤ n.toNat := by
    have htoNat : (e : ℤ) ≤ (n.toNat : ℤ) := by
      simpa [Int.toNat_of_nonneg hnn] using hn
    exact_mod_cast htoNat
  have hbound_nat :
      Module.finrank k (homogeneousIdealQuotientDegreePiece I n.toNat) ≤
        Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n.toNat) -
          Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k (n.toNat - e)) :=
    homogeneous_ideal_quotient_degree_piece_finrank_le_ambient_sub_shift
      (I := I) hf_ne hf_mem hf_hom hen
  constructor
  · -- The Hilbert function is a nonnegative finrank in nonnegative degree.
    rw [homogeneousIdealQuotientHilbertFunction_of_nonneg (I := I) n hnn]
    exact_mod_cast Nat.zero_le (Module.finrank k (homogeneousIdealQuotientDegreePiece I n.toNat))
  · -- Rewrite the ambient dimensions by `multichoose` to recover the source's explicit bound.
    rw [homogeneousIdealQuotientHilbertFunction_of_nonneg (I := I) n hnn]
    let _ : Module.Finite k (homogeneousIdealQuotientDegreePiece I n.toNat) :=
      homogeneousIdealQuotientDegreePiece_moduleFinite (I := I) (k := k) (d := d) n.toNat
    have hbound_nat' :
        Module.finrank k (homogeneousIdealQuotientDegreePiece I n.toNat) ≤
          d.multichoose n.toNat - d.multichoose (n.toNat - e) := by
      simpa [ambient_degree_piece_finrank_eq_multichoose (k := k) (d := d) n.toNat,
        ambient_degree_piece_finrank_eq_multichoose (k := k) (d := d) (n.toNat - e)] using hbound_nat
    have hsub :
        d.multichoose (n.toNat - e) ≤ d.multichoose n.toNat := by
      have hsum :=
        homogeneous_ideal_quotient_degree_piece_finrank_add_degreePiece (I := I) n.toNat
      have hshift :=
        homogeneousIdealDegreePiece_finrank_ge_shift_of_homogeneous_mem
          (I := I) hf_ne hf_mem hf_hom hen
      have hdegpiece_le :
          Module.finrank k (homogeneousIdealDegreePiece I n.toNat) ≤
            Module.finrank k (𝒜 n.toNat) := by
        omega
      have hsub_finrank :
          Module.finrank k (𝒜 (n.toNat - e)) ≤ Module.finrank k (𝒜 n.toNat) :=
        le_trans hshift hdegpiece_le
      rw [ambient_degree_piece_finrank_eq_multichoose (k := k) (d := d) n.toNat,
        ambient_degree_piece_finrank_eq_multichoose (k := k) (d := d) (n.toNat - e)] at hsub_finrank
      exact hsub_finrank
    rw [← Int.ofNat_sub hsub]
    exact_mod_cast hbound_nat'

-- Proof sketch: choose a nonzero homogeneous element of `I`, compare the degree-`n` piece of the
-- quotient with the corresponding degree-`n` piece of the ambient polynomial ring modulo the image
-- of multiplication by that element, and use the binomial-coefficient formula for the Hilbert
-- function of the standard graded polynomial ring to obtain a drop in degree.
/-- Chap10 Lemma 10 58 10: for a nonzero homogeneous ideal in `k[X₁, …, X_d]`, the Hilbert function of
the quotient graded module `k[X₁, …, X_d] ⧸ I` is a numerical polynomial of degree `< d - 1`,
with the source's exceptional `d = 1` case absorbed by the convention that an eventually zero
function has degree `-∞`. -/
@[stacks 00K3]
theorem nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound
    (hI : I ≠ ⊥) :
    HasNumericalPolynomialDegreeLT
      (homogeneousIdealQuotientHilbertFunction I) (d - 1 : ℤ) := by
  by_cases hItop : I = ⊤
  · -- If `I = ⊤`, then the quotient ring is zero and every Hilbert value vanishes.
    exact Or.inl <| Filter.EventuallyEq.of_eq
      (homogeneousIdealQuotientHilbertFunction_eq_zero_of_top (I := I) hItop)
  · -- Route correction: the proof now separates the trivial `I = ⊤` branch and fixes one
    -- positive-degree homogeneous witness in the proper branch before attacking the degreewise
    -- quotient estimate.
    obtain ⟨e, f, he_pos, hf_ne, hf_mem, hf_hom⟩ :=
      exists_nonzero_positive_degree_homogeneous_mem_of_nonbot_ne_top
        (I := I) hI hItop
    have hbound :
        ∀ᶠ n : ℤ in atTop,
          0 ≤ homogeneousIdealQuotientHilbertFunction I n ∧
            homogeneousIdealQuotientHilbertFunction I n ≤
              ((d.multichoose n.toNat : ℤ) - (d.multichoose (n.toNat - e) : ℤ)) :=
      homogeneousIdealQuotientHilbertFunction_eventually_le_multichoose_difference
        (I := I) hf_ne hf_mem hf_hom
    by_cases hd1 : d = 1
    · -- In the exceptional one-variable case, the source upper bound is eventually zero.
      refine Or.inl ?_
      filter_upwards [hbound] with n hn
      have hEq :
          ((d.multichoose n.toNat : ℤ) - (d.multichoose (n.toNat - e) : ℤ)) = 0 := by
        subst hd1
        simp [Nat.multichoose_one]
      omega
    have hd0 : d ≠ 0 := by
      intro hd0
      subst hd0
      let _ : Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin 0) k e) :=
        ambient_degree_piece_moduleFinite (k := k) (d := 0) e
      have hfinrank_zero :
          Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin 0) k e) = 0 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he_pos.ne'
        simpa using ambient_degree_piece_finrank_eq_multichoose (k := k) (d := 0) (m + 1)
      have hzero :
          (⟨f, hf_hom⟩ : MvPolynomial.homogeneousSubmodule (Fin 0) k e) = 0 := by
        exact (finrank_zero_iff_forall_zero).1 hfinrank_zero ⟨f, hf_hom⟩
      exact hf_ne (Subtype.ext_iff.mp hzero)
    have hd_gt : 1 < d := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hd0, hd1⟩
    have hnum : IsNumericalPolynomial (homogeneousIdealQuotientHilbertFunction I) :=
      homogeneousIdealQuotientHilbertFunction_isNumericalPolynomial_aux (I := I)
    exact
      hasNumericalPolynomialDegreeLT_of_isNumericalPolynomial_and_eventually_le_multichoose_difference
        (d := d) he_pos hd_gt hnum hbound

/-- For any homogeneous ideal `I`, the quotient Hilbert function is a numerical polynomial in the
sense of Definition 10.58.3. This companion forgets the sharper source-facing degree bound from
Lemma 10.58.10 and retains only the chapter's core owner notion `IsNumericalPolynomial`. The
nonzero hypothesis is needed for the degree bound itself, not for eventual polynomiality. -/
theorem homogeneousIdeal_quotientHilbertFunction_isNumericalPolynomial :
    IsNumericalPolynomial (homogeneousIdealQuotientHilbertFunction I) := by
  by_cases hI : I = ⊥
  · -- The zero ideal case is the ambient Hilbert function, handled by the multichoose recursion.
    exact
      IsNumericalPolynomial.congr
        (ambientHilbertFunction_isNumericalPolynomial d)
        (Filter.EventuallyEq.of_eq
          (homogeneousIdealQuotientHilbertFunction_eq_ambient_of_bot (I := I) hI))
  · -- Reuse the auxiliary quotient-grading bridge directly instead of routing through the sharper
    -- degree-bound theorem.
    exact homogeneousIdealQuotientHilbertFunction_isNumericalPolynomial_aux (I := I)

/-- In the exceptional case `d = 1`, Lemma 10.58.10 says that the quotient Hilbert function is
eventually zero. -/
theorem nonzero_homogeneousIdeal_quotientHilbertFunction_eventuallyEq_zero_of_eq_one
    (hI : I ≠ ⊥) (hd : d = 1) :
    homogeneousIdealQuotientHilbertFunction I =ᶠ[atTop] fun _ ↦ (0 : ℤ) := by
  simpa [hd, hasNumericalPolynomialDegreeLT_zero_iff] using
    (nonzero_homogeneousIdeal_quotientHilbertFunction_degree_bound I hI)

end
