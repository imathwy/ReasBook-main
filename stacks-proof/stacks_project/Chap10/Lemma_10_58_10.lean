import Mathlib
import stacks_project.Chap10.Lemma_10_55_1
import stacks_project.Chap10.Lemma_10_58_4
import stacks_project.Chap10.Definition_10_58_3
import stacks_project.Chap10.Lemma_10_58_5
import stacks_project.Chap10.Example_10_58_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u

section

variable {A : Type u} [AddCommGroup A]

/-- A function on the integers has degree `< m` if it is eventually zero, or eventually agrees
with a binomial-coefficient expansion indexed only up to some `r < m`. This packages the zero
function as having degree `-∞`, which is the convention used in Lemma 10.58.10. -/
def HasNumericalPolynomialDegreeLT (f : ℤ → A) (m : ℤ) : Prop :=
  (f =ᶠ[atTop] fun _ ↦ (0 : A)) ∨
    ∃ r : ℕ, (r : ℤ) < m ∧ ∃ a : Fin (r + 1) → A,
      f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

/- Bridge/view: a degree bound in the source-facing sense still lands in the chapter's owner
notion `IsNumericalPolynomial`. -/
theorem HasNumericalPolynomialDegreeLT.isNumericalPolynomial
    {f : ℤ → A} {m : ℤ} (hf : HasNumericalPolynomialDegreeLT f m) :
    IsNumericalPolynomial f := by
  rcases hf with hzero | ⟨r, -, a, ha⟩
  · refine ⟨0, fun _ ↦ 0, ?_⟩
    exact hzero.trans <| Filter.EventuallyEq.of_eq <| by
      ext n
      simp
  · exact ⟨r, a, ha⟩

private theorem hasNumericalPolynomialDegreeLT_zero_iff {f : ℤ → A} :
    HasNumericalPolynomialDegreeLT f 0 ↔ f =ᶠ[atTop] fun _ ↦ (0 : A) := by
  constructor
  · intro hf
    rcases hf with hzero | ⟨r, hr, -, -⟩
    · exact hzero
    · have hnonneg : (0 : ℤ) ≤ r := by
        exact_mod_cast Nat.zero_le r
      exact (not_lt_of_ge hnonneg hr).elim
  · intro hzero
    exact Or.inl hzero

end

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

/-- Helper for Lemma 10.58.10: the actual quotient degree piece in degree `n`, viewed as a class
in `K'_0(k)`. This is the owner-level object needed for the source's numerical-polynomial step. -/
private noncomputable def quotient_hilbert_k0_class (n : ℤ) :
    finiteGrothendieckGroup k :=
  let _ : Module.Finite k (quotientHilbertGrading I n) :=
    quotientHilbertGrading_moduleFinite (I := I) (k := k) (d := d) n
  finiteGrothendieckGroupOf k (FGModuleCat.of k (quotientHilbertGrading I n))

/-- Helper for Lemma 10.58.10: applying the field-length map to the quotient degree-piece class
recovers the `k`-dimension of that degree piece. -/
private theorem quotient_hilbert_k0_class_length_eq_finrank
    (n : ℤ) :
    finiteGrothendieckGroup_lengthMap k (quotient_hilbert_k0_class (I := I) (k := k) (d := d) n) =
      (Module.finrank k (quotientHilbertGrading I n) : ℤ) := by
  let _ : Module.Finite k (quotientHilbertGrading I n) :=
    quotientHilbertGrading_moduleFinite (I := I) (k := k) (d := d) n
  -- Evaluate the canonical length map on the generator class and rewrite length as dimension.
  rw [quotient_hilbert_k0_class, finiteGrothendieckGroup_lengthMap_apply_of]
  simpa [Module.length_eq_finrank]

/-- Helper for Lemma 10.58.10: postcomposing the `K'_0(k)`-valued quotient Hilbert function with
the field-length map gives the usual numerical Hilbert function. -/
private theorem quotientHilbertGrading_finrank_isNumericalPolynomial :
    IsNumericalPolynomial
      (fun n ↦ (Module.finrank k (quotientHilbertGrading I n) : ℤ)) := by
  -- Route correction: prove numerical polynomiality directly at the scalar-valued Hilbert
  -- function, using Example 10.58.9 on the quotient grading rather than routing first through a
  -- separate `K'_0(k)`-valued owner.
  -- TODO: build the missing quotient-grading bridge from the file-local
  -- `quotientHilbertGrading : ℤ → Submodule k (S ⧸ I.toIdeal)` to the grading owner expected by
  -- Example 10.58.9. The compile probe shows the current bottleneck is not numerical
  -- polynomiality itself, but the absence of an earlier-allowed direct-sum/graded-action package
  -- that lets the Example 10.58.9 theorem elaborate on these degree pieces.
  sorry

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

/-- Helper for Lemma 10.58.10: the rational polynomial attached to a binomial-coefficient
expansion. -/
private noncomputable def numericalPolynomialCandidate {r : ℕ} (a : Fin (r + 1) → ℚ) :
    Polynomial ℚ :=
  ∑ i : Fin (r + 1), a i • Polynomial.preHilbertPoly ℚ i i

/-- Helper for Lemma 10.58.10: the candidate polynomial evaluates to the expected
binomial-coefficient expansion on the natural-number tail. -/
private theorem numericalPolynomialCandidate_spec_nat {r : ℕ} (a : Fin (r + 1) → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      (numericalPolynomialCandidate a).eval (n : ℚ) =
        ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
  filter_upwards [eventually_ge_atTop r] with n hn
  simp only [numericalPolynomialCandidate, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add]
  · rw [Nat.sub_add_cancel (le_trans (Nat.lt_succ_iff.mp i.2) hn)]
    simp [Ring.choose_natCast, mul_comm]
  · exact le_trans (Nat.lt_succ_iff.mp i.2) hn

/-- Helper for Lemma 10.58.10: `preHilbertPoly` is never the zero polynomial over `ℚ`. -/
private theorem preHilbertPoly_ne_zero (m k : ℕ) :
    Polynomial.preHilbertPoly ℚ m k ≠ 0 := by
  intro hzero
  have hcoeff : (Polynomial.preHilbertPoly ℚ m k).coeff m = 0 := by
    simpa [hzero]
  have hfac : ((m.factorial : ℚ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
  rw [Polynomial.coeff_preHilbertPoly_self] at hcoeff
  exact hfac hcoeff

/-- Helper for Lemma 10.58.10: coefficients above the natural degree of `preHilbertPoly`
vanish. -/
private theorem preHilbertPoly_coeff_eq_zero_of_lt {m k j : ℕ} (hj : m < j) :
    (Polynomial.preHilbertPoly ℚ m k).coeff j = 0 := by
  have hdeg : (Polynomial.preHilbertPoly ℚ m k).degree < j := by
    rw [Polynomial.degree_eq_natDegree (preHilbertPoly_ne_zero m k),
      Polynomial.natDegree_preHilbertPoly]
    exact_mod_cast hj
  exact (Polynomial.degree_lt_iff_coeff_zero _ j).1 hdeg j le_rfl

/-- Helper for Lemma 10.58.10: the top coefficient of a numerical-polynomial candidate is the
last binomial coefficient scaled by `(r!)⁻¹`. -/
private theorem numericalPolynomialCandidate_coeff_top {r : ℕ} (a : Fin (r + 1) → ℚ) :
    (numericalPolynomialCandidate a).coeff r =
      a (Fin.last r) * ((r.factorial : ℚ)⁻¹) := by
  -- Separate the top-degree term from the lower-degree terms and use triangularity of the
  -- `preHilbertPoly` basis.
  rw [numericalPolynomialCandidate, Fin.sum_univ_castSucc, Polynomial.coeff_add]
  have hsum_zero :
      (∑ i : Fin r, a i.castSucc • Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).coeff r = 0 := by
    simpa [preHilbertPoly_coeff_eq_zero_of_lt] using
      (show
        (∑ i : Fin r, a i.castSucc • Polynomial.preHilbertPoly ℚ (i : ℕ) (i : ℕ)).coeff r = 0 by
          simp)
  simp [hsum_zero, Polynomial.coeff_smul, Polynomial.coeff_preHilbertPoly_self]

/-- Helper for Lemma 10.58.10: the source comparison function is represented by an explicit
pre-Hilbert-polynomial difference. -/
private noncomputable def multichooseDifferencePolynomial (d e : ℕ) : Polynomial ℚ :=
  Polynomial.preHilbertPoly ℚ (d - 1) 0 - Polynomial.preHilbertPoly ℚ (d - 1) e

/-- Helper for Lemma 10.58.10: the explicit comparison polynomial evaluates to the multichoose
difference on the natural-number tail. -/
private theorem multichooseDifferencePolynomial_spec_nat (d e : ℕ) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (multichooseDifferencePolynomial d e).eval (n : ℚ) =
        (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
  filter_upwards [eventually_ge_atTop e] with n hn
  have hleft :
      (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) = (d.multichoose n : ℚ) := by
    have hleft' :
        (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) =
          (((n + (d - 1)).choose (d - 1) : ℕ) : ℚ) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) (d - 1) (k := 0) (n := n)
          (by simp))
    calc
      (Polynomial.preHilbertPoly ℚ (d - 1) 0).eval (n : ℚ) =
          (((n + (d - 1)).choose (d - 1) : ℕ) : ℚ) := hleft'
      _ = (((d - 1 + n).choose n : ℕ) : ℚ) := by
          have hchoose_nat : (n + (d - 1)).choose (d - 1) = (d - 1 + n).choose n := by
            rw [Nat.add_comm n (d - 1)]
            exact Nat.choose_symm_add (a := d - 1) (b := n)
          exact_mod_cast hchoose_nat
      _ = (d.multichoose n : ℚ) := by
          rw [Nat.multichoose_eq]
          have hs : d - 1 + n = d + n - 1 := by
            cases d with
            | zero => cases (Nat.lt_asymm hd hd)
            | succ d =>
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          simp [hs]
  have hright :
      (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) = (d.multichoose (n - e) : ℚ) := by
    have hright' :
        (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) =
          ((((n - e) + (d - 1)).choose (d - 1) : ℕ) : ℚ) := by
      simpa [Nat.sub_add_comm hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) (d - 1) (k := e) (n := n) hn)
    calc
      (Polynomial.preHilbertPoly ℚ (d - 1) e).eval (n : ℚ) =
          ((((n - e) + (d - 1)).choose (d - 1) : ℕ) : ℚ) := hright'
      _ = (((d - 1 + (n - e)).choose (n - e) : ℕ) : ℚ) := by
          have hchoose_nat :
              ((n - e) + (d - 1)).choose (d - 1) = (d - 1 + (n - e)).choose (n - e) := by
            rw [Nat.add_comm (n - e) (d - 1)]
            exact Nat.choose_symm_add (a := d - 1) (b := n - e)
          exact_mod_cast hchoose_nat
      _ = (d.multichoose (n - e) : ℚ) := by
          rw [Nat.multichoose_eq]
          have hs : d - 1 + (n - e) = d + (n - e) - 1 := by
            cases d with
            | zero => cases (Nat.lt_asymm hd hd)
            | succ d =>
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          simp [hs]
  -- Rewrite both pre-Hilbert polynomials by their multichoose evaluations and then cast the
  -- integer subtraction to `ℚ`.
  calc
    (multichooseDifferencePolynomial d e).eval (n : ℚ) =
        (d.multichoose n : ℚ) - (d.multichoose (n - e) : ℚ) := by
          simp [multichooseDifferencePolynomial, hleft, hright]
    _ = (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
          norm_num

/-- Helper for Lemma 10.58.10: for `d > 1`, the explicit multichoose-difference polynomial has
degree `< d - 1`. -/
private theorem multichooseDifferencePolynomial_degree_lt (d e : ℕ) (hd : 1 < d) :
    (multichooseDifferencePolynomial d e).degree < ((d - 1 : ℕ) : WithBot ℕ) := by
  refine (Polynomial.degree_lt_iff_coeff_zero _ (d - 1)).2 ?_
  intro j hj
  by_cases hj_eq : j = d - 1
  · subst hj_eq
    simp [multichooseDifferencePolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_preHilbertPoly_self]
  · have hj_gt : d - 1 < j := lt_of_le_of_ne hj (Ne.symm hj_eq)
    simp [multichooseDifferencePolynomial, Polynomial.coeff_sub,
      preHilbertPoly_coeff_eq_zero_of_lt (k := 0) hj_gt,
      preHilbertPoly_coeff_eq_zero_of_lt (k := e) hj_gt]

/-- Helper for Lemma 10.58.10: an eventually nonnegative polynomial bounded above by another
polynomial cannot have larger degree. -/
private theorem degree_le_of_eventually_nonneg_le {E Q : Polynomial ℚ}
    (hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ E.eval (n : ℚ) ∧ E.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    E.degree ≤ Q.degree := by
  by_contra hEQ
  have hQE : Q.degree < E.degree := lt_of_not_ge hEQ
  have hE0 : E ≠ 0 := Polynomial.ne_zero_of_degree_gt hQE
  have hNoRoot :
      ∀ᶠ n : ℕ in atTop, ¬ E.IsRoot (n : ℚ) := by
    exact tendsto_natCast_atTop_atTop.eventually
      (Polynomial.eventually_atTop_not_isRoot (P := E) hE0)
  have hPos :
      ∀ᶠ n : ℕ in atTop, 0 < E.eval (n : ℚ) := by
    -- Eventual nonnegativity plus eventual nonvanishing forces eventual positivity.
    filter_upwards [hbound, hNoRoot] with n hn hnr
    have hne : E.eval (n : ℚ) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hnr
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  have hDiv :
      Tendsto (fun n : ℕ ↦ Q.eval (n : ℚ) / E.eval (n : ℚ)) atTop (nhds 0) := by
    exact (Polynomial.div_tendsto_atTop_zero_of_degree_lt (P := Q) (Q := E) hQE).comp
      tendsto_natCast_atTop_atTop
  have hSmall :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) / E.eval (n : ℚ) ∈ Set.Ioo (-1) 1 := by
    exact hDiv.eventually
      (Ioo_mem_nhds (by norm_num : (-1 : ℚ) < 0) (by norm_num : (0 : ℚ) < 1))
  have hFalse : ∀ᶠ n : ℕ in atTop, False := by
    -- The ratio tends to `0`, but the eventual upper bound forces it to be at least `1`.
    filter_upwards [hPos, hSmall, hbound] with n hPosN hSmallN hBoundN
    have hRatioGe : (1 : ℚ) ≤ Q.eval (n : ℚ) / E.eval (n : ℚ) := by
      rw [one_le_div hPosN]
      exact hBoundN.2
    exact (not_le_of_gt hSmallN.2) hRatioGe
  rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
  exact hN N le_rfl

/-- Helper for Lemma 10.58.10: if the associated rational polynomial has degree `< m`, the
original binomial-coefficient witness can be trimmed to degree `< m`. -/
private theorem hasNumericalPolynomialDegreeLT_of_choose_witness_degree_lt
    {f : ℤ → ℤ} {m r : ℕ} (hm : 0 < m) (a : Fin (r + 1) → ℤ)
    (ha : f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i)
    (hdeg : (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).degree < m) :
    HasNumericalPolynomialDegreeLT f (m : ℤ) := by
  induction r with
  | zero =>
      exact Or.inr ⟨0, by exact_mod_cast hm, a, ha⟩
  | succ r ih =>
      by_cases hrm : r + 1 < m
      · exact Or.inr ⟨r + 1, by exact_mod_cast hrm, a, ha⟩
      · have hdeg_top :
          (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).degree < r + 1 := by
          exact lt_of_lt_of_le hdeg (by exact_mod_cast Nat.le_of_not_lt hrm)
        have hcoeff_zero :
            (numericalPolynomialCandidate fun i ↦ (a i : ℚ)).coeff (r + 1) = 0 := by
          exact (Polynomial.degree_lt_iff_coeff_zero _ (r + 1)).1 hdeg_top (r + 1) le_rfl
        have hlast_q :
            (a (Fin.last (r + 1)) : ℚ) = 0 := by
          have htop :
              (a (Fin.last (r + 1)) : ℚ) * (((r + 1).factorial : ℚ)⁻¹) = 0 := by
            simpa [numericalPolynomialCandidate_coeff_top] using hcoeff_zero
          have hfac : (((r + 1).factorial : ℚ)⁻¹) ≠ 0 := by
            exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
          exact (mul_eq_zero.mp htop).resolve_right hfac
        have hlast : a (Fin.last (r + 1)) = 0 := by
          exact_mod_cast hlast_q
        let a' : Fin (r + 1) → ℤ := fun i ↦ a i.castSucc
        have ha' :
            f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a' i := by
          -- Drop the vanishing top-degree term from the binomial expansion.
          filter_upwards [ha] with n hn
          rw [hn, Fin.sum_univ_castSucc]
          simp [a', hlast]
        have hdeg' :
            (numericalPolynomialCandidate fun i ↦ (a' i : ℚ)).degree < m := by
          -- The rational polynomial is unchanged after deleting the zero top coefficient.
          simpa [numericalPolynomialCandidate, a', hlast, Fin.sum_univ_castSucc] using hdeg
        exact ih a' ha' hdeg'

/-- Helper for Lemma 10.58.10: numerical polynomiality plus the source upper bound by one fixed
multichoose difference forces the Hilbert function to have degree `< d - 1`. -/
private theorem hasNumericalPolynomialDegreeLT_of_isNumericalPolynomial_and_eventually_le_multichoose_difference
    {f : ℤ → ℤ} {e : ℕ} (he : 0 < e) (hd : 1 < d)
    (hnum : IsNumericalPolynomial f)
    (hbound : ∀ᶠ n : ℤ in atTop, 0 ≤ f n ∧
      f n ≤ ((d.multichoose n.toNat : ℤ) - (d.multichoose (n.toNat - e) : ℤ))) :
    HasNumericalPolynomialDegreeLT f (d - 1 : ℤ) := by
  rcases hnum with ⟨r, a, ha⟩
  let P : Polynomial ℚ := numericalPolynomialCandidate fun i ↦ (a i : ℚ)
  let Q : Polynomial ℚ := multichooseDifferencePolynomial d e
  have hPevent :
      ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = (f n : ℚ) := by
    have hNat :
        (fun n : ℕ ↦ f n) =ᶠ[atTop]
          fun n ↦ ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
      simpa using ha.comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
    filter_upwards [hNat, numericalPolynomialCandidate_spec_nat (fun i ↦ (a i : ℚ))] with n hn hP
    -- Rewrite the numerical-polynomial witness through the rational candidate.
    calc
      P.eval (n : ℚ) = ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • (a i : ℚ) := by
        simpa [P] using hP
      _ = (f n : ℚ) := by
        simpa [hn, zsmul_eq_mul]
  have hQevent :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) =
        (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
    simpa [Q] using multichooseDifferencePolynomial_spec_nat d e (Nat.lt_trans Nat.zero_lt_one hd)
  have hbound_nat :
      ∀ᶠ n : ℕ in atTop, 0 ≤ (f n : ℚ) ∧ (f n : ℚ) ≤ Q.eval (n : ℚ) := by
    have hbound' :
        ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧
          f n ≤ ((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) := by
      rcases Filter.eventually_atTop.mp hbound with ⟨N, hN⟩
      refine Filter.eventually_atTop.mpr ⟨Int.toNat N, ?_⟩
      intro n hn
      have hN' : N ≤ (n : ℤ) := by
        calc
          N ≤ Int.toNat N := Int.self_le_toNat N
          _ ≤ n := by exact_mod_cast hn
      simpa using hN (n : ℤ) hN'
    filter_upwards [hbound', hQevent] with n hn hQ
    constructor
    · exact_mod_cast hn.1
    · have hcast :
          (f n : ℚ) ≤ (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := by
          exact_mod_cast hn.2
      calc
        (f n : ℚ) ≤ (((d.multichoose n : ℤ) - (d.multichoose (n - e) : ℤ)) : ℚ) := hcast
        _ = Q.eval (n : ℚ) := hQ.symm
  have hPbound :
      ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    -- Replace the Hilbert function by its eventual polynomial representative.
    filter_upwards [hPevent, hbound_nat] with n hP hn
    rw [hP]
    exact hn
  have hQdeg : Q.degree < ((d - 1 : ℕ) : WithBot ℕ) :=
    multichooseDifferencePolynomial_degree_lt d e hd
  have hPdeg : P.degree < ((d - 1 : ℕ) : WithBot ℕ) := by
    exact lt_of_le_of_lt (degree_le_of_eventually_nonneg_le hPbound) hQdeg
  have hm : 0 < d - 1 := Nat.sub_pos_of_lt hd
  -- Convert the degree bound on the rational candidate back to the chapter's source-facing
  -- binomial-coefficient degree notion.
  have hdegInt : (((d - 1 : ℕ) : ℤ)) = (d : ℤ) - 1 := by
    exact Int.ofNat_sub (Nat.one_le_of_lt hd)
  simpa [P, hdegInt] using
    hasNumericalPolynomialDegreeLT_of_choose_witness_degree_lt (m := d - 1) hm a ha hPdeg

-- Proof sketch: choose a nonzero homogeneous element of `I`, compare the degree-`n` piece of the
-- quotient with the corresponding degree-`n` piece of the ambient polynomial ring modulo the image
-- of multiplication by that element, and use the binomial-coefficient formula for the Hilbert
-- function of the standard graded polynomial ring to obtain a drop in degree.
/-- Lemma 10.58.10: for a nonzero homogeneous ideal in `k[X₁, …, X_d]`, the Hilbert function of
the quotient graded module `k[X₁, …, X_d] ⧸ I` is a numerical polynomial of degree `< d - 1`,
with the source's exceptional `d = 1` case absorbed by the convention that an eventually zero
function has degree `-∞`. -/
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
