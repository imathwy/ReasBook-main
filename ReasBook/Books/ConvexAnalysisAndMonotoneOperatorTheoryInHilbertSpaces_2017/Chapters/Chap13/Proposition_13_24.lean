import Mathlib
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_19
import BauschkeLean.Chap13.Proposition_13_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 24: subtracting an indexed infimum from a finite real scalar equals
the supremum of the corresponding pointwise defects. -/
lemma ereal_realCast_sub_iInf_eq_iSup_sub
    {ι : Sort*} (a : ℝ) (φ : ι → EReal) :
    ((a : EReal) - ⨅ i, φ i) = ⨆ i, ((a : EReal) - φ i) := by
  -- Rewrite subtraction as addition with negation, turn the negated infimum into a supremum,
  -- and then move the finite real shift through the supremum.
  calc
    ((a : EReal) - ⨅ i, φ i) = ((a : EReal) + -(⨅ i, φ i)) := by
      rw [sub_eq_add_neg]
    _ = ((a : EReal) + ⨆ i, -φ i) := by
      congr 1
      exact OrderIso.map_iInf EReal.negOrderIso φ
    _ = ((⨆ i, -φ i) + (a : EReal)) := by
      rw [add_comm]
    _ = ⨆ i, (-φ i) + (a : EReal) := by
      symm
      simpa using ereal_iSup_add_of_real_shift a (fun i ↦ -φ i)
    _ = ⨆ i, ((a : EReal) - φ i) := by
      refine iSup_congr fun i ↦ ?_
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 13 24: the supremum of independent sums separates into the sum of the
two supremums. -/
lemma iSup_iSup_add_eq_add_iSup
    {ι κ : Sort*} (a : ι → EReal) (b : κ → EReal) :
    (⨆ i, ⨆ j, a i + b j) = (⨆ i, a i) + (⨆ j, b j) := by
  -- Bound the double supremum from above termwise, then recover the reverse inequality by
  -- approximating each outer supremum from below.
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    refine iSup_le fun j ↦ ?_
    exact add_le_add (le_iSup a i) (le_iSup b j)
  · refine EReal.add_le_of_forall_lt ?_
    intro a' ha b' hb
    rcases lt_iSup_iff.mp ha with ⟨i, hi⟩
    rcases lt_iSup_iff.mp hb with ⟨j, hj⟩
    exact (EReal.add_lt_add hi hj).le.trans <| le_iSup_of_le i <| le_iSup_of_le j le_rfl

/-- Helper for Proposition 13 24: when the two function values are `]-∞,+∞]`-valued, the affine
defect of their sum splits into the sum of the two affine defects. -/
lemma affine_defect_add_split
    (f g : H → Set.Ioi (⊥ : EReal)) (x y z : H) :
    (((⟪x, y + z⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g x : EReal))) =
      ((((⟪x, y⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
        (((⟪x, z⟫_ℝ : ℝ) : EReal) - (g x : EReal))) := by
  have hf_bot : (f x : EReal) ≠ ⊥ := (ne_of_gt (f x).2)
  have hg_bot : (g x : EReal) ≠ ⊥ := (ne_of_gt (g x).2)
  have hinner :
      (((⟪x, y + z⟫_ℝ : ℝ) : EReal)) =
        (((⟪x, y⟫_ℝ : ℝ) : EReal) + ((⟪x, z⟫_ℝ : ℝ) : EReal)) := by
    simp [inner_add_right]
  -- Rewrite the negated sum as the sum of the negated values, then reassociate the terms.
  rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hf_bot) (.inr hg_bot), sub_eq_add_neg,
    sub_eq_add_neg]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 13 24: after translating `x = y + z`, the affine defect of the
infimal-convolution summand splits into the two separate conjugate defects. -/
lemma infimal_convolution_affine_defect_split
    (f g : H → Set.Ioi (⊥ : EReal)) (y z u : H) :
    (((⟪z + y, u⟫_ℝ : ℝ) : EReal) - ((f y : EReal) + (g z : EReal))) =
      ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
        (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgz_bot : (g z : EReal) ≠ ⊥ := ne_of_gt (g z).2
  have hinner :
      (((⟪z + y, u⟫_ℝ : ℝ) : EReal)) =
        (((⟪y, u⟫_ℝ : ℝ) : EReal) + ((⟪z, u⟫_ℝ : ℝ) : EReal)) := by
    simpa [add_comm] using congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) (inner_add_left z y u)
  -- Separate the two finite pairing terms and the two function values, then reassociate.
  rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hfy_bot) (.inr hgz_bot), sub_eq_add_neg,
    sub_eq_add_neg]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: expand the conjugate of `f □ g`, rewrite the defining infimum as a translated
-- supremum over decompositions `x = y + z`, and separate the two resulting suprema.
/-- Proposition 13 24 (1): the Fenchel conjugate of the infimal convolution `f □ g` is the
pointwise sum `f* + g*`. -/
theorem conjugate_infimalConvolution_eq
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f □ g)∗ = f.asEReal∗ + g.asEReal∗ := by
  ext u
  -- Expand the conjugate and the infimal convolution so the inner infimum can be dualized.
  rw [conjugate_apply, Pi.add_apply, conjugate_apply, conjugate_apply]
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (f □ g) x)) =
        (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ⨅ y : H, ((f y : EReal) + (g (x - y) : EReal)))) := by
            refine iSup_congr fun x ↦ ?_
            exact congrArg
              (fun t : EReal ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - t))
              (infimalConvolution_apply f.asEReal g.asEReal x)
    _ =
        ⨆ x : H, ⨆ y : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ((f y : EReal) + (g (x - y) : EReal))) := by
            -- Turn the finite-minus-infimum expression into a supremum of affine defects.
            refine iSup_congr fun x ↦ ?_
            simpa using
              ereal_realCast_sub_iInf_eq_iSup_sub
                (a := ⟪x, u⟫_ℝ)
                (φ := fun y : H ↦ (f y : EReal) + (g (x - y) : EReal))
    _ = ⨆ y : H, ⨆ z : H, ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
          (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
            -- Reindex each decomposition by `x = z + y` and split the affine defect.
            rw [iSup_comm]
            refine iSup_congr fun y ↦ ?_
            calc
              (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
                  ((f y : EReal) + (g (x - y) : EReal)))) =
                  ⨆ z : H, (((⟪z + y, u⟫_ℝ : ℝ) : EReal) -
                    ((f y : EReal) + (g z : EReal))) := by
                      exact ((Equiv.addRight y).surjective.iSup_congr (Equiv.addRight y) fun z ↦ by
                        simp).symm
              _ = ⨆ z : H, ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
                    (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
                      refine iSup_congr fun z ↦ ?_
                      exact infimal_convolution_affine_defect_split f g y z u
    _ = (⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal))) +
        ⨆ z : H, (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal)) := by
          -- The two reindexed supremums are independent and therefore separate.
          exact iSup_iSup_add_eq_add_iSup
            (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)))
            (fun z : H ↦ (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal)))

-- Proof sketch: apply Proposition 13.16 to `f + g ≥ f** + g**`, then use clause (1) together
-- with the general inequality `h** ≤ h` for the EReal-valued infimal convolution of the
-- conjugates.
/-- Proposition 13 24 (2): the conjugate of the pointwise sum is bounded above by the infimal
convolution `f* □ g*` of the conjugates. -/
theorem conjugate_add_le_infimalConvolution_conjugate
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f.asEReal + g.asEReal)∗ ≤ f.asEReal∗ □ g.asEReal∗ := by
  intro u
  -- Route correction: clause (1) only applies to `]-∞,+∞]`-valued inputs, so here we majorize
  -- each affine defect directly against an arbitrary decomposition `u = y + (u - y)`.
  rw [conjugate_apply, infimalConvolution_apply]
  refine le_iInf fun y ↦ ?_
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g x : EReal))) =
        ((((⟪x, y⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
          (((⟪x, u - y⟫_ℝ : ℝ) : EReal) - (g x : EReal))) := by
            -- Split the single affine defect into the two conjugate defects at `y` and `u - y`.
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, sub_eq_add_neg,
              add_sub_assoc] using affine_defect_add_split f g x y (u - y)
    _ ≤ f.asEReal∗ y + g.asEReal∗ (u - y) := by
          -- Each summand is bounded by the corresponding conjugate value.
          refine add_le_add ?_ ?_
          · rw [conjugate_apply]
            exact le_iSup (fun z : H ↦ (((⟪z, y⟫_ℝ : ℝ) : EReal) - (f z : EReal))) x
          · rw [conjugate_apply]
            exact le_iSup (fun z : H ↦ (((⟪z, u - y⟫_ℝ : ℝ) : EReal) - (g z : EReal))) x

/-- Helper for Proposition 13 24: the Moreau quadratic kernel is the positive scalar multiple of
the half-squared norm evaluated at the inverse homothety. -/
lemma moreau_quadratic_kernel_as_ereal_eq_pos_smul_precompose_inv_smul_half_squared_norm
    (γ : Set.Ioi (0 : ℝ)) :
    (moreauQuadraticKernel γ).asEReal =
      fun x : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal (((γ : ℝ)⁻¹) • x) := by
  funext x
  -- Normalize the rescaled quadratic explicitly and use positivity of `γ` to remove `|γ⁻¹|`.
  have hγ : (0 : ℝ) < (γ : ℝ) := γ.2
  rw [Function.asEReal_apply, Function.asEReal_apply, moreauQuadraticKernel_apply,
    halfSquaredNorm_apply]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ)]
  field_simp [ne_of_gt hγ]

/-- Helper for Proposition 13 24: the Fenchel conjugate of the Moreau quadratic kernel is the
scaled half-squared norm. -/
lemma conjugate_moreauQuadraticKernel_eq_smul_halfSquaredNorm
    (γ : Set.Ioi (0 : ℝ)) :
    (moreauQuadraticKernel γ).asEReal∗ =
      (((γ : ℝ) : EReal) • (halfSquaredNorm (H := H)).asEReal) := by
  -- Rewrite the kernel into the exact positive-scaling shape required by Proposition 13.23.
  rw [moreau_quadratic_kernel_as_ereal_eq_pos_smul_precompose_inv_smul_half_squared_norm]
  ext u
  -- Conjugating the scaled precomposition returns the same scaling on the conjugate.
  calc
    (fun x : H ↦ ((γ : ℝ) : EReal) * halfSquaredNorm.asEReal (((γ : ℝ)⁻¹) • x))∗ u =
        ((γ : ℝ) : EReal) * ((halfSquaredNorm (H := H)).asEReal)∗ u := by
          simpa using
            congrFun
              (conjugate_pos_smul_precompose_inv_smul
                (f := (halfSquaredNorm (H := H)).asEReal) γ)
              u
    _ = ((γ : ℝ) : EReal) * (halfSquaredNorm (H := H)).asEReal u := by
          rw [← half_squared_norm_self_conjugate (H := H)]
    _ = ((((γ : ℝ) : EReal) • (halfSquaredNorm (H := H)).asEReal) u) := by
          simp

-- Proof sketch: specialize clause (1) to the decomposition of the Moreau envelope as `f □ qγ`,
-- then identify the conjugate of the quadratic kernel `qγ` with the scaled canonical quadratic
-- owner `γ • halfSquaredNorm.asEReal`.
/-- Proposition 13 24 (3): for every `γ ∈ ℝ_{++}`, the conjugate of the `γ`-Moreau envelope
`{}^[γ] f` is `f* + (γ / 2) ‖·‖²`. -/
theorem conjugate_moreauEnvelope_eq
    (f : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) :
    ({}^[γ] f)∗ = f.asEReal∗ + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
  -- Identify the Moreau envelope with an infimal convolution and then conjugate the kernel.
  calc
    ({}^[γ] f)∗ = (f □ moreauQuadraticKernel γ)∗ := by
      rfl
    _ = f.asEReal∗ + (moreauQuadraticKernel γ).asEReal∗ := by
      exact conjugate_infimalConvolution_eq f (moreauQuadraticKernel γ)
    _ = f.asEReal∗ + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := by
      rw [conjugate_moreauQuadraticKernel_eq_smul_halfSquaredNorm]

section LinearMaps

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable [CompleteSpace H] [CompleteSpace K]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 13 24: the infimal postcomposition rewrites as an indexed infimum over
the concrete fiber subtype. -/
lemma infimal_postcomposition_apply_eq_iInf_fiber
    {α : Type*} [CoeTC α EReal] (L : H → K) (f : H → α) (y : K) :
    (L ▷ f) y = ⨅ x : {x // L x = y}, (f x.1 : EReal) := by
  -- Replace the image of the fiber by the range of the subtype-valued map and use `sInf_range`.
  change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' ({y} : Set K))) =
    ⨅ x : {x // L x = y}, (f x.1 : EReal)
  rw [show ((fun x ↦ (f x : EReal)) '' (L ⁻¹' ({y} : Set K))) =
      Set.range (fun x : {x // L x = y} ↦ (f x.1 : EReal)) by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxy : L x = y := by
        simpa using hx
      exact ⟨⟨x, hxy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, by simp, rfl⟩]
  exact sInf_range

/-- Helper for Proposition 13 24: rewriting the primal-dual pairing through the adjoint leaves
the affine defect unchanged. -/
lemma adjoint_affine_defect
    (L : H →L[ℝ] K) (x : H) (v : K) (a : EReal) :
    (((⟪L x, v⟫_ℝ : ℝ) : EReal) - a) =
      (((⟪x, L.adjoint v⟫_ℝ : ℝ) : EReal) - a) := by
  -- Transport the real adjoint identity through the finite `EReal` shift.
  exact congrArg (fun r : ℝ ↦ ((r : EReal) - a))
    (ContinuousLinearMap.adjoint_inner_right (A := L) x v).symm

-- Proof sketch: expand the fiberwise infimum defining `L ▷ f`, rewrite the dual pairing
-- `⟪L x, v⟫` as `⟪x, L.adjoint v⟫`, and identify the remaining supremum with `f* (L* v)`.
/-- Proposition 13 24 (4): for a bounded linear operator `L : H → K`, the conjugate of the
infimal postcomposition `L ▷ f` is the composition `f* ∘ L*`. -/
theorem conjugate_infimalPostcomposition_eq_comp_adjoint
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    (L ▷ f)∗ = f.asEReal∗ ∘ L.adjoint := by
  ext v
  -- Expand the conjugate and replace the postcomposition infimum by the concrete fiber subtype.
  rw [Function.comp_apply, conjugate_apply, conjugate_apply]
  calc
    (⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (L ▷ f) y)) =
        ⨆ y : K, ⨆ x : {x // L x = y}, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (f x.1 : EReal)) := by
          refine iSup_congr fun y ↦ ?_
          calc
            (((⟪y, v⟫_ℝ : ℝ) : EReal) - (L ▷ f) y) =
                (((⟪y, v⟫_ℝ : ℝ) : EReal) -
                  ⨅ x : {x // L x = y}, (f x.1 : EReal)) := by
                    exact congrArg
                      (fun t : EReal ↦ (((⟪y, v⟫_ℝ : ℝ) : EReal) - t))
                      (infimal_postcomposition_apply_eq_iInf_fiber
                        (L := (L : H → K)) (f := f) (y := y))
            _ = ⨆ x : {x // L x = y}, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (f x.1 : EReal)) := by
                  simpa using
                    ereal_realCast_sub_iInf_eq_iSup_sub
                      (a := ⟪y, v⟫_ℝ)
                      (φ := fun x : {x // L x = y} ↦ (f x.1 : EReal))
    _ = ⨆ p : Σ y : K, {x // L x = y}, (((⟪p.1, v⟫_ℝ : ℝ) : EReal) - (f p.2.1 : EReal)) := by
          -- Replace the iterated supremum by the equivalent sigma-indexed supremum.
          rw [iSup_sigma']
    _ = ⨆ x : H, (((⟪L x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)) := by
          -- Collapse the sigma of fibers back to the primal space through the
          -- canonical equivalence.
          exact (Equiv.sigmaFiberEquiv L).iSup_congr fun p ↦ by
            rcases p with ⟨y, x⟩
            simp [x.2]
    _ = ⨆ x : H, (((⟪x, L.adjoint v⟫_ℝ : ℝ) : EReal) - (f x : EReal)) := by
          -- Move `L` from the primal variable to the dual variable by the adjoint identity.
          refine iSup_congr fun x ↦ ?_
          exact adjoint_affine_defect L x v (f x : EReal)

-- Proof sketch: apply clause (4) to `L.adjoint` and Proposition 13.16 to the inequality
-- `(L.adjoint ▷ f*)* ≤ f ∘ L`, then dualize once more to obtain the stated upper bound by the
-- infimal postcomposition along the adjoint.
/-- Proposition 13 24 (5): for a bounded linear operator `L : K → H`, the conjugate of the
precomposition `f ∘ L` is bounded above by the infimal postcomposition of `f*` along `L*`
(equivalently, the fiberwise infimum over `{v | L* v = u}`). -/
theorem conjugate_comp_le_fiberInf_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (L : K →L[ℝ] H) :
    (f.asEReal ∘ L)∗ ≤ L.adjoint ▷ f.asEReal∗ := by
  intro u
  -- Compare the affine defect at `u` against any dual point on the adjoint fiber above `u`.
  rw [conjugate_apply]
  change (⨆ x : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (f.asEReal ∘ L) x)) ≤
    (L.adjoint ▷ f.asEReal∗) u
  calc
    (⨆ x : K, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (f.asEReal ∘ L) x)) ≤
        ⨅ v : {v // L.adjoint v = u}, (f.asEReal∗ v.1 : EReal) := by
          refine le_iInf fun v ↦ ?_
          refine iSup_le fun x ↦ ?_
          have hpair :
              ⟪x, u⟫_ℝ = ⟪L x, v.1⟫_ℝ := by
            calc
              ⟪x, u⟫_ℝ = ⟪x, L.adjoint v.1⟫_ℝ := by rw [v.2]
              _ = ⟪L x, v.1⟫_ℝ := ContinuousLinearMap.adjoint_inner_right (A := L) x v.1
          -- After rewriting the pairing through the adjoint fiber equation, the term is a single
          -- point of the defining supremum for `f.asEReal∗ v`.
          rw [Function.comp_apply, hpair]
          rw [conjugate_apply]
          exact le_iSup (fun y : H ↦ (((⟪y, v.1⟫_ℝ : ℝ) : EReal) - (f y : EReal))) (L x)
    _ = (L.adjoint ▷ f.asEReal∗) u := by
          symm
          exact infimal_postcomposition_apply_eq_iInf_fiber
            (L := L.adjoint) (f := f.asEReal∗) (y := u)

end LinearMaps

end Conjugation

end ERealFunction
