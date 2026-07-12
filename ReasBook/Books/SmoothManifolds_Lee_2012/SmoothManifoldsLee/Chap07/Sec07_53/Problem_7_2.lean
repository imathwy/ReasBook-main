import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uH uE uG

-- Domain sampling: these statements live in Lie-group differential calculus. The source-facing
-- identities are best stated on the canonical identity-tangent owner `GroupLieAlgebra I G`, and
-- `mfderiv%` is the transport-stable manifold-derivative surface for these formulas.

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]

/-- Helper for Problem 7-2: `invMfderivAtOne X` is the derivative of inversion at `1`,
transported along `inv_one` to the canonical identity tangent space `GroupLieAlgebra I G`. -/
noncomputable abbrev invMfderivAtOne (X : GroupLieAlgebra I G) : GroupLieAlgebra I G :=
  Eq.ndrec (motive := fun g => TangentSpace I g)
    (mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) inv_one

/-- Helper for Problem 7-2: the transported value `invMfderivAtOne X` agrees with the raw
inversion derivative at `1`. -/
lemma invMfderivAtOne_eq
    (X : GroupLieAlgebra I G) :
    invMfderivAtOne X = mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X := by
  apply HEq.eq
  exact rec_heq_of_heq
    (e := (inv_one : (1 : G)⁻¹ = (1 : G)))
    (x := mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X)
    HEq.rfl

/-- Problem 7-2 (1): after identifying `T_(1,1)(G × G)` with `T₁G × T₁G`, the derivative of the
multiplication map at the identity pair sends `(X, Y)` to `X + Y`. -/
theorem mfderiv_mul_at_one_one_apply
    (X Y : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) (X, Y) = X + Y := by
  -- Differentiate multiplication by splitting it into the two coordinate directions.
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) := by
    simpa using (contMDiff_mul I (∞ : WithTop ℕ∞)).mdifferentiableAt
  have mulRight_eq_id : (fun z : G ↦ z * 1) = id := by
    funext z
    simp
  have oneMul_eq_id : (fun z : G ↦ 1 * z) = id := by
    funext z
    simp
  have happly :=
    mfderiv_prod_eq_add_apply
      (I := I) (I' := I) (I'' := I)
      (M := G) (M' := G) (M'' := G)
      (f := fun p : G × G ↦ p.1 * p.2)
      (p := ((1 : G), (1 : G)))
      (v := (X, Y))
      hMul
  rw [mulRight_eq_id, oneMul_eq_id] at happly
  simpa using happly

/-- Helper for Problem 7-2: the derivative of `g ↦ (g, g⁻¹)` at `1` is the product of the
identity derivative and the inversion derivative. -/
lemma pairWithInvMfderiv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X =
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) := by
  -- Differentiate the two coordinates separately and repackage them in the product tangent space.
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    simpa using (contMDiff_inv I (∞ : WithTop ℕ∞)).mdifferentiableAt
  have hmfderiv :
      mfderiv% (fun g : G ↦ ((id : G → G) g, (fun g : G ↦ g⁻¹) g)) (1 : G) =
        (mfderiv% (id : G → G) (1 : G)).prod (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)) :=
    mfderiv_prodMk mdifferentiableAt_id hInv
  have happly := congrArg
    (fun F : TangentSpace I (1 : G) →L[𝕜] TangentSpace (I.prod I) ((1 : G), (1 : G)⁻¹) ↦ F X)
    hmfderiv
  simpa using happly

/-- Helper for Problem 7-2: differentiating the identity `g * g⁻¹ = 1` at `1` gives zero. -/
lemma mulInvCompositeMfderiv_apply_eq_zero
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X = 0 := by
  -- Rewrite the composite to the constant map `1` and differentiate that constant map.
  have hfun : (fun g : G ↦ g * g⁻¹) = fun _ : G ↦ (1 : G) := by
    funext g
    simp
  calc
    mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X
        = mfderiv% (fun _ : G ↦ (1 : G)) (1 : G) X := by
          rw [hfun]
          rfl
    _ = 0 := by
      rw [mfderiv_const]
      rfl

/-- Helper for Problem 7-2: multiplying the pair `(X, di₁ X)` at the identity pair gives
`X + invMfderivAtOne X`. -/
lemma mfderiv_mul_at_one_invMfderiv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) = X + invMfderivAtOne X := by
  -- Normalize the inversion derivative into `GroupLieAlgebra I G` and reuse part (1).
  rw [inv_one]
  simpa [invMfderivAtOne_eq] using
    (mfderiv_mul_at_one_one_apply X (invMfderivAtOne X))

/-- Problem 7-2 (2): the derivative of the inversion map at the identity sends `X` to `-X`. -/
theorem mfderiv_inv_at_one_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = -X := by
  -- Route correction: rewrite `g ↦ g * g⁻¹` as a genuine composition so the chain rule applies
  -- directly to the pair map `g ↦ (g, g⁻¹)`.
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹) := by
    simpa using (contMDiff_mul I (∞ : WithTop ℕ∞)).mdifferentiableAt
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    simpa using (contMDiff_inv I (∞ : WithTop ℕ∞)).mdifferentiableAt
  have hPair : MDiffAt (fun g : G ↦ (g, g⁻¹)) (1 : G) := by
    exact mdifferentiableAt_id.prodMk hInv
  have hcomp :
      mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X =
        mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
          (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
    have hfun :
        (fun g : G ↦ g * g⁻¹) =
          (fun p : G × G ↦ p.1 * p.2) ∘ fun g : G ↦ (g, g⁻¹) := by
      rfl
    rw [hfun]
    simpa using (mfderiv_comp_apply (x := (1 : G))
      (g := fun p : G × G ↦ p.1 * p.2)
      (f := fun g : G ↦ (g, g⁻¹))
      hMul hPair X)
  have hneg : -X = invMfderivAtOne X := by
    apply (neg_eq_iff_add_eq_zero).2
    -- Evaluate the multiplication derivative on the product tangent vector from the pair map.
    calc
      X + invMfderivAtOne X
          = mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
              (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
            rw [pairWithInvMfderiv_apply]
            exact (mfderiv_mul_at_one_invMfderiv_apply X).symm
      _ = mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X := hcomp.symm
      _ = 0 := mulInvCompositeMfderiv_apply_eq_zero X
  -- Turn the additive identity into the explicit formula for the inversion derivative.
  calc
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = invMfderivAtOne X := (invMfderivAtOne_eq X).symm
    _ = -X := hneg.symm
