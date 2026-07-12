import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]

namespace LinearMap

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- Helper for Lemma 15.119.6: a finite projective module can be presented as a split summand of
some finite free module `Fin n → R`. -/
structure SplitFreePresentation where
  rank : ℕ
  pi : (Fin rank → R) →ₗ[R] M
  iota : M →ₗ[R] Fin rank → R
  pi_comp_iota : pi ∘ₗ iota = LinearMap.id

/-- Helper for Lemma 15.119.6: finite projective modules admit split finite free
presentations. -/
theorem nonempty_splitFreePresentation : Nonempty (SplitFreePresentation (R := R) (M := M)) := by
  -- Choose the split surjection supplied by projectivity.
  obtain ⟨n, pi, iota, -, -, hpiiota⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨{ rank := n, pi := pi, iota := iota, pi_comp_iota := hpiiota }⟩

/-- Helper for Lemma 15.119.6: fix one split finite free presentation of a finite projective
module. -/
noncomputable def splitFreePresentation : SplitFreePresentation (R := R) (M := M) :=
  Classical.choice (nonempty_splitFreePresentation (R := R) (M := M))

/-- Helper for Lemma 15.119.6: the ambient free endomorphism lifting an endomorphism of a finite
projective module through a split presentation. -/
def SplitFreePresentation.lift (p : SplitFreePresentation (R := R) (M := M)) (f : M →ₗ[R] M) :
    (Fin p.rank → R) →ₗ[R] Fin p.rank → R :=
  (LinearMap.id - p.iota ∘ₗ p.pi) + p.iota ∘ₗ f ∘ₗ p.pi

/-- The determinant of an endomorphism of a finite projective module, computed on a chosen split
finite free presentation. -/
noncomputable def projectiveDet (f : M →ₗ[R] M) : R :=
  let p := splitFreePresentation (R := R) (M := M)
  LinearMap.det (p.lift f)

/-- Helper for Lemma 15.119.6: after passing to split finite free presentations, the lift of
`1 + a ∘ b` becomes the standard free endomorphism `1 + AB`. -/
theorem lift_id_add_comp_eq_one_add_lifted_comp
    (pM : SplitFreePresentation (R := R) (M := M))
    (pN : SplitFreePresentation (R := R) (M := N))
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    pN.lift (1 + a ∘ₗ b) =
      1 + (pN.iota ∘ₗ a ∘ₗ pM.pi) ∘ₗ (pM.iota ∘ₗ b ∘ₗ pN.pi) := by
  -- Evaluate both maps on an arbitrary vector and use the splitting relation on `M`.
  ext v i
  have hsplit :
      pM.pi (pM.iota (b (pN.pi (Pi.single v (1 : R))))) = b (pN.pi (Pi.single v (1 : R))) := by
    -- The chosen presentation of `M` is a split retract, so `π ∘ ι` is the identity.
    simpa [LinearMap.comp_apply] using
      congrArg (fun f ↦ f (b (pN.pi (Pi.single v (1 : R))))) pM.pi_comp_iota
  simp [SplitFreePresentation.lift, LinearMap.comp_assoc, hsplit, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

/-- Helper for Lemma 15.119.6: on finite free modules, the Weinstein-Aronszajn identity is the
matrix identity `det(1 + AB) = det(1 + BA)`. -/
theorem linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a_free
    [Module.Free R M] [Module.Free R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    LinearMap.det (1 + a ∘ₗ b) = LinearMap.det (1 + b ∘ₗ a) := by
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  let A := LinearMap.toMatrix bM bN a
  let B := LinearMap.toMatrix bN bM b
  have hcompN :
      LinearMap.toMatrix bN bN (a ∘ₗ b) = A * B := by
    -- Compute the matrix of the composite in the chosen bases.
    simpa [A, B] using LinearMap.toMatrix_comp bN bM bN a b
  have hcompM :
      LinearMap.toMatrix bM bM (b ∘ₗ a) = B * A := by
    -- Compute the matrix of the opposite composite in the chosen bases.
    simpa [A, B] using LinearMap.toMatrix_comp bM bN bM b a
  have hN :
      LinearMap.toMatrix bN bN (1 + a ∘ₗ b) = 1 + A * B := by
    -- Add the identity matrix on the `N`-side.
    simp [A, B, hcompN]
  have hM :
      LinearMap.toMatrix bM bM (1 + b ∘ₗ a) = 1 + B * A := by
    -- Add the identity matrix on the `M`-side.
    simp [A, B, hcompM]
  -- Finish on matrices, where the classical determinant identity applies directly.
  calc
    LinearMap.det (1 + a ∘ₗ b) = (1 + A * B).det := by
      rw [← LinearMap.det_toMatrix bN (1 + a ∘ₗ b), hN]
    _ = (1 + B * A).det := Matrix.det_one_add_mul_comm A B
    _ = LinearMap.det (1 + b ∘ₗ a) := by
      rw [← hM, LinearMap.det_toMatrix bM (1 + b ∘ₗ a)]

/-- Lemma 15.119.6: for finite projective `R`-modules `M` and `N`, the determinants of
`id_N + a ∘ b` and `id_M + b ∘ a` agree. -/
@[stacks 0FJF]
theorem det_id_add_a_comp_b_eq_det_id_add_b_comp_a
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    projectiveDet (1 + a ∘ₗ b) = projectiveDet (1 + b ∘ₗ a) := by
  let pM : SplitFreePresentation (R := R) (M := M) := splitFreePresentation (R := R) (M := M)
  let pN : SplitFreePresentation (R := R) (M := N) := splitFreePresentation (R := R) (M := N)
  let A : (Fin pM.rank → R) →ₗ[R] Fin pN.rank → R := pN.iota ∘ₗ a ∘ₗ pM.pi
  let B : (Fin pN.rank → R) →ₗ[R] Fin pM.rank → R := pM.iota ∘ₗ b ∘ₗ pN.pi
  have hN :
      projectiveDet (1 + a ∘ₗ b) = LinearMap.det (1 + A ∘ₗ B) := by
    -- Normalize the lifted `N`-side endomorphism to the standard `1 + AB` form.
    simpa [projectiveDet, A, B, pN] using
      congrArg LinearMap.det
        (lift_id_add_comp_eq_one_add_lifted_comp (pM := pM) (pN := pN) a b)
  have hM :
      projectiveDet (1 + b ∘ₗ a) = LinearMap.det (1 + B ∘ₗ A) := by
    -- Normalize the lifted `M`-side endomorphism to the standard `1 + BA` form.
    simpa [projectiveDet, A, B, pM] using
      congrArg LinearMap.det
        (lift_id_add_comp_eq_one_add_lifted_comp (pM := pN) (pN := pM) b a)
  -- Route correction: work entirely on chosen split finite free presentations and reduce to the
  -- free determinant identity, avoiding the broken determinant-line import chain.
  calc
    projectiveDet (1 + a ∘ₗ b) = LinearMap.det (1 + A ∘ₗ B) := hN
    _ = LinearMap.det (1 + B ∘ₗ A) :=
      linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a_free A B
    _ = projectiveDet (1 + b ∘ₗ a) := hM.symm

section FreeBridge

variable [Module.Free R M] [Module.Free R N]

/-- Bridge/view: in the finite free case, Lemma 15.119.6 is exactly the usual determinant
identity `det(1 + ab) = det(1 + ba)`. -/
theorem linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    LinearMap.det (1 + a ∘ₗ b) = LinearMap.det (1 + b ∘ₗ a) := by
  -- No stabilization is needed in the free case.
  simpa using
    linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a_free (R := R) (M := M) (N := N) a b

end FreeBridge

end LinearMap

end
