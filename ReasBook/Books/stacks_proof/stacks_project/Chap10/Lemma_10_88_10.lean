import Mathlib
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w t

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Lemma 10 88 10: a finite free `ModuleCat` object is finitely presented. -/
private lemma finitePresentation_of_finite_free_moduleCat
    (F : ModuleCat.{max u v w} R) [Module.Free R F] [Module.Finite R F] :
    Module.FinitePresentation R F := by
  letI : Module.Projective R F := Module.Projective.of_free
  -- Proof comment: finite free modules are projective and finite, so the standard projective
  -- finite-presentation lemma applies.
  exact Module.finitePresentation_of_projective R F

/-- Helper for Chap10 Lemma 10 88 10: vanishing after tensoring with the shrunken unit detects
pointwise vanishing. -/
private lemma eq_zero_of_rTensor_shrink_one_eq_zero
    [Small.{max u v w} R]
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (x : A)
    (h : (f.rTensor (Shrink.{max u v w} R))
      (x ⊗ₜ[R] ((Shrink.linearEquiv R R).symm 1)) = 0) :
    f x = 0 := by
  let eB : B ⊗[R] (Shrink.{max u v w} R) ≃ₗ[R] B ⊗[R] R :=
    TensorProduct.congr (LinearEquiv.refl R B) (Shrink.linearEquiv R R)
  have hR : (f.rTensor R) (x ⊗ₜ[R] (1 : R)) = 0 := by
    -- Proof comment: transport the shrunken tensor factor back to `R`, carrying the assumed
    -- vanishing to the ordinary tensor with `1`.
    calc
      (f.rTensor R) (x ⊗ₜ[R] (1 : R)) =
          eB ((f.rTensor (Shrink.{max u v w} R))
            (x ⊗ₜ[R] ((Shrink.linearEquiv R R).symm 1))) := by
        simp [eB, LinearMap.rTensor_tmul]
      _ = eB 0 := by rw [h]
      _ = 0 := by simp [eB]
  have hRid := congrArg (TensorProduct.rid R B) hR
  -- Proof comment: the right unitor identifies `f x ⊗ 1` with `f x`.
  simpa [LinearMap.rTensor_tmul, TensorProduct.rid_tmul] using hRid

/-- Helper for Chap10 Lemma 10 88 10: equality of tensor kernels after precomposition forces the
upstairs witness to kill `LinearMap.ker π`. -/
private lemma ker_le_of_tensorKernel_eq_comp
    [Small.{max u v w} R]
    {L P Q : Type (max u v w)} {T : Type t}
    [AddCommGroup L] [Module R L]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (π : L →ₗ[R] P) (f : P →ₗ[R] T) (gL : L →ₗ[R] Q)
    (hker : ∀ N : ModuleCat.{max u v w} R,
      LinearMap.ker ((f.comp π).rTensor N) = LinearMap.ker (gL.rTensor N))
    {x : L} (hx : x ∈ LinearMap.ker π) :
    x ∈ LinearMap.ker gL := by
  let s : Shrink.{max u v w} R := (Shrink.linearEquiv R R).symm 1
  have hx0 : π x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hxTensor :
      (x ⊗ₜ[R] s) ∈ LinearMap.ker (((f.comp π).rTensor (Shrink.{max u v w} R))) := by
    -- Proof comment: an element of `ker π` maps to zero after tensoring the composite
    -- `f.comp π`.
    simp [LinearMap.mem_ker, LinearMap.rTensor_tmul, s, hx0]
  have hgTensor : (x ⊗ₜ[R] s) ∈ LinearMap.ker (gL.rTensor (Shrink.{max u v w} R)) := by
    let N : ModuleCat.{max u v w} R := ModuleCat.of.{max u v w} R (Shrink.{max u v w} R)
    have hxTensorN : (x ⊗ₜ[R] s) ∈ LinearMap.ker (((f.comp π).rTensor N)) := by
      simpa [N] using hxTensor
    -- Proof comment: specialize the assumed equality of tensor kernels to the shrunken copy
    -- of `R`.
    simpa [N] using (show (x ⊗ₜ[R] s) ∈ LinearMap.ker (gL.rTensor N) from
      (by simpa [hker N] using hxTensorN))
  have hgZero : (gL.rTensor (Shrink.{max u v w} R)) (x ⊗ₜ[R] s) = 0 := by
    simpa [LinearMap.mem_ker] using hgTensor
  have hxg : gL x = 0 :=
    eq_zero_of_rTensor_shrink_one_eq_zero.{u, v, w}
      (R := R) (A := L) (B := Q) gL x (by simpa [s] using hgZero)
  simpa [LinearMap.mem_ker] using hxg

/-- Helper for Chap10 Lemma 10 88 10: the map descended through `ker π` composes with `π` to the
original map. -/
private lemma quotKer_descendedMap_comp
    {L P Q : Type (max u v w)}
    [AddCommGroup L] [Module R L]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (π : L →ₗ[R] P) (gL : L →ₗ[R] Q)
    (hπ : Function.Surjective π)
    (hker : LinearMap.ker π ≤ LinearMap.ker gL) :
    (((LinearMap.ker π).liftQ gL hker).comp
      (π.quotKerEquivOfSurjective hπ).symm.toLinearMap).comp π = gL := by
  -- Proof comment: on representatives this is exactly the quotient-by-kernel computation rule.
  ext x
  simp [LinearMap.comp_assoc]

/-- Helper for Chap10 Lemma 10 88 10: a tensor-kernel equality after precomposition by a
surjection descends. -/
private lemma tensor_kernel_eq_of_surjective_comp
    {L P Q : Type (max u v w)} {T : Type t}
    [AddCommGroup L] [Module R L]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (π : L →ₗ[R] P) (hπ : Function.Surjective π)
    (f : P →ₗ[R] T) (g : P →ₗ[R] Q)
    (hker : ∀ N : ModuleCat.{max u v w} R,
      LinearMap.ker ((f.comp π).rTensor N) = LinearMap.ker ((g.comp π).rTensor N))
    (N : ModuleCat.{max u v w} R) :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective (Q := N) hπ x
    have hx0 : (f.rTensor N) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hyF0 : (((f.comp π).rTensor N) y) = 0 := by
      -- Proof comment: lift `x` along `π.rTensor N`, then rewrite tensoring of the composite.
      calc
        (((f.comp π).rTensor N) y) = (f.rTensor N) ((π.rTensor N) y) := by
          simp [LinearMap.rTensor_comp]
        _ = (f.rTensor N) x := by rw [hy]
        _ = 0 := hx0
    have hyF : y ∈ LinearMap.ker (((f.comp π).rTensor N)) := by
      simpa [LinearMap.mem_ker] using hyF0
    have hyG : y ∈ LinearMap.ker (((g.comp π).rTensor N)) := by
      simpa [hker N] using hyF
    have hyG0 : (((g.comp π).rTensor N) y) = 0 := by
      simpa [LinearMap.mem_ker] using hyG
    have hxG0 : (g.rTensor N) x = 0 := by
      calc
        (g.rTensor N) x = (g.rTensor N) ((π.rTensor N) y) := by rw [hy]
        _ = (((g.comp π).rTensor N) y) := by
          simp [LinearMap.rTensor_comp]
        _ = 0 := hyG0
    simpa [LinearMap.mem_ker] using hxG0
  · intro x hx
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective (Q := N) hπ x
    have hx0 : (g.rTensor N) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hyG0 : (((g.comp π).rTensor N) y) = 0 := by
      -- Proof comment: the reverse inclusion is the same lifting argument with `f` and `g`
      -- interchanged.
      calc
        (((g.comp π).rTensor N) y) = (g.rTensor N) ((π.rTensor N) y) := by
          simp [LinearMap.rTensor_comp]
        _ = (g.rTensor N) x := by rw [hy]
        _ = 0 := hx0
    have hyG : y ∈ LinearMap.ker (((g.comp π).rTensor N)) := by
      simpa [LinearMap.mem_ker] using hyG0
    have hyF : y ∈ LinearMap.ker (((f.comp π).rTensor N)) := by
      simpa [hker N] using hyG
    have hyF0 : (((f.comp π).rTensor N) y) = 0 := by
      simpa [LinearMap.mem_ker] using hyF
    have hxF0 : (f.rTensor N) x = 0 := by
      calc
        (f.rTensor N) x = (f.rTensor N) ((π.rTensor N) y) := by rw [hy]
        _ = (((f.comp π).rTensor N) y) := by
          simp [LinearMap.rTensor_comp]
        _ = 0 := hyF0
    simpa [LinearMap.mem_ker] using hxF0

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the finitely
  presented tensor-kernel criterion from Proposition `10.88.6`.
* inspected owner declarations:
  `directed_colimit_presentation_mittag_leffler_tfae` from `Proposition_10_88_6`,
  `Module.FinitePresentation.equiv_quotient`, and
  `Module.finitePresentation_of_projective`.
* best owner abstraction: the finitely presented tensor-kernel criterion, with finitely presented
  modules as the canonical auxiliary presentation objects.
* layer: `source-facing`; this lemma is the finite-free-source bridge to that criterion.
* primitive data: the module `M`, a finite free source module `F`, and a map `f : F →ₗ[R] M`.
* derived API: the finitely presented comparison module `Q` and the tensor-kernel comparison map
  produced from the criterion.
-/
-- Proof sketch: one direction specializes the finitely presented criterion from Proposition
-- `10.88.6` to finite free source modules. For the converse, given a map from a finitely presented
-- module, use the canonical finite free presentation of that source from
-- `Module.FinitePresentation.equiv_quotient`, apply the assumed finite-free condition on the
-- presenting free module, and descend the resulting comparison map through the quotient to recover
-- the finitely presented criterion.
/-- Chap10 Lemma 10 88 10: an `R`-module `M` is Mittag-Leffler if and only if every map from a finite
free `R`-module to `M` has the same tensor kernels as some map to a finitely presented
`R`-module. -/
@[stacks 05CP]
theorem mittagLeffler_iff_finiteFree_maps_share_tensor_kernels_with_finitelyPresented_maps :
    (∀ (P : ModuleCat.{max u v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (Q : ModuleCat.{max u v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
          ∀ N : ModuleCat.{max u v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : ModuleCat.{max u v w} R) [Module.Free R F] [Module.Finite R F] (f : F →ₗ[R] M),
        ∃ (Q : ModuleCat.{max u v w} R) (_ : Module.FinitePresentation R Q) (g : F →ₗ[R] Q),
          ∀ N : ModuleCat.{max u v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  constructor
  · intro h F _ _ f
    letI : Module.FinitePresentation R F :=
      finitePresentation_of_finite_free_moduleCat.{u, v, w} F
    -- Proof comment: the finitely-presented-source criterion immediately applies to a finite
    -- free source after installing the standard finite-presentation instance.
    exact h F f
  · intro hfree P _ f
    classical
    letI : Small.{max u v w} R := inferInstance
    obtain ⟨L, hAddL, hModL, K, e, hFreeL, hFiniteL, _hKfg⟩ :=
      Module.FinitePresentation.equiv_quotient
        (R := R) (M := (P : Type (max u v w)))
    letI : AddCommGroup L := hAddL
    letI : Module R L := hModL
    letI : Module.Free R L := hFreeL
    letI : Module.Finite R L := hFiniteL
    let π : L →ₗ[R] P := e.symm.toLinearMap.comp K.mkQ
    have hπ : Function.Surjective π := by
      intro p
      obtain ⟨q, hq⟩ := e.symm.surjective p
      obtain ⟨l, hl⟩ := Submodule.mkQ_surjective K q
      refine ⟨l, ?_⟩
      -- Proof comment: the presentation map is the quotient map followed by the presentation
      -- equivalence.
      simp [π, hl, hq]
    obtain ⟨Q, hQfp, gL, hkerL⟩ :=
      hfree (ModuleCat.of.{max u v w} R L) (f.comp π)
    have hkerπ : LinearMap.ker π ≤ LinearMap.ker gL := by
      intro x hx
      -- Proof comment: testing the upstairs equality at the shrunken unit shows that the
      -- comparison map kills the kernel of the finite-free presentation.
      exact ker_le_of_tensorKernel_eq_comp.{u, v, w, v} (R := R) π f gL hkerL hx
    let gP : P →ₗ[R] Q :=
      ((LinearMap.ker π).liftQ gL hkerπ).comp
        (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
    refine ⟨Q, hQfp, gP, ?_⟩
    intro N
    have hgP_comp : gP.comp π = gL :=
      quotKer_descendedMap_comp.{u, v, w} (R := R) π gL hπ hkerπ
    -- Proof comment: the finite-free tensor-kernel equality descends along the surjective
    -- presentation map `π`.
    exact tensor_kernel_eq_of_surjective_comp.{u, v, w, v} (R := R) π hπ f gP (by
      intro N
      simpa [hgP_comp] using hkerL N) N

end

end Module
