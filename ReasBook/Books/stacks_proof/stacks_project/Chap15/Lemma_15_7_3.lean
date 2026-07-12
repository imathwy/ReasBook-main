import Mathlib
import StacksProject_2024.Chap15.Situation_15_7_1

open CategoryTheory Limits

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

-- Proof sketch: an element of `ker(A' → A)` determines the pullback pair `(0, a')`, so the image
-- of `ker(B' → B)` in `A'` is exactly `ker(A' → A)`.
/-- In Situation `15.7.1`, the kernel of `B' → B` maps onto the kernel of `A' → A`. -/
theorem kernelIdealToB_image_eq_kernelIdealInAprime
    (S : Situation) :
    Ideal.map S.bprimeToAprime (RingHom.ker S.bprimeToB) = RingHom.ker S.fromAprime := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine RingHom.mem_ker.mpr ?_
    rw [← show S.toA (S.bprimeToB x) = S.fromAprime (S.bprimeToAprime x) from
      congrArg (fun k ↦ k x) S.comm]
    simpa using congrArg S.toA (RingHom.mem_ker.mp hx)
  · intro x hx
    let f : CommRingCat.of B ⟶ CommRingCat.of A := CommRingCat.ofHom S.toA
    let g : CommRingCat.of A' ⟶ CommRingCat.of A := CommRingCat.ofHom S.fromAprime
    let y : ↑(pullback f g) :=
      Concrete.pullbackMk f g (0 : B) x
        (by simpa [f, g] using (RingHom.mem_ker.mp hx).symm)
    have hy : y ∈ RingHom.ker S.bprimeToB := by
      refine RingHom.mem_ker.mpr ?_
      change pullback.fst f g y = 0
      simp [y, f, g]
    rw [← show S.bprimeToAprime y = x by
      change pullback.snd f g y = x
      simp [y, f, g]]
    exact Ideal.mem_map_of_mem S.bprimeToAprime hy

theorem dprimeToCPrime_comp_bprimeToDp
    (S : Situation) :
    S.dprimeToCPrime.comp S.bprimeToDp = S.aprimeToCPrime.comp S.bprimeToAprime := by
  ext x
  change
    (((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom.comp
      (algebraMap S.Bprime Dp)) x) =
      (((Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom.comp
        (algebraMap S.Bprime A')) x)
  simpa using congrArg (fun f : S.Bprime →+* S.CPrime ↦ f x)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      ((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom.comp
          (algebraMap S.Bprime Dp)) =
        ((Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom.comp
          (algebraMap S.Bprime A')))

-- Proof sketch: write `C' = D' ⊗[B'] A'`. Then `I C'` is the image of `D' ⊗[B'] I → C'` by the
-- tensor-product description of extended ideals. The pullback hypothesis identifies
-- `ker(B' → B)` with `ker(A' → A)` via `B' → A'`, so tensoring with `D'` transports generators of
-- `J D'` onto generators of `I C'`.
/-- Lemma 15.7.3: in Situation 15.7.1, if `J = ker(B' → B)`, then the image of the extended ideal
`J D'` under the canonical map `D' → C'` is the extended ideal `I C'`, equivalently the map
`J D' → I C'` is surjective. -/
@[stacks 08KN]
theorem kernelIdealToBInDp_image_eq_kernelIdealInCPrime
    (S : Situation) :
    Ideal.map S.dprimeToCPrime (Ideal.map S.bprimeToDp (RingHom.ker S.bprimeToB)) =
      Ideal.map S.aprimeToCPrime (RingHom.ker S.fromAprime) := by
  rw [Ideal.map_map, S.dprimeToCPrime_comp_bprimeToDp, ← Ideal.map_map]
  simpa using congrArg (Ideal.map S.aprimeToCPrime) (S.kernelIdealToB_image_eq_kernelIdealInAprime)

end FiberProductBaseChangeSituation

end
