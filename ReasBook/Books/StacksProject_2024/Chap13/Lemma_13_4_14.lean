import Mathlib
import StacksProject_2024.Chap12.Lemma_12_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryTheory.Arrow
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.14:
- primary domain: pretriangulated categories, distinguished triangles, and the canonical owner
  notion `IsIdempotentComplete D`;
- sampled owner declarations:
  `IsIdempotentComplete`,
  `isIdempotentComplete_of_countableProducts_of_splitEpi_kernels`,
  `isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels`,
  `exists_iso_binaryBiproduct_of_distTriang`,
  `IsKernel.ofIso`,
  `IsCokernel.ofIso`;
- best owner abstraction: the public target of the Stacks lemma is the canonical owner
  `IsIdempotentComplete D`, while the pretriangulated input is expressed through the distinguished
  triangle API and the standard biproduct kernels/cokernels;
- primitive data vs derived API: the primitive data are only the ambient pretriangulated category
  and the countable product/coproduct hypotheses. The kernels of split epis and cokernels of split
  monos are derived by identifying such morphisms with the canonical biproduct projection/inclusion
  and transporting the standard kernel/cokernel along an arrow isomorphism.

Source/core/bridge triage:
- `source-facing`: the two implications recorded in Lemma 13.4.14;
- `core/canonical`: `IsIdempotentComplete D`;
- `bridge/view`: `Lemma_12_4_3` together with the pretriangulated biproduct splitting of a
  distinguished triangle whose remaining morphism vanishes.
-/

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private theorem hasKernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasKernel g] : HasKernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  refine ⟨⟨KernelFork.ofι (kernel.ι g ≫ eX.inv) ?_, ?_⟩⟩
  · show (kernel.ι g ≫ eX.inv) ≫ f = 0
    calc
      (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
        simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
      _ = 0 := by simp
  · exact IsKernel.ofIso g (kernelIsKernel g)
      (KernelFork.ofι (kernel.ι g ≫ eX.inv) (by
        show (kernel.ι g ≫ eX.inv) ≫ f = 0
        calc
          (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
            simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
          _ = 0 := by simp))
      eX.symm eY.symm (Iso.refl _) (by simpa [eX, eY] using Arrow.w e.inv) (by simp)

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private theorem hasCokernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasCokernel g] : HasCokernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  refine ⟨⟨CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) ?_, ?_⟩⟩
  · show f ≫ (eY.hom ≫ cokernel.π g) = 0
    calc
      f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
        simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
      _ = 0 := by simp
  · exact IsCokernel.ofIso g (cokernelIsCokernel g)
      (CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) (by
        show f ≫ (eY.hom ≫ cokernel.π g) = 0
        calc
          f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
            simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
          _ = 0 := by simp))
      eX.symm eY.symm (Iso.refl _) (by simpa [eX, eY] using Arrow.w e.inv) (by simp)

-- Proof sketch: apply the owner theorem
-- `isIdempotentComplete_of_countableProducts_of_splitEpi_kernels`. In a pretriangulated category,
-- every split epi extends to a distinguished triangle whose third morphism vanishes, hence the
-- split theorem `exists_iso_binaryBiproduct_of_distTriang` identifies it with `biprod.snd`; the
-- standard kernel of `biprod.snd` then transports back along the resulting arrow isomorphism.
/-- Lemma 13.4.14 (1): in a pre-triangulated category with countable products, idempotents split.
-/
theorem pretriangulated_isIdempotentComplete_of_countableProducts [HasCountableProducts D] :
    IsIdempotentComplete D := by
  refine isIdempotentComplete_of_countableProducts_of_splitEpi_kernels ?_
  intro X Y f _
  obtain ⟨K, i, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi f)
  obtain ⟨e, _, hf⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i f h) hT hzero
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.snd : K ⊞ Y ⟶ Y) :=
    Arrow.isoMk e (Iso.refl _) (by simpa using hf.symm)
  letI : HasKernel (biprod.snd : K ⊞ Y ⟶ Y) := inferInstance
  exact hasKernel_of_arrow_iso e'

-- Proof sketch: argue dually with
-- `isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels`. A split mono extends to a
-- distinguished triangle whose first morphism vanishes, so the same pretriangulated splitting
-- theorem identifies it with `biprod.inl`; the standard cokernel of `biprod.inl` transports back
-- along the induced arrow isomorphism.
/-- Lemma 13.4.14 (2): in a pre-triangulated category with countable coproducts, idempotents
split. -/
theorem pretriangulated_isIdempotentComplete_of_countableCoproducts [HasCountableCoproducts D] :
    IsIdempotentComplete D := by
  refine isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels ?_
  intro X Y f _
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ _ hT (inferInstance : Mono f)
  obtain ⟨e, hf, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT hzero
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.inl : X ⟶ X ⊞ Z) :=
    Arrow.isoMk (Iso.refl _) e (by simpa using hf.symm)
  letI : HasCokernel (biprod.inl : X ⟶ X ⊞ Z) := inferInstance
  exact hasCokernel_of_arrow_iso e'

end CategoryTheory
