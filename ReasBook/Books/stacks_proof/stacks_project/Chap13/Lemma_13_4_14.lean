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
/-- Helper for Lemma 13.4.14: an isomorphism in the arrow category transports kernel existence
backward along the source morphism. -/
private theorem hasKernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasKernel g] : HasKernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Transport the canonical kernel fork of `g` across the object isomorphisms coming from `e`.
  have hcomp : (kernel.ι g ≫ eX.inv) ≫ f = 0 := by
    calc
      (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
        simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
      _ = 0 := by simp
  let fork : KernelFork f := KernelFork.ofι (kernel.ι g ≫ eX.inv) hcomp
  -- The universal property also transports along the same arrow-category square.
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_fork : (Iso.refl _).hom ≫ fork.ι = kernel.ι g ≫ eX.inv := by
    simp [fork]
  refine ⟨⟨fork, ?_⟩⟩
  exact IsKernel.ofIso g (kernelIsKernel g) fork eX.symm eY.symm (Iso.refl _) h_arrow h_fork

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Helper for Lemma 13.4.14: an isomorphism in the arrow category transports cokernel existence
backward along the source morphism. -/
private theorem hasCokernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasCokernel g] : HasCokernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  -- Transport the canonical cokernel cofork of `g` across the object isomorphisms from `e`.
  have hcomp : f ≫ (eY.hom ≫ cokernel.π g) = 0 := by
    calc
      f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
        simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
      _ = 0 := by simp
  let cofork : CokernelCofork f := CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) hcomp
  -- The cocone comparison is again the square encoded by the arrow-category isomorphism.
  have h_arrow : eX.inv ≫ f = g ≫ eY.inv := by
    simpa [eX, eY] using Arrow.w e.inv
  have h_cofork : eY.inv ≫ cofork.π = cokernel.π g ≫ (Iso.refl _).hom := by
    simp [cofork]
  refine ⟨⟨cofork, ?_⟩⟩
  exact IsCokernel.ofIso g (cokernelIsCokernel g) cofork eX.symm eY.symm (Iso.refl _) h_arrow
    h_cofork

/-- Helper for Lemma 13.4.14: in a pre-triangulated category, every split epimorphism has a
kernel. -/
private theorem split_epi_hasKernel_of_pretriangulated {X Y : D} (f : X ⟶ Y) [IsSplitEpi f] :
    HasKernel f := by
  -- Extend `f` to a distinguished triangle and force the third morphism to vanish using epiness.
  obtain ⟨K, i, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi f)
  -- The split triangle is canonically isomorphic to the biproduct triangle on `K` and `Y`.
  obtain ⟨e, _, hf⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i f h) hT hzero
  have h_arrow : e.hom ≫ (biprod.snd : K ⊞ Y ⟶ Y) = f ≫ (Iso.refl Y).hom := by
    simpa using hf.symm
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.snd : K ⊞ Y ⟶ Y) := Arrow.isoMk e (Iso.refl _) h_arrow
  -- Transport the standard kernel of `biprod.snd` back along the induced arrow isomorphism.
  exact hasKernel_of_arrow_iso e'

/-- Helper for Lemma 13.4.14: in a pre-triangulated category, every split monomorphism has a
cokernel. -/
private theorem split_mono_hasCokernel_of_pretriangulated {X Y : D} (f : X ⟶ Y) [IsSplitMono f] :
    HasCokernel f := by
  -- Extend `f` to a distinguished triangle and force the third morphism to vanish using monicity.
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ _ hT (inferInstance : Mono f)
  -- The split triangle is canonically isomorphic to the biproduct triangle on `X` and `Z`.
  obtain ⟨e, hf, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT hzero
  have h_arrow : (Iso.refl X).hom ≫ (biprod.inl : X ⟶ X ⊞ Z) = f ≫ e.hom := by
    simpa using hf.symm
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.inl : X ⟶ X ⊞ Z) := Arrow.isoMk (Iso.refl _) e h_arrow
  -- Transport the standard cokernel of `biprod.inl` back along the induced arrow isomorphism.
  exact hasCokernel_of_arrow_iso e'

-- Proof sketch: apply the owner theorem
-- `isIdempotentComplete_of_countableProducts_of_splitEpi_kernels`. In a pretriangulated category,
-- every split epi extends to a distinguished triangle whose third morphism vanishes, hence the
-- split theorem `exists_iso_binaryBiproduct_of_distTriang` identifies it with `biprod.snd`; the
-- standard kernel of `biprod.snd` then transports back along the resulting arrow isomorphism.
/-- Lemma 13.4.14 (1): in a pre-triangulated category with countable products, idempotents split.
-/
@[stacks 05QW]
theorem pretriangulated_isIdempotentComplete_of_countableProducts [HasCountableProducts D] :
    IsIdempotentComplete D := by
  -- Reduce to the canonical countable-product criterion from Lemma 12.4.3.
  refine isIdempotentComplete_of_countableProducts_of_splitEpi_kernels ?_
  -- The source proof reduces split epimorphisms to the kernel existence statement above.
  intro X Y f _
  exact split_epi_hasKernel_of_pretriangulated f

-- Proof sketch: argue dually with
-- `isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels`. A split mono extends to a
-- distinguished triangle whose first morphism vanishes, so the same pretriangulated splitting
-- theorem identifies it with `biprod.inl`; the standard cokernel of `biprod.inl` transports back
-- along the induced arrow isomorphism.
/-- Lemma 13.4.14 (2): in a pre-triangulated category with countable coproducts, idempotents
split. -/
@[stacks 05QW]
theorem pretriangulated_isIdempotentComplete_of_countableCoproducts [HasCountableCoproducts D] :
    IsIdempotentComplete D := by
  -- Reduce to the canonical countable-coproduct criterion from Lemma 12.4.3.
  refine isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels ?_
  -- The dual source argument reduces split monomorphisms to the cokernel existence statement.
  intro X Y f _
  exact split_mono_hasCokernel_of_pretriangulated f

end CategoryTheory
