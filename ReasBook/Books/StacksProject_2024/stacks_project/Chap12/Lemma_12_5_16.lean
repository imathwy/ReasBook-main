import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Category Limits
open ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)

/- Domain-style sampling for Lemma 12.5.16:
- primary domain: exactness of the kernel and cokernel rows induced by a morphism of short
  complexes in an abelian category;
- inspected owner declarations:
  `ShortComplex.exact_iff_exact_up_to_refinements`,
  `ShortComplex.Exact.exact_up_to_refinements`,
  `ShortComplex.exact_unop_iff`,
  `CategoryTheory.kernelOpUnop`;
- best owner abstraction: `ShortComplex.Exact`, accessed through the refinement criterion
  `exact_up_to_refinements`, is the core exactness owner matching the textbook assumptions, while
  the induced kernel and cokernel rows themselves are built canonically from `kernel.map` and
  `cokernel.map`; the stronger snake-lemma owner `ShortComplex.SnakeInput` packages extra endpoint
  exactness hypotheses that this lemma does not assume;
- primitive data: a morphism `φ : S₁ ⟶ S₂`, exactness of one horizontal row, and one endpoint
  mono/epi hypothesis;
- derived API: exactness of the induced row on kernels or cokernels.

Source/core/bridge triage:
- `source-facing`: the two exactness statements for the kernel row and cokernel row of `φ`;
- `core/canonical`: `ShortComplex.Exact.exact_up_to_refinements`, `kernel.map`, `cokernel.map`,
  and the opposite-category comparison isomorphisms;
- `bridge/view`: this file keeps the source-facing theorem names, but rewrites them directly in
  terms of the core owner API instead of introducing parallel local row definitions.
-/

private noncomputable abbrev kernelRow (φ : S₁ ⟶ S₂) : ShortComplex C :=
  ShortComplex.mk
    (kernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
    (kernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)

private noncomputable abbrev cokernelRow (φ : S₁ ⟶ S₂) : ShortComplex C :=
  ShortComplex.mk
    (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
    (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)

private noncomputable def cokernelRowIsoUnopKernelRowOpMap (φ : S₁ ⟶ S₂) :
    cokernelRow φ ≅ (kernelRow (opMap φ)).unop :=
  ShortComplex.isoMk
    (kernelOpUnop φ.τ₁).symm
    (kernelOpUnop φ.τ₂).symm
    (kernelOpUnop φ.τ₃).symm
    (by
      have hπ₁ :
          cokernel.π φ.τ₁ ≫ (kernelOpUnop φ.τ₁).symm.hom =
            (kernel.ι (φ.τ₁.op)).unop := by
        simpa using (kernel.ι_op φ.τ₁).symm
      have hπ₂ :
          cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom =
            (kernel.ι (φ.τ₂.op)).unop := by
        simpa using (kernel.ι_op φ.τ₂).symm
      have hK :
          (kernelRow (opMap φ)).g ≫ kernel.ι (φ.τ₁.op) =
            kernel.ι (φ.τ₂.op) ≫ S₂.f.op := by
        change
          kernel.map (opMap φ).τ₂ (opMap φ).τ₃ (S₂.op).g (S₁.op).g (opMap φ).comm₂₃ ≫
              kernel.ι (φ.τ₁.op) =
            kernel.ι (φ.τ₂.op) ≫ S₂.f.op
        simp [kernel.map]
      apply (cancel_epi (cokernel.π φ.τ₁)).1
      calc
        cokernel.π φ.τ₁ ≫ (kernelOpUnop φ.τ₁).symm.hom ≫ (kernelRow (opMap φ)).unop.f =
            (kernel.ι (φ.τ₁.op)).unop ≫ (kernelRow (opMap φ)).unop.f := by
          simpa [assoc] using congrArg (fun k ↦ k ≫ (kernelRow (opMap φ)).unop.f) hπ₁
        _ = S₂.f ≫ (kernel.ι (φ.τ₂.op)).unop := by
          change ((kernelRow (opMap φ)).g ≫ kernel.ι (φ.τ₁.op)).unop =
            (kernel.ι (φ.τ₂.op) ≫ S₂.f.op).unop
          exact congrArg Quiver.Hom.unop hK
        _ = S₂.f ≫ cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom := by
          simpa [assoc] using congrArg (fun k ↦ S₂.f ≫ k) hπ₂.symm
        _ = cokernel.π φ.τ₁ ≫ cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂ ≫
              (kernelOpUnop φ.τ₂).symm.hom := by
          simp [cokernel.map, assoc])
    (by
      have hπ₂ :
          cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom =
            (kernel.ι (φ.τ₂.op)).unop := by
        simpa using (kernel.ι_op φ.τ₂).symm
      have hπ₃ :
          cokernel.π φ.τ₃ ≫ (kernelOpUnop φ.τ₃).symm.hom =
            (kernel.ι (φ.τ₃.op)).unop := by
        simpa using (kernel.ι_op φ.τ₃).symm
      have hK :
          (kernelRow (opMap φ)).f ≫ kernel.ι (φ.τ₂.op) =
            kernel.ι (φ.τ₃.op) ≫ S₂.g.op := by
        change
          kernel.map (opMap φ).τ₁ (opMap φ).τ₂ (S₂.op).f (S₁.op).f (opMap φ).comm₁₂ ≫
              kernel.ι (φ.τ₂.op) =
            kernel.ι (φ.τ₃.op) ≫ S₂.g.op
        simp [kernel.map]
      apply (cancel_epi (cokernel.π φ.τ₂)).1
      calc
        cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom ≫ (kernelRow (opMap φ)).unop.g =
            (kernel.ι (φ.τ₂.op)).unop ≫ (kernelRow (opMap φ)).unop.g := by
          simpa [assoc] using congrArg (fun k ↦ k ≫ (kernelRow (opMap φ)).unop.g) hπ₂
        _ = S₂.g ≫ (kernel.ι (φ.τ₃.op)).unop := by
          change ((kernelRow (opMap φ)).f ≫ kernel.ι (φ.τ₂.op)).unop =
            (kernel.ι (φ.τ₃.op) ≫ S₂.g.op).unop
          exact congrArg Quiver.Hom.unop hK
        _ = S₂.g ≫ cokernel.π φ.τ₃ ≫ (kernelOpUnop φ.τ₃).symm.hom := by
          simpa [assoc] using congrArg (fun k ↦ S₂.g ≫ k) hπ₃.symm
        _ = cokernel.π φ.τ₂ ≫ cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃ ≫
              (kernelOpUnop φ.τ₃).symm.hom := by
          simp [cokernel.map, assoc])

/-- Lemma 12.5.16 (1): for a morphism of short complexes in an abelian category, if the source row
is exact and the first map in the target row is a monomorphism, then the induced sequence on the
kernels of the vertical morphisms is exact. -/
-- Proof sketch: apply the canonical lifting operation for exact short complexes to
-- `x₂ ≫ kernel.ι φ.τ₂`. Exactness of `S₁` and monicity of `S₂.f` give the needed lift to
-- `kernel φ.τ₁`, and the result is exactly the kernel row built from `kernel.map`.
theorem kernel_sequence_exact_of_exact_of_mono (hS₁ : S₁.Exact) [Mono S₂.f] :
    (ShortComplex.mk
      (kernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
      (kernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)).Exact := by
  let K := kernelRow φ
  change K.Exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := hS₁.exact_up_to_refinements (x₂ ≫ kernel.ι φ.τ₂) (by
    have hx₂' : x₂ ≫ K.g ≫ kernel.ι φ.τ₃ = 0 := by
      simpa [assoc] using hx₂ =≫ kernel.ι φ.τ₃
    simpa [K, kernel.map, assoc] using hx₂')
  have hy₁' : y₁ ≫ φ.τ₁ = 0 := by
    have hx₂' : x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ = 0 := by
      simpa [assoc] using congrArg (fun t ↦ x₂ ≫ t) (kernel.condition φ.τ₂)
    have hy₁'' : y₁ ≫ S₁.f ≫ φ.τ₂ = 0 := by
      have hcomp : π₁ ≫ x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ = 0 := by
        simpa [assoc] using congrArg (fun t ↦ π₁ ≫ t) hx₂'
      calc
        y₁ ≫ S₁.f ≫ φ.τ₂ = π₁ ≫ x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ := by
          simpa [assoc] using congrArg (fun t ↦ t ≫ φ.τ₂) hy₁.symm
        _ = 0 := hcomp
    apply (cancel_mono S₂.f).1
    simpa [assoc, φ.comm₁₂] using hy₁''
  refine ⟨A₁, π₁, hπ₁, kernel.lift φ.τ₁ y₁ hy₁', ?_⟩
  apply (cancel_mono (kernel.ι φ.τ₂)).1
  simpa [K, kernel.map, assoc] using hy₁

/-- Lemma 12.5.16 (2): for a morphism of short complexes in an abelian category, if the target row
is exact and the second map in the source row is an epimorphism, then the induced sequence on the
cokernels of the vertical morphisms is exact. -/
-- Proof sketch: apply part (1) in the opposite category to `ShortComplex.opMap φ`, then transport
-- the resulting exactness statement to the canonical cokernel row using the standard
-- abelian-opposite comparison isomorphisms.
theorem cokernel_sequence_exact_of_exact_of_epi (hS₂ : S₂.Exact) [Epi S₁.g] :
    (ShortComplex.mk
      (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
      (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)).Exact := by
  let K := kernelRow (opMap φ)
  change (cokernelRow φ).Exact
  letI : Mono (S₁.op).f := by
    dsimp [ShortComplex.op]
    infer_instance
  have hK : K.Exact := by
    simpa [K] using kernel_sequence_exact_of_exact_of_mono (opMap φ) hS₂.op
  exact (ShortComplex.exact_iff_of_iso (cokernelRowIsoUnopKernelRowOpMap φ)).2
    ((ShortComplex.exact_unop_iff K).2 hK)

end CategoryTheory
