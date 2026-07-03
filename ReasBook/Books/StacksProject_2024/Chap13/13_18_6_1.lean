import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]

/-
Domain-style sampling for 13.18.6.1:
- primary domain: cochain complexes in an abelian category, with degreewise exactness expressed by
  the short-complex API on cochain complexes, together with the translation of exactness into
  subobject equalities in an abelian category;
- sampled owner declarations:
  `ShortComplex.cokernelSequence`,
  `ShortComplex.ShortExact`,
  `HomologicalComplex.Acyclic`,
  `CategoryTheory.ShortComplex.exact_iff_image_eq_kernel`;
- best owner abstraction: `HomologicalComplex.Acyclic` applied to `cokernel α`, with the canonical
  short exact row `ShortComplex.cokernelSequence α` supplying the bridge from the quasi-isomorphism
  hypothesis to degreewise exactness;
- primitive data: the morphism `α : K ⟶ L`, the quasi-isomorphism structure, and the termwise
  monomorphism hypothesis;
- derived API: the source-facing image/intersection identity inside `L.X n`.

Source/core/bridge triage:
- `source-facing`: the image/intersection identity inside `L.X n`;
- `core/canonical`: `HomologicalComplex.Acyclic` and `HomologicalComplex.ExactAt` for
  `cokernel α`;
- `bridge/view`: the canonical short exact row `ShortComplex.cokernelSequence α`, together with
  its long exact homology sequence, and then
  `CategoryTheory.ShortComplex.exact_iff_image_eq_kernel` to convert degreewise exactness into the
  source-facing subobject identity.
-/

-- Proof sketch: use the canonical short exact row `0 ⟶ K ⟶ L ⟶ cokernel α ⟶ 0`, encoded by
-- `ShortComplex.cokernelSequence α`. Its long exact homology sequence shows that the homology of
-- `cokernel α` vanishes in every degree because `α` is a quasi-isomorphism.
/-- The cokernel complex of a termwise monomorphic quasi-isomorphism is acyclic. -/
theorem cokernel_acyclic_of_termwiseMono_quasiIso
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    (cokernel α).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.cokernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_
      (HomologicalComplex.mono_of_mono_f α hmono) inferInstance
    exact ShortComplex.cokernelSequence_exact α
  refine ((hS.homology_exact₃ n (n + 1) (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₂ n).epi_f_iff]
    have : Epi (homologyMap α n) := by infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₁ n (n + 1) (by simp)).mono_g_iff]
    have : Mono (homologyMap α (n + 1)) := by infer_instance
    simpa [S] using this

-- Proof sketch: apply `cokernel_acyclic_of_termwiseMono_quasiIso` to the cokernel complex of the
-- termwise-monomorphic quasi-isomorphism `α`, specialize the resulting acyclicity to degree `n`,
-- and then rewrite exactness in `𝒜` via `ShortComplex.exact_iff_image_eq_kernel` together with
-- the abelian mono/cokernel API.
/-- 13.18.6.1: for a quasi-isomorphism of cochain complexes that is termwise monomorphic, the
image of the incoming differential of `K` inside `L.X n` equals the intersection of the image of
`α.f n` with the image of the incoming differential of `L`. -/
theorem image_prev_d_eq_inf_of_termwiseMono_quasiIso
    (hmono : ∀ n : ℤ, Mono (α.f n))
    (n : ℤ) :
    imageSubobject (K.dTo n ≫ α.f n) =
      imageSubobject (α.f n) ⊓ imageSubobject (L.dTo n) := sorry

end CochainComplex
