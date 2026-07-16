import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_91_2
import stacks_proof.stacks_project.Chap15.Definition_15_24_1

open scoped TensorProduct

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.MittagLeffler A M]

/- Domain triage:
- primary domain: flat Mittag-Leffler modules and content ideals over a commutative ring;
- sampled owner declarations:
  `Module.MittagLeffler`,
  `Module.MittagLeffler.exists_smallest_supporting_submodule`,
  `IsContentIdeal`;
- best owner abstraction: the chapter owner `Module.MittagLeffler A M`;
- primitive data here: an element `x : M`;
- derived API reused here: the Chapter 10 owner theorem
  `Module.MittagLeffler.exists_smallest_supporting_submodule`, together with the Chapter 15 owner
  predicate `IsContentIdeal x I`.

Layering:
- `source-facing`: `Module.MittagLeffler.exists_contentIdeal`;
- `core/canonical`: `Module.MittagLeffler A M`;
- no new `bridge/view` owner is needed in this file.
-/

namespace Module.MittagLeffler

-- Proof sketch: apply the smallest-supporting-submodule characterization of flat Mittag-Leffler
-- modules to the tensor `1 ⊗ₜ x : A ⊗[A] M`, then identify submodules of the free rank-one module
-- `A` with ideals of `A`; the resulting least ideal is exactly a content ideal of `x`.
/-- Lemma 15.24.4: if `M` is a flat Mittag-Leffler `A`-module, then every element `x : M` admits a
content ideal. -/
@[stacks 0ASD]
theorem exists_contentIdeal (x : M) :
    ∃ I : Ideal A, IsContentIdeal x I := by
  let e := TensorProduct.lid A M
  have mem_range_iff (I : Ideal A) :
      e.symm x ∈ LinearMap.range (I.subtype.rTensor M) ↔ x ∈ I • (⊤ : Submodule A M) := by
    rw [← Submodule.mem_map_equiv (LinearMap.range (I.subtype.rTensor M))]
    simpa [LinearMap.range_comp] using
      (Submodule.ext_iff.mp (Ideal.subtype_rTensor_range M I) x)
  rcases exists_smallest_supporting_submodule (ModuleCat.of A A) (e.symm x) with ⟨I, hI⟩
  exact ⟨I, by simpa [IsContentIdeal, mem_range_iff] using hI⟩

end Module.MittagLeffler

end
