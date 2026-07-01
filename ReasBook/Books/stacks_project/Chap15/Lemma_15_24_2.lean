import stacks_project.Chap15.Definition_15_24_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommSemiring A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

/- Domain triage:
- primary domain: content ideals in modules over a commutative semiring;
- sampled declarations of the same kind:
  `IsContentIdeal`,
  `Ideal.FG`,
  `IsContentIdeal.mem_smul_top`,
  `IsContentIdeal.le`,
  `Submodule.mem_ideal_smul_span_iff_exists_sum`;
- best owner abstraction: the chapter owner `IsContentIdeal x I` from Definition `15.24.1`;
- primitive data: the element `x : M` and the ideal `I : Ideal A`;
- derived API: the owner projections `IsContentIdeal.mem_smul_top` and `IsContentIdeal.le`.

Layering:
- `source-facing`: `IsContentIdeal x I`;
- `core/canonical`: `IsLeast {J : Ideal A | x ∈ J • ⊤} I`;
- this file contributes the derived finite-generation theorem for the owner predicate.
-/

namespace IsContentIdeal

-- Proof sketch: from `x ∈ I M`, write `x` as a finite sum `∑ fᵢ xᵢ` with coefficients `fᵢ ∈ I`.
-- The finitely generated ideal `I' = (f₁, …, fₙ)` still satisfies `x ∈ I' M`, so minimality of
-- the content ideal gives `I ≤ I'`; since `I' ≤ I` by construction, we get `I = I'`, hence `I`
-- is finitely generated.
/-- Lemma 15.24.2: if `I` is the content ideal of `x` in the `A`-module `M`, then `I` is
finitely generated. -/
theorem fg {x : M} {I : Ideal A} (hI : IsContentIdeal x I) : I.FG := by
  classical
  rcases (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : M → M) x).mp
      (by simpa [Submodule.span_univ] using hI.mem_smul_top) with
    ⟨a, ha, rfl⟩
  let J : Ideal A := Ideal.span ↑(a.support.image a)
  have hJ_le : J ≤ I := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, -, rfl⟩
    exact ha i
  have hxJ : a.sum (fun i c ↦ c • i) ∈ J • (⊤ : Submodule A M) := by
    simpa [Submodule.span_univ] using
      (Submodule.mem_ideal_smul_span_iff_exists_sum J (id : M → M) _).mpr <| by
      refine ⟨a, ?_, rfl⟩
      intro i
      by_cases hi : i ∈ a.support
      · exact Ideal.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      · have hi0 : a i = 0 := by
          simpa [Finsupp.mem_support_iff] using hi
        simp [hi0]
  have hI_le : I ≤ J := hI.le hxJ
  refine ⟨a.support.image a, ?_⟩
  simpa [J] using le_antisymm hJ_le hI_le

end IsContentIdeal

end
