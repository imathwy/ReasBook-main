import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_24_1 (from Chap15) -/
universe u v

section

variable {A : Type u} {M : Type v} [CommSemiring A] [AddCommMonoid M] [Module A M]

/- Domain triage:
- primary domain: commutative semiring algebra of ideals acting on modules, organized by least
  ideals in the ideal lattice;
- sampled owner declarations of the same kind:
  `IsLeast`,
  `Submodule.mem_smul_top_iff`,
  `Ideal.FG`,
  `Ideal.span`;
- best owner abstraction: the source-facing predicate `IsContentIdeal x I`, defined as the
  `IsLeast` witness for ideals `J` with `x ∈ J • ⊤`;
- primitive data: the element `x : M` and the ideal `I : Ideal A`;
- derived API: the generic `IsLeast` reformulation and the expanded minimality criterion used by
  the direct downstream 15.24 lemmas.

Layering:
- `source-facing`: the textbook notion “`I` is the content ideal of `x`”;
- `core/canonical`: `IsLeast` on the ideal lattice;
- no separate `bridge/view` owner is needed here.
-/

/-- Definition 15.24.1: an ideal `I` is a content ideal of `x` if it is the smallest ideal of `A`
whose product with `M` contains `x`. -/
def IsContentIdeal (x : M) (I : Ideal A) : Prop :=
  IsLeast { J : Ideal A | x ∈ J • (⊤ : Submodule A M) } I

namespace IsContentIdeal

/-- If `I` is a content ideal of `x`, then `x ∈ IM`. -/
theorem mem_smul_top {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    x ∈ I • (⊤ : Submodule A M) :=
  hI.1

/-- If `I` is a content ideal of `x`, then every ideal `J` with `x ∈ JM` contains `I`. -/
theorem le {x : M} {I J : Ideal A} (hI : IsContentIdeal x I)
    (hx : x ∈ J • (⊤ : Submodule A M)) : I ≤ J :=
  hI.2 hx

end IsContentIdeal

end

/-! ### Lemma_15_24_2 (from Chap15) -/
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

/-! ### Lemma_15_24_3 (from Chap15) -/
universe u v w

open LinearMap

namespace IsContentIdeal

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/- Domain triage:
- primary domain: commutative algebra of content ideals and universally injective linear maps;
- sampled owner declarations of the same kind:
  `IsContentIdeal`,
  `LinearMap.UniversallyInjective`,
  `LinearMap.quotientMapByIdeal`;
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective`;
- best owner abstraction: the source-facing owner predicate `IsContentIdeal x I`, together with
  the canonical transport owner `LinearMap.UniversallyInjective`; the Chapter 10 bridge theorem
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective` supplies the quotient-level
  injectivity needed by the source-facing transport proof;
- primitive data: a linear map `u : M →ₗ[A] N`, an element `x : M`, and an ideal `I : Ideal A`;
- derived API: the owner-level transport theorem below and its local maximal-ideal specialization.

Layering:
- `source-facing`: the local maximal-ideal transport statement later in the file;
- `core/canonical`: the owner theorem `map_of_universallyInjective`;
- `bridge/view`: `LinearMap.quotientMapByIdeal` together with the Chapter 10 bridge theorem
  `LinearMap.injective_quotientMapByIdeal_of_universallyInjective`.
-/

variable {x : M} {I : Ideal A}

-- Proof sketch: transport the containment `x ∈ IM` across `u` for the existence part. For
-- minimality, if `u x ∈ JN`, then the class of `u x` vanishes in `N / JN`; injectivity of
-- `u.quotientMapByIdeal J`, supplied by universal injectivity, forces the class of `x` to vanish
-- in `M / JM`, hence `x ∈ JM`, and the defining minimality of the content ideal yields `I ≤ J`.
/-- Content ideals are preserved by universally injective linear maps. -/
theorem map_of_universallyInjective (hI : IsContentIdeal x I) (u : M →ₗ[A] N)
    (hu : UniversallyInjective.{u, v, w, u} u) :
    IsContentIdeal (u x) I := by
  classical
  refine ⟨?_, ?_⟩
  · have hux : u x ∈ Submodule.map u (I • (⊤ : Submodule A M)) :=
      Submodule.mem_map_of_mem hI.mem_smul_top
    have hux' : u x ∈ I • LinearMap.range u := by
      simpa [Submodule.map_smul'', Submodule.map_top] using hux
    exact
      (Submodule.smul_mono le_rfl
        (by simp : LinearMap.range u ≤ (⊤ : Submodule A N))) hux'
  · intro J hxJ
    have hu' : Function.Injective (u.quotientMapByIdeal J) :=
      injective_quotientMapByIdeal_of_universallyInjective u hu J
    have hxmem : x ∈ J • (⊤ : Submodule A M) := by
      apply (Submodule.Quotient.mk_eq_zero (J • (⊤ : Submodule A M))).1
      apply hu'
      simpa [LinearMap.quotientMapByIdeal] using
        (Submodule.Quotient.mk_eq_zero (J • (⊤ : Submodule A N))).2 hxJ
    exact hI.le hxmem

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

/- Domain triage:
- primary domain: local commutative algebra of flat modules and content ideals under reduction
  modulo the maximal ideal;
- sampled owner declarations of the same kind:
  `IsContentIdeal`,
  `IsContentIdeal.map_of_universallyInjective`,
  `LinearMap.UniversallyInjective`,
  `LinearMap.quotientMapByIdeal`,
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`;
- best owner abstraction: the source-facing owner predicate `IsContentIdeal x I`, together with
  the canonical transport owner `LinearMap.UniversallyInjective`; the finite-ideal criterion from
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal` and the closed-fiber map
  `u.quotientMapByIdeal (maximalIdeal A)` are bridge API into the owner-level local criterion
  proved below;
- primitive data: a linear map `u : M →ₗ[A] N`, an element `x : M`, and an ideal `I : Ideal A`;
- derived API: the owner theorem `IsContentIdeal.map_of_universallyInjective` and the
  source-facing local specialization below;
  the maximal-ideal bridge criterion is internal proof support only.

Layering:
- `source-facing`: the local content-ideal transport statement below;
- `core/canonical`: `IsContentIdeal.map_of_universallyInjective`;
- `bridge/view`: the internal owner-level criterion upgrading closed-fiber injectivity to
  the public owner-level criterion
  `LinearMap.universallyInjective_of_injective_mod_maximalIdeal`.
-/

variable {x : M} {I : Ideal A}

-- Proof sketch: apply the owner-level local criterion
-- `LinearMap.universallyInjective_of_injective_mod_maximalIdeal` and then transport the content
-- ideal along the canonical owner theorem `IsContentIdeal.map_of_universallyInjective`.
/-- Lemma 15.24.3: over a local ring, if the induced map `M/𝔪M → N/𝔪N` is injective, then any
content ideal of `x` is also a content ideal of its image under a map of flat modules. -/
theorem map_of_injective_mod_maximalIdeal (hI : IsContentIdeal x I) (u : M →ₗ[A] N)
    (hu : Function.Injective (u.quotientMapByIdeal (maximalIdeal A))) :
    IsContentIdeal (u x) I :=
  hI.map_of_universallyInjective u <| universallyInjective_of_injective_mod_maximalIdeal u hu

end

end IsContentIdeal

/-! ### Lemma_15_24_4 (from Chap15) -/
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
