import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: the transitivity sequence for Kähler differentials over a tower
  `A → B → C`, under the formal-smoothness hypothesis on `B → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `Algebra.formallySmooth_iff`;
- best owner abstraction: the canonical `KaehlerDifferential` maps in the transitivity sequence,
  with projectivity/subsingleton data supplied by `Algebra.formallySmooth_iff`;
- primitive data: a tower of commutative rings `A → B → C` and the formal smoothness of `B → C`;
- derived API: injectivity of `KaehlerDifferential.mapBaseChange A B C` and a `C`-linear section
  of `KaehlerDifferential.map A B C C`;
- layer triage:
  - `source-facing`: split exactness of the transitivity sequence
    `0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
  - `core/canonical`: the owner maps `KaehlerDifferential.mapBaseChange A B C` and
    `KaehlerDifferential.map A B C C`, together with the upstream exactness/surjectivity and
    formal-smoothness characterizations;
  - `bridge/view`: the source-facing split statement below, phrased directly as injectivity of the
    left map and a section of the right map.

The previous theorem used `Function.RightInverse`, which is less canonical than the linear-map
section equation already used throughout this chapter. The refined statement keeps the same
mathematics while exposing the split data in the owner-facing form
`(KaehlerDifferential.map A B C C).comp s = LinearMap.id`.
-/

-- Proof sketch: formal smoothness of `B → C` gives `Module.Projective C Ω[C⁄B]`, so the
-- surjection `KaehlerDifferential.map A B C C` from Lemma `10.131.7` splits by
-- `Module.Projective.iff_split_of_projective`. The Jacobi-Zariski exact sequence of
-- Lemma `10.134.4` and the subsingleton property of `H¹(L_{C/B})` coming from formal smoothness
-- force `KaehlerDifferential.mapBaseChange A B C` to be injective.
/-- Helper for Lemma 10.138.9: if `H¹(L_{C/B})` is subsingleton, then the connecting morphism in
the Jacobi-Zariski sequence vanishes. -/
lemma h1Cotangent_delta_eq_zero_of_subsingleton
    [Subsingleton (Algebra.H1Cotangent B C)] :
    Algebra.H1Cotangent.δ A B C = 0 := by
  -- Every element of the source is equal to `0`, so the linear map agrees with the zero map.
  ext x
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx]
  simp

/-- Helper for Lemma 10.138.9: vanishing of `H¹(L_{C/B})` turns the middle exactness in the
Jacobi-Zariski sequence into injectivity of the base-change map on Kähler differentials. -/
lemma kaehlerDifferential_mapBaseChange_injective_of_subsingleton_h1Cotangent
    [Subsingleton (Algebra.H1Cotangent B C)] :
    Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
  -- The Jacobi-Zariski sequence identifies the kernel of the base-change map with the range of
  -- the connecting morphism.
  have hExact :
      Function.Exact (Algebra.H1Cotangent.δ A B C) (KaehlerDifferential.mapBaseChange A B C) := by
    simpa using Algebra.H1Cotangent.exact_δ_mapBaseChange A B C
  have hKer :
      LinearMap.ker (KaehlerDifferential.mapBaseChange A B C) =
        LinearMap.range (Algebra.H1Cotangent.δ A B C) :=
    LinearMap.exact_iff.mp hExact
  -- Since the connecting morphism is zero, that kernel is trivial.
  rw [h1Cotangent_delta_eq_zero_of_subsingleton (A := A) (B := B) (C := C),
    LinearMap.range_zero] at hKer
  exact LinearMap.ker_eq_bot.mp hKer

/-- Helper for Lemma 10.138.9: if `Ω[C⁄B]` is projective, then the surjective transitivity map
`Ω[C⁄A] → Ω[C⁄B]` admits a `C`-linear section. -/
lemma kaehlerDifferential_map_has_section_of_projective_target
    [Module.Projective C Ω[C⁄B]] :
    ∃ s : Ω[C⁄B] →ₗ[C] Ω[C⁄A],
      (KaehlerDifferential.map A B C C).comp s = LinearMap.id := by
  -- Projectivity lifts the identity of the codomain across the canonical surjection.
  simpa using
    (Module.projective_lifting_property
      (KaehlerDifferential.map A B C C)
      LinearMap.id
      (KaehlerDifferential.map_surjective A B C))

/-- Lemma 10.138.9: if `B → C` is formally smooth, then in the canonical sequence
`0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
of Lemma `10.131.7`, the left map is injective and the right map admits a `C`-linear section.
Equivalently, this sequence is split short exact. -/
theorem kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth
    [Algebra.FormallySmooth B C] :
    Function.Injective (KaehlerDifferential.mapBaseChange A B C) ∧
      ∃ s : Ω[C⁄B] →ₗ[C] Ω[C⁄A],
        (KaehlerDifferential.map A B C C).comp s = LinearMap.id := by
  -- Proposition `10.138.8` packages formal smoothness as vanishing of `H¹(L_{C/B})` together
  -- with projectivity of `Ω[C⁄B]`.
  have hSmoothData :
      Subsingleton (Algebra.H1Cotangent B C) ∧ Module.Projective C Ω[C⁄B] := by
    simpa [and_comm] using
      (Algebra.formallySmooth_iff (R := B) (A := C)).mp
        (inferInstance : Algebra.FormallySmooth B C)
  rcases hSmoothData with ⟨hH1, hProj⟩
  letI : Subsingleton (Algebra.H1Cotangent B C) := hH1
  letI : Module.Projective C Ω[C⁄B] := hProj
  -- The left map is injective by Jacobi-Zariski exactness, and the right map splits by
  -- projectivity of the target.
  refine ⟨?_, ?_⟩
  · exact
      kaehlerDifferential_mapBaseChange_injective_of_subsingleton_h1Cotangent
        (A := A) (B := B) (C := C)
  · exact kaehlerDifferential_map_has_section_of_projective_target (A := A) (B := B) (C := C)

end
