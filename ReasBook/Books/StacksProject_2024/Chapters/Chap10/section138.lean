import Mathlib
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_138_1 (from Chap10) -/
universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.138.1: an `R`-algebra `S` is formally smooth if every `R`-algebra map
`S → A ⧸ I` lifts across the quotient map `A → A ⧸ I` whenever `I` is a square-zero ideal. -/
recall FormallySmooth

/- The infinitesimal lifting formulation of formal smoothness is the square-zero lifting criterion
for maps into quotient algebras `A ⧸ I`. -/
recall FormallySmooth.iff_comp_surjective

end Algebra

/-! ### Lemma_10_138_2 (from Chap10) -/
/- Lemma 10.138.2: if `R → S` is formally smooth and `R → R'` is any ring map, then the base
change `R' ⊗[R] S` is formally smooth over `R'`. This is the canonical tensor-product base-change
instance `Algebra.FormallySmooth.instTensorProduct`. -/
recall Algebra.FormallySmooth.instTensorProduct

/-! ### Lemma_10_138_3 (from Chap10) -/
/- Lemma 10.138.3: a composition of formally smooth ring maps is formally smooth. This is exactly
the canonical mathlib theorem `RingHom.FormallySmooth.comp`. -/
recall RingHom.FormallySmooth.comp

/-! ### Lemma_10_138_4 (from Chap10) -/
universe u v

/-
Domain triage:
* primary domain: formal smoothness of commutative algebras, especially polynomial algebras;
* sampled owner declarations:
  `Algebra.FormallySmooth`,
  `Algebra.mvPolynomial`,
  `Algebra.FormallySmooth.iff_split_surjection`,
  and the chapter-level recall items `Definition_10_138_1` and `Remark_10_138_6`;
* layer: `core/canonical`, since the source statement is exactly the upstream owner instance for the
  polynomial algebra;
* primitive data: only the base ring `R` and variable type `σ`;
* derived API: the `Algebra.FormallySmooth R (MvPolynomial σ R)` instance itself.

There is no source-facing extra structure to package here, so the right refinement is direct recall
of the owner instance rather than a local wrapper or an anonymous `inferInstance` check.
-/
section

variable (R : Type u) (σ : Type v) [CommRing R]

/- Lemma 10.138.4: for any family of variables `σ`, the polynomial ring `R[σ]`, formalized as
`MvPolynomial σ R`, is formally smooth over `R`. This is exactly the canonical mathlib instance
`Algebra.FormallySmooth R (MvPolynomial σ R)`. -/
recall Algebra.mvPolynomial

end

/-! ### Lemma_10_138_5 (from Chap10) -/
universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: formal smoothness of commutative algebras via square-zero thickenings;
* sampled owner declarations:
  `Algebra.FormallySmooth`,
  `Algebra.mvPolynomial`,
  `Algebra.FormallySmooth.iff_split_surjection`,
  `AlgHom.kerSquareLift`;
* layer: `source-facing`, since the Stacks item is the polynomial-presentation specialization of the
  canonical split-surjection criterion;
* primitive data: a surjective polynomial presentation `f : MvPolynomial ι R →ₐ[R] S`;
* derived API: the section of `f.kerSquareLift`, already the canonical owner map
  `(MvPolynomial ι R) ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] S`.

There is no additional source-defined structure beyond this specialization, so the correct
refinement is to reuse the owner theorem directly rather than keep a parallel local criterion.
-/
-- Proof sketch: specialize `Algebra.FormallySmooth.iff_split_surjection` to the surjective
-- `R`-algebra map `f : MvPolynomial ι R →ₐ[R] S`. The source polynomial algebra is formally
-- smooth by the canonical instance from Lemma 10.138.4, and `f.kerSquareLift` is the quotient map
-- `P / J² → S` for `J = ker f`.
/-- Lemma 10.138.5: for a surjective `R`-algebra map from a polynomial ring
`f : MvPolynomial ι R →ₐ[R] S`, the `R`-algebra `S` is formally smooth over `R` if and only if
the induced surjection `(MvPolynomial ι R) ⧸ (RingHom.ker f.toRingHom) ^ 2 →ₐ[R] S` admits an
`R`-algebra section. -/
theorem formallySmooth_iff_exists_polynomial_presentation_section_mod_ker_sq
    (f : MvPolynomial ι R →ₐ[R] S) (hf : Function.Surjective f) :
    Algebra.FormallySmooth R S ↔
      ∃ σ : S →ₐ[R] MvPolynomial ι R ⧸ (RingHom.ker f.toRingHom) ^ 2,
        f.kerSquareLift.comp σ = AlgHom.id R S := by
  simpa using Algebra.FormallySmooth.iff_split_surjection f hf

end

/-! ### Remark_10_138_6 (from Chap10) -/
/- Remark 10.138.6: Lemma 10.138.5 extends from polynomial presentations to any surjective
`R`-algebra map `f : P →ₐ[R] A` whose source `P` is formally smooth over `R`. This is exactly the
canonical mathlib theorem `Algebra.FormallySmooth.iff_split_surjection`. -/
recall Algebra.FormallySmooth.iff_split_surjection

/-! ### Lemma_10_138_7 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable (R : Type u) (ι : Type v) (S : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/- Domain triage:
- primary domain: formal smoothness criteria for surjective polynomial presentations via the
  conormal sequence and Kähler differentials;
- sampled owner declarations:
  `Algebra.FormallySmooth.iff_split_injection`,
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `KaehlerDifferential.mapBaseChange_surjective`,
  and the chapter bridge `kaehlerDifferential_exact_cotangent_tensor_of_surjective`;
- best owner abstraction: the canonical split-injection owner
  `Algebra.FormallySmooth.iff_split_injection`, specialized to the polynomial presentation
  `MvPolynomial ι R → S`;
- primitive data: the surjective polynomial presentation `algebraMap (MvPolynomial ι R) S`;
- derived API: the retraction map on the conormal morphism, expressed in owner form by the
  equation `τ ∘ₗ kerCotangentToTensor = LinearMap.id`.

This item is `source-facing`: it keeps the polynomial-presentation specialization from the source,
but there is no extra owner-level mathematics beyond the canonical split-injection criterion, so
the refined theorem should reuse that owner directly rather than restating it through
`Function.LeftInverse`. -/

-- Proof sketch: specialize `Algebra.FormallySmooth.iff_split_injection` to the chosen surjective
-- polynomial presentation `MvPolynomial ι R → S`. The map
-- `KaehlerDifferential.kerCotangentToTensor R (MvPolynomial ι R) S` is the left map
-- `J/J² → Ω[P⁄R] ⊗[P] S` in the conormal sequence, and Lemma `10.131.9` supplies the exactness
-- and surjectivity needed to read a left inverse as split exactness.
/-- Lemma 10.138.7: for a surjective polynomial presentation `MvPolynomial ι R → S`, the
`R`-algebra `S` is formally smooth over `R` if and only if the conormal map
`J/J² → Ω[MvPolynomial ι R⁄R] ⊗[MvPolynomial ι R] S` is split injective, equivalently admits a
retraction; by Lemma `10.131.9`, this is exactly the split exactness of
`0 → J/J² → Ω[MvPolynomial ι R⁄R] ⊗[MvPolynomial ι R] S → Ω[S⁄R] → 0`. -/
theorem formallySmooth_iff_polynomial_conormal_has_retraction
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    Algebra.FormallySmooth R S ↔
      ∃ τ : S ⊗[MvPolynomial ι R] Ω[MvPolynomial ι R⁄R] →ₗ[MvPolynomial ι R]
          (RingHom.ker (algebraMap (MvPolynomial ι R) S)).Cotangent,
        τ ∘ₗ KaehlerDifferential.kerCotangentToTensor R (MvPolynomial ι R) S = LinearMap.id := by
  simpa using
    (Algebra.FormallySmooth.iff_split_injection hSurj)

end

/-! ### Proposition_10_138_8 (from Chap10) -/
open scoped TensorProduct

noncomputable section

universe u v

namespace Algebra

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: formal smoothness of commutative algebras via surjective presentations,
  infinitesimal thickenings, and the conormal sequence;
* sampled owner declarations:
  `Algebra.FormallySmooth.iff_split_surjection`,
  `Algebra.Extension.formallySmooth_iff_split_injection`,
  `Algebra.formallySmooth_iff`,
  `Algebra.Extension.cotangentComplex`;
* best owner abstraction: `Algebra.FormallySmooth R S`, with presentation-level conditions derived
  from the canonical extension owners `P.infinitesimal` and `P.cotangentComplex`;
* primitive data: a surjective presentation `P : Extension R S`;
* derived API: a section of `P.infinitesimal.Ring → S`, a retraction of `P.cotangentComplex`,
  and the cotangent-homology characterization from `Algebra.formallySmooth_iff`.

This proposition is `source-facing`: it keeps the textbook TFAE list, but each presentation-level
condition is stated directly through the canonical owner maps rather than through parallel local
wrapper predicates.
-/

-- Proof sketch: use `Algebra.FormallySmooth.iff_split_surjection` for the infinitesimal-section
-- clauses, `Algebra.Extension.formallySmooth_iff_split_injection` for the conormal-splitting
-- clauses, and `Algebra.formallySmooth_iff` for the cotangent-complex condition.
/-- Helper for Proposition 10.138.8: the canonical polynomial presentation of `S` is formally
smooth over `R`. -/
lemma self_generators_toExtension_formallySmooth :
    FormallySmooth R ((Generators.self R S).toExtension).Ring := by
  -- The self-generators presentation is definitionally the polynomial ring `R[S]`.
  change FormallySmooth R (MvPolynomial S R)
  infer_instance

/-- Proposition 10.138.8: for a ring map `R → S`, the following are equivalent: `S` is formally
smooth over `R`; some formally smooth surjective presentation `P → S` admits a section
`P / J² → S`; every formally smooth surjective presentation `P → S` admits such a section; some
formally smooth surjective presentation has split conormal sequence
`0 → J/J² → Ω[P⁄R] ⊗[P] S → Ω[S⁄R] → 0`; every formally smooth surjective presentation has split
conormal sequence; and the naive cotangent complex `NL_{S/R}` is quasi-isomorphic to a projective
`S`-module in degree `0`, i.e. `H¹(L_{S/R}) = 0` and `Ω[S⁄R]` is projective. -/
theorem formallySmooth_tfae_presentation_section_conormal_sequence_projective :
    List.TFAE
      [FormallySmooth R S,
        ∃ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring ∧
            ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
              (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S,
        ∀ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring →
            ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
              (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S,
        ∃ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring ∧
            ∃ τ : P.CotangentSpace →ₗ[S] P.Cotangent,
              τ ∘ₗ P.cotangentComplex = LinearMap.id,
        ∀ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring →
            ∃ τ : P.CotangentSpace →ₗ[S] P.Cotangent,
              τ ∘ₗ P.cotangentComplex = LinearMap.id,
        Subsingleton (H1Cotangent R S) ∧ Module.Projective S Ω[S⁄R]] := by
  -- Clause (6) is exactly the owner characterization of formal smoothness, with the conjunction
  -- reordered to match the statement.
  tfae_have 1 ↔ 6 := by
    simpa [and_comm] using (Algebra.formallySmooth_iff (R := R) (A := S))
  -- A formally smooth target lifts across every formally smooth presentation to the
  -- infinitesimal thickening `P / J²`.
  tfae_have 1 → 3 := by
    intro hS P hP
    letI : FormallySmooth R P.Ring := hP
    simpa using
      (Algebra.FormallySmooth.iff_split_surjection
        (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mp hS
  -- For the existential infinitesimal-section clause, use the canonical polynomial presentation.
  tfae_have 3 → 2 := by
    intro h
    let P : Extension.{max u v} R S := (Generators.self R S).toExtension
    have hP : FormallySmooth R P.Ring := by
      simpa [P] using (self_generators_toExtension_formallySmooth (R := R) (S := S))
    refine ⟨P, ?_⟩
    refine ⟨hP, ?_⟩
    exact h P hP
  -- A single infinitesimal section for one formally smooth presentation already forces formal
  -- smoothness of `S`, and then the same presentation has a split conormal sequence.
  tfae_have 2 → 4 := by
    intro h
    rcases h with ⟨P, hP, σ, hσ⟩
    letI : FormallySmooth R P.Ring := hP
    have hS : FormallySmooth R S := by
      exact
        (Algebra.FormallySmooth.iff_split_surjection
          (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr ⟨σ, hσ⟩
    refine ⟨P, hP, ?_⟩
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS
  -- Once one section exists for a fixed presentation, it recovers formal smoothness of `S`, and
  -- then the same presentation has a split conormal sequence by the owner splitting criterion.
  tfae_have 3 → 5 := by
    intro h P hP
    letI : FormallySmooth R P.Ring := hP
    have hSection :
        ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
          (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S :=
      h P hP
    have hS : FormallySmooth R S := by
      exact
        (Algebra.FormallySmooth.iff_split_surjection
          (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr hSection
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS
  -- Again use the canonical polynomial presentation to forget the universal quantifier.
  tfae_have 5 → 4 := by
    intro h
    let P : Extension.{max u v} R S := (Generators.self R S).toExtension
    have hP : FormallySmooth R P.Ring := by
      simpa [P] using (self_generators_toExtension_formallySmooth (R := R) (S := S))
    refine ⟨P, ?_⟩
    refine ⟨hP, ?_⟩
    exact h P hP
  -- A split conormal sequence for one formally smooth presentation is the owner criterion for
  -- formal smoothness of the target.
  tfae_have 4 → 1 := by
    intro h
    rcases h with ⟨P, hP, τ, hτ⟩
    letI : FormallySmooth R P.Ring := hP
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mpr ⟨τ, hτ⟩
  tfae_finish

end

end Algebra

/-! ### Lemma_10_138_9 (from Chap10) -/
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

/-! ### Lemma_10_138_10 (from Chap10) -/
open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.FormallySmooth A C]

-- Proof sketch: Lemma `10.131.9` gives a surjection
-- `KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`.
-- By Proposition `10.138.8`, formal smoothness of `A → C` implies that `Ω[C⁄A]` is a
-- projective `C`-module, so this surjection admits a `C`-linear section. Together with the
-- exactness statement of Lemma `10.131.9`, this is exactly the split exactness of
-- `0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`.
/-- Lemma 10.138.10: if `A → C` is formally smooth and `B → C` is surjective with kernel `J`, then
the exact sequence
`0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`
of Lemma `10.131.9` is split exact. In canonical library form, the surjection
`KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`
admits a `C`-linear section. -/
theorem kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth
    (hsurj : Function.Surjective (algebraMap B C)) :
    ∃ σ : Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A],
      (KaehlerDifferential.mapBaseChange A B C).comp σ = LinearMap.id := by
  simpa using
    Module.projective_lifting_property
      (KaehlerDifferential.mapBaseChange A B C)
      LinearMap.id
      (KaehlerDifferential.mapBaseChange_surjective A B C hsurj)

end

/-! ### Lemma_10_138_11 (from Chap10) -/
open Algebra
open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.FormallySmooth A B]

/- Domain triage:
* primary domain: the surjective Jacobi-Zariski conormal sequence on first cotangent homology for
  a tower `A → B → C`;
* sampled owner declarations:
  - `H1Cotangent.δ`, the canonical surjection candidate in the Jacobi-Zariski sequence;
  - `surjective_jacobi_zariski_conormal_sequence`, the chapter owner of exactness and surjectivity
    for `H1Cotangent.map A B C C` and `H1Cotangent.δ A B C` under `A → C` surjective;
  - `Algebra.formallySmooth_iff`, which packages formal smoothness as
    `Subsingleton (H1Cotangent A B)` plus projectivity of `Ω[B⁄A]`;
  - `Module.Projective.iff_split_of_projective`, the owner criterion turning projectivity of the
    codomain of a surjective linear map into a section.
* best owner abstraction: the new split data should be carried by the canonical surjection
  `H1Cotangent.δ A B C`; the retraction of `H1Cotangent.map A B C C` is derived from exactness via
  `Function.Exact.split_tfae'`, so it should not remain the primitive public surface here.
* primitive data vs. derived API:
  - primitive data: the surjective map `A → C` and the formally smooth algebra `A → B`;
  - derived API: a section of `H1Cotangent.δ A B C`, with the left-map retraction recoverable from
    the earlier exactness theorem.
* layer triage:
  - `source-facing`: split exactness of the surjective Jacobi-Zariski conormal sequence;
  - `core/canonical`: `H1Cotangent.δ A B C` together with
    `surjective_jacobi_zariski_conormal_sequence` and `Algebra.formallySmooth_iff`;
  - `bridge/view`: translating the split surjection into a retraction of
    `H1Cotangent.map A B C C`.
-/

-- Proof sketch: Lemma `10.134.7` gives exactness of
-- `H1Cotangent.map A B C C` followed by `H1Cotangent.δ A B C`, and also surjectivity of
-- `H1Cotangent.δ A B C`, when `A → C` is surjective. Since `A → B` is formally smooth,
-- `Ω[B⁄A]` is projective over `B`, hence after base change to `C` the module
-- `C ⊗[B] Ω[B⁄A]` is projective over `C`. Therefore the surjection `H1Cotangent.δ A B C`
-- admits a `C`-linear section, which is the canonical split-exact owner data for this sequence.
/-- Lemma 10.138.11: if `A → C` is surjective and `A → B` is formally smooth, then the exact
sequence of Lemma `10.134.7`,
`0 → I/I² → J/J² → Ω[B⁄A] ⊗[B] C → 0`,
is split exact. In the canonical Jacobi-Zariski formulation, this means that the surjection
`H1Cotangent.δ A B C : H1Cotangent B C →ₗ[C] C ⊗[B] Ω[B⁄A]` admits a `C`-linear section. -/
theorem jacobi_zariski_conormal_sequence_splits_of_formallySmooth
    (hAC : Function.Surjective (algebraMap A C)) :
    ∃ σ : C ⊗[B] Ω[B⁄A] →ₗ[C] H1Cotangent B C,
      (H1Cotangent.δ A B C).comp σ = LinearMap.id := by
  -- Lemma `10.134.7` supplies the canonical Jacobi-Zariski surjection `δ`.
  obtain ⟨_, hδsurj⟩ :=
    surjective_jacobi_zariski_conormal_sequence (A := A) (B := B) (C := C) hAC
  -- Formal smoothness makes `Ω[B⁄A]` projective, and tensoring with `C` preserves projectivity.
  let _ : Module.Projective C (C ⊗[B] Ω[B⁄A]) := inferInstance
  -- Lift the identity of the projective codomain across the surjection `δ`.
  simpa using
    (Module.projective_lifting_property
      (R := C) (P := C ⊗[B] Ω[B⁄A]) (M := H1Cotangent B C) (N := C ⊗[B] Ω[B⁄A])
      (H1Cotangent.δ A B C) (LinearMap.id) hδsurj)

end

/-! ### Lemma_10_138_12 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) [Module.Flat R S]

-- Proof sketch: apply the canonical quotient-descent theorem
-- `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` to the quotient maps
-- `R → R ⧸ I` and `S → S ⧸ IS`. For quotient maps, surjectivity is automatic, the kernel of
-- `S → S ⧸ IS` is exactly `IS`, and the square-zero hypothesis is precisely `(ker q_R)^2 = ⊥`.
/-- Lemma 10.138.12: if `I` is a square-zero ideal of `R`, `S` is flat over `R`, and the
quotient map `R ⧸ I → S ⧸ IS` is formally smooth, then `R → S` is formally smooth. -/
theorem formallySmooth_of_square_zero_ideal_of_flat_of_quotient_formallySmooth
    (hSq : I ^ 2 = ⊥)
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    Algebra.FormallySmooth R S := by
  have hsurjR : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  have hsurjS : Function.Surjective (algebraMap S (S ⧸ Ideal.map (algebraMap R S) I)) := by
    simpa using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)))
  simpa using
    (Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
      hsurjR hsurjS
      (by simp)
      (by simpa using hSq)
      hSmooth)

end

/-! ### Proposition_10_138_13 (from Chap10) -/
/- Proposition 10.138.13: for a ring map `R → S`, being of finite presentation and formally
smooth is equivalent to being smooth. This is exactly the canonical mathlib theorem
`Algebra.smooth_iff`. -/
recall Algebra.smooth_iff

/-! ### Lemma_10_138_14 (from Chap10) -/
/- Lemma 10.138.14: a smooth `R`-algebra admits a smooth model over a finitely generated
`ℤ`-subalgebra of `R`; using `Subalgebra.fg_iff_finiteType`, this is the book's finite-type
integer-subalgebra model statement. This is exactly the canonical theorem
`Algebra.Smooth.exists_subalgebra_fg`. -/
recall Algebra.Smooth.exists_subalgebra_fg

/-! ### Lemma_10_138_15 (from Chap10) -/
open Algebra CategoryTheory Limits
open scoped TensorProduct

universe u w

section

variable {J : Type u} [Category.{u} J] [IsFiltered J]

/-- Helper for Lemma 10.138.15: the canonical ring hom from `ULift ℤ` to a commutative ring. -/
def ulift_int_hom (A : Type u) [CommRing A] : ULift.{u} ℤ →+* A :=
  (Int.castRingHom A).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom

omit [IsFiltered J] in
/-- Helper for Lemma 10.138.15: every morphism in a diagram of commutative rings commutes with the
canonical `ULift ℤ`-algebra maps. -/
lemma ulift_integers_to_ring_diagram_naturality
    (F : J ⥤ CommRingCat.{u}) {i j : J} (f : i ⟶ j) :
    ((Functor.const J).obj (CommRingCat.of (ULift.{u} ℤ))).map f ≫
        CommRingCat.ofHom (ulift_int_hom (A := F.obj j)) =
      CommRingCat.ofHom (ulift_int_hom (A := F.obj i)) ≫ F.map f := by
  -- Proof comment: ring morphisms preserve the canonical map from the initial commutative ring
  -- object `ULift ℤ`.
  apply CommRingCat.hom_ext
  ext n
  cases n with
  | up n =>
      change ((Int.castRingHom (F.obj j)) n) = (F.map f).hom ((Int.castRingHom (F.obj i)) n)
      simpa using (map_intCast ((F.map f).hom) n).symm

omit [IsFiltered J] in
/-- Helper for Lemma 10.138.15: a diagram of commutative rings carries the canonical natural
transformation from the constant `ULift ℤ`-diagram. -/
def ulift_integers_to_ring_diagram
    (F : J ⥤ CommRingCat.{u}) :
    (Functor.const J).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F :=
  { app := fun j => CommRingCat.ofHom (ulift_int_hom (A := F.obj j))
    naturality := fun {_ _} f => ulift_integers_to_ring_diagram_naturality (F := F) f }

/- Domain-style sampling:
* primary domain: smooth commutative algebras and filtered-colimit descent of finitely presented
  algebra data;
* sampled owner declarations:
  `Algebra.Smooth.exists_finiteType`,
  `Algebra.FinitePresentation.of_finiteType`,
  `RingHom.FinitePresentation.comp`,
  `finitelyPresented_algebra_is_baseChange_of_stage`;
* best owner abstraction: `Smooth`, with finite-presentation descent treated as derived bridge API;
* layer triage:
  - `source-facing`: the filtered-colimit descent theorem for a smooth algebra over `c.pt`;
  - `core/canonical`: the owner predicate `Smooth`;
  - `bridge/view`: factoring the finite-type model through a stage and recovering `B` by tensor
    base change;
* primitive data: the filtered diagram `F`, its colimit cocone `c`, and the smooth `c.pt`-algebra
  `B`;
* derived API: the finite-type model from `Algebra.Smooth.exists_finiteType`, the finite
  presentation of that model, and the stagewise base-change recovery.
-/

-- Proof sketch: first apply `Algebra.Smooth.exists_finiteType` to descend the smooth algebra over
-- the colimit ring to a smooth algebra over a finite-type intermediate ring. Since a finite-type
-- algebra is finitely presented, Lemma `10.127.3` factors the structure map of that intermediate
-- ring through some stage of the filtered diagram. This yields a stage algebra whose primary
-- owner-level property is smoothness; base changing that smooth model along the stage map then
-- recovers `B` as companion bridge data.
/-- Lemma 10.138.15: if `c` is a filtered colimit cocone of commutative rings and `B` is smooth
over the colimit ring `c.pt`, then `B` is obtained by base change from a smooth algebra over some
stage of the diagram. The descended stage algebra naturally lives in the universe of the diagram
stages, and the tensor-product equivalence back to `B` is companion bridge data. -/
theorem smooth_is_baseChange_of_stage_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Smooth c.pt B] :
    ∃ (j : J) (B_j : Type u) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Smooth (F.obj j) B_j ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := by
  let α := ulift_integers_to_ring_diagram (F := F)
  -- Proof comment: first descend the smooth `c.pt`-algebra to a smooth model over a finitely
  -- generated `ℤ`-subalgebra of `c.pt`.
  obtain ⟨A₀, B₀, _instB₀, _instAlgB₀, hA₀fg, _instSmoothB₀, hB⟩ :=
    Algebra.Smooth.exists_subalgebra_fg (R := ℤ) (A := c.pt) (B := B)
  haveI : Algebra.FinitePresentation ℤ A₀ := by
    -- Proof comment: finite generation over `ℤ` upgrades to finite presentation because `ℤ` is
    -- noetherian.
    have hfiniteType : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀fg
    exact (Algebra.FinitePresentation.of_finiteType (R := ℤ) (A := A₀)).mp hfiniteType
  have hA₀fpZ : (algebraMap ℤ A₀).FinitePresentation := by
    -- Proof comment: reinterpret the algebra-level finite-presentation instance as the ring-hom
    -- predicate required by the filtered-colimit factorization theorem.
    simpa [RingHom.finitePresentation_algebraMap] using
      (show Algebra.FinitePresentation ℤ A₀ from inferInstance)
  have hA₀fp : (ulift_int_hom (A := A₀)).FinitePresentation := by
    -- Proof comment: the category-level theorem is universe-polymorphic in the base ring, so we
    -- transfer finite presentation along `ULift.ringEquiv : ULift ℤ ≃+* ℤ`.
    rw [show ulift_int_hom (A := A₀) =
        (algebraMap ℤ A₀).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom by rfl]
    exact RingHom.FinitePresentation.comp hA₀fpZ
      (RingHom.FinitePresentation.of_bijective
        (ULift.ringEquiv.{0, u} (R := ℤ)).bijective)
  have hcompat :
      ∀ i,
        CommRingCat.ofHom (ulift_int_hom (A := A₀)) ≫ CommRingCat.ofHom A₀.val =
          α.app i ≫ c.ι.app i := by
    intro i
    -- Proof comment: both composites are the canonical map `ULift ℤ → c.pt`.
    apply CommRingCat.hom_ext
    ext n
    simpa [ulift_int_hom, CommRingCat.hom_comp] using
      (map_intCast ((c.ι.app i).hom) n.down).symm
  -- Proof comment: finite presentation of the intermediate `ℤ`-algebra lets its structure map
  -- factor through some stage of the filtered system.
  obtain ⟨j, φj, hφj_alg, hφj_factor⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := CommRingCat.of (ULift.{u} ℤ)) (F := F) (α := α)
      (S := CommRingCat.of A₀) (f := CommRingCat.ofHom (ulift_int_hom (A := A₀)))
      (c := c) (hc := _hc) hA₀fp (CommRingCat.ofHom A₀.val) hcompat
  letI : Algebra A₀ (F.obj j) := φj.hom.toAlgebra
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let _ := hφj_alg
  have hstage_eq :
      algebraMap A₀ c.pt = (algebraMap (F.obj j) c.pt).comp (algebraMap A₀ (F.obj j)) := by
    -- Proof comment: the factorization identity is exactly the compatibility needed for the
    -- scalar tower `A₀ → F.obj j → c.pt`.
    ext a
    simpa [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using
      congrArg (fun k : CommRingCat.of A₀ ⟶ c.pt => k.hom a) hφj_factor
  haveI : IsScalarTower A₀ (F.obj j) c.pt := IsScalarTower.of_algebraMap_eq' hstage_eq
  let B_j : Type u := (F.obj j) ⊗[A₀] B₀
  refine ⟨j, B_j, inferInstance, inferInstance, ?_⟩
  -- Proof comment: smoothness base-changes from `A₀ → B₀` to the stage `F.obj j`, and
  -- `cancelBaseChange` identifies the resulting tensor model with the original smooth algebra.
  constructor
  · infer_instance
  · refine ⟨hB.some.trans ?_⟩
    exact (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj j) c.pt c.pt B₀).symm

end

/-! ### Lemma_10_138_16 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

-- Proof sketch: the forward implication is the standard base-change stability of
-- `Algebra.FormallySmooth`. For the converse, rewrite formal smoothness through the owner theorem
-- `Algebra.formallySmooth_iff`, descend projectivity of `Ω[S⁄R]` from the base-changed Kähler
-- module via `KaehlerDifferential.tensorKaehlerEquiv` and faithfully flat descent for projective
-- modules, and descend `Subsingleton (H1Cotangent R S)` from `Algebra.tensorH1CotangentOfFlat`
-- using `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`.
/-- Lemma 10.138.16: formal smoothness is equivalent to formal smoothness after faithfully flat
base change; in canonical tensor-product order, `R → S` is formally smooth if and only if
`R' → R' ⊗[R] S` is formally smooth. -/
theorem formallySmooth_iff_formallySmooth_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FormallySmooth R S ↔ Algebra.FormallySmooth R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  constructor
  · intro h
    letI : Algebra.FormallySmooth R S := h
    infer_instance
  · intro h
    rw [Algebra.formallySmooth_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
      letI : Module.FaithfullyFlat S (S ⊗[R] R') := by infer_instance
      letI : Module.FaithfullyFlat S (R' ⊗[R] S) :=
        Module.FaithfullyFlat.of_linearEquiv S (S ⊗[R] R')
          (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
      letI : Module.Projective (R' ⊗[R] S) (Ω[R' ⊗[R] S⁄R']) := h.1
      let e := KaehlerDifferential.tensorKaehlerEquiv R R' S (R' ⊗[R] S)
      letI : Module.Projective (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[S] Ω[S⁄R]) :=
        Module.Projective.of_equiv e.symm
      exact Module.Projective.of_projective_tensorProduct_of_faithfullyFlat (R' ⊗[R] S)
    · letI : Subsingleton (Algebra.H1Cotangent R' (R' ⊗[R] S)) := h.2
      let e := Algebra.tensorH1CotangentOfFlat R S R'
      letI : Subsingleton (R' ⊗[R] Algebra.H1Cotangent R S) := e.injective.subsingleton
      simpa using
        (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
          R R').1 (show Subsingleton (R' ⊗[R] Algebra.H1Cotangent R S) from inferInstance)

end

end Algebra

/-! ### Lemma_10_138_17 (from Chap10) -/
universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Smooth R S]

/-- Helper for Lemma 10.138.17: a finitely generated subideal of a locally nilpotent ideal is
nilpotent. -/
lemma isNilpotent_of_fg_le_of_isLocallyNilpotent {I J : Ideal A}
    (hJfg : J.FG) (hJI : J ≤ I) (hI : I.IsLocallyNilpotent) :
    IsNilpotent J := by
  -- Local nilpotence places every element of `J` in the nilradical.
  have hJnilrad : J ≤ nilradical A := by
    intro x hx
    exact (Ideal.isLocallyNilpotent_iff I).mp hI x (hJI hx)
  -- Finite generation upgrades elementwise nilpotence to nilpotence of the ideal.
  exact (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).2 hJnilrad

/- Domain-style sampling:
- primary domain: infinitesimal lifting for smooth algebras across quotient maps by locally
  nilpotent ideals;
- sampled owner declarations: the chapter owner `Ideal.IsLocallyNilpotent`, together with
  mathlib's `Algebra.FormallySmooth.exists_lift` and the owner field
  `Algebra.Smooth.formallySmooth`;
- best owner abstraction: `Smooth R S` is the source-facing ambient owner, while local nilpotence
  should be expressed through `Ideal.IsLocallyNilpotent` rather than restating the containment
  `I ≤ nilradical A`.

Source/core/bridge triage:
- `source-facing`: the theorem below, which matches Lemma `10.138.17`;
- `core/canonical`: `Algebra.FormallySmooth.exists_lift`;
- `bridge/view`: the reduction from a locally nilpotent ideal to a nilpotent ideal inside a
  finite type subalgebra used in the proof sketch.
-/

-- Proof sketch: smoothness gives formal smoothness together with finite presentation. Descend the
-- given map `S → A ⧸ I` and finitely many chosen lifts of generators to a finite type
-- `ℤ`-subalgebra `A₀ ⊆ A`; then `I ∩ A₀` is nilpotent because `A₀` is Noetherian, so the
-- infinitesimal lifting theorem for formally smooth algebras applies to produce a lift into `A₀`,
-- hence into `A`.
/-- Lemma 10.138.17: if `R → S` is smooth and `I` is a locally nilpotent ideal of the
`R`-algebra `A`, then every commutative square
`S → A ⧸ I ← A` over `R` admits a lift `S → A`. In canonical form, the locally nilpotent
hypothesis is expressed by the chapter owner `I.IsLocallyNilpotent`. -/
theorem smooth_exists_lift_of_quotient_by_locally_nilpotent
    (I : Ideal A) (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  classical
  obtain ⟨n, φ, hφ, hkerφfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let qI : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  -- Choose lifts in `A` of the images of the finitely many presentation variables.
  have hliftX : ∀ i : Fin n, ∃ a : A, qI a = f (φ (MvPolynomial.X i)) := by
    intro i
    exact Ideal.Quotient.mkₐ_surjective R I (f (φ (MvPolynomial.X i)))
  choose a ha using hliftX
  let ψ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval a
  have hqIψ : qI.comp ψ = f.comp φ := by
    -- The chosen lifts make the two maps agree on the polynomial generators.
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simpa [qI, ψ] using ha i
  let J : Ideal A := (RingHom.ker φ.toRingHom).map ψ.toRingHom
  have hker_le_comap_I : RingHom.ker φ.toRingHom ≤ I.comap ψ.toRingHom := by
    intro p hp
    -- Relations of the presentation map into `I` because they vanish after quotienting by `I`.
    rw [RingHom.mem_ker] at hp
    have hp' : φ p = 0 := hp
    change ψ p ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa [qI, AlgHom.comp_apply, hp'] using AlgHom.congr_fun hqIψ p)
  have hJ_le_I : J ≤ I := by
    exact Ideal.map_le_iff_le_comap.mpr hker_le_comap_I
  have hJfg : J.FG := Ideal.FG.map hkerφfg ψ.toRingHom
  have hJnil : IsNilpotent J :=
    isNilpotent_of_fg_le_of_isLocallyNilpotent hJfg hJ_le_I hI
  let qJ : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  have hker_le_comap_J : RingHom.ker φ.toRingHom ≤ RingHom.ker ((qJ.comp ψ).toRingHom) := by
    intro p hp
    -- Modding out by the defect ideal kills the images of all presentation relations.
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem ψ.toRingHom hp)
  let g : S →ₐ[R] A ⧸ J := AlgHom.liftOfSurjective φ hφ (qJ.comp ψ) hker_le_comap_J
  have hg_comp : g.comp φ = qJ.comp ψ := by
    -- This is the defining descent property of `AlgHom.liftOfSurjective`.
    exact AlgHom.liftOfSurjective_comp φ hφ (qJ.comp ψ) hker_le_comap_J
  have hg_mod_I : (Ideal.Quotient.factorₐ R hJ_le_I).comp g = f := by
    -- After passing from `A ⧸ J` to `A ⧸ I`, the descended map is the original quotient map.
    apply AlgHom.ext
    intro s
    obtain ⟨p, rfl⟩ := hφ s
    exact AlgHom.congr_fun (by
      calc
        (((Ideal.Quotient.factorₐ R hJ_le_I).comp g).comp φ)
            = (Ideal.Quotient.factorₐ R hJ_le_I).comp (g.comp φ) := by
                rw [AlgHom.comp_assoc]
        _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp (qJ.comp ψ) := by
              rw [hg_comp]
        _ = ((Ideal.Quotient.factorₐ R hJ_le_I).comp qJ).comp ψ := by
              rw [AlgHom.comp_assoc]
        _ = qI.comp ψ := by
              rw [Ideal.Quotient.factorₐ_comp_mk]
        _ = f.comp φ := hqIψ) p
  obtain ⟨f', hf'⟩ := FormallySmooth.exists_lift (R := R) (A := S) (B := A) J hJnil g
  refine ⟨f', ?_⟩
  -- The nilpotent lift over `A ⧸ J` also lifts the original map over `A ⧸ I`.
  calc
    qI.comp f' = ((Ideal.Quotient.factorₐ R hJ_le_I).comp qJ).comp f' := by
      rw [Ideal.Quotient.factorₐ_comp_mk]
    _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp (qJ.comp f') := by
          rw [AlgHom.comp_assoc]
    _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp g := by rw [hf']
    _ = f := hg_mod_I

end

end Algebra
