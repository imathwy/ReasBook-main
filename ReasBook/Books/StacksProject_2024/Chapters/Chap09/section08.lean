import Mathlib
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_8_1 (from Chap09) -/
/- Domain-style sampling for Definition 9.8.1:
- primary domain: algebraic elements and algebraic field extensions;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`,
  `Algebra.isAlgebraic_def`;
- sampled derived/specification API:
  `Transcendental`,
  `transcendental_iff`,
  `Algebra.isAlgebraic_iff`;
- best owner abstraction: the pointwise owner predicate `IsAlgebraic`, with the extension-level
  owner `Algebra.IsAlgebraic` derived by quantifying pointwise algebraicity over the top field;
- primitive data: none locally, since Definition 9.8.1 is already owned upstream by mathlib;
- derived API: the extension-level owner and its specification theorem
  `Algebra.isAlgebraic_def`.

Source/core/bridge triage:
- `source-facing`: the textbook notions "an element is algebraic over the base field" and "the
  extension is algebraic";
- `core/canonical`: `IsAlgebraic` and `Algebra.IsAlgebraic`;
- `bridge/view`: `Algebra.isAlgebraic_def`, which restates the extension-level owner as the
  textbook pointwise condition.

This file should therefore remain a pure recall surface: the source statement is already the
canonical owner declaration, so any local wrapper or rephrased duplicate would only create
parallel API without adding mathematics. -/

/- Definition 9.8.1 (Tag 09GC): for a field extension `F/E`, an element `α ∈ F` is algebraic
over `E` exactly when it is the root of a nonzero polynomial with coefficients in `E`; this is
the canonical mathlib predicate `IsAlgebraic`. -/
recall IsAlgebraic

/- Companion recall: an algebraic extension in the sense of Definition 9.8.1 is the canonical
mathlib typeclass `Algebra.IsAlgebraic`, whose fields are exactly the pointwise algebraicity
statements for elements of the top field. -/
recall Algebra.IsAlgebraic

/- Companion recall: the extension `F/E` is algebraic exactly when every element of `F` is
algebraic over `E`, as expressed by `Algebra.isAlgebraic_def`. -/
recall Algebra.isAlgebraic_def

/-! ### Example_9_8_2 (from Chap09) -/
open Polynomial
open Complex
open scoped ComplexConjugate

/- Domain-style sampling for Example 9.8.2:
- primary domain: algebraic field extensions, with the concrete companion of writing an explicit
  annihilating polynomial for a complex number over `ℝ`;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`,
  `Algebra.IsAlgebraic.isAlgebraic`;
- sampled supporting API for the explicit quadratic companion:
  `Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`,
  `Complex.mul_conj'`;
- best owner abstraction: the extension-level owner `Algebra.IsAlgebraic ℝ ℂ`, with pointwise
  algebraicity derived from that owner rather than introduced through a local wrapper;
- primitive data: none locally for the main example, since algebraicity of `ℂ/ℝ` is already the
  upstream canonical instance;
- derived API: the textbook quadratic polynomial attached to `z : ℂ`, exhibited here only as a
  thin source-facing companion.

Source/core/bridge triage:
- `source-facing`: the explicit quadratic over `ℝ` vanishing at `z`;
- `core/canonical`: `Algebra.IsAlgebraic ℝ ℂ`;
- `bridge/view`: the factorization of the mapped real quadratic as
  `(X - C (conj z)) * (X - C z)` in `ℂ[X]`.

This file should therefore keep the owner-level statement as a direct instance check and retain
only the explicit quadratic as companion API; introducing any separate local owner for the same
algebraicity notion would duplicate upstream chapter and mathlib declarations. -/

/- Example 9.8.2: the field `ℂ` is algebraic over `ℝ`; this is the canonical mathlib instance
`Algebra.IsAlgebraic ℝ ℂ`. -/
#check (inferInstance : Algebra.IsAlgebraic ℝ ℂ)

/-- Companion theorem: the textbook quadratic over `ℝ` attached to `z : ℂ` vanishes at `z`,
so every complex number is explicitly seen to be algebraic over `ℝ`. -/
theorem aeval_complex_quadratic_over_real (z : ℂ) :
    aeval z (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map]
  calc
    eval z (map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ)) =
        eval z ((X - C (conj z)) * (X - C z)) := by
          congr 1
          calc
            map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ) =
                X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by
                  simp
            _ = (X - C (conj z)) * (X - C z) := by
                rw [← add_conj, map_add, ← mul_conj', map_mul]
                ring
    _ = 0 := by
      simp

/-! ### Example_9_8_3 (from Chap09) -/
open scoped IntermediateField Manifold
open IntermediateField
open IntermediateField.AdjoinSimple

universe u v

/- Domain-style sampling for Example 9.8.3:
- primary domain: one-dimensional function fields and simple subextensions generated by a single
  transcendental element;
- sampled owner declarations:
  `compactRiemannSurface_functionField`,
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`,
  `IntermediateField.adjoin_simple_eq_bot_iff`,
  `algebraicIndependent_singleton_iff`,
  `IsTranscendenceBasis.isAlgebraic_field`;
- best owner abstraction: the singleton `IsTranscendenceBasis` generated by `f`;
- primitive data: the meromorphic function field `ℂ(X)` and the chosen element `f`;
- derived API: transcendence of `f` over `ℂ`, then algebraicity of `ℂ(X)` over `ℂ⟮f⟯`.

Source/core/bridge triage:
- `source-facing`: the nonconstant meromorphic function `f` and the simple subextension `ℂ⟮f⟯`;
- `core/canonical`: the singleton transcendence-basis owner for `f`;
- `bridge/view`: the algebraicity statement over `ℂ⟮f⟯` obtained from
  `IsTranscendenceBasis.isAlgebraic_field`.

The refined file keeps the source semantics but removes a universe-lifted singleton index and the
hand-rolled algebraically-closed-field argument, rewriting the proofs directly against the
canonical owners.
-/

/-- Helper for Example 9.8.3: a nonconstant meromorphic function on a compact Riemann surface is
transcendental over `ℂ`. -/
theorem meromorphicFunctionField_transcendental_of_not_mem_range
    {X : CompactRiemannSurface.{u}} {f : ℂ(X)}
    (hf : f ∉ Set.range (algebraMap ℂ (ℂ(X)))) :
    Transcendental ℂ f := by
  -- Convert the transcendence claim into the negation of algebraicity.
  change ¬ IsAlgebraic ℂ f
  intro hf_alg
  -- If `f` were algebraic, then the simple extension `ℂ⟮f⟯` would collapse to the constants.
  have hbot : (ℂ⟮f⟯ : IntermediateField ℂ (ℂ(X))) = ⊥ := by
    letI : Algebra.IsAlgebraic ℂ ℂ⟮f⟯ := isAlgebraic_adjoin_simple hf_alg.isIntegral
    simpa using eq_bot_of_isAlgClosed_of_isAlgebraic (ℂ⟮f⟯ : IntermediateField ℂ (ℂ(X)))
  -- But `f ∈ ℂ⟮f⟯`, so this would force `f` to lie in the image of the constant field.
  exact hf <| mem_bot.mp <| adjoin_simple_eq_bot_iff.mp hbot

/-- Helper for Example 9.8.3: the one-variable rational function field has transcendence degree
one over its base field. -/
lemma ratFunc_trdeg_eq_one (k : Type u) [Field k] :
    Algebra.trdeg k (RatFunc k) = 1 := by
  -- Identify `RatFunc k` with the fraction field of the polynomial ring `k[X]`.
  let e : RatFunc k ≃ₐ[k] FractionRing (Polynomial k) := RatFunc.toFractionRingAlgEquiv k k
  -- Passing from `k[X]` to its fraction field adds no transcendence.
  letI : Algebra.IsAlgebraic (Polynomial k) (FractionRing (Polynomial k)) := by
    exact (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial k)
      (K := FractionRing (Polynomial k)) (C := FractionRing (Polynomial k))).2 inferInstance
  have hfrac : Algebra.trdeg (Polynomial k) (FractionRing (Polynomial k)) = 0 := by
    simpa using
      (trdeg_eq_zero : Algebra.trdeg (Polynomial k) (FractionRing (Polynomial k)) = 0)
  have hpoly : Algebra.trdeg k (Polynomial k) = 1 := Polynomial.trdeg_of_isDomain
  -- Additivity in the tower `k → k[X] → Frac(k[X])` computes the fraction-field transcendence degree.
  have htrdegFrac : Algebra.trdeg k (FractionRing (Polynomial k)) = 1 := by
    have hsum := trdeg_add_eq k (Polynomial k) (A := FractionRing (Polynomial k))
    rw [hpoly, hfrac] at hsum
    simpa using hsum.symm
  simpa [htrdegFrac] using e.trdeg_eq

/-- Helper for Example 9.8.3: any finite extension of `RatFunc k` still has transcendence degree
one over `k`. -/
lemma trdeg_eq_one_of_finiteDimensional_over_ratFunc
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FiniteDimensional (RatFunc k) K] :
    Algebra.trdeg k K = 1 := by
  -- Finite-dimensional extensions are algebraic, so the top layer contributes no new transcendence.
  letI : Algebra.IsAlgebraic (RatFunc k) K := Algebra.IsAlgebraic.of_finite (RatFunc k) K
  have htop : Algebra.trdeg (RatFunc k) K = 0 := by
    simpa using (trdeg_eq_zero : Algebra.trdeg (RatFunc k) K = 0)
  -- Additivity in the tower reduces the computation to `RatFunc k`.
  have hsum := lift_trdeg_add_eq k (RatFunc k) K
  rw [ratFunc_trdeg_eq_one k, htop] at hsum
  simpa using hsum.symm

/-- Helper for Example 9.8.3: if `K` is algebraic over the simple extension `k⟮t⟯` generated by
a transcendental element `t`, then `K/k` has transcendence degree one. -/
lemma trdeg_eq_one_of_transcendental_isAlgebraic_over_adjoinSimple
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {t : K} (ht : Transcendental k t)
    (halg : Algebra.IsAlgebraic (↥k⟮t⟯) K) :
    Algebra.trdeg k K = 1 := by
  let x : ULift.{v} (Fin 1) → K := fun _ ↦ t
  -- The chosen transcendental element gives an algebraically independent one-element family.
  have hx : AlgebraicIndependent k x := by
    rw [algebraicIndependent_singleton_iff (ULift.up 0)]
    simpa [x] using ht
  have hx_range : Set.range x = ({t} : Set K) := by
    ext z
    simp [x]
  -- Repackage the simple extension as the algebra generated by that one-element family.
  have halgField : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := by
    rw [hx_range]
    simpa using halg
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K := by
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp halgField
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K := halg'
  -- Since the extension is algebraic over the adjoined singleton, this singleton is a
  -- transcendence basis once its cardinality bounds the transcendence degree from above.
  have hbasis : IsTranscendenceBasis k x := by
    refine AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      (R := k) (A := K) (ι := ULift.{v} (Fin 1)) (x := x) hx ?_
    simpa [x] using (Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range x))
  -- A one-element transcendence basis has cardinality `1`.
  have hcard := IsTranscendenceBasis.cardinalMk_eq_trdeg
    (R := k) (A := K) (ι := ULift.{v} (Fin 1)) (x := x) hbasis
  simpa using hcard.symm

/-- Helper for Example 9.8.3: the geometric input needed for the function-field computation is
the existence of one nonconstant meromorphic generator whose simple subextension is algebraically
cofinal in `ℂ(X)`. -/
theorem compactRiemannSurface_exists_functionFieldGenerator (X : CompactRiemannSurface.{u}) :
    ∃ f : ℂ(X), f ∉ Set.range (algebraMap ℂ (ℂ(X))) ∧
      Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)) := by
  -- Route correction: the earlier search for a universal `∀ f` algebraicity theorem was too
  -- strong; the main computation only needs one witness with the desired algebraicity property.
  -- TODO: prove the geometric bridge that a compact Riemann surface admits some nonconstant
  -- meromorphic function `f` and that `ℂ(X)` is algebraic over the simple field `ℂ⟮f⟯`.
  sorry

/-- Helper for Example 9.8.3: one generator that is transcendental over `ℂ` and algebraically
cofinal already forces the meromorphic function field to have transcendence degree one. -/
lemma compactRiemannSurface_functionField_of_exists_functionFieldGenerator
    {X : CompactRiemannSurface.{u}}
    (hgen : ∃ f : ℂ(X), f ∉ Set.range (algebraMap ℂ (ℂ(X))) ∧
      Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X))) :
    Algebra.trdeg ℂ (ℂ(X)) = 1 := by
  obtain ⟨f, hf_nonconst, hf_alg⟩ := hgen
  -- The chosen generator is transcendental because it does not come from the constant field.
  have hf_trans : Transcendental ℂ f :=
    meromorphicFunctionField_transcendental_of_not_mem_range hf_nonconst
  -- The existing singleton-adjoin helper then computes the full transcendence degree.
  simpa using
    trdeg_eq_one_of_transcendental_isAlgebraic_over_adjoinSimple
      (K := ℂ(X)) hf_trans hf_alg

/-- Bridge for Example 9.8.3: the meromorphic function field of a compact Riemann surface has
transcendence degree one over `ℂ`. -/
theorem compactRiemannSurface_functionField (X : CompactRiemannSurface.{u}) :
    Algebra.trdeg ℂ (ℂ(X)) = 1 := by
  -- Route correction: the main theorem now reduces immediately to the single geometric witness
  -- packaged in `compactRiemannSurface_exists_functionFieldGenerator`.
  exact compactRiemannSurface_functionField_of_exists_functionFieldGenerator
    (compactRiemannSurface_exists_functionFieldGenerator X)

/-- Example 9.8.3: if `X` is a compact Riemann surface and `f ∈ ℂ(X)` is nonconstant, then the
field of meromorphic functions `ℂ(X)` is algebraic over the simple subextension `ℂ⟮f⟯ = ℂ(f)`
generated by `f`. -/
-- Proof sketch: Example 9.26.8 identifies `ℂ(X)` as a one-dimensional function field, so
-- `trdeg ℂ ℂ(X) = 1`. A nonconstant meromorphic function is transcendental over `ℂ`, hence the
-- singleton family generated by `f` is a transcendence basis of `ℂ(X)/ℂ`; then the canonical
-- theorem `IsTranscendenceBasis.isAlgebraic_field` gives algebraicity over `ℂ⟮f⟯`.
theorem meromorphicFunctionField_isAlgebraic_over_adjoin_of_nonconstant
    (X : CompactRiemannSurface.{u}) (f : ℂ(X))
    (hf : f ∉ Set.range (algebraMap ℂ (ℂ(X)))) :
    Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)) := by
  let x : Unit → ℂ(X) := fun _ ↦ f
  -- Rewrite the singleton family into the concrete singleton set `{f}`.
  have hx_range : Set.range x = ({f} : Set ℂ(X)) := by
    ext z
    simp [x]
  -- The previous lemma turns nonconstancy into algebraic independence of the singleton family.
  have hAI : AlgebraicIndependent ℂ x := by
    rw [algebraicIndependent_singleton_iff ()]
    exact meromorphicFunctionField_transcendental_of_not_mem_range hf
  -- Example 9.26.8 computes the transcendence degree as `1`, so this singleton is a basis.
  have hbasis : IsTranscendenceBasis ℂ x := by
    refine hAI.isTranscendenceBasis_of_lift_trdeg_le_of_finite ?_
    rw [compactRiemannSurface_functionField X]
    simp
  -- Algebraicity over the field generated by a transcendence basis is the canonical conclusion.
  change Algebra.IsAlgebraic (IntermediateField.adjoin ℂ ({f} : Set ℂ(X))) (ℂ(X))
  rw [← hx_range]
  exact hbasis.isAlgebraic_field

/-! ### Lemma_9_8_4 (from Chap09) -/
/- Domain-style sampling for Lemma 9.8.4:
- primary domain: algebraic elements and algebraic extensions in a tower of field extensions;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`;
- sampled derived API:
  `IsAlgebraic.tower_top`,
  `Algebra.IsAlgebraic.tower_top`;
- best owner abstraction: the pointwise owner `IsAlgebraic`, with the extension-level owner
  `Algebra.IsAlgebraic` for the quantified version;
- primitive data: none locally, since the tower-stability statements are already canonical
  mathlib theorems on these owners;
- derived API: the two `tower_top` theorems.

Source/core/bridge triage:
- `source-facing`: algebraicity descends along the base field in a tower `F ⟶ E ⟶ K`;
- `core/canonical`: `IsAlgebraic` and `Algebra.IsAlgebraic`;
- `bridge/view`: `IsAlgebraic.tower_top` and `Algebra.IsAlgebraic.tower_top`, which express the
  tower-stability property for the pointwise and extension-level owners.

This file should therefore stay recall-only: a local theorem shell would duplicate the canonical
owner-derived API without adding new mathematics or improving the statement surface. -/

/- Lemma 9.8.4: in a tower of field extensions `K/E/F`, any element of `K` that is algebraic
over `F` is also algebraic over `E`; this is the canonical theorem `IsAlgebraic.tower_top`. -/
recall IsAlgebraic.tower_top

/- Companion recall: if the extension `K/F` is algebraic, then the extension `K/E` is algebraic;
this is the canonical theorem `Algebra.IsAlgebraic.tower_top`. -/
recall Algebra.IsAlgebraic.tower_top

/-! ### Lemma_9_8_5 (from Chap09) -/
universe u v

open IntermediateField
open IntermediateField.AdjoinSimple

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/- Domain-style sampling for Lemma 9.8.5:
- primary domain: algebraic field extensions and simple intermediate-field adjoin;
- sampled owner declarations:
  `Algebra.IsAlgebraic.of_finite`,
  `IntermediateField.adjoin.finiteDimensional`,
  `IntermediateField.isAlgebraic_iff`,
  `IntermediateField.isAlgebraic_adjoin_simple`;
- best owner abstraction: the ambient extension-level owner `Algebra.IsAlgebraic k E`, with
  `IntermediateField.adjoin k ({α} : Set E)` as the canonical simple-subextension owner;
- primitive data: the element `α : E` generating the simple intermediate field `k⟮α⟯`;
- derived API: finite-dimensionality of `k⟮α⟯` and algebraicity of its distinguished generator.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of algebraicity by finiteness of every simple
  subextension `k⟮α⟯/k`;
- `core/canonical`: `Algebra.IsAlgebraic`, `IntermediateField.adjoin`, and their owner-derived API;
- `bridge/view`: the iff theorem below, which packages the source statement by quantifying the
  canonical simple-subextension owner over all generators `α : E`.

The file should therefore keep the source-facing iff theorem, but its proof should route directly
through the canonical owner API rather than introducing any parallel wrapper definitions. -/

/- Companion recall: a finite field extension is algebraic. This is the canonical mathlib theorem
`Algebra.IsAlgebraic.of_finite`; for field extensions, `FiniteDimensional k E` supplies the
required `Module.Finite k E` instance. -/
recall Algebra.IsAlgebraic.of_finite

-- Proof sketch: for the forward direction, if `E/k` is algebraic then each `α : E` is algebraic,
-- hence integral, so `IntermediateField.adjoin.finiteDimensional` makes `k⟮α⟯` finite over `k`.
-- For the reverse direction, if every `k⟮α⟯/k` is finite, then `α` is algebraic over `k` by
-- `IsAlgebraic.of_finite` applied inside the simple extension, and therefore `E/k` is algebraic.
/-- Lemma 9.8.5: an extension `E/k` is algebraic if and only if every simple subextension
`k⟮α⟯/k` generated by some `α : E` is finite-dimensional over `k`. -/
theorem isAlgebraic_iff_finiteDimensional_adjoin_simple
    : Algebra.IsAlgebraic k E ↔ ∀ α : E, FiniteDimensional k k⟮α⟯ := by
  constructor
  · intro h α
    -- Each element of an algebraic extension is integral, so its simple adjoin is finite.
    exact IntermediateField.adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (h.isAlgebraic α))
  · intro h
    constructor
    intro α
    -- A finite-dimensional simple subextension is algebraic over `k`.
    letI : FiniteDimensional k k⟮α⟯ := h α
    have hSub : Algebra.IsAlgebraic k k⟮α⟯ := Algebra.IsAlgebraic.of_finite k k⟮α⟯
    have hgen : IsAlgebraic k (AdjoinSimple.gen k α) := hSub.isAlgebraic (AdjoinSimple.gen k α)
    -- Transfer algebraicity of the distinguished generator back to the ambient element `α`.
    have hα : IsAlgebraic k ((AdjoinSimple.gen k α : k⟮α⟯) : E) :=
      (IntermediateField.isAlgebraic_iff
        (K := k) (L := E) (S := k⟮α⟯) (x := AdjoinSimple.gen k α)).mp hgen
    simpa using hα

/-! ### Lemma_9_8_6 (from Chap09) -/
universe u v

/- Source/core/bridge triage:
- primary domain: algebraic field extensions and intermediate-field adjoin;
- sampled owner declarations: `IntermediateField.adjoin`,
  `IntermediateField.finiteDimensional_adjoin`, `IntermediateField.adjoin.finiteDimensional`, and
  `Algebra.IsAlgebraic.of_finite`;
- core/canonical owner abstraction: `IntermediateField.adjoin k S`;
- layer: `bridge/view`; this source-facing family-indexed statement is a specialization of the
  canonical finite-set owner theorem for `adjoin`;
- primitive data: the finite family `α : ι → K` together with the pointwise algebraicity witness
  `hα`;
- derived API: finite-dimensionality of the intermediate field generated by `Set.range α`.
-/

/-- Lemma 9.8.6 (Tag 09GH): the core owner theorem is
`IntermediateField.finiteDimensional_adjoin`, whose primitive input is a finite set of integral
elements. This is the source-facing family-indexed bridge obtained by applying it to `Set.range α`
and using that algebraic elements of a field extension are integral. -/
theorem finiteDimensional_adjoin_range_of_isAlgebraic
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {ι : Type*} [Finite ι] {α : ι → K}
    (hα : ∀ i, IsAlgebraic k (α i)) :
    FiniteDimensional k (IntermediateField.adjoin k (Set.range α)) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x ⟨i, rfl⟩
  exact (hα i).isIntegral

/-! ### Lemma_9_8_7 (from Chap09) -/
universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/- Domain-style sampling for Lemma 9.8.7:
- primary domain: algebraic field extensions and the intermediate field cut out by algebraic
  elements;
- sampled owner declarations:
  `algebraicClosure`,
  `mem_algebraicClosure_iff`,
  `le_algebraicClosure`,
  `le_algebraicClosure_iff`;
- best owner abstraction: the canonical intermediate field `algebraicClosure k E`;
- primitive data: none locally, since the source statement is already owned by mathlib's
  `algebraicClosure`;
- derived API: the membership/specification theorem `mem_algebraicClosure_iff` and the order
  characterization `le_algebraicClosure_iff`.

Source/core/bridge triage:
- `source-facing`: the set of elements of `E` algebraic over `k` forms a subextension of `E / k`;
- `core/canonical`: `algebraicClosure k E : IntermediateField k E`;
- `bridge/view`: `mem_algebraicClosure_iff`, which identifies membership in the owner with the
  textbook pointwise algebraicity predicate.

This file should therefore remain a pure recall surface: the source statement is already the
canonical owner declaration, so any local `def` or wrapper theorem would only duplicate upstream
API. -/

/- Lemma 9.8.7 (Tag 09GI): for a field extension `E / k`, the elements of `E` algebraic over `k`
form a subextension of `E / k`; in mathlib this subextension is the canonical intermediate field
`algebraicClosure k E`, i.e. the relative algebraic closure of `k` in `E`. -/
recall algebraicClosure

/- Companion recall: membership in `algebraicClosure k E` is exactly algebraicity over `k`. -/
recall mem_algebraicClosure_iff

/-! ### Lemma_9_8_8 (from Chap09) -/
/- Domain-style sampling for Lemma 9.8.8:
- primary domain: transitivity of algebraic field extensions in a tower;
- sampled owner declarations:
  `IsAlgebraic.restrictScalars`,
  `Algebra.IsAlgebraic.trans`,
  `Algebra.IsAlgebraic.tower_top`;
- best owner abstraction: `Algebra.IsAlgebraic.trans`;
- primitive data: a tower of field extensions with algebraicity hypotheses on the two stages;
- derived API: the pointwise restriction-of-scalars route proving the top extension is algebraic.

Source/core/bridge triage:
- `source-facing`: algebraicity of the composite field extension;
- `core/canonical`: `Algebra.IsAlgebraic.trans`;
- `bridge/view`: `IsAlgebraic.restrictScalars`, which is the pointwise mechanism used by the owner
  theorem.

This file should therefore remain a pure recall surface: the source statement is already exactly
the canonical owner theorem, so any local theorem restating transitivity would only duplicate
upstream API. -/

/- Lemma 9.8.8 (Tag 09GJ): if `E / k` and `F / E` are algebraic extensions of fields, then
`F / k` is an algebraic extension of fields; this is the canonical transitivity theorem
`Algebra.IsAlgebraic.trans`. -/
recall Algebra.IsAlgebraic.trans

/-! ### Lemma_9_8_9 (from Chap09) -/
universe u

open Cardinal

section

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.8.9:
- primary domain: cardinality bounds for algebraic extensions;
- sampled owner declarations:
  `Algebra.IsAlgebraic.cardinalMk_le_max`,
  `Algebra.IsAlgebraic.lift_cardinalMk_le_max`,
  `IsTranscendenceBasis.cardinalMk_eq`,
  `Algebra.trdeg`;
- best owner abstraction: `Algebra.IsAlgebraic.cardinalMk_le_max`;
- primitive data: the field extension `F ⟶ E` together with the algebraicity hypothesis;
- derived API: textbook rewrites such as commuting the `max` arguments are mere consequences, not a
  second owner theorem.

Source/core/bridge triage:
- `source-facing`: the field-theoretic cardinality bound in Tag `09GK`;
- `core/canonical`: `Algebra.IsAlgebraic.cardinalMk_le_max`;
- `bridge/view`: none needed here, since the source statement is exactly the canonical owner theorem
  specialized to fields. -/

/- Lemma 9.8.9 (Tag 09GK): if `E / F` is an algebraic extension of fields, then
`|E| ≤ max (|F|, ℵ₀)`; this is the canonical mathlib theorem
`Algebra.IsAlgebraic.cardinalMk_le_max`, already tagged `[stacks 09GK]`. -/
recall Algebra.IsAlgebraic.cardinalMk_le_max

end

/-! ### Lemma_9_8_10 (from Chap09) -/
universe u

section

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.8.10:
- primary domain: algebraic field extensions and the canonical bundled subobject hierarchy over a
  base field;
- sampled owner declarations:
  `Subalgebra.isField_of_algebraic`,
  `Subalgebra.toIntermediateField'`,
  `Subfield`,
  `Subfield.toIntermediateField`;
- best owner abstraction: `Subalgebra.isField_of_algebraic`;
- primitive data: a subring `R : Subring E` together with the condition that `R` contains the
  image of `F`, which is exactly the data needed to regard `R` as an `F`-subalgebra of `E`;
- derived API: the induced `Subalgebra F E`, the resulting field structure on `R`, and any
  bundled `Subfield` or `IntermediateField` obtained from that field structure.

Source/core/bridge triage:
- `source-facing`: a subring of an algebraic field extension containing the image of the base
  field is a field;
- `core/canonical`: `Subalgebra.isField_of_algebraic`;
- `bridge/view`: the conversion from a `Subring E` plus `hF` to a `Subalgebra F E`.

This file should therefore stay a minimal bridge theorem: the source statement is not literally
the owner theorem, but it should delegate directly to that owner instead of introducing any
parallel local wrapper API. -/

namespace Subring

/-- Lemma 9.8.10: in an algebraic extension `E/F`, any subring `R ⊆ E` containing the image of
`F` is a field. This is the minimal `Subring` bridge to the canonical owner theorem
`Subalgebra.isField_of_algebraic`. -/
theorem isField_of_algebraic (R : Subring E) (hF : ∀ x : F, algebraMap F E x ∈ R) :
    IsField R := by
  -- View `R` as the corresponding `F`-subalgebra of `E` using the hypothesis that it contains
  -- the image of the base field.
  -- The canonical owner theorem proves that this bundled subalgebra is a field in an algebraic
  -- extension, and the carrier is definitionally the original subring.
  simpa using
    (Subalgebra.isField_of_algebraic (Subalgebra.mk R.toSubsemiring hF : Subalgebra F E))

end Subring

end

/-! ### Lemma_9_8_11 (from Chap09) -/
/- Domain-style sampling for Lemma 9.8.11:
- primary domain: algebraic field extensions and their endomorphisms;
- sampled owner declarations:
  `Algebra.IsAlgebraic.algHom_bijective`,
  `Algebra.IsAlgebraic.algEquivEquivAlgHom`,
  `AlgEquiv.ofBijective`,
  `AlgEquiv.toAlgHom`;
- best owner abstraction: the extension-level owner theorem
  `Algebra.IsAlgebraic.algHom_bijective`, which directly states bijectivity of an
  `F`-algebra endomorphism of an algebraic field extension;
- primitive data: the algebraic field extension `F ⟶ E` and an endomorphism `f : E →ₐ[F] E`;
- derived API: turning that bijective endomorphism into an automorphism via `AlgEquiv.ofBijective`,
  or packaging all such endomorphisms as equivalences via
  `Algebra.IsAlgebraic.algEquivEquivAlgHom`.

Source/core/bridge triage:
- `source-facing`: the textbook fact that an endomorphism of an algebraic field extension is an
  automorphism;
- `core/canonical`: `Algebra.IsAlgebraic.algHom_bijective`;
- `bridge/view`: `AlgEquiv.ofBijective` and `Algebra.IsAlgebraic.algEquivEquivAlgHom`, which
  convert the bijectivity statement into the automorphism viewpoint.

This file should therefore remain recall-only: the source lemma is owned canonically by the
bijection theorem `Algebra.IsAlgebraic.algHom_bijective`, and the automorphism viewpoint is
already provided upstream by `Algebra.IsAlgebraic.algEquivEquivAlgHom`. Any local theorem or
abbrev would only duplicate owner-level API. -/

/- Lemma 9.8.11: for an algebraic field extension `E/F`, any `F`-algebra endomorphism
`f : E →ₐ[F] E` is bijective, hence an `F`-algebra automorphism. This is the canonical mathlib
theorem `Algebra.IsAlgebraic.algHom_bijective`. -/
recall Algebra.IsAlgebraic.algHom_bijective

/- Companion recall: the automorphism viewpoint is already packaged canonically by the
multiplicative equivalence between `F`-algebra automorphisms of `E` and `F`-algebra endomorphisms
of `E`, namely `Algebra.IsAlgebraic.algEquivEquivAlgHom`. -/
recall Algebra.IsAlgebraic.algEquivEquivAlgHom
