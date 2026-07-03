import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_38_2_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.2.1 is about the bifunction infimal convolution `F₁ D F₂`, the
  slice-domain `dom F`, the properness owner `IsProper`, and the adjoint-side closure formula.
- `core/canonical`: the chapter owners already present upstream are `Bifunction.infimalConvolution`
  with notation `D`, `Bifunction.dom`, `Bifunction.IsProper`, `Bifunction.adjoint`,
  `Bifunction.IsClosedConvex`, and `Bifunction.closure`.
- `bridge/view`: the only remaining bridge is the relation between that source-facing bifunction
  owner and the Chapter 2 one-variable closure owner `cl(·)` on ordinary graph functions.

Domain-style sampling used here:
- `Bifunction.infimalConvolution`, notation `D`, and `Bifunction.dom` from `Chap08.Theorem_38_1`;
- `Bifunction.IsProper` from `Chap08.Theorem_38_1`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `dom(·)`, `riDom(·)`, and `cl(·)` on ordinary graph functions from earlier chapters.

Primitive data vs derived API:
- primitive owner data reused from the chapter: `F₁`, `F₂`, `dom F`, `IsProper F`, `F₁ D F₂`,
  `adjoint F`, and `closure F`;
- derived API: the closed-convex clause for `F₁ D F₂` and the adjoint-side closure identity.

Layer target:
- the corollary remains `source-facing` on the chapter's bifunction owners `dom`, `D`, and
  `IsProper`, `adjoint`;
- the closure on the right-hand side is `bridge/view`, written through the source-facing owner
  `closure`.
-/

section Closedness

variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

-- Proof sketch: the graph function of `F₁ D F₂` is the Chapter 1 partial infimal convolution of
-- the two graph functions, and the common-relative-interior hypothesis is already expressed on the
-- Chapter 38 slice-domain owner `dom`. Apply the corresponding closed-convex infimal-convolution
-- theorem to the graph functions and read the result back through `Bifunction.IsClosedConvex`.
/-- Corollary 38.2.1 (1): if closed convex bifunctions `F₁` and `F₂` have a common point in
`ri (dom F₁) ∩ ri (dom F₂)`, then `F₁ D F₂` is closed convex. The separate properness hypotheses
are redundant here, since the common-relative-interior assumption already forces both slice-domains
to be nonempty. -/
theorem isClosedConvex_infimalConvolution_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁ : IsClosedConvex F₁) (hF₂ : IsClosedConvex F₂)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    IsClosedConvex (F₁ D F₂) := by
  sorry

end Closedness

section Adjoint

variable {UStar : Type u} {XStar : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Neg UStar]
variable [TopologicalSpace XStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]

-- Proof sketch: identify the pairing-based adjoint of `F₁ D F₂` with the closure of the
-- adjoint-side infimal convolution, using the same common-relative-interior hypothesis on
-- `dom F₁` and `dom F₂`. The right-hand side is expressed through the source-facing closure owner.
/-- Corollary 38.2.1 (2): under the same common-relative-interior hypothesis,
`(F₁ D F₂)^* = cl (F₁^* D F₂^*)`, rendered by `adjoint`, `D`, and `closure`. -/
theorem
    adjointFunction_infimalConvolution_eq_closure_adjoint_infimalConvolution_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁ : IsClosedConvex F₁) (hF₂ : IsClosedConvex F₂)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    adjoint XStar UStar (F₁ D F₂) =
      closure
        ((adjoint XStar UStar F₁) D
          (adjoint XStar UStar F₂)) := by
  sorry

end Adjoint

end

end Bifunction

/-! ### Proposition_38_2_1 (from Chap08) -/
noncomputable section

open Function
open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.2.1 compares the graph closure of the bifunction infimal
  convolution `F₁ D F₂` with the ordinary lower-semicontinuous hull of the slice
  `(F₁ u) □ (F₂ u)` at parameter values `u` in the relative interior of the bifunction domain.
- `core/canonical`: the existing owners are `Bifunction.infimalConvolution` with notation `D`,
  `Bifunction.dom`, `Bifunction.closure`, and the Chapter 2 function closure owner `cl(·)`.
- `bridge/view`: `cl F` is defined by graph closure and currying, so the proposition is a
  slice theorem relating that source-facing owner to the one-variable closure owner `cl(·)` on
  the slicewise infimal convolution.

Domain-style sampling used here:
- `Bifunction.closure` and `Bifunction.uncurry_closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.uncurry_infimalConvolution_isConvex` and
  `Bifunction.dom_infimalConvolution_eq_inter` from `Chap08.Theorem_38_1`;
- `Bifunction.convex_dom` from `Chap06.Proposition_6_29_2`;
- `Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior` from `Chap02.Theorem_6_5`.

Primitive data vs derived API:
- primitive source data: convex bifunctions `F₁` and `F₂`;
- primitive owners reused directly: `F₁ D F₂`, `dom (F₁ D F₂)`, and
  `cl ((F₁ u) □ (F₂ u))`;
- source-facing closure owner reused directly: `cl (F₁ D F₂)`;
- derived API: the bridge reformulation from the source-facing qualification
  `u ∈ ri(dom F₁) ∩ ri(dom F₂)` to the owner-side qualification
  `u ∈ ri(dom (F₁ D F₂))`.

Codomain normalization:
- this item uses the chapter's canonical codomain `WithBotTop ℝ` rather than the alias `EReal`,
  because the closure, domain, and infimal-convolution owners imported here already live on that
  canonical layer.

Layer target: `source-facing`, stated directly on the existing bifunction owners and the canonical
one-variable closure owner.
-/

-- Proof sketch: first use `uncurry_infimalConvolution_isConvex` to see that `F₁ D F₂` is again a
-- convex bifunction on `U × X`. Then apply the chapter theorem identifying the graph closure of a
-- convex bifunction with the lower-semicontinuous hull of each slice on `ri(dom (F₁ D F₂))`,
-- and finally rewrite the slice `(F₁ D F₂) u` as `(F₁ u) □ (F₂ u)`.
/-- Bridge lemma: under the owner-side qualification `u ∈ ri (dom (F₁ D F₂))`, the `u`-slice of
the bifunction closure of the infimal convolution equals the lower-semicontinuous hull of the
slicewise infimal convolution. -/
theorem closure_infimalConvolution_slice_eq_sliceClosure_of_mem_ri_dom
    {F₁ F₂ : U → X → WithBotTop ℝ}
    (hF₁_convex : (uncurry F₁).IsConvex ℝ)
    (hF₂_convex : (uncurry F₂).IsConvex ℝ)
    {u : U} (hu : u ∈ ri(dom (F₁ D F₂))) :
    cl (F₁ D F₂) u = cl((F₁ u) □ (F₂ u)) := sorry

-- Proof sketch: identify `dom (F₁ D F₂)` with `dom F₁ ∩ dom F₂` through Theorem 38.1. Because
-- both domains are convex, Theorem 6.5 upgrades the source-facing hypothesis
-- `u ∈ ri(dom F₁) ∩ ri(dom F₂)` to `u ∈ ri(dom (F₁ D F₂))`. Then apply the bridge lemma above.
/-- Proposition 38.2.1: if `u ∈ ri (dom F₁) ∩ ri (dom F₂)`, then the `u`-slice of the bifunction
closure of `F₁ D F₂` equals the lower-semicontinuous hull of the slicewise infimal convolution
`(F₁ u) □ (F₂ u)`. -/
theorem closure_infimalConvolution_slice_eq_sliceClosure_of_mem_inter_ri_dom
    {F₁ F₂ : U → X → WithBotTop ℝ}
    (hF₁_convex : (uncurry F₁).IsConvex ℝ)
    (hF₂_convex : (uncurry F₂).IsConvex ℝ)
    {u : U} (hu : u ∈ ri(dom F₁) ∩ ri(dom F₂)) :
    cl (F₁ D F₂) u = cl((F₁ u) □ (F₂ u)) := by
  have hF₁_slice_convex : ∀ u, (F₁ u).IsConvex ℝ := hF₁_convex.slice_uncurry
  have hF₂_slice_convex : ∀ u, (F₂ u).IsConvex ℝ := hF₂_convex.slice_uncurry
  have hF₁_dom_convex : Convex ℝ (dom F₁) := convex_dom hF₁_convex
  have hF₂_dom_convex : Convex ℝ (dom F₂) := convex_dom hF₂_convex
  have hri_inter :
      ri(dom F₁ ∩ dom F₂) = ri(dom F₁) ∩ ri(dom F₂) := by
    let C : Bool → Set U := fun b ↦ cond b (dom F₁) (dom F₂)
    have hC_convex : ∀ b : Bool, Convex ℝ (C b) := by
      intro b
      cases b
      · simpa [C] using hF₂_dom_convex
      · simpa [C] using hF₁_dom_convex
    have hC_ri : (⋂ b : Bool, ri(C b)).Nonempty := by
      refine ⟨u, Set.mem_iInter.2 ?_⟩
      intro b
      cases b
      · simpa [C] using hu.2
      · simpa [C] using hu.1
    calc
      ri(dom F₁ ∩ dom F₂) = ri(⋂ b : Bool, C b) := by
        rw [Set.inter_eq_iInter]
      _ = ⋂ b : Bool, ri(C b) := by
        simpa [C] using
          Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior hC_convex hC_ri
      _ = ri(dom F₁) ∩ ri(dom F₂) := by
        ext x
        constructor
        · intro hx
          exact ⟨by simpa [C] using (Set.mem_iInter.1 hx) true,
            by simpa [C] using (Set.mem_iInter.1 hx) false⟩
        · rintro ⟨hx₁, hx₂⟩
          refine Set.mem_iInter.2 fun b ↦ ?_
          cases b
          · simpa [C] using hx₂
          · simpa [C] using hx₁
  have hu' : u ∈ ri(dom (F₁ D F₂)) := by
    rw [dom_infimalConvolution_eq_inter hF₁_slice_convex hF₂_slice_convex, hri_inter]
    exact hu
  exact closure_infimalConvolution_slice_eq_sliceClosure_of_mem_ri_dom
    hF₁_convex hF₂_convex hu'

end

end Bifunction

/-! ### Definition_38_2_2 (from Chap08) -/
noncomputable section

open scoped Pointwise
open Function

universe u v

namespace Bifunction

section

variable {U : Type u} {X : Type v} {𝕜 : Type*} {α : Type*}
variable [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [ConditionallyCompleteLinearOrder α]
variable [SMul 𝕜 X] [SMul 𝕜 α]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 38.2.2 introduces the scalar multiple `F λ` of a convex bifunction
  `F`, with the slicewise formula `((F λ) u) x = λ (F u) (λ⁻¹ x)` for positive `λ`.
- `core/canonical`: the owner abstraction already present upstream is the Chapter 5 slice owner
  `Function.rightScalarMul`, together with its positive-parameter evaluation theorem
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`.
- `bridge/view`: the bifunction scalar multiple is just the slicewise lift of that owner to
  curried two-variable functions, not a second scalar-rescaling mechanism.

Domain-style sampling used here:
- `Function.rightScalarMul` and the notation `λ •ʳ f` from `Chap01.Text_5_4_2`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from `Chap01.Text_5_4_3`;
- `Function.IsConvex.rightScalarMul` from `Chap01.Text_5_4_2`, showing the chapter already treats
  scalar rescaling as slice-level derived API.

Primitive data vs derived API:
- primitive source-facing owner: `Bifunction.rightScalarMul`;
- primitive bridge data: for each `u`, the slice `rightScalarMul F λ u` is the Chapter 5 owner
  `(⟨(λ : 𝕜), λ.2.le⟩ : Set.Ici (0 : 𝕜)) •ʳ F u`;
- derived API: the slice-bridge theorem and the pointwise positive-scalar formula below.

Notation decision:
- no new bifunction notation is introduced here. The chapter already uses `•ʳ` for the canonical
  slice owner, while the textbook juxtaposition `F λ` does not translate to an inference-stable
  Lean notation distinct from ordinary function application.

Redundant-source-assumption elimination:
- the source says “let `F` be a convex bifunction”, but the scalar-rescaling construction itself
  depends only on the bifunction and the positive scalar. Convexity belongs in later theorems
  about preservation of convexity, not in this defining owner.

Layer target: `source-facing`, implemented as a thin bridge to the existing `core/canonical`
slice owner.
-/

/-- Definition 38.2.2: for a positive scalar `λ`, the scalar multiple of a bifunction `F` is
obtained by taking the Chapter 5 right scalar multiple of each slice `F u`. -/
abbrev rightScalarMul (F : U → X → WithBotTop α) (lam : Set.Ioi (0 : 𝕜)) :
    U → X → WithBotTop α :=
  fun u ↦ ((⟨(lam : 𝕜), lam.2.le⟩ : 𝕜≥0) •ʳ F u)

/-- Each slice of the bifunction scalar multiple is exactly the Chapter 5 right scalar multiple of
the corresponding slice of `F`. -/
@[simp] theorem rightScalarMul_slice
    (F : U → X → WithBotTop α) (lam : Set.Ioi (0 : 𝕜)) (u : U) :
    rightScalarMul F lam u = (⟨(lam : 𝕜), lam.2.le⟩ : 𝕜≥0) •ʳ F u :=
  rfl

end

section

variable {U : Type u} {X : Type v} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [MulAction 𝕜 X]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- For each `u`, the scalar multiple of the slice `F u` is given pointwise by
`x ↦ λ (F u) (λ⁻¹ • x)`. -/
theorem rightScalarMul_apply
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) (u : U) (x : X) :
    rightScalarMul F lam u x = (lam : WithBotTop 𝕜) * F u ((lam : 𝕜)⁻¹ • x) := by
  simpa using
    rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (F u) (a := (lam : 𝕜)) lam.2 x

end

end Bifunction

/-! ### Theorem_38_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.2 is the adjoint-duality identity for the bifunction infimal
  convolution `F₁ D F₂`.
- `core/canonical`: the stable owners already present upstream are `D`, `adjoint`, the
  bifunction-domain owner `dom F`, and the graph-properness owner `(Function.uncurry F).IsProper`.
- `bridge/view`: Proposition 6.29.3 already gives the exact bridge
  `dom_eq_setOf_slice_isProper_of_isProper`, identifying `dom F` with the source set
  `{u | (F u).IsProper}` under the graphwise properness hypothesis. The theorem should therefore
  use the established owner `dom F` on its public surface rather than restating that set.

Domain-style sampling used here:
- `Bifunction.dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.dom_eq_setOf_slice_isProper_of_isProper` from `Chap06.Proposition_6_29_3`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `Bifunction.infimalConvolution`, notation `D`, from `Chap08.Definition_38_0_1`.

Primitive data vs derived API:
- primitive source data: bifunctions `F₁` and `F₂`;
- primitive owner hypotheses: convexity and graphwise properness of `Function.uncurry F₁` and
  `Function.uncurry F₂`, together with the chapter qualification owner
  `ri(dom F₁) ∩ ri(dom F₂)`;
- derived bridge data: the source qualification set `{u | (F u).IsProper}` is recovered from
  `dom F` via `dom_eq_setOf_slice_isProper_of_isProper`.

Layer target: `source-facing`.
-/

-- Proof sketch: combine the Chapter 38 infimal-convolution owner `D` with the Chapter 6 adjoint
-- owner `adjoint` under the common-relative-interior qualification on `dom F₁` and
-- `dom F₂`. The source wording in terms of proper slices is recovered owner-theoretically by
-- `dom_eq_setOf_slice_isProper_of_isProper`, while the exact adjoint identity keeps the graphwise
-- properness hypotheses on `Function.uncurry F₁` and `Function.uncurry F₂`.
/- Bridge/view form of the source qualification: under graphwise properness, the textbook sets
`{u | (F₁ u).IsProper}` and `{u | (F₂ u).IsProper}` may be replaced by the chapter owner
`dom F₁` and `dom F₂`. -/
omit [FiniteDimensional ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
  [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ] in
theorem common_riDom_of_common_ri_setOf_slice_isProper
    {F₁ F₂ : U → X → EReal}
    (hF₁_graphProper : (Function.uncurry F₁).IsProper)
    (hF₂_graphProper : (Function.uncurry F₂).IsProper)
    (hri :
      (ri({u : U | (F₁ u).IsProper}) ∩ ri({u : U | (F₂ u).IsProper})).Nonempty) :
    (ri(dom F₁) ∩ ri(dom F₂)).Nonempty := by
  have hdom₁ : dom F₁ = {u : U | (F₁ u).IsProper} :=
    dom_eq_setOf_slice_isProper_of_isProper hF₁_graphProper
  have hdom₂ : dom F₂ = {u : U | (F₂ u).IsProper} :=
    dom_eq_setOf_slice_isProper_of_isProper hF₂_graphProper
  simpa [hdom₁, hdom₂] using hri

/-- Theorem 38.2: if convex bifunctions `F₁` and `F₂` are graphwise proper and have a common
point in `ri (dom F₁) ∩ ri (dom F₂)`, then the adjoint of their infimal convolution is the
infimal convolution of their adjoints, i.e. `(F₁ D F₂)^* = F₁^* D F₂^*`, rendered by the owners
`dom`, `D`, and `adjoint`. The convexity, graph-properness, and common-`ri(dom)`
qualification hypotheses are part of the public owner surface; the preceding bridge theorem only
recovers the source wording in terms of `{u | (F u).IsProper}`. -/
theorem
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjointFunction_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁_convex : Function.IsConvex ℝ (Function.uncurry F₁))
    (hF₁_graphProper : (Function.uncurry F₁).IsProper)
    (hF₂_convex : Function.IsConvex ℝ (Function.uncurry F₂))
    (hF₂_graphProper : (Function.uncurry F₂).IsProper)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    adjoint X U (F₁ D F₂) =
      (adjoint X U F₁) D (adjoint X U F₂) := sorry

end

end Bifunction

/-! ### Proposition_38_2_3 (from Chap08) -/
noncomputable section

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.2.3 says that if `F` is the convex indicator bifunction of a
  linear transformation `A`, then the positive scalar multiple `F λ` is the convex indicator
  bifunction of the scaled linear transformation `(lam : 𝕜) • A`.
- `core/canonical`: the chapter already owns the two relevant constructions as
  `Bifunction.rightScalarMul` from Definition 38.2.2 and the singleton-graph owner
  `Bifunction.graphIndicator` from Definition 6.29.9.
- `bridge/view`: the proposition is the source-facing slice identity obtained by applying
  `rightScalarMul` to `graphIndicator 𝕜 A`; the slice formula of Definition 6.29.9 is now derived
  API rather than the public owner surface.

Primary mathematical domain:
- convex-analysis bifunctions built from singleton indicators of linear maps and their positive
  scalar rescaling.

Domain-style sampling used here:
- `Bifunction.rightScalarMul` and `Bifunction.rightScalarMul_apply`
  from `Chap08.Definition_38_2_2`;
- `Bifunction.graphIndicator` and `Bifunction.graphIndicator_slice`
  from `Chap06.Definition_6_29_9`;
- the scalar action on linear maps `U →ₗ[𝕜] X` from mathlib.

Primitive data vs derived API:
- primitive source data: a linear map `A : U →ₗ[𝕜] X` and a positive scalar `lam`;
- primitive owners reused directly: `rightScalarMul` and `graphIndicator`;
- derived API: the displayed slice identity for the scaled graph-indicator bifunction.

Layer target: `source-facing`, expressed directly in the existing owner language.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: evaluate both bifunctions pointwise. `rightScalarMul_apply` rewrites the left-hand
-- side as `(lam : 𝕜) * graphIndicator 𝕜 A u ((lam : 𝕜)⁻¹ • x)`, and `graphIndicator_cases`
-- reduces each side to the `0`/`⊤` singleton-indicator alternatives. The two branches are
-- equivalent because multiplying by `lam` and by `lam⁻¹` are inverse scalar actions.
/-- Proposition 38.2.3: the right scalar multiple of the singleton-graph indicator bifunction of a
linear map `A` is the singleton-graph indicator bifunction of the scaled linear map
`(lam : 𝕜) • A`. -/
theorem rightScalarMul_graphIndicator
    (A : U →ₗ[𝕜] X) (lam : Set.Ioi (0 : 𝕜)) :
    rightScalarMul (graphIndicator 𝕜 A) lam =
      graphIndicator 𝕜 ((lam : 𝕜) • A) := by
  ext u x
  by_cases hx : x = (lam : 𝕜) • A u
  · subst hx
    simp [rightScalarMul_apply, graphIndicator_cases, inv_smul_smul₀, lam.2.ne']
  · have hne : ((lam : 𝕜)⁻¹ • x) ≠ A u := by
      intro h
      apply hx
      calc
        x = (lam : 𝕜) • ((lam : 𝕜)⁻¹ • x) := by
          simpa using (smul_inv_smul₀ lam.2.ne' x).symm
        _ = (lam : 𝕜) • A u := by rw [h]
    simpa [rightScalarMul_apply, graphIndicator_cases, hx, hne] using
      (WithBotTop.coe_mul_top_of_pos lam.2 : (lam : WithBotTop 𝕜) * ⊤ = (⊤ : WithBotTop 𝕜))

/-- Slice form of Proposition 38.2.3. -/
theorem rightScalarMul_graphIndicator_apply
    (A : U →ₗ[𝕜] X) (lam : Set.Ioi (0 : 𝕜)) (u : U) :
    rightScalarMul (graphIndicator 𝕜 A) lam u =
      graphIndicator 𝕜 ((lam : 𝕜) • A) u := by
  simpa using congrFun (rightScalarMul_graphIndicator A lam) u

end

end Bifunction
