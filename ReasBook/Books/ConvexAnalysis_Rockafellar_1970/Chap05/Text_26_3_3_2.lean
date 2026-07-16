import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_26_3_3

noncomputable section

open scoped Rockafellar

universe u v

section

variable {E : Type u} {F : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]

/- The owner-level convexity clause only uses the chapter convexity owner `Function.IsConvex`
and the source-facing linear-image owner `Function.linearImage`, so it lives on the minimal
`ℝ`-module layer. -/
/-- The linear image of a globally convex real-valued function is globally convex. -/
theorem linearImage_convexOn_univ (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (A ◁ f) := by
  sorry

/-- The linear image of the lifted source function is convex on the canonical extended-real owner
layer. -/
theorem linearImage_toEReal_isConvex (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    (A ◁ f.toEReal).IsConvex ℝ := by
  simpa [Function.toEReal] using
    Function.isConvex_linearImage A f.toEReal
      (Function.isConvex_coe_of_convexOn_univ hf_convex)

end

section

variable {𝕜 α : Type*} {E : Type u} {F : Type v}
variable [Semiring 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

/-- Positivity of the recession function on every nonzero kernel vector gives the canonical
Chapter 2 owner hypothesis `A.noAsymmetricRecessionKernel h`. -/
theorem noAsymmetricRecessionKernel_of_positive_recession_on_ker
    (h : E → WithBotTop α) (A : E →ₗ[𝕜] F)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < ((h)₀⁺) x) :
    A.noAsymmetricRecessionKernel h := by
  intro x hx_nonpos hx_neg
  by_contra hxA
  by_cases hx_zero : x = 0
  · have hx_nonpos_zero : ((h)₀⁺) 0 ≤ 0 := by simpa [hx_zero] using hx_nonpos
    have hx_pos_zero : 0 < ((h)₀⁺) 0 := by simpa [hx_zero] using hx_neg
    exact (not_lt_of_ge hx_nonpos_zero hx_pos_zero).elim
  · have hx_pos : 0 < ((h)₀⁺) x :=
      hpositive_recession_on_ker x (LinearMap.mem_ker.mp hxA) hx_zero
    exact (not_lt_of_ge hx_nonpos hx_pos).elim

end

section

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]

/-- The textbook positivity condition on nonzero kernel vectors implies the canonical Chapter 2
owner hypothesis `A.noAsymmetricRecessionKernel f.toEReal`. -/
theorem noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
    (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x) :
    A.noAsymmetricRecessionKernel f.toEReal :=
  noAsymmetricRecessionKernel_of_positive_recession_on_ker
    f.toEReal A hpositive_recession_on_ker

end

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: this text says that a differentiable convex real-valued function remains
  differentiable convex after taking its linear image under a surjective map, provided the
  recession function is strictly positive on every nonzero kernel vector.
- `core/canonical`: the relevant owners already present in the project are `Function.linearImage`
  with notation `A ◁ f`, the finite-branch owner `Function.realBranch`, the relative-domain
  notation `riDom(·)`, Fenchel conjugation `f⋆`, the recession-function notation `0⁺`, and the
  essential-smoothness owner `Function.IsEssentiallySmooth`.
- `bridge/view`: the source real-valued function is expressed through the canonical lifted owner
  `f.toEReal`, while the source-facing image function remains the real-valued owner `A ◁ f`.
  The lifted image `A ◁ f.toEReal` is used only to invoke the Chapter 26 essential-smoothness
  owner and then bridge back to `A ◁ f` by identifying `A ◁ f.toEReal = (A ◁ f).toEReal`.

Domain-style sampling used here:
- `exists_image_mem_intrinsicInterior_effectiveDomain_iff_no_adjoint_asymmetric_recession`;
- `isConvex_toWithBotTopOn_iff`;
- `Function.isConvex_linearImage`;
- `linearImage_isEssentiallySmooth_of_isEssentiallySmooth_of_exists_adjoint_mem_riDom_conjugate`;
- `Function.IsEssentiallySmooth.differentiableOn_realBranch`.

Primitive data vs derived API:
- primitive source data: the convex real-valued function `f`, the surjective linear map `A`, and
  the Chapter 2 owner hypothesis `A.noAsymmetricRecessionKernel f.toEReal`;
- source-facing bridge data: the stronger textbook positivity condition on nonzero kernel vectors,
  used only to recover the owner hypothesis when one wants the theorem in its original prose form;
- derived API: the adjoint relative-interior qualification, essential smoothness of
  `A ◁ f.toEReal`, the canonical lift bridge `A ◁ f.toEReal = (A ◁ f).toEReal`, and the resulting
  differentiability of the source-facing real-valued image `A ◁ f`.
-/

-- Proof sketch: apply Corollary 16.2.1 to the adjoint map `A.adjoint` and to the conjugate
-- `(f.toEReal)⋆`. The source recession hypothesis on `ker A` is exactly the negation of the
-- asymmetric-recession obstruction after rewriting `(A.adjoint).adjoint = A` and viewing
-- `((f.toEReal)⋆)⋆0⁺` as the source recession function `f0⁺`.
variable (f : E → ℝ) (A : E →ₗ[ℝ] F)

/-- The canonical Chapter 2 recession-kernel owner forces the adjoint range to meet the relative
interior of the conjugate domain, expressed as `A.adjoint yStar ∈ riDom((f.toEReal)⋆)`. -/
theorem exists_adjoint_mem_riDom_convexConjugate_toEReal_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal) :
    ∃ yStar : F, A.adjoint yStar ∈ riDom((f.toEReal)⋆) := sorry

/-- The positivity of `f0⁺` on the nonzero kernel of `A` forces the adjoint range to meet the
relative interior of the conjugate domain, expressed as `A.adjoint yStar ∈ riDom((f.toEReal)⋆)`. -/
theorem exists_adjoint_mem_riDom_convexConjugate_toEReal_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x) :
    ∃ yStar : F, A.adjoint yStar ∈ riDom((f.toEReal)⋆) :=
  exists_adjoint_mem_riDom_convexConjugate_toEReal_of_no_asymmetric_recession_kernel
    f A hf_convex (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)

-- Proof sketch: a differentiable convex real-valued function on all of `E` gives an essentially
-- smooth lifted function `f.toEReal`, because `dom(f.toEReal) = Set.univ` and the boundary
-- blow-up clause is vacuous. Then use the qualification theorem above together with
-- Corollary 26.3.3 for the surjective map `A`.
/-- Under the canonical Chapter 2 recession-kernel owner, the lifted image `A ◁ f.toEReal` is
essentially smooth on the canonical extended-real owner layer. -/
theorem linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    (A ◁ f.toEReal).IsEssentiallySmooth := sorry

/-- Under the textbook positivity condition on nonzero kernel vectors, the lifted image
`A ◁ f.toEReal` is essentially smooth. -/
theorem linearImage_toEReal_isEssentiallySmooth_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    (A ◁ f.toEReal).IsEssentiallySmooth :=
  linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

-- Proof sketch: surjectivity makes every fiber of `A` nonempty, so the lifted image
-- `A ◁ f.toEReal` is finite above at every point. The Chapter 9 attainment theorem then produces
-- a fiber minimizer, which is also a minimizer for the real-valued image owner `A ◁ f`. This
-- identifies the lifted owner with the canonical codomain lift of `A ◁ f`.
/-- Under the canonical Chapter 2 recession-kernel owner, the lifted image is exactly the
canonical codomain lift of the real-valued image owner. -/
theorem linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hA : Function.Surjective A) :
    A ◁ f.toEReal = (A ◁ f).toEReal := sorry

/-- Under the textbook positivity condition on nonzero kernel vectors, the lifted image is exactly
the canonical codomain lift of the real-valued image owner. -/
theorem linearImage_toEReal_eq_toEReal_linearImage_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hA : Function.Surjective A) :
    A ◁ f.toEReal = (A ◁ f).toEReal :=
  linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hA

-- Proof sketch: apply essential smoothness of `A ◁ f.toEReal`, rewrite that lifted owner as
-- `(A ◁ f).toEReal`, identify the real branch with `A ◁ f`, and use `dom((A ◁ f).toEReal) =
-- Set.univ` to upgrade `DifferentiableOn` on the interior domain to global differentiability.
/-- Under the canonical Chapter 2 recession-kernel owner, the real-valued image `A ◁ f` is
differentiable on all of `F`. -/
theorem linearImage_differentiable_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    Differentiable ℝ (A ◁ f) := by
  have hess : (A ◁ f.toEReal).IsEssentiallySmooth :=
    linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
      f A hf_convex hkernel hf_diff hA
  have hEq :
      A ◁ f.toEReal = (A ◁ f).toEReal :=
    linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
      f A hf_convex hkernel hA
  have hbranch : (A ◁ f.toEReal).realBranch = A ◁ f := by
    funext y
    rw [hEq]
    simp
  have hdom0 : dom(A ◁ f.toEReal) = Set.univ := by
    ext y
    rw [mem_effectiveDomain]
    constructor
    · intro _
      simp
    · intro _
      have hEqAt : (A ◁ f.toEReal) y = ((A ◁ f) y : EReal) := congrFun hEq y
      exact hEqAt ▸ WithBotTop.coe_lt_top ((A ◁ f) y)
  have hdom : interior (dom(A ◁ f.toEReal)) = Set.univ := by
    rw [hdom0]
    simp
  have hdiffOn : DifferentiableOn ℝ (A ◁ f) (interior (dom(A ◁ f.toEReal))) := by
    simpa [hbranch] using hess.differentiableOn_realBranch
  have hdiffOn_univ : DifferentiableOn ℝ (A ◁ f) Set.univ := by
    simpa [hdom] using hdiffOn
  exact differentiableOn_univ.1 hdiffOn_univ

/-- Under the textbook positivity condition on nonzero kernel vectors, the real-valued image
`A ◁ f` is differentiable on all of `F`. -/
theorem linearImage_differentiable_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    Differentiable ℝ (A ◁ f) :=
  linearImage_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

/-- Canonical owner-layer form of Text 26.3.3.2: under the Chapter 2 recession-kernel owner
`A.noAsymmetricRecessionKernel f.toEReal`, the real-valued image `A ◁ f` is convex on `univ`
and differentiable on all of `F`. -/
theorem linearImage_convexOn_univ_and_differentiable_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    ConvexOn ℝ Set.univ (A ◁ f) ∧ Differentiable ℝ (A ◁ f) := by
  refine ⟨linearImage_convexOn_univ f A hf_convex, ?_⟩
  exact linearImage_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex hkernel hf_diff hA

/-- Text 26.3.3.2: if `f : E → ℝ` is differentiable and convex on the whole space, and if
`A : E →ₗ[ℝ] F` is surjective with `A x = 0`, `x ≠ 0` implying `0 < (f.toEReal)₀⁺ x`, then the
real-valued linear image `A ◁ f` is convex and differentiable on all of `F`. -/
theorem linearImage_convexOn_univ_and_differentiable_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    ConvexOn ℝ Set.univ (A ◁ f) ∧ Differentiable ℝ (A ◁ f) :=
  linearImage_convexOn_univ_and_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

end
