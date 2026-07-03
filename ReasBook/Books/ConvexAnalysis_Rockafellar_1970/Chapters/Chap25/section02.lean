import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.2 says that for a finite convex function, differentiability at `x`
  is equivalent to linearity of the directional-derivative function `y ↦ f'(x; y)`.
- `core/canonical`: the owner level is the Chapter 23 directional-derivative owner
  `Function.directionalDerivativeAt` on extended-real-valued functions together with the Chapter 1
  linear-lift owner `Function.IsLinearLift`; the resulting Chapter 25 owner is
  `Function.HasLinearDirectionalDerivativeAt` for `f : E → WithBotTop 𝕜`.
- `bridge/view`: the finite scalar-valued textbook setting is expressed through the canonical lift
  `f.toWithBotTop`, so the dual-valued Chapter 23 subdifferential owner is
  `∂ f.toWithBotTop at x`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  `Chap05.Definition_23_0_6`;
- `_root_.subdifferentialAt_nonempty_of_mem_riDom` from `Chap05.Theorem_23_4`;
- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from `Chap05.Theorem_23_2`;
- `Function.subdifferentialWithinAt_eq_singleton_fderiv` and
  `Function.differentiableAt_of_existsUnique_mem_subdifferentialWithinAt` from
  `Chap05.Theorem_25_1`;
- `Function.IsLinearLift` and `Function.IsLinearLift.odd` from `Chap01.Theorem_4_8`.

Primitive data vs derived API:
- primitive source data: an extended-real-valued directional-derivative owner
  `directionalDerivativeAt f x` together with a base point `x`;
- primitive owner surface: `f.HasLinearDirectionalDerivativeAt x` for `f : E → WithBotTop 𝕜`;
- derived API: the finite scalar-valued specialization through `f.toWithBotTop` and uniqueness of
  the dual subdifferential owner `∂ f.toWithBotTop at x`.

Ambient-assumption minimization:
- the owner `Function.HasLinearDirectionalDerivativeAt` only needs the primitive module layer
  `[AddCommMonoid E] [Module 𝕜 E]`, because it is defined from the directional-derivative owner
  and the top-submodule linear-lift owner;
- the core equivalence is stated on an arbitrary finite-dimensional `𝕜`-normed space, because the
  Chapter 23 directional-derivative and dual-subdifferential owners already live there and no
  inner-product structure appears in the mathematical content of Theorem 25.2 itself;
- no Euclidean-coordinate or standard-basis partial-derivative theorem is owned in this file:
  such coordinate bridges belong downstream from the canonical owner layer.

Notation evaluation:
- no extra symbolic notation is introduced for directional-derivative linearity: the object-prefix
  owner `f.HasLinearDirectionalDerivativeAt x` is already the short, inference-stable public
  surface, while the scalar-valued theorem surface reads this canonically through
  `f.toWithBotTop` rather than a duplicate owner.
-/

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-- Rockafellar's condition that the directional derivative `y ↦ f'(x; y)` is linear. This
Chapter 5 owner lives on the canonical extended-real directional-derivative layer and asks that
the top-submodule restriction of `directionalDerivativeAt f x` be the `WithBotTop` lift of a
linear map. -/
abbrev HasLinearDirectionalDerivativeAt (f : E → WithBotTop 𝕜) (x : E) : Prop :=
  (((directionalDerivativeAt f x) ∘ (⊤ : Submodule 𝕜 E).subtype)).IsLinearLift

end Function
end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function

-- Proof sketch: for a finite convex function, differentiability at `x` yields a unique supporting
-- dual functional at `x` through the relative-owner theorem on `Set.univ`; conversely, uniqueness
-- of the Chapter 23 owner `∂ f.toWithBotTop at x` is the `Set.univ` specialization of the
-- finite-dimensional converse theorem from Theorem 25.1.
/-- Theorem 25.2, core owner form: for a finite convex function on a finite-dimensional
normed space, differentiability at `x` is equivalent to uniqueness of the dual-valued
subdifferential owner `∂ f.toWithBotTop at x`. -/
theorem differentiableAt_iff_existsUnique_mem_subdifferentialAt
    {f : E → 𝕜} {x : E} (hf_convex : ConvexOn 𝕜 Set.univ f) :
    DifferentiableAt 𝕜 f x ↔
      ∃! xStar : StrongDual 𝕜 E, xStar ∈ (∂ f.toWithBotTop at x) := by
  have h_univ : Function.toWithBotTopOn f Set.univ = f.toWithBotTop := by
    funext z
    simp [Function.toWithBotTopOn, Function.toWithBotTop]
  have hx_int_univ : x ∈ interior (Set.univ : Set E) := by simp
  have hx_ri_univ : x ∈ ri[𝕜](Set.univ) :=
    interior_subset_intrinsicInterior (𝕜 := 𝕜) hx_int_univ
  constructor
  · intro hdiff
    refine ⟨fderiv 𝕜 f x, ?_, ?_⟩
    · have hsub : _root_.subdifferentialWithinAt f Set.univ x = {fderiv 𝕜 f x} :=
        Function.subdifferentialWithinAt_eq_singleton_fderiv
          (U := Set.univ) hf_convex (x := x) hx_ri_univ hdiff.hasFDerivAt
      have hmem : fderiv 𝕜 f x ∈ _root_.subdifferentialWithinAt f Set.univ x := by
        simp [hsub]
      change fderiv 𝕜 f x ∈ _root_.subdifferentialAt (Function.toWithBotTopOn f Set.univ) x at hmem
      rw [h_univ] at hmem
      exact hmem
    · intro y hy
      have hsub : _root_.subdifferentialWithinAt f Set.univ x = {fderiv 𝕜 f x} :=
        Function.subdifferentialWithinAt_eq_singleton_fderiv
          (U := Set.univ) hf_convex (x := x) hx_ri_univ hdiff.hasFDerivAt
      have hy' : y ∈ _root_.subdifferentialWithinAt f Set.univ x := by
        change y ∈ _root_.subdifferentialAt (Function.toWithBotTopOn f Set.univ) x
        rw [h_univ]
        exact hy
      have hy'' : y ∈ ({fderiv 𝕜 f x} : Set (StrongDual 𝕜 E)) := by
        simpa [hsub] using hy'
      simpa using hy''
  · intro huniq
    have huniq' :
        ∃! xStar : StrongDual 𝕜 E, xStar ∈ _root_.subdifferentialWithinAt f Set.univ x := by
      refine ⟨huniq.choose, ?_, ?_⟩
      · change huniq.choose ∈ _root_.subdifferentialAt (Function.toWithBotTopOn f Set.univ) x
        rw [h_univ]
        exact huniq.choose_spec.1
      · intro y hy'
        have hy : y ∈ _root_.subdifferentialAt f.toWithBotTop x := by
          change y ∈ _root_.subdifferentialAt (Function.toWithBotTopOn f Set.univ) x at hy'
          rw [h_univ] at hy'
          exact hy'
        exact huniq.unique hy huniq.choose_spec.1
    exact Function.differentiableAt_of_existsUnique_mem_subdifferentialWithinAt
      (U := Set.univ) hf_convex (x := x) hx_ri_univ huniq'

-- Proof sketch: differentiability gives a Fréchet derivative, and the Chapter 23 value theorem
-- identifies the directional derivative with that linear functional in every direction.
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

omit [FiniteDimensional 𝕜 E] in
private theorem hasLinearDirectionalDerivativeAt_of_differentiableAt
    {f : E → 𝕜} {x : E} (hdiff : DifferentiableAt 𝕜 f x) :
    (f.toWithBotTop).HasLinearDirectionalDerivativeAt x := by
  refine ⟨(fderiv 𝕜 f x).toLinearMap.comp (⊤ : Submodule 𝕜 E).subtype, ?_⟩
  funext y
  change ((fderiv 𝕜 f x y.1 : 𝕜) : WithBotTop 𝕜) =
      Function.directionalDerivativeAt f.toWithBotTop x y.1
  simpa using
    (Function.directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt
      (f := f) (x := x) (y := y.1) hdiff.hasFDerivAt).symm

-- Proof sketch: for a finite convex function, the directional derivative owner is convex and has
-- nonempty subdifferential at `x`; a linear lift gives oddness of the directional derivative,
-- which turns the one-sided subgradient inequality from Theorem 23.2 into equality, forcing
-- uniqueness.
/-- Bridge form of Theorem 25.2: for a finite convex function on a finite-dimensional normed
space, Rockafellar's condition that `y ↦ f'(x; y)` is linear is equivalent to uniqueness of the
dual-valued subdifferential at `x`. -/
theorem hasLinearDirectionalDerivativeAt_iff_existsUnique_mem_subdifferentialAt
    {f : E → 𝕜} {x : E} (hf_convex : ConvexOn 𝕜 Set.univ f) :
    (f.toWithBotTop).HasLinearDirectionalDerivativeAt x ↔
      ∃! xStar : StrongDual 𝕜 E, xStar ∈ (∂ f.toWithBotTop at x) := by
  constructor
  · intro hlin
    have hf_convex_ext : (f.toWithBotTop).IsConvex 𝕜 :=
      Function.isConvex_coe_of_convexOn_univ hf_convex
    have hf_proper : (f.toWithBotTop).IsProper := by
      refine ⟨⟨x, ?_⟩, ?_⟩
      · exact WithBotTop.coe_lt_top (f x)
      · intro z
        exact WithBotTop.coe_ne_bot (f z)
    have hx_riDom : x ∈ riDom[𝕜](f.toWithBotTop) := by
      have hdom : dom(f.toWithBotTop) = (Set.univ : Set E) := by
        ext z
        constructor
        · intro _
          simp
        · intro _
          exact WithBotTop.coe_lt_top (f z)
      have hx_int : x ∈ interior (dom(f.toWithBotTop)) := by
        rw [hdom]
        simp
      exact interior_subset_intrinsicInterior (𝕜 := 𝕜) hx_int
    have hnonempty : (∂ f.toWithBotTop at x).Nonempty :=
      _root_.subdifferentialAt_nonempty_of_mem_riDom
        (f := f.toWithBotTop) (x := x) (Y := StrongDual 𝕜 E) hf_convex_ext hf_proper hx_riDom
    rcases hnonempty with ⟨xStar0, hxStar0⟩
    refine ⟨xStar0, hxStar0, ?_⟩
    have hx_dom : x ∈ dom(f.toWithBotTop) := WithBotTop.coe_lt_top (f x)
    have hx_bot : f.toWithBotTop x ≠ ⊥ := WithBotTop.coe_ne_bot (f x)
    let g : (⊤ : Submodule 𝕜 E) →ₗ[𝕜] 𝕜 := Classical.choose hlin
    have hg : (g : (⊤ : Submodule 𝕜 E) → 𝕜).toWithBotTop =
        ((Function.directionalDerivativeAt f.toWithBotTop x) ∘ (⊤ : Submodule 𝕜 E).subtype) :=
      Classical.choose_spec hlin
    have hdir_eq :
        ∀ zStar : StrongDual 𝕜 E,
          zStar ∈ (∂ f.toWithBotTop at x) →
          ∀ d : E,
            ((⟪d, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜) =
              Function.directionalDerivativeAt f.toWithBotTop x d := by
      intro zStar hzStar d
      have hdir_d :
          Function.directionalDerivativeAt f.toWithBotTop x d =
            ((g ⟨d, trivial⟩ : 𝕜) : WithBotTop 𝕜) := by
        have h := congrArg (fun hfun => hfun ⟨d, trivial⟩) hg
        simpa using h.symm
      have hz_le :
          ∀ d : E,
            ((⟪d, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤
              Function.directionalDerivativeAt f.toWithBotTop x d :=
        (_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt
          (f := f.toWithBotTop) hf_convex_ext (x := x) hx_dom hx_bot (xStar := zStar)).mp hzStar
      have hz_le_d : (⟪d, zStar⟫ₚ : 𝕜) ≤ g ⟨d, trivial⟩ := by
        have hz_le_d' :
            ((⟪d, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ ((g ⟨d, trivial⟩ : 𝕜) : WithBotTop 𝕜) := by
          have hz_le_d0 := hz_le d
          rw [hdir_d] at hz_le_d0
          exact hz_le_d0
        exact WithBotTop.coe_le_coe.mp hz_le_d'
      have hz_ge_d : g ⟨d, trivial⟩ ≤ (⟪d, zStar⟫ₚ : 𝕜) := by
        have hz_neg' :
            ((⟪-d, zStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ ((g ⟨-d, trivial⟩ : 𝕜) : WithBotTop 𝕜) := by
          have hdir_neg :
              Function.directionalDerivativeAt f.toWithBotTop x (-d) =
                ((g ⟨-d, trivial⟩ : 𝕜) : WithBotTop 𝕜) := by
            have h := congrArg (fun hfun => hfun ⟨-d, trivial⟩) hg
            simpa using h.symm
          have hz_le_neg0 := hz_le (-d)
          rw [hdir_neg] at hz_le_neg0
          exact hz_le_neg0
        have hz_neg : (⟪-d, zStar⟫ₚ : 𝕜) ≤ g ⟨-d, trivial⟩ := WithBotTop.coe_le_coe.mp hz_neg'
        have hz_neg_simp : -(zStar d : 𝕜) ≤ -(g ⟨d, trivial⟩) := by
          have hg_neg : g ⟨-d, trivial⟩ = -(g ⟨d, trivial⟩) := by
            change g (-⟨d, trivial⟩) = -(g ⟨d, trivial⟩)
            exact g.map_neg ⟨d, trivial⟩
          have hz_neg_eval : (zStar (-d) : 𝕜) ≤ g ⟨-d, trivial⟩ := by
            change (zStar (-d) : 𝕜) ≤ g ⟨-d, trivial⟩ at hz_neg
            exact hz_neg
          rw [hg_neg] at hz_neg_eval
          simpa using hz_neg_eval
        have hz_ge_d_eval : g ⟨d, trivial⟩ ≤ (zStar d : 𝕜) :=
          neg_le_neg_iff.mp hz_neg_simp
        change g ⟨d, trivial⟩ ≤ (⟪d, zStar⟫ₚ : 𝕜)
        exact hz_ge_d_eval
      have hpair_eq_g : (⟪d, zStar⟫ₚ : 𝕜) = g ⟨d, trivial⟩ := le_antisymm hz_le_d hz_ge_d
      exact (congrArg (fun t : 𝕜 => (t : WithBotTop 𝕜)) hpair_eq_g).trans hdir_d.symm
    intro y hy
    ext d
    have hy_eq :
        ((⟪d, y⟫ₚ : 𝕜) : WithBotTop 𝕜) =
          Function.directionalDerivativeAt f.toWithBotTop x d :=
      hdir_eq y hy d
    have hx0_eq :
        ((⟪d, xStar0⟫ₚ : 𝕜) : WithBotTop 𝕜) =
          Function.directionalDerivativeAt f.toWithBotTop x d :=
      hdir_eq xStar0 hxStar0 d
    have hxy :
        ((⟪d, y⟫ₚ : 𝕜) : WithBotTop 𝕜) =
          ((⟪d, xStar0⟫ₚ : 𝕜) : WithBotTop 𝕜) :=
      hy_eq.trans hx0_eq.symm
    have hxy_eval : ((y d : 𝕜) : WithBotTop 𝕜) = ((xStar0 d : 𝕜) : WithBotTop 𝕜) := by
      change ((⟪d, y⟫ₚ : 𝕜) : WithBotTop 𝕜) = ((⟪d, xStar0⟫ₚ : 𝕜) : WithBotTop 𝕜)
      exact hxy
    exact WithBotTop.coe_eq_coe_iff.mp hxy_eval
  · intro hsub
    have hdiff : DifferentiableAt 𝕜 f x :=
      (differentiableAt_iff_existsUnique_mem_subdifferentialAt (f := f) (x := x) hf_convex).2 hsub
    exact hasLinearDirectionalDerivativeAt_of_differentiableAt hdiff

-- Proof sketch: combine the core owner theorem with the preceding bridge between uniqueness of the
-- dual subdifferential and Rockafellar linearity of the directional derivative.
/-- Theorem 25.2, source-facing bridge form: for a finite convex function on a finite-dimensional
normed space, `f` is differentiable at `x` if and only if its directional derivative at `x`
is linear in Rockafellar's sense, expressed by the canonical extended-real owner
`(f.toWithBotTop).HasLinearDirectionalDerivativeAt x`. -/
theorem differentiableAt_iff_hasLinearDirectionalDerivativeAt
    {f : E → 𝕜} {x : E} (hf_convex : ConvexOn 𝕜 Set.univ f) :
    DifferentiableAt 𝕜 f x ↔ (f.toWithBotTop).HasLinearDirectionalDerivativeAt x := by
  constructor
  · intro hdiff
    exact hasLinearDirectionalDerivativeAt_of_differentiableAt hdiff
  · intro hlin
    exact
      (differentiableAt_iff_existsUnique_mem_subdifferentialAt (f := f) (x := x) hf_convex).2
        ((hasLinearDirectionalDerivativeAt_iff_existsUnique_mem_subdifferentialAt
          (f := f) (x := x) hf_convex).1 hlin)

end Function

end
