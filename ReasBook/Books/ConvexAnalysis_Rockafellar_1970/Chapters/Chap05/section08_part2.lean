import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_8_3 (from Chap01) -/
noncomputable section

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*} {α : Type*}
variable [AddCommMonoid 𝕜] [One 𝕜] [Preorder 𝕜] [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

namespace StdSimplex

/-- For fixed simplex weights `w`, the corresponding family of weighted right scalar multiples. -/
def rightScalarFamily (w : StdSimplex 𝕜 ι) (f : ι → E → WithBotTop α) :
    ι → E → WithBotTop α :=
  fun i ↦ (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i

end StdSimplex

/-!
Source/core/bridge triage for this item.

-- `source-facing`: Theorem 5.8.3 fixes a finite family of convex functions on a `𝕜`-smul ambient
  and defines `h(x)` as the infimum, over all simplex weights `λ`, of the finite maximum
  of the scaled functions `(fᵢ λᵢ)(x)`. The textbook states the stronger hypotheses that the
  family is nonempty and that the `fᵢ` are proper convex; for this convexity conclusion, both the
  nonemptiness guard and the properness part are redundant.
- `core/canonical`: the chapter-level owner abstractions already exist upstream as
  `StdSimplex 𝕜 ι` from `Definition_2_2_10`, `Function.IsConvex`,
  `Function.IsConvex.iSup`, and `rightScalarMul`.
- `bridge/view`: for fixed simplex data `w : StdSimplex 𝕜 ι`, the textbook finite maximum is
  exactly the owner-side pointwise supremum
  `⨆ i, w.rightScalarFamily f i`; the outer infimum is then
  the direct function-lattice infimum over `w`, while the equivalent `sInf` formula is companion
  bridge API.
- Primitive data vs derived API: `w : StdSimplex 𝕜 ι` is the primitive owner for the simplex
  coefficients; the nonnegative scalar fed to `rightScalarMul` at coordinate `i` is the primitive
  subtype coefficient `⟨w.weights i, w.nonneg i⟩`, packaged by `w.rightScalarFamily`; for fixed
  `w` the finite maximum is the canonical pointwise supremum `⨆ i, w.rightScalarFamily f i`.
  The simplex-indexed function-lattice infimum
  is the source-facing object; its `sInf` value formula and convexity are derived API.
- Layer target: `source-facing`; the theorem keeps the textbook simplex-weighted maximum as its
  public object while reusing the chapter's canonical simplex owner and function-lattice infimum
  instead of a parallel support-set wrapper.

Domain-style sampling used here:
- `StdSimplex` from `Definition_2_2_10`;
- `StdSimplex.weights` and `StdSimplex.nonneg` from `Definition_2_2_10`;
- `StdSimplex.rightScalarFamily` from this item;
- `Function.IsConvex` from `Theorem_4_2` via `Theorem_5_3`;
- `Function.IsConvex.iSup` from `Theorem_5_5`;
- `rightScalarMul` from `Text_5_4_2`;
- `StdSimplex.total` from mathlib's `ConvexSpace`.

Ambient minimization: the source-facing owner `simplex_right_scalar_infimal_maximum` and its
`sInf` specification only use the chapter owner `rightScalarMul`, so they live at the primitive
`𝕜`-smul layer on the ambient space and codomain; they do not require the codomain to equal the
scalar type. The stronger additive commutative `𝕜`-module structure and codomain specialization
to `WithBotTop 𝕜` appear only in the derived convexity theorem through
`Function.IsConvex.rightScalarMul` and `Function.IsConvex.iSup`.
-/

variable (𝕜)

/-- The simplex-weighted infimal maximum attached to a finite family sends `x` to
the infimum, over all nonnegative weights summing to `1`, of the maximum of the values
`(fᵢ λᵢ)(x)`. -/
def simplex_right_scalar_infimal_maximum [Fintype ι] (f : ι → E → WithBotTop α) :
    E → WithBotTop α :=
  ⨅ w : StdSimplex 𝕜 ι, ⨆ i, w.rightScalarFamily f i

-- Proof sketch: the definition is already the direct function-lattice infimum over simplex
-- weights. Evaluating at `x` turns that outer `iInf` into the infimum of the range of the values
-- `⨆ i, (w.rightScalarFamily f i) x`, and `sInf_range` rewrites that infimum as the source-facing
-- `sInf` over exact finite maxima indexed by `w : StdSimplex 𝕜 ι`.
/-- The value of `simplex_right_scalar_infimal_maximum f` at `x` is the infimum over simplex
weights of the finite maximum of the corresponding weighted right scalar multiples. -/
theorem simplex_right_scalar_infimal_maximum_eq_sInf
    [Fintype ι]
    (f : ι → E → WithBotTop α) (x : E) :
    simplex_right_scalar_infimal_maximum 𝕜 f x =
      sInf {r : WithBotTop α |
          ∃ w : StdSimplex 𝕜 ι,
            r = ⨆ i, (w.rightScalarFamily f i) x} := by
  rw [simplex_right_scalar_infimal_maximum, iInf_apply, ← sInf_range]
  congr
  ext r
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa [iSup_apply] using hw.symm
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa [iSup_apply] using hw.symm

end

section

variable {E : Type*} {ι : Type*} {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [Fintype ι]

-- Proof sketch: for each simplex weight `w`, the function
-- `x ↦ ⨆ i, (w.rightScalarFamily f i) x` is convex by combining
-- `Function.IsConvex.rightScalarMul` with the owner theorem `Function.IsConvex.iSup`.
-- The outer simplex infimum is the source-facing object; the convexity proof uses the same
-- simplex-parameter epigraph/vertical-infimum bridge pattern as the neighboring weighted
-- infimum constructions.
/-- Theorem 5.8.3: if `fᵢ` is a finite family of convex functions on a `𝕜`-module, then
the function
`x ↦ inf {max_i (fᵢ λᵢ)(x) | λᵢ ≥ 0, ∑ i λᵢ = 1}` is convex. -/
theorem Function.isConvex_simplex_right_scalar_infimal_maximum
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_maximum 𝕜 f).IsConvex 𝕜 := sorry

/-- Textbook properness-form restatement of Theorem 5.8.3. This companion adds no new
mathematics: properness is not used in the convexity proof and is kept only as a source-facing
bridge from the stronger textbook wording to the owner-minimal convexity theorem above. -/
theorem Function.isConvex_simplex_right_scalar_infimal_maximum_of_proper
    (f : ι → E → WithBotTop 𝕜)
    (_hf_proper : ∀ i, (f i).IsProper)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (simplex_right_scalar_infimal_maximum 𝕜 f).IsConvex 𝕜 := by
  simpa using Function.isConvex_simplex_right_scalar_infimal_maximum f hf_convex

end

/-! ### Theorem_5_8_4 (from Chap01) -/
open scoped BigOperators

noncomputable section

section

variable {E : Type*} {ι : Type*} {α : Type*}
variable [ConditionallyCompleteLattice α]

section Weighted

variable (𝕜 : Type*)
variable [Preorder 𝕜] [AddCommMonoid 𝕜] [One 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E] [SMul 𝕜 α] [Fintype ι]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.8.4 forms, from a finite nonempty family of convex functions, the
  function sending `x` to the infimum over simplex weights and decompositions `x = ∑ i xᵢ` of the
  finite maximum of the weighted right scalar multiples `((λ i : Set.Ici (0 : 𝕜)) •ʳ f i) (xᵢ)`.
  As in
  Theorem 5.8.3, the textbook's extra properness hypothesis is redundant for this convexity
  conclusion.
- `core/canonical`: the owner abstractions already live upstream as
  `StdSimplex 𝕜 ι`, `StdSimplex.rightScalarFamily`, `Function.IsConvex`, `rightScalarMul`,
  and `infimal_max_convolution`.
- `bridge/view`: for fixed simplex weights `w : StdSimplex 𝕜 ι`, the textbook weighted
  decomposition formula is exactly
  `infimal_max_convolution (w.rightScalarFamily f)`, where
  `w.rightScalarFamily f i = (⟨w.weights i, w.nonneg i⟩ : Set.Ici (0 : 𝕜)) •ʳ f i`.
  The new source-facing owner in this file
  is only the outer simplex infimum of that imported chapter construction.
- Primitive data vs derived API: the family `f` and simplex owner `w : StdSimplex 𝕜 ι` are
  primitive; `weighted_infimal_max_convolution` is the direct function-lattice simplex infimum of
  the upstream owner `infimal_max_convolution`. The expanded decomposition formula and convexity
  theorem are derived API.
- Layer target: `source-facing`; the public object remains the textbook weighted infimal
  max-convolution, now defined directly from the earlier chapter owner
  `infimal_max_convolution` instead of through a parallel local support-set wrapper.

Domain-style sampling used here:
- `StdSimplex` from `Definition_2_2_10`;
- `StdSimplex.rightScalarFamily` from `Theorem_5_8_3`;
- `Function.IsConvex` from `Theorem_4_2` via `Theorem_5_8_1`;
- `rightScalarMul` from `Text_5_4_2`;
- `infimal_max_convolution` from `Theorem_5_8_1`;
- `Function.isConvex_infimal_max_convolution` from `Theorem_5_8_1`.

The source is stated on `R^n`, but the source-facing owner abstractions used here only require an
additive commutative monoid with an `𝕜`-scalar action on the ambient space, an `𝕜`-action on the
value layer `WithBotTop α`, and a finite index type. The source's nonempty-family guard is
redundant at this owner level: when `ι` is empty, the simplex type is empty and the outer infimum
is the constant `⊤`. The stronger ordered-ring `𝕜`-module assumptions are needed only for the
derived convexity theorem. The public API is therefore minimized to that intrinsic level rather
than pinned to `EuclideanSpace ℝ (Fin n)` and `Fin m`.
-/

/-- The weighted infimal max-convolution of a finite family of extended-order-valued functions on
an additive commutative monoid with `𝕜`-scalar action sends `x` to the infimum, over all simplex
weights, of the imported chapter owner `infimal_max_convolution` applied to the corresponding
family of weighted right scalar multiples. -/
def weighted_infimal_max_convolution (f : ι → E → WithBotTop α) : E → WithBotTop α :=
  ⨅ w : StdSimplex 𝕜 ι, infimal_max_convolution (w.rightScalarFamily f)

-- Proof sketch: unfold the direct `iInf` owner `weighted_infimal_max_convolution`, then expand
-- the imported owner `infimal_max_convolution` for the weighted family attached to
-- `w : StdSimplex 𝕜 ι`. This gives exactly the textbook infimum over simplex weights and
-- decompositions of `x`.
/-- The value of `weighted_infimal_max_convolution f` at `x` is the infimum over simplex weights
and decompositions of `x` of the finite supremum of the corresponding weighted right scalar
multiples. -/
theorem weighted_infimal_max_convolution_eq_sInf_decompositions
    (f : ι → E → WithBotTop α) (x : E) :
    weighted_infimal_max_convolution 𝕜 f x =
      sInf
        {z : WithBotTop α |
          ∃ (w : StdSimplex 𝕜 ι) (x' : ι → E),
            (∑ i, x' i) = x ∧
              z = ⨆ i, (w.rightScalarFamily f i) (x' i)} := by
  let g :
      (Sigma fun _ : StdSimplex 𝕜 ι ↦ {x' : ι → E // ∑ i, x' i = x}) →
        WithBotTop α :=
    fun wx ↦
      match wx with
      | ⟨w, ⟨x', _⟩⟩ => ⨆ i, (w.rightScalarFamily f i) (x' i)
  have h1 :
      weighted_infimal_max_convolution 𝕜 f x =
        ⨅ w : StdSimplex 𝕜 ι,
          ⨅ x' : {x' : ι → E // ∑ i, x' i = x},
            ⨆ i, (w.rightScalarFamily f i) (x'.1 i) := by
    rw [weighted_infimal_max_convolution, iInf_apply]
    refine iInf_congr fun w ↦ ?_
    rw [infimal_max_convolution_eq_sInf_decompositions]
    have hset :
        {z : WithBotTop α |
            ∃ x' : ι → E, (∑ i, x' i) = x ∧
              z = ⨆ i, (w.rightScalarFamily f i) (x' i)} =
          Set.range
            (fun x' : {x' : ι → E // ∑ i, x' i = x} ↦
              ⨆ i, (w.rightScalarFamily f i) (x'.1 i)) := by
      ext z
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact ⟨⟨x', hx'⟩, rfl⟩
      · rintro ⟨x', rfl⟩
        exact ⟨x'.1, x'.2, rfl⟩
    calc
      sInf {z : WithBotTop α |
          ∃ x' : ι → E, (∑ i, x' i) = x ∧
            z = ⨆ i, (w.rightScalarFamily f i) (x' i)}
          = sInf
              (Set.range
                (fun x' : {x' : ι → E // ∑ i, x' i = x} ↦
                  ⨆ i, (w.rightScalarFamily f i) (x'.1 i))) :=
            congrArg sInf hset
      _ = ⨅ x' : {x' : ι → E // ∑ i, x' i = x},
            ⨆ i, (w.rightScalarFamily f i) (x'.1 i) := by
            rw [sInf_range]
  have h2 :
      (⨅ w : StdSimplex 𝕜 ι,
          ⨅ x' : {x' : ι → E // ∑ i, x' i = x},
            ⨆ i, (w.rightScalarFamily f i) (x'.1 i)) =
        ⨅ wx : Sigma fun _ : StdSimplex 𝕜 ι ↦ {x' : ι → E // ∑ i, x' i = x}, g wx := by
    simpa [g] using
      (show
        (⨅ wx : Sigma (fun _ : StdSimplex 𝕜 ι ↦ {x' : ι → E // ∑ i, x' i = x}), g wx) =
          ⨅ w : StdSimplex 𝕜 ι,
            ⨅ x' : {x' : ι → E // ∑ i, x' i = x}, g ⟨w, x'⟩ from
        iInf_sigma).symm
  have h3 :
      (⨅ wx : Sigma fun _ : StdSimplex 𝕜 ι ↦ {x' : ι → E // ∑ i, x' i = x}, g wx) =
        sInf
          {z : WithBotTop α |
            ∃ (w : StdSimplex 𝕜 ι) (x' : ι → E),
              (∑ i, x' i) = x ∧
                z = ⨆ i, (w.rightScalarFamily f i) (x' i)} := by
    have hset :
        {z : WithBotTop α |
            ∃ (w : StdSimplex 𝕜 ι) (x' : ι → E),
              (∑ i, x' i) = x ∧
                z = ⨆ i, (w.rightScalarFamily f i) (x' i)} =
          Set.range g := by
      ext z
      constructor
      · rintro ⟨w, x', hx', rfl⟩
        exact ⟨⟨w, ⟨x', hx'⟩⟩, rfl⟩
      · rintro ⟨⟨w, ⟨x', hx'⟩⟩, rfl⟩
        exact ⟨w, x', hx', rfl⟩
    calc
      (⨅ wx : Sigma fun _ : StdSimplex 𝕜 ι ↦ {x' : ι → E // ∑ i, x' i = x}, g wx)
          = sInf (Set.range g) := by
            rw [sInf_range]
      _ = sInf
            {z : WithBotTop α |
              ∃ (w : StdSimplex 𝕜 ι) (x' : ι → E),
                (∑ i, x' i) = x ∧
                  z = ⨆ i, (w.rightScalarFamily f i) (x' i)} := by
            rw [hset.symm]
  exact h1.trans (h2.trans h3)

end Weighted

section

variable {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] [Fintype ι]

-- Proof sketch: for each simplex weight `w : StdSimplex 𝕜 ι`, the family
-- `w.rightScalarFamily f` is convex by `Function.IsConvex.rightScalarMul`, so the imported owner
-- theorem `Function.isConvex_infimal_max_convolution` gives convexity of the corresponding
-- infimal max-convolution. To handle the outer simplex infimum, adjoin the simplex parameter `w`
-- to the support-set/vertical-infimum construction from Theorem 5.8.1; this is the same
-- owner-level epigraph argument already used in the neighboring simplex-weighted items.
--
-- As in Theorem 5.8.3, the source states this with "proper convex" hypotheses, but the
-- properness part is redundant for the convexity conclusion.
/-- Theorem 5.8.4: if `f₁, ..., f_m` are convex functions, then the function
`k(x) = inf { max { lambda_1 f_1(x_1), ..., lambda_m f_m(x_m) } }` is convex, where the infimum
is taken over all decompositions `x_1 + ... + x_m = x` and all nonnegative weights summing to `1`
(encoded here by `w : StdSimplex 𝕜 ι`). The textbook states this on `R^n`; the chapter owner
abstractions show the convexity conclusion depends only on the ambient `𝕜`-module structure. -/
theorem Function.isConvex_weighted_infimal_max_convolution
    (f : ι → E → WithBotTop 𝕜) (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (weighted_infimal_max_convolution 𝕜 f).IsConvex 𝕜 := sorry

end

end

/-! ### Text_5_8_5 (from Chap01) -/
open scoped BigOperators
open scoped Pointwise

section

variable {E : Type*} [AddCommMonoid E]
variable {α : Type*} [ConditionallyCompleteLinearOrder α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.8.5 identifies the strict `μ`-sublevel set of the binary infimal
  max-convolution with the Minkowski sum of the strict `μ`-sublevel sets of the two input
  functions.
- `core/canonical`: the chapter owner abstraction is `infimal_max_convolution` from
  `Theorem_5_8_1`, specialized here to the canonical `Fin 2` family `![f₁, f₂]`.
- `bridge/view`: the `Fin 2` decomposition data `xs : Fin 2 → E` is the source-facing binary
  presentation of the owner object. The subtraction-based formula
  `x ↦ ⨅ y, max (f₁ (x - y)) (f₂ y)` from `Theorem_5_8_1` is a further bridge view available under
  stronger additive-group hypotheses, but it is not the right owner layer for this strict-sublevel
  identity.
- Primitive data vs derived API: the primitive data are the two functions `f₁`, `f₂`; the
  strict-sublevel-set identity is derived API of the owner construction, and the one-parameter
  infimum-of-`max` formula is a source-facing view.

Domain-style sampling used here:
- the chapter owner `infimal_max_convolution`;
- its owner-side decomposition formula `infimal_max_convolution_eq_sInf_decompositions`;
- `sInf_lt_iff` on `WithBotTop α`, `Fin.sum_univ_two`, and the order operation `max`;
- pointwise set addition on subsets of `E`.

The source phrases this corollary for proper convex functions on `ℝ^n`, but the displayed
set-theoretic identity depends only on the binary infimal-max construction itself. As in
`Text_5_4_0`, `Text_5_4_1`, and `Theorem_5_8_1`, the Lean statements therefore live at the
intrinsic additive-monoid owner level, with Euclidean-space applications handled by
specialization.
-/

/-- Bridge lemma for Text 5.8.5: the strict sublevel inequality for the binary infimal
max-convolution is equivalent to the existence of a binary decomposition whose two values are both
strictly below `μ`. -/
-- Proof sketch: rewrite the binary owner with the upstream bridge
-- `infimal_max_convolution_eq_sInf_decompositions`, then specialize the `Fin 2` family maximum to
-- `max`. A witness decomposition `xs : Fin 2 → E` with `x = xs 0 + xs 1` yields the two strict
-- inequalities, and conversely any decomposition `x = u + v` with strict bounds at `u` and `v`
-- gives a witness family `![u, v]` for the owner-side infimum.
private theorem infimal_max_convolution_two_lt_iff_exists_add
    (f₁ f₂ : E → WithBotTop α) (μ : WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x < μ ↔
      ∃ u v, f₁ u < μ ∧ f₂ v < μ ∧ u + v = x := by
  have hmax : ∀ xs : Fin 2 → E,
      (⨆ i : Fin 2, (![f₁, f₂] i) (xs i)) = max (f₁ (xs 0)) (f₂ (xs 1)) := by
    intro xs
    rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
    simp
  constructor
  · intro hx
    rw [infimal_max_convolution_eq_sInf_decompositions] at hx
    rcases sInf_lt_iff.mp hx with ⟨r, ⟨xs, hxs, rfl⟩, hr⟩
    have hlt : max (f₁ (xs 0)) (f₂ (xs 1)) < μ := by
      rw [← hmax xs]
      exact hr
    exact ⟨xs 0, xs 1, (max_lt_iff.mp hlt).1, (max_lt_iff.mp hlt).2,
      by simpa [Fin.sum_univ_two] using hxs⟩
  · intro hx
    rcases hx with ⟨u, v, hu, hv, huv⟩
    rw [infimal_max_convolution_eq_sInf_decompositions]
    refine sInf_lt_iff.mpr ?_
    refine ⟨max (f₁ u) (f₂ v), ?_, max_lt_iff.mpr ⟨hu, hv⟩⟩
    refine ⟨![u, v], ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using huv
    · rw [← Finset.sup_univ_eq_iSup, Finset.univ_fin2]
      simp

/-- Pointwise owner-level form of Text 5.8.5: the strict sublevel inequality for the binary
infimal max-convolution is equivalent to membership in the Minkowski sum of strict sublevel sets
of the two input functions. -/
theorem infimal_max_convolution_two_lt_iff_mem_add_strict_sublevel_set
    (f₁ f₂ : E → WithBotTop α) (μ : WithBotTop α) (x : E) :
    infimal_max_convolution ![f₁, f₂] x < μ ↔
      x ∈ {u : E | f₁ u < μ} + {v : E | f₂ v < μ} := by
  constructor
  · intro hx
    rcases (infimal_max_convolution_two_lt_iff_exists_add (f₁ := f₁) (f₂ := f₂) (μ := μ)
      (x := x)).mp hx with ⟨u, v, hu, hv, huv⟩
    exact Set.mem_add.mpr ⟨u, hu, v, hv, huv⟩
  · intro hx
    rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
    exact (infimal_max_convolution_two_lt_iff_exists_add (f₁ := f₁) (f₂ := f₂) (μ := μ)
      (x := x)).mpr ⟨u, v, hu, hv, huv⟩

/-- Text 5.8.5: the strict `μ`-sublevel set of the binary infimal max-convolution is the
Minkowski sum of the strict `μ`-sublevel sets of the two input functions. -/
theorem infimal_max_convolution_two_strict_sublevel_set_eq_add
    (f₁ f₂ : E → WithBotTop α) (μ : WithBotTop α) :
    {x : E | infimal_max_convolution ![f₁, f₂] x < μ} =
      {u : E | f₁ u < μ} + {v : E | f₂ v < μ} := by
  ext x
  simpa using infimal_max_convolution_two_lt_iff_mem_add_strict_sublevel_set
    (f₁ := f₁) (f₂ := f₂) (μ := μ) (x := x)

end
