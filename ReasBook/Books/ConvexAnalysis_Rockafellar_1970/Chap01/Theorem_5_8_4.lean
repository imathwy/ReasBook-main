import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_8_3

-- Declarations for this item will be appended below by the statement pipeline.

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
