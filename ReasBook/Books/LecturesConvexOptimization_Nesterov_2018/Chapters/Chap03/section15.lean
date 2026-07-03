import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_15 (from Chap03) -/
/- Definition 3.15 is a bridge/view item in the chapter's convex-analysis normal-cone API.

Primary domain:
- convex analysis of extended-real-valued functions on Euclidean space.

Relevant owner-style declarations sampled before refinement:
- `extendedRealEffectiveDomain`
- the source-facing sublevel set `{x ∈ dom f | f x ≤ f x0}`
- `normalCone`
- `level_set_inequality_at_iff`

Best owner abstraction:
- `normalCone`

Primitive data:
- the finite-value domain `extendedRealEffectiveDomain f`
- the level set `{x ∈ dom f | f x ≤ f x0}`

Derived API:
- the bridge theorem `level_set_inequality_at_iff`

Source/core/bridge triage:
- source-facing: the textbook level-set inequality at `x0`
- core/canonical: `normalCone`
- bridge/view: `level_set_inequality_at_iff`

The normal-cone and sublevel-set vocabulary is already owned upstream, so this file recalls only
the numbered bridge statement rather than re-recalling that upstream surface. -/

recall level_set_inequality_at_iff

/-! ### Lemma_3_15 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 3.15 is the chapter's real-valued bridge over the upstream `WithTop`-valued
subdifferential owner.

Primary domain:
- real-valued subdifferentials of positively homogeneous functions.

Sampled owner-style declarations:
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owner for
  subgradients, already stated on `E → WithTop ℝ`;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `subdifferential_eq_subdifferential_zero_touching_of_convex_oneHomogeneous` in
  `Lemma_3_1_15`, an earlier Euclidean real-valued restatement of the same source fact with a
  redundant convexity hypothesis;
- `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing` in `Theorem_3_1_24`, an existing
  downstream use of the canonical owner on the real-to-`WithTop` coercion.

Best owner abstraction:
- primitive predicate `IsSubgradientAt` from `Definition_3_1_5`, specialized to
  `fun y ↦ (f y : WithTop ℝ)`;
- derived set-valued owner `subdifferential` from `Definition_3_1_5`;
- `IsPositivelyHomogeneousOn 1 Set.univ f` for the positive-homogeneity input to Lemma 3.15.

Primitive data:
- the affine lower-support predicate `IsSubgradientAt (fun y ↦ (f y : WithTop ℝ))`;
- the positive-homogeneity owner hypothesis.

Internal bridge:
- the coercion lemma identifying the owner predicate with the usual real-valued inequality.

Source/core/bridge triage:
- source-facing: Lemma 3.15's description of `∂f(x)` for one-homogeneous real-valued `f`;
- core/canonical: `IsSubgradientAt`, `subdifferential`, `IsPositivelyHomogeneousOn`;
- bridge/view: `mem_subdifferential_coe_real_iff`, the owner-level real-valued coercion bridge
  from `Definition_3_1_5`.

This file therefore stops duplicating the real-valued subgradient owner. Its public API keeps only
the source-facing Lemma 3.15 statement and reuses the owner-level real-valued bridge from
`Definition_3_1_5` instead of carrying a private copy.
-/

/-- Lemma 3.15: for a positively `1`-homogeneous function on a real inner-product space,
the subdifferential at `x` is exactly the intersection of the origin subdifferential with the
touching condition `⟪g, x⟫ = f x`. -/
-- Proof sketch: if `g ∈ ∂f(x)`, apply the subgradient inequality at `0` and at `2 • x`; positive
-- homogeneity gives the two opposite inequalities needed for `⟪g, x⟫ = f x`, and then the same
-- supporting inequality shows `g ∈ ∂f(0)`. Conversely, if `g ∈ ∂f(0)` and `⟪g, x⟫ = f x`,
-- rewrite the support inequality at `0` to obtain the support inequality at `x`. No convexity
-- hypothesis is needed once the owner subgradient inequality is used directly.
theorem subdifferential_eq_subdifferential_zero_of_posHomogeneous
    {f : E → ℝ} (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f) (x : E) :
    ∂ (fun y ↦ (f y : WithTop ℝ))(x) =
      ∂ (fun y ↦ (f y : WithTop ℝ))(0) ∩ {g | inner ℝ g x = f x} := by
  have h0 : f 0 = 0 := by
    simpa using hf_hom.map_smul (show x ∈ Set.univ by simp) (0 : NNReal)
  ext g
  constructor
  · intro hg
    have hsub : ∀ y : E, f y ≥ f x + inner ℝ g (y - x) :=
      mem_subdifferential_coe_real_iff.mp hg
    have hfx_le : f x ≤ inner ℝ g x := by
      have hzero : 0 ≥ f x - inner ℝ g x := by
        simpa [h0, sub_eq_add_neg] using hsub 0
      linarith
    have htwo : f (x + x) = 2 * f x := by
      simpa [NNReal.smul_def, two_smul, smul_eq_mul] using
        hf_hom.map_smul (show x ∈ Set.univ by simp) (2 : NNReal)
    have hinner_le : inner ℝ g x ≤ f x := by
      have htwo_sub : f (x + x) ≥ f x + inner ℝ g x := by
        simpa [two_smul] using hsub ((2 : ℝ) • x)
      linarith
    have htouch : inner ℝ g x = f x := le_antisymm hinner_le hfx_le
    refine ⟨?_, htouch⟩
    exact mem_subdifferential_coe_real_iff.mpr <| fun y ↦ by
      calc
        f y ≥ f x + inner ℝ g (y - x) := hsub y
        _ = inner ℝ g y := by
          rw [sub_eq_add_neg, inner_add_right, inner_neg_right]
          linarith
        _ = f 0 + inner ℝ g (y - 0) := by
          simp [h0]
  · rintro ⟨hg0, htouch⟩
    have hsub0 : ∀ y : E, f y ≥ f 0 + inner ℝ g (y - 0) :=
      mem_subdifferential_coe_real_iff.mp hg0
    exact mem_subdifferential_coe_real_iff.mpr <| fun y ↦ by
      calc
        f y ≥ f 0 + inner ℝ g (y - 0) := hsub0 y
        _ = inner ℝ g y := by simp [h0]
        _ = f x + inner ℝ g (y - x) := by
          rw [← htouch, sub_eq_add_neg, inner_add_right, inner_neg_right]
          linarith

end

/-! ### Proposition_3_15 (from Chap03) -/
noncomputable section

open Set
open EuclideanSpace
open scoped WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.15 lies in the chapter's Euclidean coordinatewise-maximum / subdifferential
domain.

Relevant owner-style declarations sampled before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`;
- `pointwiseSupremumOn` in `PointwiseSupremumOn` and
  `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`, the chapter owners for pointwise suprema
  and their active-index sets;
- `subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials` in
  `Lemma_3_13`, the finite active-family subdifferential formula.

Best owner abstraction:
- source-facing: Proposition 3.15 as the Euclidean coordinate-family specialization of the finite
  `Set.univ` supremum;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `subdifferential`.

Primitive data:
- the positive-dimension witness `hn : 0 < n`, which supplies the nonempty finite index type
  `Fin n`;
- the coordinate projection family `fun y i ↦ (y i : WithTop ℝ)`.

Derived API:
- the active-coordinate set
  `activePointwiseSupremumOnIndices (Set.univ : Set (Fin n))
    (fun y i ↦ (y i : WithTop ℝ)) x`;
- the convex-hull description of the subdifferential by active basis vectors.

Source/core/bridge triage:
- source-facing: the Euclidean coordinatewise-maximum specialization of Proposition 3.15;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `subdifferential`;
- bridge/view: the coordinate projection family and the active-basis embedding
  `i ↦ EuclideanSpace.single i 1`.

The earlier refinement duplicated the chapter finite-maximum owner with separate public
`coordinatewiseMaximum` and `activeCoordinateIndices` wrappers. This file now states the two
propositions directly on the chapter owners `pointwiseSupremumOn` and
`activePointwiseSupremumOnIndices`, using the source-facing hypothesis `hn : 0 < n` only to
supply the local `Nonempty (Fin n)` instance required by the finite `Set.univ` specialization.
-/

local notation "coordinateFamily" =>
  (fun y : E ↦ fun i ↦ (y i : WithTop ℝ))

section

variable (hn : 0 < n)

local instance : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

/-- Helper for Proposition 3.15: the coordinatewise maximum has full effective domain, so every
point lies in the interior of its domain. -/
lemma coordinatewiseMaximum_interior_dom_eq_univ
    (hn : 0 < n) :
    interior (dom (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)) = Set.univ := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- The finite `Set.univ` supremum is finite exactly when each coordinate slice is finite.
  simpa [withTopEffectiveDomain] using
    (interior_dom_pointwiseSupremumOn_univ (ι := Fin n) (φ := coordinateFamily))

/-- Helper for Proposition 3.15: each coordinate slice has singleton subdifferential equal to the
corresponding standard basis vector. -/
lemma coordinate_slice_subdifferential_eq_singleton_basis
    (i : Fin n) (x : E) :
    ∂ (fun y : E ↦ (y i : WithTop ℝ))(x) = {single i (1 : ℝ)} := by
  have hconv :
      ConvexOn ℝ (dom (fun y : E ↦ (y i : WithTop ℝ)))
        (withTopRealPart (fun y : E ↦ (y i : WithTop ℝ))) := by
    -- The `i`-th coordinate map is linear, hence convex on all of `E`.
    simpa [withTopEffectiveDomain, withTopRealPart] using
      (EuclideanSpace.projₗ i).convexOn convex_univ
  have hgrad :
      HasGradientAt (withTopRealPart (fun y : E ↦ (y i : WithTop ℝ)))
        (single i (1 : ℝ)) x := by
    -- Identify the Fréchet derivative of the coordinate projection with pairing against `e_i`.
    rw [hasGradientAt_iff_hasFDerivAt]
    have hderiv :
        HasFDerivAt (fun y : E ↦ y i) (EuclideanSpace.proj i : E →L[ℝ] ℝ) x := by
      simpa using (EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt
    have hdual :
        (EuclideanSpace.proj i : E →L[ℝ] ℝ) =
          InnerProductSpace.toDual ℝ E (single i (1 : ℝ)) := by
      ext y
      simpa using (EuclideanSpace.inner_single_left i (1 : ℝ) y).symm
    simpa [withTopRealPart] using hderiv.congr_fderiv hdual
  have hx : x ∈ interior (dom (fun y : E ↦ (y i : WithTop ℝ))) := by
    -- A real-valued coordinate slice is finite everywhere.
    simp [withTopEffectiveDomain]
  exact subdifferential_eq_singleton_of_hasGradientAt hconv hx hgrad

/-- Helper for Proposition 3.15: each coordinate slice is a closed convex function. -/
lemma coordinate_slice_closedConvexFunction
    (i : Fin n) :
    ClosedConvexFunction (fun y : E ↦ (y i : WithTop ℝ)) := by
  -- Package linearity and continuity of the coordinate projection into the chapter owner API.
  apply closedConvexFunction_coe_of_convexOn_continuous
  · simpa using (EuclideanSpace.projₗ i).convexOn convex_univ
  · simpa using (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous

/-- Helper for Proposition 3.15: at the origin every coordinate attains the common maximum `0`,
so every index is active. -/
lemma active_coordinateFamily_zero_eq_univ
    (hn : 0 < n) :
    activePointwiseSupremumOnIndices
        (Set.univ : Set (Fin n)) coordinateFamily (0 : E) =
      Set.univ := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ext i
  -- At `0`, each coordinate slice and the finite supremum both evaluate to `0`.
  rw [mem_activePointwiseSupremumOnIndices_univ_iff, pointwiseSupremumOn_univ_eq_sup']
  simp

/-- Helper for Proposition 3.15: rewriting the active slice-subgradient union replaces each slice
subdifferential by the corresponding basis vector. -/
lemma active_slice_subgradient_set_eq_activeBasisImage
    (x : E) :
    {g | ∃ i : Fin n,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x ∧
          g ∈ ∂ (fun y : E ↦ (y i : WithTop ℝ))(x)} =
      ((fun i : Fin n ↦ single i (1 : ℝ)) ''
        activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x) := by
  ext g
  constructor
  · rintro ⟨i, hi, hg⟩
    -- Each active slice contributes only the singleton `{e_i}`.
    rw [coordinate_slice_subdifferential_eq_singleton_basis] at hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    -- Conversely, every active basis vector comes from the matching active slice.
    refine ⟨i, hi, ?_⟩
    rw [coordinate_slice_subdifferential_eq_singleton_basis]
    simp

/-- Proposition 3.15: the convex subdifferential of the coordinatewise maximum
`x ↦ max_{1 ≤ i ≤ n} x^{(i)}` is the convex hull of the standard basis vectors indexed by the
active coordinates of `x`. -/
-- Proof sketch: one inclusion writes a convex combination of active basis vectors and checks the
-- subgradient inequality coordinatewise, using that active coordinates realize the maximum at
-- `x`. For the reverse inclusion, test a subgradient against perturbations in coordinate
-- directions to show its coordinates are nonnegative, vanish off the active set, and sum to `1`;
-- this identifies the subgradient as a convex combination of the active basis vectors.
theorem subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis
    (hn : 0 < n)
    (x : E) :
    ∂ (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)(x) =
      convexHull ℝ
        ((fun i : Fin n ↦ single i (1 : ℝ)) ''
          activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Route correction: the positivity witness must be explicit in the theorem binder, because the
  -- source theorem specializes a nonempty finite supremum.
  have hx :
      x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)) := by
    -- The coordinatewise maximum is finite everywhere on `E`.
    rw [coordinatewiseMaximum_interior_dom_eq_univ (hn := hn)]
    simp
  have hmain :=
    subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
      (ι := Fin n) (φ := coordinateFamily)
      (fun i ↦ coordinate_slice_closedConvexFunction i) hx
  -- Rewrite the abstract active slice-subgradient hull to the active basis-vector hull.
  rw [hmain, active_slice_subgradient_set_eq_activeBasisImage]

/-- At the origin, every coordinate is active, so the subdifferential of the coordinatewise
maximum is the convex hull of all standard basis vectors, i.e. the standard simplex in `ℝⁿ`. -/
-- Proof sketch: specialize
-- `subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis` to `x = 0` and observe that
-- all coordinates of `0` equal the common maximum value `0`, so the active-index set is all of
-- `Fin n`.
theorem subdifferential_coordinatewiseMaximum_zero_eq_convexHull_basis
    (hn : 0 < n)
    :
    ∂ (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)((0 : E)) =
      convexHull ℝ (Set.range fun i : Fin n ↦ single i (1 : ℝ)) := by
  -- Specialize the general active-basis formula at the origin.
  rw [subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis (hn := hn) (x := (0 : E))]
  -- At `0`, the active set is all of `Fin n`, so the image is the full basis range.
  rw [active_coordinateFamily_zero_eq_univ (hn := hn)]
  simp [Set.image_univ]

end

end

/-! ### Theorem_3_15 (from Chap03) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 3.15 lies in the chapter's strong-separation domain for disjoint closed convex sets in
`ℝⁿ`.

Relevant sampled declarations:
- the chapter owner predicate `AreStronglySeparable` and its coordinate bridge
  `areStronglySeparable_iff` in `Definition_3_12`;
- the project theorem `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side` in
  `Theorem_3_1_13`, the canonical one-sided-bounded strong-separation owner theorem;
- mathlib `geometric_hahn_banach_compact_closed`, the compact/closed strong-separation theorem;
- mathlib `geometric_hahn_banach_closed_compact`, the symmetric closed/compact variant;
- mathlib `Metric.isCompact_of_isClosed_isBounded`, the bounded-to-compact bridge in Euclidean
  spaces, already internalized by `Theorem_3_1_13`.

Best owner abstraction:
- `AreStronglySeparable`.

Primitive data:
- the sets `Q₁`, `Q₂`;
- nonemptiness, closedness, convexity, disjointness, and one-sided boundedness.

Derived API:
- the owner-level separation `AreStronglySeparable Q₂ Q₁`;
- the coordinate witness `g ≠ 0`, `γ` recovered from `areStronglySeparable_iff`.

Source/core/bridge triage:
- source-facing: this textbook coordinate theorem surface in `ℝⁿ`;
- core/canonical: `AreStronglySeparable`;
- bridge/view: this file, which re-expresses the owner theorem on the swapped pair `(Q₂, Q₁)` via
  `areStronglySeparable_iff`.
-/

/-- Theorem 3.15: if `Q₁, Q₂ ⊆ ℝⁿ` are nonempty closed convex sets with empty intersection, and at
least one of them is bounded, then there exist a nonzero vector `g` and a scalar `γ` such that
`⟪g, x⟫ < γ` for every `x ∈ Q₂` and `γ < ⟪g, y⟫` for every `y ∈ Q₁`. -/
-- Proof sketch: reduce the bounded side to a compact convex set, apply the appropriate geometric
-- Hahn--Banach strict-separation theorem, and recenter the two strict bounds at an intermediate
-- value `γ`.
theorem areStronglySeparable_of_disjoint_closed_convex_of_one_bounded
    (Q₁ Q₂ : Set E) (hQ₁_nonempty : Q₁.Nonempty) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdisj : Disjoint Q₁ Q₂)
    (hbounded : Bornology.IsBounded Q₁ ∨ Bornology.IsBounded Q₂) :
    ∃ (g : E) (_ : g ≠ 0) (γ : ℝ),
      (∀ x ∈ Q₂, inner ℝ g x < γ) ∧
      ∀ y ∈ Q₁, γ < inner ℝ g y := by
  have hE_nontrivial : Nontrivial E := by
    rcases subsingleton_or_nontrivial E with hE_sub | hE_nontrivial
    · rcases hQ₁_nonempty with ⟨x, hx⟩
      rcases hQ₂_nonempty with ⟨y, hy⟩
      have hxy : x = y := hE_sub.elim _ _
      exact False.elim ((Set.disjoint_left.mp hdisj hx) (hxy ▸ hy))
    · exact hE_nontrivial
  letI : Nontrivial E := hE_nontrivial
  have hstrong : AreStronglySeparable Q₂ Q₁ := by
    refine areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side
      Q₂ Q₁ hQ₂_closed hQ₁_closed hQ₂_convex hQ₁_convex hdisj.symm ?_
    rcases hbounded with hQ₁_bounded | hQ₂_bounded
    · right
      exact ⟨hQ₁_nonempty, hQ₁_bounded⟩
    · left
      exact ⟨hQ₂_nonempty, hQ₂_bounded⟩
  rcases areStronglySeparable_iff.mp hstrong with ⟨g, hg, γ, hsep⟩
  exact ⟨g, hg, γ, fun x hx ↦ by simpa using hsep.1 x hx, fun y hy ↦ by simpa using hsep.2 y hy⟩

end
