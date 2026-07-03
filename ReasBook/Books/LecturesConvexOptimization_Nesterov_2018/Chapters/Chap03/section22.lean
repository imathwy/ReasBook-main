import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_22 (from Chap03) -/
noncomputable section

open ProperCone

universe u

/- Definition 3.22 is the source-facing normal-cone owner built on the chapter's dual-cone
abstraction.

Primary domain:
- tangent and normal cones in real inner-product-space convex analysis.

Relevant sampled declarations:
- `Set.vsub_singleton`
- `ProperCone.innerDual`
- `ProperCone.mem_innerDual`

Owner abstraction:
- `ProperCone.innerDual (Q -ᵥ ({xBar} : Set E))`

Primitive data:
- the set `Q`
- the base point `xBar`

Derived API:
- `mem_normalCone_iff`
- `neg_mem_normalCone_iff`
- downstream bridge/view lemmas such as `level_set_inequality_at_iff`

Source/core/bridge triage:
- source-facing: the textbook normal cone at `xBar`
- core/canonical: `ProperCone.innerDual (Q -ᵥ ({xBar} : Set E))`
- bridge/view: the membership and sign-reversal companion lemmas

The defining object itself does not need closedness, convexity, or the side condition `xBar ∈ Q`;
those hypotheses belong only to later theorems that use this owner abstraction. -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Definition 3.22: the normal cone to `Q` at `xBar`, realized as the inner dual cone of the
displacement set `Q - xBar`. -/
abbrev normalCone (Q : Set V) (xBar : V) : ProperCone ℝ V :=
  innerDual (Q -ᵥ ({xBar} : Set V))

/- Source-facing Lean notation for the textbook normal-cone family `N_Q`. -/
namespace NormalCone

scoped notation:max "N[" Q "]" => normalCone Q

end NormalCone

open scoped NormalCone

/-- Membership in the normal cone is exactly the defining supporting-halfspace inequality against
every point of `Q`. -/
theorem mem_normalCone_iff {Q : Set V} {xBar g : V} :
    g ∈ N[Q] xBar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ g (x - xBar) := by
  simp [normalCone, real_inner_comm]

/-- Rewriting the normal-cone condition for `-g` gives the textbook inequality
`⟪g, xBar - x⟫ ≥ 0`. -/
theorem neg_mem_normalCone_iff {Q : Set V} {xBar g : V} :
    -g ∈ N[Q] xBar ↔ ∀ x ∈ Q, inner ℝ g (xBar - x) ≥ 0 := by
  rw [mem_normalCone_iff]
  constructor <;> intro hg x hx <;>
    simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_comm] using hg x hx

end

/-! ### Lemma_3_22 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u v

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/-- Helper for Lemma 3.22: a real-valued objective whose `WithTop` lift is closed and convex on a
nonempty feasible set, and whose constrained sublevel sets are all bounded, attains a feasible
minimum on that set. -/
-- Proof sketch: choose one feasible reference point and minimize the objective on its constrained
-- sublevel slice. That slice is nonempty, closed, and bounded, hence compact in the proper space.
-- Lower semicontinuity on the slice gives a minimizer there, and any feasible point outside the
-- slice has larger objective value than the slice threshold.
lemma exists_isMinOn_of_closedConvexOn_bounded_sublevels
    {Q : Set X} (hQ_nonempty : Q.Nonempty) {f : X → ℝ}
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ (f x : WithTop ℝ)) α)) :
    ∃ x ∈ Q, IsMinOn f Q x := by
  let β₀ : ℝ := f hQ_nonempty.some
  let S : Set X := constrainedSublevelSet Q (fun x ↦ (f x : WithTop ℝ)) β₀
  have hsome_memS : hQ_nonempty.some ∈ S := by
    -- The reference feasible point lies in its own constrained sublevel slice.
    refine mem_constrainedSublevelSet_iff.2 ?_
    exact ⟨hQ_nonempty.some_mem, le_rfl⟩
  have hS_subset : S ⊆ Q := by
    -- Membership in the constrained sublevel set already records feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    -- Closed convexity of the lifted objective gives closedness of every constrained sublevel set.
    simpa [S, β₀] using hf.isClosed_constrainedSublevelSet β₀
  have hS_convex : Convex ℝ S := by
    -- The same lifted owner also provides convexity of the slice.
    simpa [S, β₀] using hf.convex_constrainedSublevelSet β₀
  have hS_bounded : Bornology.IsBounded S := by
    -- The bounded-sublevel hypothesis applies directly at the reference value `β₀`.
    simpa [S, β₀] using hbounded β₀
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hS_nonempty : S.Nonempty := ⟨hQ_nonempty.some, hsome_memS⟩
  have hfS : ClosedConvexOn S (fun x ↦ (f x : WithTop ℝ)) :=
    hf.restrict hS_closed hS_convex hS_subset
  have hlscS : LowerSemicontinuousOn f S :=
    hfS.lowerSemicontinuousOn_real hS_closed
  obtain ⟨x, hxS, hxMinS⟩ := hlscS.exists_isMinOn hS_nonempty hS_compact
  have hxQ : x ∈ Q := hS_subset hxS
  have hxβ : f x ≤ β₀ := by
    exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxS).2
  have hxMinQ : IsMinOn f Q x := by
    -- Points inside `S` are handled by compact-slice minimality; points outside have value above
    -- the slice threshold `β₀`, which already dominates `f x`.
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxMinS hyS
    · have hy_not_le : ¬ f y ≤ β₀ := by
        intro hyβ
        exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
      exact le_trans hxβ (le_of_lt (lt_of_not_ge hy_not_le))
  exact ⟨x, hxQ, hxMinQ⟩

/-- Helper for Lemma 3.22: the pointwise maximum of the `u`- and `uStar`-slices inherits the
closed-convex owner structure on `P`. -/
-- Proof sketch: apply the chapter closure rule `ClosedConvexOn.max_inter` to the two primal
-- slices and simplify the resulting `sup` to the real-valued maximum.
lemma parametric_maximum_closed_convex_on
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {uStar u : U}
    (hΨ_primal_closedConvex :
      ∀ ⦃w : U⦄, w ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x w : WithTop ℝ)))
    (huStar_mem : uStar ∈ S) (hu : u ∈ S) :
    ClosedConvexOn P (fun x ↦ ((max (Ψ x u) (Ψ x uStar) : ℝ) : WithTop ℝ)) := by
  -- The pointwise maximum is the `WithTop` supremum of the two lifted slices on the common set `P`.
  change ClosedConvexOn P
    (((fun x ↦ (Ψ x u : WithTop ℝ)) ⊔ fun x ↦ (Ψ x uStar : WithTop ℝ)))
  simpa [Set.inter_self] using
    (ClosedConvexOn.max_inter
      (hΨ_primal_closedConvex hu)
      (hΨ_primal_closedConvex huStar_mem))

/-- Helper for Lemma 3.22: every constrained sublevel set of the two-slice maximum is bounded,
because it sits inside the corresponding `uStar`-slice constrained sublevel set. -/
-- Proof sketch: if `max (Ψ(x,u)) (Ψ(x,uStar)) ≤ α`, then in particular `Ψ(x,uStar) ≤ α`, so the
-- max-sublevel slice is contained in the bounded `uStar`-slice sublevel set.
lemma parametric_maximum_bounded_sublevel_sets
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {uStar u : U}
    (hlevel_bounded :
      ∀ ⦃w : U⦄, w ∈ S → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (Ψ x w : WithTop ℝ)) α))
    (huStar_mem : uStar ∈ S) :
    ∀ α : ℝ,
      Bornology.IsBounded
        (constrainedSublevelSet P
          (fun x ↦ ((max (Ψ x u) (Ψ x uStar) : ℝ) : WithTop ℝ)) α) := by
  intro α
  refine (hlevel_bounded huStar_mem α).subset ?_
  intro x hx
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxP, hxα⟩
  have hxα' : max (Ψ x u) (Ψ x uStar) ≤ α := by
    exact_mod_cast hxα
  refine mem_constrainedSublevelSet_iff.2 ⟨hxP, ?_⟩
  exact_mod_cast (le_trans (le_max_right (Ψ x u) (Ψ x uStar)) hxα')

/-- Helper for Lemma 3.22: the dual closed-concavity owner on `v ↦ -Ψ(x,v)` yields ordinary
concavity of the real-valued dual slice `v ↦ Ψ(x,v)` on `S`. -/
-- Proof sketch: first pass from the lifted owner statement to ordinary convexity of the real part
-- of `v ↦ -Ψ(x,v)`, then use the standard `neg_convexOn_iff` equivalence to recover concavity.
lemma dual_slice_concave_on
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ}
    (hΨ_dual_closedConcave :
      ∀ ⦃x : X⦄, x ∈ P →
        ClosedConvexOn S (fun v ↦ (-Ψ x v : WithTop ℝ)))
    {x : X} (hx : x ∈ P) :
    ConcaveOn ℝ S (fun v ↦ Ψ x v) := by
  have hconv : ConvexOn ℝ S (fun v ↦ -Ψ x v) := by
    simpa [withTopRealPart] using (hΨ_dual_closedConcave hx).convexOn_withTopRealPart
  exact neg_convexOn_iff.mp hconv

/-
Lemma 3.22 lies in the chapter's parametric minimax / convex-analysis domain on a proper real
normed space, with the textbook `ℝⁿ × ℝᵐ` statement recovered by specialization.

Sampled owner-style declarations:
- `IsMinOn`
- `ClosedConvexOn.convex`
- `ClosedConvexOn.max_inter`
- `IsMaxOn`

Best owner abstraction:
- source-facing: the attained minimum of the two-slice maximum
  `x ↦ max (Ψ x u) (Ψ x uStar)` and its identification with the lower value
  `sInf ((fun x ↦ Ψ x uStar) '' P)` at a maximizing parameter
- core/canonical: the slice-infimum expression justified by the primal-slice hypotheses,
  the closed-convex two-function max owner `ClosedConvexOn.max_inter`,
  and the two-function minimax owner
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: the coercion of the real-valued kernel `Ψ` to `WithTop ℝ` inside the slice
  closed-convexity and bounded-sublevel hypotheses

Primitive data:
- the feasible set `P`
- the parameter set `S`
- the real-valued kernel `Ψ`
- nonemptiness of `P`, which lets one extract any dual slice and recover `Convex ℝ S` from the
  owner theorem `ClosedConvexOn.convex`
- the closed-convexity of each primal slice `x ↦ Ψ x u` on `P`
- the boundedness of the constrained sublevel sets of each primal slice
- the closed-concavity of each dual slice `u ↦ Ψ x u` on `S`, encoded through
  `u ↦ -Ψ x u`
- the canonical maximizing-parameter datum
  `uStar ∈ S ∧ IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar`

Derived API:
- the real-valued two-slice maximum `x ↦ max (Ψ x u) (Ψ x uStar)`
- the feasible attained minimizer supplied by the theorem below

Source/core/bridge triage:
- source-facing: Lemma 3.22 itself, expressed for a real-valued convex-concave kernel
- core/canonical: `IsMinOn` and the Chapter 3 closed-convex minimizer-existence
  owners above
- bridge/view: the internal `WithTop` lift used to apply those owners

The previous version kept duplicate public wrappers for the lower value and the two-slice maximum
and overstated the ambient space as an arbitrary real inner-product space. This refinement deletes
that wrapper layer and states the lemma directly in terms of the actual slice-infimum expression
and the source-facing real-valued maximum, while keeping the `WithTop` lift only in the
hypotheses that genuinely use the closed-convex owner API and matching the proper real normed-
space layer of the underlying minimax owner theorem. The textbook `ℝⁿ × ℝᵐ` statement is
recovered by specializing `X` and `U` to Euclidean spaces, using the canonical properness of
finite-dimensional real normed spaces on the primal side.
-/

/-- Lemma 3.22: if every primal slice `x ↦ Ψ(x, u)` is closed and convex on `P` with bounded real
sublevel sets, every dual slice `u ↦ Ψ(x, u)` is closed and concave on `S`, and `uStar` is a
dual-feasible maximizer of the lower value `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` on `S`,
then for every `u ∈ S`
the two-slice maximum `x ↦ max (Ψ(x, u)) (Ψ(x, uStar))` has a feasible minimizer `xBar ∈ P`, and
that minimum value is `sInf ((fun x ↦ Ψ x uStar) '' P)`. The convexity of `S` is recovered from the
dual closed-concavity owner by `ClosedConvexOn.convex`. This owner-level statement lives on the
same proper real normed-space layer as the chapter's minimax-linearization existence theorem. -/
-- Proof sketch: apply `ClosedConvexOn.max_inter` to the two primal slices to keep the source
-- maximum as the public objective, then use
-- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` to replace that maximum by one
-- convex combination of the two slices. Dual concavity and the convexity of `S` compare that
-- convex combination to the slice at `λ u + (1 - λ) uStar`; here `Convex ℝ S` is derived from
-- any witness of `hΨ_dual_closedConcave` using `hP_nonempty` and `ClosedConvexOn.convex`. The
-- proper-space hypotheses on `X` are exactly the owner-level hypotheses needed for that
-- minimax-linearization step. The maximizing property of `uStar` for
-- `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` then gives the reverse inequality,
-- while the bounded sublevel-set
-- hypotheses supply attainment for the relevant slice minima.
-- The lower bound
-- `sInf ((fun x ↦ Ψ x uStar) '' P) ≤ max (Ψ x u) (Ψ x uStar)` is immediate from the `uStar` slice.
theorem exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer
    {P : Set X} (hP_nonempty : P.Nonempty)
    {S : Set U} {Ψ : X → U → ℝ}
    (hΨ_primal_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hlevel_bounded :
      ∀ ⦃u : U⦄, u ∈ S → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (Ψ x u : WithTop ℝ)) α))
    (hΨ_dual_closedConcave :
      ∀ ⦃x : X⦄, x ∈ P →
        ClosedConvexOn S (fun v ↦ (-Ψ x v : WithTop ℝ)))
    {uStar u : U}
    (huStar_mem : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar)
    (hu : u ∈ S) :
    ∃ xBar ∈ P,
      IsMinOn (fun x ↦ max (Ψ x u) (Ψ x uStar)) P xBar ∧
        max (Ψ xBar u) (Ψ xBar uStar) = sInf ((fun x ↦ Ψ x uStar) '' P) := by
  let F : X → ℝ := fun x ↦ max (Ψ x u) (Ψ x uStar)
  -- First isolate the `uStar`-slice minimum so the easy lower bound uses an attained value.
  obtain ⟨xStar, hxStar_mem, hxStar_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty
      (hΨ_primal_closedConvex huStar_mem)
      (hlevel_bounded huStar_mem)
  have hvalue_uStar_eq :
      sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := by
    -- The attained `uStar`-slice minimum identifies the value function with that slice value.
    exact (hxStar_min.isGLB hxStar_mem).csInf_eq ⟨Ψ xStar uStar, ⟨xStar, hxStar_mem, rfl⟩⟩
  have hF_closedConvex :
      ClosedConvexOn P (fun x ↦ (F x : WithTop ℝ)) :=
    parametric_maximum_closed_convex_on hΨ_primal_closedConvex huStar_mem hu
  have hF_bounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (F x : WithTop ℝ)) α) :=
    parametric_maximum_bounded_sublevel_sets hlevel_bounded huStar_mem
  -- Then attain the minimum of the two-slice maximum by the same compact-sublevel argument.
  obtain ⟨xBar, hxBar_mem, hxBar_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty hF_closedConvex hF_bounded
  have hS_convex : Convex ℝ S :=
    (hΨ_dual_closedConcave hP_nonempty.some_mem).convex
  obtain ⟨lam, hlam⟩ :=
    exists_minimax_parameter_of_bounded_constrainedSublevelSets
      (hΨ_primal_closedConvex hu)
      (hΨ_primal_closedConvex huStar_mem)
      hF_bounded
  let uLam : U := (1 - (lam : ℝ)) • uStar + (lam : ℝ) • u
  let line : X → ℝ := fun x ↦ (1 - (lam : ℝ)) * Ψ x uStar + (lam : ℝ) * Ψ x u
  have huLam_mem : uLam ∈ S := by
    -- Convexity of `S` comes from any dual slice owner, so the affine combination stays feasible.
    simpa [uLam] using
      hS_convex huStar_mem hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
  obtain ⟨xLam, hxLam_mem, hxLam_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty
      (hΨ_primal_closedConvex huLam_mem)
      (hlevel_bounded huLam_mem)
  have hvalue_uLam_eq :
      sInf ((fun x ↦ Ψ x uLam) '' P) = Ψ xLam uLam := by
    -- The `uLam` slice also attains its lower value on `P`.
    exact (hxLam_min.isGLB hxLam_mem).csInf_eq ⟨Ψ xLam uLam, ⟨xLam, hxLam_mem, rfl⟩⟩
  have hline_le_uLam : ∀ x ∈ P, line x ≤ Ψ x uLam := by
    -- Dual concavity turns the weighted average of the two slice values into the slice value at the
    -- weighted parameter `uLam`.
    intro x hx
    have hconcave : ConcaveOn ℝ S (fun v ↦ Ψ x v) :=
      dual_slice_concave_on hΨ_dual_closedConcave hx
    have hineq :=
      hconcave.2 huStar_mem hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
    simpa [line, uLam, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hineq
  have hline_le_F : ∀ x : X, line x ≤ F x := by
    -- Any convex combination of two reals is bounded above by their maximum.
    intro x
    have hleft :
        (1 - (lam : ℝ)) * Ψ x uStar ≤ (1 - (lam : ℝ)) * F x := by
      exact mul_le_mul_of_nonneg_left (le_max_right (Ψ x u) (Ψ x uStar))
        (sub_nonneg.mpr lam.2.2)
    have hright : (lam : ℝ) * Ψ x u ≤ (lam : ℝ) * F x := by
      exact mul_le_mul_of_nonneg_left (le_max_left (Ψ x u) (Ψ x uStar)) lam.2.1
    change (1 - (lam : ℝ)) * Ψ x uStar + (lam : ℝ) * Ψ x u ≤ F x
    nlinarith
  have hminimax :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) =
        sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) := by
    -- The chapter minimax-parameter theorem identifies the max-objective infimum with the
    -- weighted-line infimum on the feasible subtype.
    simpa [F, line, max_def, AffineMap.lineMap_apply_ring, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      (isMinimaxLinearizationParameter_iff
        (fun x : P ↦ Ψ x u) (fun x : P ↦ Ψ x uStar) lam).mp hlam
  have hsInf_line_le_value :
      sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) ≤
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    -- Evaluate the weighted line at a minimizing point of the `uLam` slice, then use that `uStar`
    -- maximizes the lower-value function on `S`.
    have hline_mem :
        (((line xLam : ℝ) : EReal)) ∈ Set.range fun x : P ↦ ((line x : ℝ) : EReal) :=
      ⟨⟨xLam, hxLam_mem⟩, rfl⟩
    calc
      sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) ≤ ((line xLam : ℝ) : EReal) :=
        sInf_le hline_mem
      _ ≤ ((Ψ xLam uLam : ℝ) : EReal) := by
        exact_mod_cast hline_le_uLam xLam hxLam_mem
      _ = (((sInf ((fun x ↦ Ψ x uLam) '' P) : ℝ)) : EReal) := by
        exact_mod_cast hvalue_uLam_eq.symm
      _ ≤ (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
        exact_mod_cast huStar_max huLam_mem
  have hvalue_le_hsInf_F :
      (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) ≤
        sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) := by
    -- The `uStar` lower value is a lower bound for every value of the max-objective.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨x, rfl⟩
    have hvalue_le_slice :
        sInf ((fun x ↦ Ψ x uStar) '' P) ≤ Ψ x uStar := by
      calc
        sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := hvalue_uStar_eq
        _ ≤ Ψ x uStar := hxStar_min x.property
    have hvalue_le_F_real :
        sInf ((fun x ↦ Ψ x uStar) '' P) ≤ F x := by
      exact hvalue_le_slice.trans (le_max_right (Ψ x u) (Ψ x uStar))
    have hvalue_le_F_ereal :
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) ≤ ((F x : ℝ) : EReal) := by
      exact_mod_cast hvalue_le_F_real
    exact hvalue_le_F_ereal
  have hsInf_F_eq :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) =
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ hvalue_le_hsInf_F
    rw [hminimax]
    exact hsInf_line_le_value
  have hxBar_le_hsInf_F :
      ((F xBar : ℝ) : EReal) ≤ sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) := by
    -- The minimizing point `xBar` is itself a lower bound for the feasible subtype image.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨x, rfl⟩
    have hxBar_le_real : F xBar ≤ F x := hxBar_min x.property
    change ((F xBar : ℝ) : EReal) ≤ ((F x : ℝ) : EReal)
    exact_mod_cast hxBar_le_real
  have hsInf_F_le_xBar :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) ≤ ((F xBar : ℝ) : EReal) :=
    sInf_le ⟨⟨xBar, hxBar_mem⟩, rfl⟩
  have hxBar_value :
      ((F xBar : ℝ) : EReal) = (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ ?_
    · exact hxBar_le_hsInf_F.trans hsInf_F_eq.le
    · exact hsInf_F_eq.symm.le.trans hsInf_F_le_xBar
  refine ⟨xBar, hxBar_mem, ?_, ?_⟩
  · simpa [F] using hxBar_min
  · exact_mod_cast hxBar_value

end

/-! ### Proposition_3_22 (from Chap03) -/
noncomputable section

open Matrix
open scoped NormalCone
open scoped TangentCone
open scoped Topology

/-
Proposition 3.22 lies in the chapter's affine linear-equality tangent/normal-cone domain.

Relevant owner declarations sampled before refinement:
* `posTangentConeAt` and the notation `𝒯[Q] xBar` in `Definition_3_23`, the chapter owner for the
  textbook tangent cone
* `normalCone` in `Definition_3_22`, the chapter owner for textbook normal cones
* `LinearMap.ker`, `LinearMap.adjoint`, and `LinearMap.range`, the canonical linear-algebra owners
* `gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet` in `Chap01/Theorem_1_4_14`, which
  already treats linear equality constraints at the intrinsic linear-map level
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `LinearEqualityFeasibleSet`, the chapter bridge/view for the ambient-`Set.univ` specialization
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the mathlib bridge identifying `Aᵀ` with the
  adjoint linear map on Euclidean space

Best owner abstraction:
* the affine level set `{x | L x = b}` of a linear map

Primitive data:
* a linear equality map `L : E →ₗ[ℝ] F`
* a right-hand side `b`
* a feasible base point `xBar`

Derived API:
* the tangent-cone kernel formula on the intrinsic affine level set `{x | L x = b}`
* the normal-cone adjoint-range formula on the same level set
* the Chapter 3 `linearEqualityFeasibleSet (Set.univ : Set Eₙ) L b` specialization
* the matrix transpose bridge for the textbook `Aᵀ` statement

Source/core/bridge triage:
* source-facing: the textbook affine set `{x | A x = b}` and the matrix `ker A` / `range Aᵀ`
  formulas
* core/canonical: `𝒯[{x | L x = b}] xBar`, `N[{x | L x = b}] xBar`, `LinearMap.ker`, and
  `LinearMap.range`
* bridge/view: `linearEqualityFeasibleSet (Set.univ : Set Eₙ) L b` and `Matrix.toEuclideanLin`,
  which recover the chapter's ambient-`Set.univ` and matrix presentations from the intrinsic
  linear-map level-set statement

This file therefore centers both affine formulas on the intrinsic linear-map level set
`{x | L x = b}` together with the chapter owners `𝒯[Q] xBar` and `N[Q] xBar`. The
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) ...` and matrix presentations remain thin
source-facing bridge theorems.
-/

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Proposition 3.22 (1), intrinsic owner-level form: at a feasible point of the affine level set
`{x | L x = b}` of a continuous linear constraint map, the textbook tangent cone is exactly
`ker L`. -/
-- Proof sketch: use the chapter owner `𝒯[Q] xBar = posTangentConeAt Q xBar`. If `h` is a feasible
-- direction, then points of the form `xBar + t • h` stay in the affine level set exactly when
-- `L h = 0`; conversely, every kernel vector gives such a feasible ray.
theorem posTangentConeAt_linearLevelSet
    (L : E →ₗ[ℝ] F) (hL : Continuous L) (b : F) {xBar : E} (hxBar : L xBar = b) :
    𝒯[{x | L x = b}] xBar =
      L.ker := by
  ext y
  constructor
  · intro hy
    rcases exists_fun_of_mem_tangentConeAt hy with ⟨α, l, hl, c, d, hd0, hlevel, hcd⟩
    change L y = 0
    have hLd : ∀ᶠ n in l, L (d n) = 0 := by
      filter_upwards [hlevel] with n hn
      have : L (xBar + d n) = b := hn
      simpa [LinearMap.map_add, hxBar] using this
    have hzero : ∀ᶠ n in l, L (c n • d n) = 0 := by
      filter_upwards [hLd] with n hn
      simpa using congrArg (fun z ↦ c n • z) hn
    have hLy : Filter.Tendsto (fun n ↦ L (c n • d n)) l (𝓝 (L y)) :=
      hL.tendsto _ |>.comp hcd
    have hzeroT : Filter.Tendsto (fun n ↦ L (c n • d n)) l (𝓝 (0 : F)) :=
      tendsto_const_nhds.congr' <| hzero.mono fun _ hn ↦ hn.symm
    have : L y = 0 := by
      apply tendsto_nhds_unique hLy
      exact hzeroT
    simpa using this
  · intro hy
    have hy0 : L y = 0 := by
      simpa using hy
    apply mem_posTangentConeAt_of_frequently_mem
    refine (Filter.Eventually.of_forall fun t ↦ ?_).frequently
    change L (xBar + t • y) = b
    simp [LinearMap.map_add, hy0, hxBar]

end

section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable [FiniteDimensional ℝ F]

/-- Proposition 3.22 (2), intrinsic linear-map form: at a feasible point of the affine level set
`{x | L x = b}`, the normal cone is exactly the adjoint range `range Lᵀ`. -/
-- Proof sketch: a normal vector annihilates every tangent direction, hence annihilates `ker L`.
-- In finite-dimensional Euclidean space this is equivalent to belonging to `L.adjoint.range`.
theorem normalCone_linearLevelSet
    (L : E →ₗ[ℝ] F) (b : F) {xBar : E} (hxBar : L xBar = b) :
    (N[{x | L x = b}] xBar : Set E) =
      L.adjoint.range := by
  ext g
  constructor
  · intro hg
    have hg_orth : g ∈ L.kerᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hy0 : L y = 0 := by
        simpa using hy
      have hplus : xBar + y ∈ ({x | L x = b} : Set E) := by
        change L (xBar + y) = b
        simp [LinearMap.map_add, hy0, hxBar]
      have hminus : xBar - y ∈ ({x | L x = b} : Set E) := by
        change L (xBar - y) = b
        simp [LinearMap.map_sub, hy0, hxBar]
      have hplusIneq := (mem_normalCone_iff.mp hg) (xBar + y) hplus
      have hminusIneq := (mem_normalCone_iff.mp hg) (xBar - y) hminus
      have hpos : 0 ≤ inner ℝ g y := by
        simpa using hplusIneq
      have hneg : inner ℝ g y ≤ 0 := by
        simpa [sub_eq_add_neg, inner_neg_right] using hminusIneq
      exact le_antisymm hneg hpos
    rwa [LinearMap.orthogonal_ker] at hg_orth
  · intro hg
    rw [← LinearMap.orthogonal_ker] at hg
    have hg_orth : g ∈ L.kerᗮ := hg
    rw [Submodule.mem_orthogonal'] at hg_orth
    exact (mem_normalCone_iff).2 <| by
      intro x hx
      have hxker : x - xBar ∈ L.ker := by
        change L (x - xBar) = 0
        have hxEq : L x = b := hx
        simp [LinearMap.map_sub, hxEq, hxBar]
      have hinner : inner ℝ g (x - xBar) = 0 := hg_orth (x - xBar) hxker
      simp [hinner]

end

section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Proposition 3.22 (1), source-facing Chapter 3 specialization: on
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b`, the tangent cone is `ker A`. -/
theorem posTangentConeAt_matrix_linearEqualityFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xBar : Eₙ}
    (hxBar : xBar ∈ linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b) :
    𝒯[linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b] xBar =
      A.toEuclideanLin.ker := by
  have hxEq : A.toEuclideanLin xBar = b := (mem_linearEqualityFeasibleSet_iff.mp hxBar).2
  have hA : Continuous A.toEuclideanLin := LinearMap.continuous_of_finiteDimensional _
  simpa [linearEqualityFeasibleSet] using
    posTangentConeAt_linearLevelSet A.toEuclideanLin hA b hxEq

/-- Proposition 3.22 (2), source-facing Chapter 3 specialization: on
`linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b`, the normal cone is the range
of the transpose map `Aᵀ`. -/
theorem normalCone_matrix_linearEqualityFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xBar : Eₙ}
    (hxBar : xBar ∈ linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b) :
    (N[linearEqualityFeasibleSet (Set.univ : Set Eₙ) A.toEuclideanLin b] xBar : Set Eₙ) =
      (Aᵀ.toEuclideanLin).range := by
  have hxEq : A.toEuclideanLin xBar = b := (mem_linearEqualityFeasibleSet_iff.mp hxBar).2
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [linearEqualityFeasibleSet, hAdj] using
    normalCone_linearLevelSet A.toEuclideanLin b hxEq

end

end

/-! ### Theorem_3_22 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Theorem 3.22 lies in the chapter's extended-valued subgradient / supporting-hyperplane domain.

Relevant sampled declarations:
- `subdifferential` and the notation `∂ f(x0)` from `Definition_3_1_5`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` from `Theorem_3_1_18`
- `AffineHyperplane.IsSupporting` and `IsSupportingHyperplane` from `Definition_3_1_4_1`

Best owner abstraction:
- the subdifferential owner hypothesis `g ∈ ∂ f(x0)` together with the earlier theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Primitive data:
- an extended-valued function `f`, a base point `x0`, and a subgradient vector `g`
- the owner hypothesis `g ∈ ∂ f(x0)`
- the nonvanishing hypothesis `g ≠ 0` for the hyperplane conclusion

Derived API:
- the sign-reversed sublevel-set inequality `⟪g, x - x0⟫ ≤ 0`
- the owner-level supporting-affine-hyperplane conclusion for `{x | f x ≤ f x0}`
- its coordinate bridge `IsSupportingHyperplane`

Source/core/bridge triage:
- source-facing: Theorem 3.22's sign convention `⟪g, x - x0⟫ ≤ 0`
- core/canonical: `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the equivalent sign change and the coordinate support predicate
  `IsSupportingHyperplane`

The earlier theorem `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` already captures
the same mathematical support statement at the owner level, with the equivalent form
`0 ≤ ⟪g, x0 - x⟫`. This file keeps the source-facing sign convention, then packages the supporting
result first at the chapter owner `AffineHyperplane.IsSupporting` and only afterwards exposes the
textbook coordinate bridge `IsSupportingHyperplane`.
-/
/-- Theorem 3.22: every subgradient `g ∈ ∂f(x₀)` is a supporting vector to the level set
`{x | f x ≤ f x₀}` at `x₀`, in the sense that `⟪g, x - x₀⟫ ≤ 0` for every point of that
sublevel set. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook statement on
`ℝⁿ`. -/
theorem subgradient_nonpos_on_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) {x : E} (hx : f x ≤ f x0) :
    inner ℝ g (x - x0) ≤ 0 := by
  simpa [inner_sub_right] using
    subgradient_nonneg_on_sublevelSet_of_mem_subdifferential hg hx

/-- A nonzero subgradient at `x₀` yields the supporting affine hyperplane with normal `g` and
offset `⟪g, x₀⟫` for the sublevel set `{x | f x ≤ f x₀}`. -/
-- Proof sketch: apply the main sublevel-set inequality to rewrite
-- `⟪g, x - x₀⟫ ≤ 0` as `⟪g, x⟫ ≤ ⟪g, x₀⟫` on `{x | f x ≤ f x₀}`, then combine this half-space
-- containment with `g ≠ 0` and the contact point
-- `x₀ ∈ {x | f x ≤ f x₀} ∩ (⟨g, hg0, ⟪g, x₀⟫⟩ : AffineHyperplane E)`.
theorem subgradient_affineHyperplane_isSupporting_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) (hg0 : g ≠ 0) :
    (⟨g, hg0, inner ℝ g x0⟩ : AffineHyperplane E).IsSupporting {x : E | f x ≤ f x0} := by
  constructor
  · intro x hx
    change inner ℝ g x ≤ inner ℝ g x0
    have hx' : inner ℝ g (x - x0) ≤ 0 :=
      subgradient_nonpos_on_sublevelSet_of_mem_subdifferential hg hx
    simpa [inner_sub_right] using hx'
  · refine ⟨x0, ?_⟩
    constructor
    · exact (le_rfl : f x0 ≤ f x0)
    · simp [AffineHyperplane.carrier]

/-- A nonzero subgradient at `x₀` yields a supporting hyperplane to the sublevel set
`{x | f x ≤ f x₀}`. -/
theorem subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) (hg0 : g ≠ 0) :
    IsSupportingHyperplane {x : E | f x ≤ f x0} g (inner ℝ g x0) := by
  exact ⟨hg0,
    subgradient_affineHyperplane_isSupporting_sublevelSet_of_mem_subdifferential hg hg0⟩

end
