import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_23_8_1 (from Chap05) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem indicator_isProper_of_nonempty
    (C : Set E) (hC : C.Nonempty) :
    (indicator ℝ C : E → EReal).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨?_, ?_⟩
  · rcases hC with ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · intro x
    by_cases hx : x ∈ C <;> simp [indicator_def, hx]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem sum_indicator_eq_indicator_iInter
    (C : Fin m → Set E) :
    (∑ i, indicator ℝ (C i)) = indicator ℝ (⋂ i, C i) := by
  funext x
  by_cases hx : ∀ i : Fin m, x ∈ C i
  · have hmem : x ∈ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hzero : ∀ i : Fin m, indicator ℝ (C i) x = 0 := by
      intro i
      simp [indicator_def, hx i]
    have hsum_zero : (∑ i, indicator ℝ (C i) x) = 0 := by
      calc
        (∑ i, indicator ℝ (C i) x) = ∑ i, (0 : EReal) := by
          congr with i
          exact hzero i
        _ = 0 := by simp
    simpa [indicator_def, hmem] using hsum_zero
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hnotmem : x ∉ ⋂ i, C i := by
      simpa [Set.mem_iInter] using hx
    have hsum_ne_bot :
        Finset.sum (Finset.univ.erase i) (fun j ↦ indicator ℝ (C j) x) ≠ (⊥ : EReal) := by
      refine WithBotTop.sum_ne_bot_of_forall_ne_bot ?_
      intro j hj
      by_cases hjx : x ∈ C j
      · rw [indicator_def, if_pos hjx]
        exact WithBotTop.zero_ne_bot
      · rw [indicator_def, if_neg hjx]
        exact WithBotTop.top_ne_bot
    have htail_bot :
        ⊥ < Finset.sum (Finset.univ.erase i) (fun j ↦ indicator ℝ (C j) x) := by
      simpa using (WithBot.bot_lt_iff_ne_bot.mpr hsum_ne_bot)
    have hsum_top : (∑ j, indicator ℝ (C j) x) = ⊤ := by
      rw [← Finset.add_sum_erase Finset.univ (fun j ↦ indicator ℝ (C j) x) (Finset.mem_univ i)]
      have hi_top : indicator ℝ (C i) x = ⊤ := by
        simp [indicator_def, hi]
      rw [hi_top]
      simpa using WithBotTop.top_add_of_ne_bot (bot_lt_iff_ne_bot.mp htail_bot)
    simpa [indicator_def, hnotmem] using hsum_top

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.8.1 is the normal-cone formula for a finite intersection of convex
  sets, together with the mixed polyhedral-prefix qualification.
- `core/canonical`: the relevant owner surfaces already present in the project are
  `N[ℝ](x | C)`, the relative-interior notation `ri[ℝ](C)`, the pointwise indicator
  `δ[ℝ](· | C)`, `s.IsPolyhedral ℝ`, and the Chapter 23 finite-sum subdifferential equalities.
- `bridge/view`: the corollary is obtained by applying Theorem 23.8 to indicator functions and
  then transporting the result back to sets via the indicator-function normal-cone bridge; no new
  wrapper around subdifferentials or intersections is introduced.
-/

-- Proof sketch: apply
-- `Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom`
-- to the indicator family `i ↦ δ[ℝ](· | C i)`. Convexity of each summand is
-- `indicator_isConvex_iff`, its relative domain is `ri[ℝ](C i)`, the pointwise sum is
-- the indicator of `⋂ i, C i`, and `Function.subdifferentialAt_indicatorFunction_eq_normalCone`
-- identifies the resulting subdifferentials with the corresponding normal cones.
/-- Corollary 23.8.1 (1): if convex sets `C 0, …, C (m - 1)` in a finite-dimensional real inner
product space have relative interiors with a common point, then the normal cone of their
intersection at `x` is the finite Minkowski sum of the individual normal cones at `x`. -/
theorem normalCone_iInter_eq_sum_normalCone_of_common_ri
    (C : Fin m → Set E)
    (hC_convex : ∀ i : Fin m, Convex ℝ (C i))
    (hri : (⋂ i, ri[ℝ](C i)).Nonempty)
    (x : E) :
    (N[ℝ](x | ⋂ i, C i) : Set E) = ∑ i, (N[ℝ](x | C i) : Set E) := by
  let f : Fin m → E → EReal := fun i ↦ indicator ℝ (C i)
  have hC_nonempty : ∀ i : Fin m, (C i).Nonempty := by
    rcases hri with ⟨y, hy⟩
    have hy : ∀ i : Fin m, y ∈ ri[ℝ](C i) := by
      simpa [Set.mem_iInter] using hy
    intro i
    exact ⟨y, intrinsicInterior_subset (hy i)⟩
  have hf_convex : ∀ i : Fin m, (f i).IsConvex ℝ := by
    intro i
    simpa [f] using ((indicator_isConvex_iff (C i)).2 (hC_convex i) :
      (indicator ℝ (C i) : E → EReal).IsConvex ℝ)
  have hf_proper : ∀ i : Fin m, (f i).IsProper := by
    intro i
    simpa [f] using (indicator_isProper_of_nonempty (C i) (hC_nonempty i) :
      (indicator ℝ (C i) : E → EReal).IsProper)
  have hri_f : (⋂ i, riDom[ℝ](f i)).Nonempty := by
    rcases hri with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    have hyi : y ∈ ri[ℝ](C i) := (Set.mem_iInter.mp hy) i
    change y ∈ ri[ℝ](effectiveDomain (f i))
    change y ∈ ri[ℝ](effectiveDomain ((indicator ℝ (C i) : E → EReal)))
    simpa [effectiveDomain_indicator] using hyi
  simpa [f, sum_indicator_eq_indicator_iInter,
    Function.subdifferentialAt_indicatorFunction_eq_normalCone] using
    Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
      f hf_convex hf_proper hri_f x

-- Proof sketch: again apply Theorem 23.8, now in its mixed-domain polyhedral-prefix form, to the
-- indicator family `i ↦ δ[ℝ](· | C i)`. The prefix polyhedral hypotheses transfer through
-- `Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral`, the suffix convexity through
-- `indicator_isConvex_iff`, the mixed common-point hypothesis becomes the theorem's
-- domain/relative-domain condition, and the indicator-function subdifferentials are the normal
-- cones by `Function.subdifferentialAt_indicatorFunction_eq_normalCone`.
/-- Corollary 23.8.1 (2): if `C 0, …, C (k - 1)` are polyhedral and the family
`C 0, …, C (k - 1), ri[ℝ](C k), …, ri[ℝ](C (m - 1))` has a common point, then the same normal-cone
sum formula holds for the intersection `⋂ i, C i`. -/
theorem normalCone_iInter_eq_sum_normalCone_of_polyhedralPrefix_mixedCommonPoint
    (C : Fin m → Set E) (k : ℕ)
    (hC_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → Convex ℝ (C i))
    (hC_poly : ∀ i : Fin m, (i : ℕ) < k → (C i).IsPolyhedral ℝ)
    (hcommon :
      ∃ y : E,
        (∀ i : Fin m, (i : ℕ) < k → y ∈ C i) ∧
          ∀ i : Fin m, k ≤ (i : ℕ) → y ∈ ri[ℝ](C i))
    (x : E) :
    (N[ℝ](x | ⋂ i, C i) : Set E) = ∑ i, (N[ℝ](x | C i) : Set E) := by
  let f : Fin m → E → EReal := fun i ↦ indicator ℝ (C i)
  have hC_nonempty : ∀ i : Fin m, (C i).Nonempty := by
    rcases hcommon with ⟨y, hy_prefix, hy_suffix⟩
    intro i
    by_cases hik : (i : ℕ) < k
    · exact ⟨y, hy_prefix i hik⟩
    · exact ⟨y, intrinsicInterior_subset (hy_suffix i (Nat.le_of_not_gt hik))⟩
  have hf_suffixConvex : ∀ i : Fin m, k ≤ (i : ℕ) → (f i).IsConvex ℝ := by
    intro i hik
    simpa [f] using ((indicator_isConvex_iff (C i)).2 (hC_suffixConvex i hik) :
      (indicator ℝ (C i) : E → EReal).IsConvex ℝ)
  have hf_proper : ∀ i : Fin m, (f i).IsProper := by
    intro i
    simpa [f] using (indicator_isProper_of_nonempty (C i) (hC_nonempty i) :
      (indicator ℝ (C i) : E → EReal).IsProper)
  have hpoly : f.HasPolyhedralPrefix k := by
    intro i hik
    simpa [f] using
      ((Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral (𝕜 := ℝ) (E := E) (C i)).2
        (hC_poly i hik) :
      (indicator ℝ (C i)).HasPolyhedralEpigraph)
  have hdom : f.HasMixedPrefixDomainPoint k := by
    rcases hcommon with ⟨y, hy_prefix, hy_suffix⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hik
      simpa [f] using hy_prefix i hik
    · intro i hik
      simpa [f, riDom_eq_intrinsicInterior_dom, effectiveDomain_indicator] using hy_suffix i hik
  simpa [f, sum_indicator_eq_indicator_iInter,
    Function.subdifferentialAt_indicatorFunction_eq_normalCone] using
    Function.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralPrefix_mixedDomain
      f k hf_suffixConvex hf_proper hpoly hdom x

end

/-! ### Theorem_23_8 (from Chap05) -/
noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u v
universe w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.8 is Rockafellar's finite-sum formula for subdifferentials,
  consisting of the general inclusion, the common-relative-interior equality, and the mixed
  polyhedral-family equality.
- `core/canonical`: the primitive owner is the intrinsic Chapter 23 subdifferential
  `∂ f at x`, together with the effective-domain owners `dom(·)` and `riDom[𝕜](·)`,
  and the Chapter 20 polyhedral-epigraph owner.
- `bridge/view`: the vector wording in terms of primal vectors is the inner-product pullback
  `∂ᵥf(x)`, so the vector-valued theorem surface belongs below as a companion bridge layer rather
  than as the main owner.

Domain-style sampling used here:
- `∂ f at x` and `∂ᵥf(x)` from `Chap05/Definition_23_0_6`;
- `Function.HasPolyhedralEpigraph` from `Chap04/Theorem_20_1`;
- `Function.lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom` from `Chap02/Theorem_9_3`
  as the chapter owner for the common-`riDom` finite-sum qualification pattern.

Primitive data vs derived API:
- primitive owner surface: intrinsic finite sums of the dual-valued subdifferentials
  `∂ (f i) at x`;
- source-facing qualification data: proper convexity, common relative-interior points, and a
  chosen polyhedral subfamily together with mixed-domain compatibility on its complement;
- derived bridge surface: the vector-valued inner-product restatements in the `Function`
  namespace.
-/

section

variable {𝕜 : Type w} [NormedField 𝕜] [LinearOrder 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Y : Type (max v w)} [AddCommMonoid Y] [HasPairing E Y 𝕜]

namespace Pairing

-- Proof sketch: an element of `∑ i, ∂[Y]fun z => f i z(x)`, i.e. of the finite Minkowski
-- sum of the pairing-level fibers, is a finite sum
-- `∑ i, xStar i` with each `xStar i` satisfying the supporting inequality for `f i` at `x`.
-- Summing those inequalities over `i` gives the supporting inequality for the pointwise sum
-- `∑ i, f i`, so the same vector belongs to `∂[Y]fun z => ∑ i, f i z(x)`.
/-- Theorem 23.8 (1), canonical owner form: for a finite family, the Minkowski sum of the
intrinsic pairing-level subdifferentials `∂[Y]f(x)` at `x` is contained in the intrinsic
subdifferential of the pointwise sum at `x`. -/
theorem sum_subdifferentialAt_subset_subdifferentialAt_sum
    (f : ι → E → WithBotTop 𝕜) (x : E) :
    (∑ i, (∂[Y]fun z => f i z(x))) ⊆
      (∂[Y]fun z => ∑ i, f i z(x)) := sorry

end Pairing

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- Proof sketch: the inclusion from clause (1) gives one containment immediately. For the reverse
-- containment, apply the Chapter 16 conjugate-of-sum formula under the common-`riDom`
-- hypothesis, then use the Fenchel-Young characterization from Theorem 23.5 to decompose any
-- subgradient of `∑ i, f i` at `x` into a sum of subgradients of the individual summands.
/-- Theorem 23.8 (2), canonical owner form: if proper convex summands have a common point in the
relative interiors `ri(dom(f i))`, equivalently in `⋂ i, riDom[𝕜](f i)`, then the intrinsic
subdifferential of the sum equals the finite Minkowski sum of the intrinsic subdifferentials. The
theorem name follows the chapter's existing `nonempty_iInter_riDom` owner vocabulary for this
hypothesis shape. -/
theorem subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty)
    (x : E) :
    (∂ (∑ i, f i) at x) = ∑ i, (∂ (f i) at x) := sorry

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- Proof sketch: use the same Fenchel-Young argument as in clause (2), but replace the common
-- `riDom` qualification by a mixed Chapter 20 qualification: a chosen polyhedral subfamily is
-- handled through the ordinary domains `dom(f i)`, while its complement still uses
-- `riDom[𝕜](f i)`. The Chapter 20 mixed-domain conjugate formula then gives the reverse
-- containment.
/-- Theorem 23.8 (3), canonical owner form: if a chosen finite subfamily is polyhedral and the
family has a point in the domains of that subfamily and in the relative interiors of the domains
of the complementary subfamily, then the same intrinsic subdifferential equality holds. This is
the finite-family abstraction of Rockafellar's ordered "polyhedral prefix" wording. -/
theorem subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain
    (f : ι → E → WithBotTop 𝕜) (S : Set ι)
    (hf_suffixConvex : ∀ i, i ∉ S → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hpoly : ∀ i, i ∈ S → (f i).HasPolyhedralEpigraph)
    (hdom : ∃ y : E, (∀ i, i ∈ S → y ∈ dom(f i)) ∧ ∀ i, i ∉ S → y ∈ riDom[𝕜](f i))
    (x : E) :
    (∂ (∑ i, f i) at x) = ∑ i, (∂ (f i) at x) := sorry

end

namespace Function

private theorem toDual_preimage_sum
    {𝕜 : Type w} [RCLike 𝕜]
    {ι : Type u} [Fintype ι]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (s : ι → Set (StrongDual 𝕜 E)) :
    (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (∑ i, s i) =
      ∑ i, (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' s i := by
  classical
  let e := InnerProductSpace.toDual 𝕜 E
  change (e : E → StrongDual 𝕜 E) ⁻¹' (∑ i, s i) =
      ∑ i, (e : E → StrongDual 𝕜 E) ⁻¹' s i
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      ext x
      simp
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Set.preimage_add e e.injective]
      · rw [ih]
      · intro y _
        exact e.surjective y
      · intro y _
        exact e.surjective y

section

variable {𝕜 : Type w} [RCLike 𝕜] [LinearOrder 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

-- Proof sketch: transport the intrinsic owner theorem
-- `Pairing.sum_subdifferentialAt_subset_subdifferentialAt_sum` along the inner-product duality
-- equivalence underlying `∂ᵥf(x)`.
/-- Theorem 23.8 (1), inner-product bridge form: for a finite family, the Minkowski sum of the
vector-valued subdifferentials at `x` is contained in the vector-valued subdifferential of the
pointwise sum at `x`. -/
theorem sum_subdifferentialAt_subset_subdifferentialAt_sum
    (f : ι → E → WithBotTop 𝕜) (x : E) :
    (∑ i, (∂ᵥfun z => f i z(x))) ⊆ (∂ᵥfun z => ∑ i, f i z(x)) := by
  have hroot :
      (∑ i, (∂[StrongDual 𝕜 E]fun z => f i z(x))) ⊆
        (∂[StrongDual 𝕜 E]fun z => ∑ i, f i z(x)) :=
    Pairing.sum_subdifferentialAt_subset_subdifferentialAt_sum f x
  have hpre :=
    Set.preimage_mono (f := InnerProductSpace.toDualMap 𝕜 E) hroot
  simpa [Function.subdifferentialAt, toDual_preimage_sum] using hpre

end

section

variable {𝕜 : Type w} [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

-- Proof sketch: transport the intrinsic equality theorem
-- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom` through the
-- inner-product bridge `∂ᵥf(x)`.
/-- Theorem 23.8 (2), inner-product bridge form: if proper convex summands have a common point in
`⋂ i, riDom[𝕜](f i)`, then the vector-valued subdifferential of the sum equals the finite Minkowski
sum of the vector-valued subdifferentials. -/
theorem subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty)
    (x : E) :
    (∂ᵥ(∑ i, f i)(x)) = ∑ i, (∂ᵥ(f i)(x)) := by
  let e := InnerProductSpace.toDual 𝕜 E
  have hroot :
      (∂ (∑ i, f i) at x) = ∑ i, (∂ (f i) at x) :=
    _root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
      f hf_convex hf_proper hri x
  rw [subdifferentialAt, ← toDual_preimage_sum (fun i ↦ (∂ (f i) at x))]
  exact congrArg (Set.preimage e) hroot

end

section

variable {𝕜 : Type w} [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {ι : Type u} [Fintype ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

-- Proof sketch: transport the intrinsic mixed-domain equality theorem
-- `_root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain`
-- through the inner-product bridge.
/-- Theorem 23.8 (3), inner-product bridge form: if a chosen finite subfamily is polyhedral and
the family has a point in the domains of that subfamily and in the relative interiors of the
domains of the complementary subfamily, then the same
vector-valued subdifferential equality holds. -/
theorem subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain
    (f : ι → E → WithBotTop 𝕜) (S : Set ι)
    (hf_suffixConvex : ∀ i, i ∉ S → (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (hpoly : ∀ i, i ∈ S → (f i).HasPolyhedralEpigraph)
    (hdom : ∃ y : E, (∀ i, i ∈ S → y ∈ dom(f i)) ∧ ∀ i, i ∉ S → y ∈ riDom[𝕜](f i))
    (x : E) :
    (∂ᵥ(∑ i, f i)(x)) = ∑ i, (∂ᵥ(f i)(x)) := by
  let e := InnerProductSpace.toDual 𝕜 E
  have hroot :
      (∂ (∑ i, f i) at x) = ∑ i, (∂ (f i) at x) :=
    _root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain
      f S hf_suffixConvex hf_proper hpoly hdom x
  rw [subdifferentialAt, ← toDual_preimage_sum (fun i ↦ (∂ (f i) at x))]
  exact congrArg (Set.preimage e) hroot

end

end Function
