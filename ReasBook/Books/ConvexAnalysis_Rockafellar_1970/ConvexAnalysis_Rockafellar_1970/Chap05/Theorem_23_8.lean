import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item were appended by the statement pipeline.

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
