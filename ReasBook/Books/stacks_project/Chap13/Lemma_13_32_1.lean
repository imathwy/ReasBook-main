import Mathlib
import stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.32.1:
- primary domain: cohomological-dimension functions controlling object-property replacements of
  cochain complexes in an abelian category;
- sampled owner declarations:
  `ObjectProperty.ContainsZero`,
  `ObjectProperty.HasMonoEmbedding`,
  `exists_quasiIso_with_terms_in_of_isZero_homology_below`;
- best owner abstraction: the categorical owner is the zero-locus object property
  `fun X ↦ d X = 0`, viewed through the canonical owners `ObjectProperty.ContainsZero` and
  `ObjectProperty.HasMonoEmbedding`; the source-facing public statements should still speak
  directly about the numerical condition `d X = 0`;
- primitive data: the source-facing zero-object equality `d 0 = 0`, the zero-locus
  mono-embedding owner, and the two numerical inequalities on biproducts and short exact
  sequences;
- derived API: the constant-zero example, the shifted-tail condition on cochain complexes, and the
  final quasi-isomorphic replacement theorem with termwise conclusion `d (L.X n) = 0`.

Source/core/bridge triage:
- `source-facing`: `IsCohomologicalDimensionFunction`,
  `ShiftedDimensionTendsToNegInf`, and the quasi-isomorphic replacement theorem;
- `core/canonical`: `ObjectProperty.ContainsZero`, `ObjectProperty.HasMonoEmbedding`,
  `ShortComplex.ShortExact`, and `QuasiIso`;
- `bridge/view`: the internal zero-locus object property `fun X ↦ d X = 0`, used only where
  `ObjectProperty`-based replacement owners are required.
-/

/-- A cohomological-dimension function on an abelian category is a function to `WithTop ℕ` whose
value on the zero object is zero, whose zero locus, viewed as an object property, has monomorphic
envelopes for all objects, whose value on biproducts is bounded by the maximum of the summand
values, and whose value on the cokernel term of a short exact sequence is bounded by the maximum
of the middle value and one less than the left value. -/
class IsCohomologicalDimensionFunction (d : 𝒜 → WithTop ℕ) : Prop where
  zero_eq : d (0 : 𝒜) = 0
  hasMonoEmbedding : HasMonoEmbedding (fun X ↦ d X = 0)
  biprod_le_max (X Y : 𝒜) : d (X ⊞ Y) ≤ max (d X) (d Y)
  shortExact_right_le_max {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)

attribute [instance] IsCohomologicalDimensionFunction.hasMonoEmbedding

namespace IsCohomologicalDimensionFunction

variable {d : 𝒜 → WithTop ℕ} [IsCohomologicalDimensionFunction d]

/-- The zero object is zero-dimensional for a cohomological-dimension function. -/
theorem prop_zero : d (0 : 𝒜) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  exact hd.zero_eq

instance zeroLocus_containsZero : ContainsZero (fun X : 𝒜 ↦ d X = 0) where
  exists_zero := ⟨0, isZero_zero 𝒜, prop_zero⟩

/-- The zero-dimensional objects for a cohomological-dimension function are closed under binary
biproducts. -/
theorem prop_biprod {X Y : 𝒜} (hX : d X = 0) (hY : d Y = 0) :
    d (X ⊞ Y) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d (X ⊞ Y) = 0
  refine le_antisymm ?_ bot_le
  simpa [hX, hY] using hd.biprod_le_max X Y

/-- If the left and middle terms of a short exact sequence are zero-dimensional, then so is the
right term. -/
theorem prop_X₃_of_shortExact {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : d S.X₁ = 0) (h₂ : d S.X₂ = 0) :
    d S.X₃ = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d S.X₃ = 0
  refine le_antisymm ?_ bot_le
  simpa [h₁, h₂] using hd.shortExact_right_le_max hS

end IsCohomologicalDimensionFunction

/-- The constant-zero function is a cohomological-dimension function. -/
instance instIsCohomologicalDimensionFunctionZero :
    IsCohomologicalDimensionFunction (fun _ : 𝒜 ↦ (0 : WithTop ℕ)) where
  zero_eq := by
    simp
  hasMonoEmbedding := by
    refine ⟨fun X ↦ ?_⟩
    exact ⟨X, by simp, 𝟙 X, inferInstance⟩
  biprod_le_max X Y := by
    simp
  shortExact_right_le_max hS := by
    simp

/-- The shifted dimension function `n + d (K.X n)` tends to `-∞` toward negative degrees when,
for every bound `N`, all sufficiently negative terms have finite `d`-value bounded so that
`n + d (K.X n) ≤ N`. -/
def ShiftedDimensionTendsToNegInf
    (d : 𝒜 → WithTop ℕ) (K : CochainComplex 𝒜 ℤ) : Prop :=
  ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n ≤ n₀, ∃ m : ℕ, d (K.X n) = m ∧ n + m ≤ N

-- Proof sketch: first use Lemma 13.15.5 to replace the high-degree tail of `K` by a
-- quasi-isomorphic bounded-below complex of `d = 0` objects. Then perform the textbook elementary
-- replacements in finitely many degrees at a time, using the monomorphic envelope axiom and the
-- short-exact-sequence inequality to decrease the quantity `n + d(K.X n)` until every term has
-- dimension zero.
/-- Lemma 13.32.1: if `d` is a cohomological-dimension function on an abelian category and
`n + d(K.X n)` tends to `-∞` as `n → -∞` in the sense that for every integer bound `N` there is a
lower cutoff below which each `d(K.X n)` is finite and satisfies `n + d(K.X n) ≤ N`, then `K` is
quasi-isomorphic to a cochain complex all of whose terms have `d = 0`. -/
theorem exists_quasiIso_to_termwise_zero_dimension_of_tendsToNegInf_shifted_dimension
    (d : 𝒜 → WithTop ℕ) [IsCohomologicalDimensionFunction d] (K : CochainComplex 𝒜 ℤ)
    (hK : ShiftedDimensionTendsToNegInf d K) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ n : ℤ, d (L.X n) = 0 := sorry

end
