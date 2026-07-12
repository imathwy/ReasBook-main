import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

namespace Module.Basis

section

variable {ι : Type u} {M : Type v} [AddCommGroup M]

/-- The positive cone determined by a `ℤ`-basis consists of the elements whose coordinates in that
basis are all nonnegative. -/
def positiveCone (b : Module.Basis ι ℤ M) : Set M :=
  {x | ∀ i, 0 ≤ b.repr x i}

/-- Membership in the positive cone of a `ℤ`-basis is equivalent to coordinatewise
nonnegativity. -/
@[simp] theorem mem_positiveCone_iff (b : Module.Basis ι ℤ M) (x : M) :
    x ∈ b.positiveCone ↔ ∀ i, 0 ≤ b.repr x i :=
  Iff.rfl

/-- A finite `ℤ`-linear combination of basis vectors with nonnegative coefficients lies in the
positive cone of that basis. -/
theorem linearCombination_mem_positiveCone_of_nonneg
    (b : Module.Basis ι ℤ M) (c : ι →₀ ℤ) (hc : ∀ i, 0 ≤ c i) :
    Finsupp.linearCombination ℤ (fun i ↦ b i) c ∈ b.positiveCone := by
  -- The basis coordinates of a basis linear combination are exactly the chosen coefficients.
  intro i
  rw [b.repr_linearCombination]
  exact hc i

/-- Membership in the positive cone of a `ℤ`-basis is equivalent to having a basis expansion with
all coefficients nonnegative. -/
theorem mem_positiveCone_iff_exists_nonneg_finsupp
    (b : Module.Basis ι ℤ M) (x : M) :
    x ∈ b.positiveCone ↔
      ∃ c : ι →₀ ℤ, (∀ i, 0 ≤ c i) ∧ Finsupp.linearCombination ℤ (fun i ↦ b i) c = x := by
  constructor
  · intro hx
    -- Use the basis coordinates of `x` as the desired nonnegative coefficient family.
    refine ⟨b.repr x, hx, ?_⟩
    simpa using b.linearCombination_repr x
  · rintro ⟨c, hc, rfl⟩
    -- A basis linear combination with nonnegative coefficients is positive by inspection of
    -- coordinates.
    exact linearCombination_mem_positiveCone_of_nonneg b c hc

-- Proof sketch: write `x` in the basis `b`. The hypothesis says that every coordinate of `n • x`
-- is nonnegative, hence every integer `n * b.repr x i` is nonnegative. Since `1 ≤ n`, each
-- coordinate `b.repr x i` is already nonnegative, so `x` lies in the positive cone.
/-- If `n • x` lies in the positive cone of a `ℤ`-basis for some `n ≥ 1`, then `x` already lies in
that positive cone. -/
theorem mem_positiveCone_of_nsmul_mem_positiveCone
    (b : Module.Basis ι ℤ M) {x : M} {n : ℕ} (hn : 1 ≤ n)
    (hx : n • x ∈ b.positiveCone) :
    x ∈ b.positiveCone := by
  intro i
  have hxi : 0 ≤ (n : ℤ) * b.repr x i := by
    simpa using hx i
  exact nonneg_of_mul_nonneg_right hxi (show (0 : ℤ) < n by exact_mod_cast hn)

-- Proof sketch: first rewrite the ambient subset `S` as the positive cone of the chosen basis,
-- then the result is exactly `mem_positiveCone_of_nsmul_mem_positiveCone`.
/-- Helper for Lemma 16-16.3-1: if a subset of a `ℤ`-module is identified with the positive cone
of a basis, then it is saturated under division by a positive integer. -/
theorem mem_of_nsmul_mem_of_eq_positiveCone
    (b : Module.Basis ι ℤ M) {S : Set M} {x : M} {n : ℕ} (hn : 1 ≤ n)
    (hS : S = b.positiveCone) (hx : n • x ∈ S) :
    x ∈ S := by
  -- Rewrite the source-facing subset into the basis cone where coordinatewise positivity applies.
  have hx_cone : n • x ∈ b.positiveCone := by
    simpa [hS] using hx
  -- The basis-cone saturation theorem now gives the desired positivity of `x`.
  have hx_pos : x ∈ b.positiveCone :=
    mem_positiveCone_of_nsmul_mem_positiveCone b hn hx_cone
  simpa [hS] using hx_pos

end

end Module.Basis

namespace Representation

section ProjectivePositiveSubset

variable (A : Type u) [CommRing A]
variable (G : Type u) [Group G]

/-
Domain-style sampling:
* Primary domain: projective Grothendieck groups of finite projective `A[G]`-modules and Serre's
  source-facing positive subset inside `P₀[A](G)`.
* Relevant owner declarations inspected in this domain:
  `finiteProjectiveGroupAlgebraGrothendieckClass`,
  `projectiveEnvelope_classes_basis_of_complete_family`,
  `projectiveGrothendieckReductionEquiv`, and
  `Module.Basis.repr`.
* Best owner abstraction: the chapter owner `finiteProjectiveGroupAlgebraGrothendieckClass` on
  `P₀[A](G)`, with the basis cone only as a bridge/view used over the residue field.
* Primitive data: actual finite projective `A[G]`-modules and their canonical classes in
  `P₀[A](G)`.
* Derived API: the source-facing subset `P⁺[A](G)` and its comparison with the canonical
  projective-envelope basis cone over the residue field.
-/
/-- Serre's positive subset `P_A^+(G)`, written here as `P⁺[A](G)`, consists of the classes in
`P_A(G)` represented by actual finite projective `A[G]`-modules. -/
def projectivePositiveSubset :
    Set (P₀[A](G)) :=
  Set.range fun P : FiniteProjectiveGroupAlgebraModule A G ↦ [P]ₚ₀

scoped[Representation] notation:max "P⁺[" A "](" G ")" =>
  projectivePositiveSubset A G

/-- Membership in `P_A^+(G)` means being the class of some finite projective `A[G]`-module. -/
@[simp] theorem mem_projectivePositiveSubset_iff
    {x : P₀[A](G)} :
    x ∈ P⁺[A](G) ↔
      ∃ P : FiniteProjectiveGroupAlgebraModule A G,
        [P]ₚ₀ = x :=
  Iff.rfl

end ProjectivePositiveSubset

end Representation
