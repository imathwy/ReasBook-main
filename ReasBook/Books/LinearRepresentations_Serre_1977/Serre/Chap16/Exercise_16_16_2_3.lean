import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_2_3.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped MonoidAlgebra Representation
open scoped Pointwise
open CategoryTheory

namespace Representation

/-
Source/core/bridge triage:
* source-facing: the two exercise statements below about the scalar extension of a finite
  projective `Λ[G]`-module to the quotient field `F`.
* core/canonical owners: `FiniteProjectiveGroupAlgebraModule.scalarExtension`,
  `Representation.asModule`, and `leftRegular_character_eq_zero_of_ne_one`.
* bridge/view: the theorem-local support files prove the local Swan character vanishing and the
  character-to-free bridge; this target file only assembles those canonical helpers into the two
  public exercise statements.
-/

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

-- Route correction: an older target-local copy tried to reprove the p-elementary trace theorem
-- and got stuck at the tensor-regular model input.  The theorem-local support API now owns that
-- local Swan argument, so the exercise proof below reuses the support character-vanishing and
-- character-to-free lemmas directly.

-- Proof sketch: this helper packages the theorem-local local Swan argument into the exact
-- zero-off-identity form consumed by both public exercise statements below.
/-- Helper for Exercise 16-16.2-3: under the residue-characteristic hypothesis, the generic-fiber
character of the scalar extension of a finite projective group-algebra module vanishes away from
the identity element. -/
lemma scalarExtension_character_eq_zero_off_one
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    ∀ g : G, g ≠ 1 → (P.scalarExtension F).character g = 0 := by
  -- The support API supplies the localized residue-prime argument for each nonidentity element.
  intro g hg
  exact scalarExtension_character_eq_zero_of_ne_one_aux
    (Λ := Λ) (F := F) (G := G) hresidue P g hg

-- Proof sketch: rewrite complement membership in the identity singleton into the nonidentity
-- predicate used by the character-vanishing API.
omit [Finite G] in
/-- Helper for Exercise 16-16.2-3: belonging to the complement of the identity singleton is
equivalent to being different from the identity element. -/
lemma mem_singleton_compl_iff_ne_one {g : G} :
    g ∈ ({1} : Set G)ᶜ ↔ g ≠ 1 := by
  -- Reduce the set-theoretic complement of `{1}` to the corresponding inequality.
  simp

omit [Finite G] in
/-- Helper for Exercise 16-16.2-3: membership in the complement of the identity singleton is the
same as being different from the identity element. -/
lemma ne_one_of_mem_singleton_compl {g : G} (hg : g ∈ ({1} : Set G)ᶜ) : g ≠ 1 := by
  -- Consume the bidirectional complement-membership bridge in the direction needed here.
  exact (mem_singleton_compl_iff_ne_one (G := G) (g := g)).mp hg

omit [Finite G] in
/-- Helper for Exercise 16-16.2-3: being different from the identity element puts an element in
the complement of the identity singleton. -/
lemma mem_singleton_compl_of_ne_one {g : G} (hg : g ≠ 1) : g ∈ ({1} : Set G)ᶜ := by
  -- Consume the same singleton-complement bridge in the reverse direction.
  exact (mem_singleton_compl_iff_ne_one (G := G) (g := g)).mpr hg

-- Proof sketch: the zero-off-identity statement is often consumed as vanishing on the complement
-- of the identity singleton; this wrapper keeps that set-theoretic form available in this file.
/-- Helper for Exercise 16-16.2-3: the generic-fiber character vanishes on the complement of the
identity singleton. -/
lemma scalarExtension_character_eq_zero_on_singleton_compl
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    {g : G} (hg : g ∈ ({1} : Set G)ᶜ) :
    (P.scalarExtension F).character g = 0 := by
  -- Membership in the complement of `{1}` is precisely the nonidentity condition.
  exact scalarExtension_character_eq_zero_off_one
    (Λ := Λ) (F := F) (G := G) hresidue P g
    (ne_one_of_mem_singleton_compl (G := G) hg)

-- Proof sketch: some set-support arguments present the side condition as `g ∉ {1}` rather than
-- as membership in the complement; this bridge normalizes that spelling once.
/-- Helper for Exercise 16-16.2-3: the generic-fiber character vanishes at every element outside
the identity singleton. -/
lemma scalarExtension_character_eq_zero_of_not_mem_singleton
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    {g : G} (hg : g ∉ ({1} : Set G)) :
    (P.scalarExtension F).character g = 0 := by
  -- Repackage negative singleton membership as complement membership and reuse the set-form
  -- vanishing lemma.
  have hcompl : g ∈ ({1} : Set G)ᶜ := by
    simpa using hg
  exact scalarExtension_character_eq_zero_on_singleton_compl
    (Λ := Λ) (F := F) (G := G) hresidue P hcompl

-- Proof sketch: package the same vanishing statement in the standard `Set.EqOn` form, so
-- downstream character-support arguments can consume it without reopening the singleton
-- complement calculation.
/-- Helper for Exercise 16-16.2-3: the generic-fiber character agrees with the zero function on
the complement of the identity singleton. -/
lemma scalarExtension_character_eqOn_zero_singleton_compl
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    Set.EqOn (P.scalarExtension F).character (fun _ : G => 0) ({1} : Set G)ᶜ := by
  -- The pointwise `EqOn` goal is exactly the complement-vanishing helper above.
  intro g hg
  exact scalarExtension_character_eq_zero_on_singleton_compl
    (Λ := Λ) (F := F) (G := G) hresidue P hg

-- Proof sketch: the character-to-free bridge expects pointwise vanishing away from `1`; this
-- helper records the equivalent set-theoretic form used by the support argument above.
/-- Helper for Exercise 16-16.2-3: vanishing on the complement of the identity singleton is
enough to make the generic fiber free over the group algebra. -/
lemma scalarExtension_free_of_eqOn_zero_singleton_compl
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (hχ : Set.EqOn (P.scalarExtension F).character (fun _ : G => 0) ({1} : Set G)ᶜ) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  -- Convert complement-wise equality with zero into the pointwise off-identity hypothesis
  -- consumed by the character-to-free theorem.
  refine scalar_extension_free_of_character_zero_off_one
    (Λ := Λ) (F := F) (G := G) hresidue P ?_
  intro g hg
  exact hχ (mem_singleton_compl_of_ne_one (G := G) hg)

-- Proof sketch: the zero-off-identity theorem is equivalently a support-containment
-- statement for the generic-fiber character; the contradiction branch uses the vanishing
-- theorem to rule out a nonzero value away from `1`.
/-- Helper for Exercise 16-16.2-3: the support of the generic-fiber character is contained in the
identity singleton. -/
lemma scalarExtension_character_nonzero_subset_singleton
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    {g : G | (P.scalarExtension F).character g ≠ 0} ⊆ ({1} : Set G) := by
  -- A nonzero character value outside `{1}` would contradict the local Swan vanishing theorem.
  intro g hg
  by_cases hg_one : g = 1
  · simp [hg_one]
  · exact False.elim (hg
      (scalarExtension_character_eq_zero_off_one
        (Λ := Λ) (F := F) (G := G) hresidue P g hg_one))

-- Proof sketch: complete `P` at each nonzero maximal ideal whose residue characteristic is a
-- prime divisor of `|G|`, apply Swan's local theorem through the support API, and use the
-- resulting zero-off-identity character to identify the generic fiber as a free `F[G]`-module.
/-- Exercise 16-16.2-3 (1): if every prime divisor of `|G|` occurs as the residue characteristic
of some nonzero maximal ideal of the Dedekind domain `Λ`, then the scalar extension of a finite
projective `Λ[G]`-module to the quotient field `F` is free over `F[G]`. -/
theorem scalarExtension_free
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  -- The support local Swan theorem is packaged as vanishing on `{1}ᶜ`, and the named bridge
  -- converts that support statement into the free `F[G]`-basis.
  exact scalarExtension_free_of_eqOn_zero_singleton_compl
    (Λ := Λ) (F := F) (G := G) hresidue P
    (scalarExtension_character_eqOn_zero_singleton_compl
      (Λ := Λ) (F := F) (G := G) hresidue P)

-- Proof sketch: choose a residue-prime witness for a prime divisor of the order of the
-- nonidentity element and apply the localized projective-character vanishing theorem.
/-- Exercise 16-16.2-3 (2): when the scalar extension is finite-dimensional over `F`, its ordinary
character is zero on every nonidentity element of `G`. -/
theorem scalarExtension_character_eq_zero_of_ne_one
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (g : G) (hg : g ≠ 1) :
    (P.scalarExtension F).character g = 0 := by
  -- Convert the nonidentity hypothesis to negative singleton membership and use the dedicated
  -- set-support bridge.
  have hnot : g ∉ ({1} : Set G) := by
    simpa using hg
  exact scalarExtension_character_eq_zero_of_not_mem_singleton
    (Λ := Λ) (F := F) (G := G) hresidue P hnot

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
