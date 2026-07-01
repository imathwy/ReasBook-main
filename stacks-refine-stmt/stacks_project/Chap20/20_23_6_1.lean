import Mathlib
import stacks_project.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Item 20.23.6.1:
- primary domain: explicit Čech-cochain homotopies on tuple-indexed ordinary Čech terms;
- sampled owner API:
  `cechIntersection`,
  `cechTerm`,
  `cechComplexFunctor`,
  `orderedCechComplexOfOrder`;
- best owner abstraction for this item: the tuplewise Čech owner layer from `Lemma_20_9_3`,
  especially `cechIntersection` and `cechTerm`, together with the canonical `Fin.predAbove`
  repetition map; this file is only the repeated-entry bridge used by the first homotopy formula,
  not a second owner for Čech complexes.

Source/core/bridge triage:
- `source-facing`: `cechFirstHomotopyToFun`;
- `core/canonical`: `cechIntersection`, `cechTerm`, and `cechComplexFunctor 𝒰`;
- `bridge/view`: `cechIntersection_comp_predAbove_eq` and `cechDuplicateTransport`.

Primitive data versus derived API:
- primitive data: an ordinary Čech tuple `σ`, a repeated position `a`, the canonical repetition
  map `a.predAbove`, and the sign/permutation datum `σₐ`;
- derived API: the equality of Čech intersections after repetition, the induced transport on
  section groups, and the first homotopy formula. -/

-- Proof sketch: repeating one entry in the tuple does not change the infimum of the associated
-- family of opens.
/-- Repeating one entry in a finite Čech tuple does not change the corresponding intersection. -/
theorem cechIntersection_comp_predAbove_eq (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    cechIntersection 𝒰 (σ ∘ a.predAbove) = cechIntersection 𝒰 σ := sorry

/-- Transport of sections along the equality obtained by repeating one entry of a Čech tuple. -/
abbrev cechDuplicateTransport (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : Fin (p + 1) → ι) (a : Fin (p + 1)) :
    F.obj (op (cechIntersection 𝒰 (σ ∘ a.predAbove))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (eqToHom (cechIntersection_comp_predAbove_eq 𝒰 σ a).symm).op

/-- 20.23.6.1: the first homotopy on ordinary Čech cochains is the alternating sum over
`0 ≤ a ≤ p`, with coefficient `(-1)^a sign(σ_a)`, obtained by evaluating the cochain on the
canonical tuple with the `a`th entry repeated and transporting back to the original Čech
intersection. -/
def cechFirstHomotopyToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v})
    (σₐ : ∀ {p : ℕ}, (Fin (p + 1) → ι) → Fin (p + 1) → Equiv.Perm (Fin (p + 1)))
    (p : ℕ) : cechTerm 𝒰 F (p + 1) → cechTerm 𝒰 F p :=
  fun s I ↦
    ∑ a : Fin (p + 1),
      (((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (σₐ I a)) •
        cechDuplicateTransport 𝒰 F I a (s (I ∘ a.predAbove))

/-- Evaluating the first Čech homotopy gives the alternating sum in its defining formula. -/
@[simp] theorem cechFirstHomotopyToFun_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v})
    (σₐ : ∀ {p : ℕ}, (Fin (p + 1) → ι) → Fin (p + 1) → Equiv.Perm (Fin (p + 1)))
    (p : ℕ) (s : cechTerm 𝒰 F (p + 1)) (I : Fin (p + 1) → ι) :
    cechFirstHomotopyToFun 𝒰 F σₐ p s I =
      ∑ a : Fin (p + 1),
        (((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (σₐ I a)) •
          cechDuplicateTransport 𝒰 F I a (s (I ∘ a.predAbove)) :=
  rfl
