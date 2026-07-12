import StacksProject_2024.Chap10.Lemma_10_127_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for finitely presented commutative ring maps and
  their stagewise base-change transitions.
* Owner declarations inspected in this domain:
  - `DirectedFiniteTypeHomApproximation`
  - `DirectedFiniteTypeHomApproximation.stageBaseChangeMap`
  - `RingHom.FinitePresentation`
* Best owner abstraction: `DirectedFiniteTypeHomApproximation f`.
* Layer triage:
  - `source-facing`: the existence theorem below
  - `core/canonical`: `DirectedFiniteTypeHomApproximation f`
  - `bridge/view`: the canonical stagewise base-change map and the stronger bijectivity condition
    on that map
* Primitive vs. derived:
  - primitive owner data: the directed system of source and target stages, transition maps,
    finite-type hypotheses, and colimit identifications
  - derived API here: the statement that the already canonical map
    `A.stageBaseChangeMap h : Sᵢ ⊗[Rᵢ] Rⱼ →+* Sⱼ` is bijective, hence an isomorphism
-/

namespace DirectedFiniteTypeHomApproximation

variable {f : R →+* S} (A : DirectedFiniteTypeHomApproximation f)

/-- The transition maps in a finite-presentation approximation identify each later target stage
with the canonical base change from an earlier one. -/
def HasBijectiveBaseChangeTransitions : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), Function.Bijective (A.stageBaseChangeMap h)

end DirectedFiniteTypeHomApproximation

-- Proof sketch: start from the finite-type approximation owner from Lemma `10.127.14`, then
-- descend a finite presentation of `S` over `R` to sufficiently large stages. Enlarging the
-- stage records finitely many generators and finitely many relations, so the target stages remain
-- finite type over the source stages, and the descended relations force each canonical
-- base-change map `S_λ ⊗[R_λ] R_μ → S_μ` to be bijective.
/-- Lemma 10.127.17: if `f : R →+* S` is of finite presentation, then `f` is the direct limit of a
directed system of ring maps `R_λ → S_λ` such that each `R_λ` is of finite type over `ℤ`, each
`S_λ` is of finite type over `R_λ`, and for every `λ ≤ μ` the canonical map
`S_λ ⊗[R_λ] R_μ → S_μ` is bijective, hence an isomorphism. -/
theorem exists_directedFinitePresentationHomApproximation (f : R →+* S)
    (hf : f.FinitePresentation) :
    ∃ A : DirectedFiniteTypeHomApproximation f, A.HasBijectiveBaseChangeTransitions := sorry
