import StacksProject_2024.stacks_project.Chap10.Definition_10_54_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for local ring homomorphisms in commutative
  algebra.
* Owner declarations inspected in this domain:
  - `RingHom.EssFiniteType`
  - `DirectedRingColimit`
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.targetStageBaseChange`
  - `DirectedLocalHomApproximation.stageBaseChangeMap`
* Best owner abstractions:
  - source-facing approximation owner: `DirectedLocalHomApproximation f`
  - essentially finite type owner: `RingHom.EssFiniteType`
* Primitive vs. derived: the stage rings, local transition maps, colimit identifications, and
  essential finite type hypotheses already belong to the owner abstraction from
  `Lemma_10_127_9`; this lemma adds only the transition property that those canonical base-change
  maps are localizations of quotients.
-/

namespace DirectedLocalHomApproximation

/-- The transition maps in a directed local approximation present each later target stage as a
localization of a quotient of the corresponding base change from an earlier stage. -/
def HasLocalizationOfQuotientTransitions {f : R →+* S}
    (A : DirectedLocalHomApproximation f) : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), RingHom.IsLocalizationOfQuotient (A.stageBaseChangeMap h)

end DirectedLocalHomApproximation

variable (f : R →+* S) [IsLocalHom f]

-- Proof sketch: start from the canonical owner object `DirectedLocalHomApproximation f` from
-- Lemma `10.127.9`, choosing stages by finite local `ℤ`-subalgebras of
-- `R` and compatible essentially finite type local subalgebras of `S`. Arrange the transition
-- maps so that after base change, each later target stage is obtained from the earlier one by a
-- quotient followed by localization.
/-- Lemma 10.127.10: a local homomorphism `R → S` that is essentially of finite type is the
pointwise colimit of a directed system of local ring maps `R_λ → S_λ` such that each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type over `R_λ`, and for
every transition `λ ≤ μ` the canonical map `S_λ ⊗[R_λ] R_μ → S_μ` presents `S_μ` as a
localization of a quotient. -/
theorem exists_directed_local_essFiniteType_approximation (hf : f.EssFiniteType) :
    ∃ A : DirectedLocalHomApproximation f,
      A.HasLocalizationOfQuotientTransitions := sorry

end
