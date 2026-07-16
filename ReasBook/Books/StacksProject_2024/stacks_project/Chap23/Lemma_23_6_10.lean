import StacksProject_2024.stacks_project.Chap15.Definition_15_83_1
import StacksProject_2024.stacks_project.Chap23.Lemma_23_6_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Source/core/bridge triage:
- `source-facing`: Lemma 23.6.10 keeps the chosen surjective finite polynomial presentation
  `π₀ : R[x_i] → S` and asserts the finite-generator refinement for the resulting Tate
  resolution.
- `core/canonical`: `RingHom.IsPseudoCoherentRingMap`, `TateResolution π₀`, and
  `TateResolution.HasFiniteDegreeGenerators`.
- `bridge/view`: the actual finite-generator existence owner is
  `exists_tateResolution_with_finiteDegreeGenerators` from Lemma 23.6.9; this file first
  specializes that owner to pseudo-coherent ring maps for an arbitrary chosen polynomial
  presentation and then recovers the Stacks-facing `Fin n` statement as a thin specialization. -/

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A pseudo-coherent ring map over a Noetherian base satisfies the finite-generator refinement
for a Tate resolution of any chosen surjective polynomial presentation `π₀ : R[x_j : j ∈ J] → S`.
This is the canonical bridge from the pseudo-coherent ring-map owner to the Chapter 23 Tate
resolution existence theorem. -/
theorem exists_tateResolution_with_finiteDegreeGenerators_of_isPseudoCoherentRingMap_of_presentation
    [IsNoetherianRing R]
    [(algebraMap R S).IsPseudoCoherentRingMap]
    {J : Type u} (π₀ : MvPolynomial J R →ₐ[R] S) (hπ₀ : Function.Surjective π₀) :
    ∃ A : TateResolution π₀, A.HasFiniteDegreeGenerators := by
  exact exists_tateResolution_with_finiteDegreeGenerators π₀ hπ₀

/-- Lemma 23.6.10: if `R → S` is a pseudo-coherent ring map, then any chosen surjective finite
polynomial presentation `π₀ : R[x_i : i ∈ Fin n] → S` admits a Tate resolution whose
positive-degree generator sets are finite. -/
@[stacks 0BZ9]
theorem exists_tateResolution_with_finiteDegreeGenerators_of_isPseudoCoherentRingMap
    [IsNoetherianRing R]
    [(algebraMap R S).IsPseudoCoherentRingMap]
    {n : ℕ} (π₀ : MvPolynomial (Fin n) R →ₐ[R] S) (hπ₀ : Function.Surjective π₀) :
    ∃ A : TateResolution π₀, A.HasFiniteDegreeGenerators := by
  exact exists_tateResolution_with_finiteDegreeGenerators π₀ hπ₀

end
