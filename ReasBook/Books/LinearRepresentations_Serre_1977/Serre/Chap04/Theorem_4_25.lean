import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.DirectSum.Module
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap04.Definition_4_23
import LinearRepresentations_Serre_1977.Chap04.Definition_4_31
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5

open MeasureTheory
open scoped ENNReal MonoidAlgebra Representation

noncomputable section

-- Semantic recall: the repository's canonical representation-level owner is
-- `Representation.isotypicSubrepresentation`, so this source-facing statement is recorded on the
-- `π`-isotypic component of `regularRepresentation μG` for an arbitrary irreducible `π`.

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [MeasurableMul G] [CompactSpace G]
variable {H : Type v} [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℂ H] [T2Space H] [FiniteDimensional ℂ H]

/-- Theorem 4-25 — Multiplicity in the Regular Representation.

For an irreducible finite-dimensional continuous complex representation `π`, the canonical
`π`-isotypic component of the regular representation on `L²(G)` is equivalent to the direct sum
of `Module.finrank ℂ H` copies of `π`. This source-facing theorem records only the existence of
such an equivariant decomposition; the basis-indexed bridge below exposes an explicit equivalence
surface when auxiliary matrix-coefficient data is chosen. -/
theorem regularRepresentation_piIsotypicComponent_nonempty_equiv_directSum_finrankCopies
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    Nonempty
      ((directSum fun _ : Fin (Module.finrank ℂ H) ↦ π).Equiv
        ((regularRepresentation μG).isotypicSubrepresentation π).toRepresentation) :=
  sorry

/-- Companion bridge to Theorem 4-25: once a basis of `Hom_G(π, L²(G))` is chosen and the
corresponding direct-sum evaluation map is known to be bijective, the chapter's canonical
evaluation owner packages that data as an explicit equivariant equivalence onto the
`π`-isotypic component of `regularRepresentation μG`. -/
def regularRepresentation_piIsotypicComponent_equiv_directSum_of_basis
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (b : Module.Basis (Fin (Module.finrank ℂ H)) ℂ
      (π.IntertwiningMap (regularRepresentation μG)))
    (hbij : Function.Bijective
      ((regularRepresentation μG).familyDirectSumEvaluation π b)) :
    (directSum fun _ : Fin (Module.finrank ℂ H) ↦ π).Equiv
      ((regularRepresentation μG).isotypicSubrepresentation π).toRepresentation :=
  ((regularRepresentation μG).familyDirectSumEvaluation π b).ofBijective hbij

omit [IsTopologicalAddGroup H] [ContinuousSMul ℂ H] [T2Space H] [FiniteDimensional ℂ H] in
@[simp] theorem
    regularRepresentation_piIsotypicComponent_equiv_directSum_of_basis_toIntertwiningMap
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (b : Module.Basis (Fin (Module.finrank ℂ H)) ℂ
      (π.IntertwiningMap (regularRepresentation μG)))
    (hbij : Function.Bijective
      ((regularRepresentation μG).familyDirectSumEvaluation π b)) :
    (regularRepresentation_piIsotypicComponent_equiv_directSum_of_basis π b hbij).toIntertwiningMap
      =
        (regularRepresentation μG).familyDirectSumEvaluation π b :=
  rfl

/-- Companion to Theorem 4-25: the `π`-isotypic component of `L²(G)` has complex dimension equal
to the square of the degree of `π`. -/
theorem finrank_regularRepresentation_piIsotypicComponent
    (π : Representation ℂ G H) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    Module.finrank ℂ (((regularRepresentation μG).isotypicSubrepresentation π).toSubmodule) =
      Module.finrank ℂ H ^ 2 := by
  rcases regularRepresentation_piIsotypicComponent_nonempty_equiv_directSum_finrankCopies π with
    ⟨e⟩
  calc
    Module.finrank ℂ (((regularRepresentation μG).isotypicSubrepresentation π).toSubmodule) =
        Module.finrank ℂ
          (DirectSum (Fin (Module.finrank ℂ H)) (fun _ : Fin (Module.finrank ℂ H) ↦ H)) := by
            exact e.finrank_eq.symm
    _ = Module.finrank ℂ H ^ 2 := by
      simp [Module.finrank_directSum, pow_two]

end

end Representation
