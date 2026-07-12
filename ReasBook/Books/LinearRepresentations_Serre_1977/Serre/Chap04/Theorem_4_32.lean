import LinearRepresentations_Serre_1977.Chap04.Definition_4_31
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_14

noncomputable section

open scoped MonoidAlgebra

-- Semantic recall: `lean_leansearch` and mathlib's isotypic-component API identify
-- `sSupIndep_isotypicComponents`, `sSup_isotypicComponents`, and
-- `mem_isotypicComponents_iff` as the canonical choice-free surface for the isotypic
-- decomposition.

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

/-- The canonical set/type of nonzero isotypic `ℂ[G]`-submodules of `ρ.asModule`. This is a thin
bridge around mathlib's owner `isotypicComponents ℂ[G] ρ.asModule`, expressed on the canonical
ambient `ℂ[G]`-module attached to `ρ` rather than via explicit instance plumbing on `V`. -/
abbrev isotypicComponentsSet : Set (Submodule ℂ[G] ρ.asModule) :=
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  isotypicComponents ℂ[G] V

/-- The ambient `ℂ`-submodule family underlying the canonical nonzero isotypic summands of `ρ`,
indexed by `ρ.isotypicComponentsSet`. -/
abbrev isotypicSubmoduleFamily :
    ρ.isotypicComponentsSet → Submodule ℂ V :=
  fun c ↦ (Subrepresentation.ofSubmodule' c.1 : Subrepresentation ρ).toSubmodule

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V] in
@[simp] theorem isotypicSubmoduleFamily_apply
    (c : ρ.isotypicComponentsSet) : ρ.isotypicSubmoduleFamily c =
      (Subrepresentation.ofSubmodule' c.1 : Subrepresentation ρ).toSubmodule := rfl

/-- Helper for Theorem 4-32: the owner `ℂ[G]`-module underlying `ρ` is semisimple, so the
canonical isotypic-component API may be used directly on `ρ.asModule`. -/
theorem ownerIsSemisimpleModule
    [Representation.IsContinuous ρ] :
    letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
    IsSemisimpleModule ℂ[G] V := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  -- Move from the semisimple representation instance to the owner-module formulation.
  simpa [Representation.asModule] using
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      inferInstance

/-- Helper for Theorem 4-32: finite-dimensionality over `ℂ` makes the owner `ℂ[G]`-module of `ρ`
noetherian, which is the hypothesis needed for the finite-instance on isotypic components. -/
theorem ownerIsNoetherianModule :
    letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
    IsNoetherian ℂ[G] V := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  -- Restrict the scalar-tower noetherianity result from `ℂ` to the monoid algebra owner.
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa [Representation.asModule] using
      (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  exact isNoetherian_of_tower ℂ inferInstance

/-- Helper for Theorem 4-32: the canonical family `ρ.isotypicSubmoduleFamily` is independent and
its supremum is all of `V`. This is the subtype-indexed reformulation of mathlib's owner-level
`sSupIndep_isotypicComponents` and `sSup_isotypicComponents`. -/
theorem isotypicSubmoduleFamily_iSupIndep_top
    [Representation.IsContinuous ρ] :
    iSupIndep (ρ.isotypicSubmoduleFamily) ∧ (⨆ c, ρ.isotypicSubmoduleFamily c) = ⊤ := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule ℂ[G] V := ρ.ownerIsSemisimpleModule
  -- Transport the set-indexed owner decomposition to the exact subtype family used by the theorem.
  simpa [Representation.isotypicComponentsSet, Representation.isotypicSubmoduleFamily] using
    (Representation.iSupIndep_and_iSup_top_of_subtype_ofSubmodule'_family
      (ρ := ρ)
      (s := isotypicComponents ℂ[G] V)
      (sSupIndep_isotypicComponents (R := ℂ[G]) (M := V))
      (sSup_isotypicComponents (R := ℂ[G]) (M := V)))

/-- Helper for Theorem 4-32: membership in the canonical summand index set is exactly the owner
characterization of being a nonzero fully invariant isotypic `ℂ[G]`-submodule. -/
theorem mem_isotypicComponentsSet_iff
    [Representation.IsContinuous ρ]
    {m : Submodule ℂ[G] ρ.asModule} :
    m ∈ ρ.isotypicComponentsSet ↔ IsIsotypic ℂ[G] m ∧ m.IsFullyInvariant ∧ m ≠ ⊥ := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSemisimpleModule ℂ[G] V := ρ.ownerIsSemisimpleModule
  -- Unfold only the local abbreviation, then reuse the owner-level characterization verbatim.
  simpa [Representation.asModule, Representation.isotypicComponentsSet] using
    (mem_isotypicComponents_iff (R := ℂ[G]) (M := V) (m := m))

/-- Theorem 4-32 (1): a finite-dimensional continuous complex representation `ρ` of a compact
group decomposes canonically as the internal direct sum of its nonzero isotypic subrepresentations.
Lean indexes the summands by the canonical subtype `isotypicComponents ℂ[G] V`, so the
decomposition is packaged without reference to any chosen irreducible decomposition. -/
theorem isInternal_isotypicSubrepresentations
    [Representation.IsContinuous ρ] :
    DirectSum.IsInternal (ρ.isotypicSubmoduleFamily) := by
  classical
  -- Repackage the canonical independence and spanning statements as an internal direct sum.
  rcases ρ.isotypicSubmoduleFamily_iSupIndep_top with ⟨hIndep, hTop⟩
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hTop

/-- Theorem 4-32 (2): only finitely many isotypic summands in the canonical decomposition of a
finite-dimensional continuous complex representation of a compact group are nonzero. In Lean this
is the finiteness of the canonical index type `isotypicComponents ℂ[G] V`. -/
instance finite_isotypicComponents
    [Representation.IsContinuous ρ] :
    Finite ρ.isotypicComponentsSet := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsNoetherian ℂ[G] V := ρ.ownerIsNoetherianModule
  -- Once the owner module is noetherian, mathlib supplies finiteness of isotypic components.
  simpa [Representation.isotypicComponentsSet] using
    (inferInstance : Finite (isotypicComponents ℂ[G] V))

/-- Theorem 4-32 (3): the canonical isotypic decomposition is intrinsic. Its summands are exactly
the nonzero fully invariant isotypic `ℂ[G]`-submodules of `ρ`, so they do not depend on any
initial choice of an irreducible direct-sum decomposition of `V`. -/
theorem isotypicComponents_eq_setOf_isIsotypic_isFullyInvariant_neBot
    [Representation.IsContinuous ρ] :
    ρ.isotypicComponentsSet =
      {m : Submodule ℂ[G] ρ.asModule | IsIsotypic ℂ[G] m ∧ m.IsFullyInvariant ∧ m ≠ ⊥} := by
  -- The owner-level characterization of canonical summands matches the desired set exactly.
  ext m
  exact ρ.mem_isotypicComponentsSet_iff

end

end Representation
