import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

local notation "CompletionMap(" A ")" =>
  algebraMap A (AdicCompletion (maximalIdeal A) A)

/- Domain-style sampling for Remark 23.9.3:
- primary domain: formal fibers of maximal-ideal completions of Noetherian local rings and their
  local-complete-intersection property;
- sampled owner declarations:
  `RingHom.HasLocalCompleteIntersectionFibers`,
  `IsLocalCompleteIntersection`,
  `AdicCompletion`,
  `maximalIdeal`;
- best owner abstraction: the completion-map predicate
  `RingHom.HasLocalCompleteIntersectionFibers (A → AdicCompletion (maximalIdeal A) A)`, which for
  a local ring is exactly the source statement that its formal fibers are local complete
  intersections;
- source/core/bridge triage:
  - `source-facing`: the remark's warning that a Noetherian local ring need not have local
    complete-intersection formal fibers;
  - `core/canonical`: the completion ring and the completion-map fiber predicate
    `RingHom.HasLocalCompleteIntersectionFibers`;
  - `bridge/view`: the existential counterexample and the negated universal statement phrased
    through the same completion-map predicate.

Semantic search note: `lean_leansearch` is unavailable in this agent environment, so the owner/API
choice was checked directly against repository declarations via `rg`.
-/

/- Remark 23.9.3: in general, a Noetherian local ring need not have local complete-intersection
formal fibers. Hence one should not expect a naive notion of local complete intersection
homomorphism for arbitrary Noetherian rings built only from completion maps and their formal
fibers. -/
@[stacks 09QC]
theorem localCompleteIntersectionFormalFibers_not_in_general :
    ¬ ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      RingHom.HasLocalCompleteIntersectionFibers (CompletionMap(A)) := by
  have hcounterexample :
      ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A),
        ¬ RingHom.HasLocalCompleteIntersectionFibers (CompletionMap(A)) := by
    sorry
  rintro h
  rcases hcounterexample with
    ⟨A, hACommRing, hALocal, hANoetherian, hA⟩
  letI : CommRing A := hACommRing
  letI : IsLocalRing A := hALocal
  letI : IsNoetherianRing A := hANoetherian
  exact hA (h A)

end
