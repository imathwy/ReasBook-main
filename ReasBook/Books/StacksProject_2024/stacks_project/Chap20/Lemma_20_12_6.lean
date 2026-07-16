import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/-- An open subset is a union of finite Čech intersections of the family `𝒰`. -/
def IsUnionOfFiniteCechIntersections (𝒰 : ι → Opens X) (U' : Opens X) : Prop :=
  ∃ (κ : Type v) (s : κ → Σ n : ℕ, Fin (n + 1) → ι),
    U' = iSup fun k ↦ cechIntersection 𝒰 (s k).2

/-- A union of finite Čech intersections of `𝒰` is contained in the union of the cover members. -/
theorem IsUnionOfFiniteCechIntersections.le_iSup
    {𝒰 : ι → Opens X} {U' : Opens X} (hU' : IsUnionOfFiniteCechIntersections 𝒰 U') :
    U' ≤ iSup 𝒰 := by
  rcases hU' with ⟨κ, s, rfl⟩
  refine iSup_le fun k ↦ ?_
  rcases s k with ⟨n, σ⟩
  simpa using cechIntersection_le_of_iSup_eq (iSup 𝒰) 𝒰 rfl σ

/- Domain-style sampling for Lemma 20.12.6:
- primary domain: Čech cohomology of sheaves of abelian groups on a topological space;
- sampled owner declarations:
  `cechIntersection`,
  `cechIntersection_le_of_iSup_eq`,
  `cechComplexFunctor`,
  `Presheaf.isFlasque_iff_restriction_surjective`;
- best owner abstraction: the Čech objects are already owned by `cechIntersection` and
  `cechComplexFunctor`; the auxiliary source-facing notion is the intrinsic open subset
  `U'` satisfying `IsUnionOfFiniteCechIntersections 𝒰 U'`, not a chosen indexing family of Čech
  tuples;
- primitive data: the cover `𝒰`, the intrinsic open `U'` satisfying
  `IsUnionOfFiniteCechIntersections 𝒰 U'`, and the sheaf `ℱ`;
- derived API: the predicate `IsUnionOfFiniteCechIntersections 𝒰 U'` and its canonical inclusion
  `hU'.le_iSup : U' ≤ iSup 𝒰`, whose witness family of finite Čech multi-indices remains
  implementation detail rather than part of the main theorem surface.

Source/core/bridge triage:
- `source-facing`: the surjectivity hypothesis for every intrinsic open `U'` that is a union of
  finite intersections of the cover, and the resulting vanishing of positive Čech cohomology;
- `core/canonical`: `cechIntersection`, `cechIntersection_le_of_iSup_eq`, and
  `((cechComplexFunctor 𝒰).obj ℱ.presheaf).homology p`;
- `bridge/view`: the predicate `IsUnionOfFiniteCechIntersections`, which hides the chosen witness
  family of finite Čech multi-indices behind the intrinsic open subset `U'`.
-/

-- Proof sketch: follow the textbook reduction to a flasque sheaf on the auxiliary space of
-- nonempty subsets of the index set. The surjectivity hypothesis exactly gives flasqueness of the
-- transported sheaf there, its Čech complex for the basic cover agrees with the Čech complex of
-- `(𝒰, ℱ)`, and Lemma `20.12.3` then forces the positive-degree Čech cohomology to vanish.
/-- Lemma 20.12.6: if every restriction map from `ℱ(⋃ᵢ Uᵢ)` to an arbitrary union of finite
intersections of the covering opens is surjective, then the positive-degree Čech cohomology of
the covering with coefficients in `ℱ` vanishes. -/
@[stacks 0A36]
theorem cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections
    (𝒰 : ι → Opens X)
    (ℱ : X.Sheaf AddCommGrpCat.{max u v})
    (hres : ∀ ⦃U' : Opens X⦄ (hU'fin : IsUnionOfFiniteCechIntersections 𝒰 U'),
      Function.Surjective
        (ℱ.presheaf.map (homOfLE hU'fin.le_iSup).op))
    (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor 𝒰).obj ℱ.presheaf).homology p) := sorry

/-- Typeclass form of the positive-degree Čech-acyclicity supplied by
`cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections`. -/
instance instIsZeroCechCohomologyOfSurjectiveRestrictionsToUnionsOfFiniteIntersections
    (𝒰 : ι → Opens X)
    (ℱ : X.Sheaf AddCommGrpCat.{max u v})
    (hres : ∀ ⦃U' : Opens X⦄ (hU'fin : IsUnionOfFiniteCechIntersections 𝒰 U'),
      Function.Surjective
        (ℱ.presheaf.map (homOfLE hU'fin.le_iSup).op))
    (p : ℕ) [Fact (0 < p)] :
    IsZero (((cechComplexFunctor 𝒰).obj ℱ.presheaf).homology p) :=
  cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections
    𝒰 ℱ hres p Fact.out
