import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u v

namespace Algebra

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: formal smoothness of commutative algebras via surjective presentations,
  infinitesimal thickenings, and the conormal sequence;
* sampled owner declarations:
  `Algebra.FormallySmooth.iff_split_surjection`,
  `Algebra.Extension.formallySmooth_iff_split_injection`,
  `Algebra.formallySmooth_iff`,
  `Algebra.Extension.cotangentComplex`;
* best owner abstraction: `Algebra.FormallySmooth R S`, with presentation-level conditions derived
  from the canonical extension owners `P.infinitesimal` and `P.cotangentComplex`;
* primitive data: a surjective presentation `P : Extension R S`;
* derived API: a section of `P.infinitesimal.Ring → S`, a retraction of `P.cotangentComplex`,
  and the cotangent-homology characterization from `Algebra.formallySmooth_iff`.

This proposition is `source-facing`: it keeps the textbook TFAE list, but each presentation-level
condition is stated directly through the canonical owner maps rather than through parallel local
wrapper predicates.
-/

-- Proof sketch: use `Algebra.FormallySmooth.iff_split_surjection` for the infinitesimal-section
-- clauses, `Algebra.Extension.formallySmooth_iff_split_injection` for the conormal-splitting
-- clauses, and `Algebra.formallySmooth_iff` for the cotangent-complex condition.
/-- Helper for Proposition 10.138.8: the canonical polynomial presentation of `S` is formally
smooth over `R`. -/
lemma self_generators_toExtension_formallySmooth :
    FormallySmooth R ((Generators.self R S).toExtension).Ring := by
  -- The self-generators presentation is definitionally the polynomial ring `R[S]`.
  change FormallySmooth R (MvPolynomial S R)
  infer_instance

/-- Proposition 10.138.8: for a ring map `R → S`, the following are equivalent: `S` is formally
smooth over `R`; some formally smooth surjective presentation `P → S` admits a section
`P / J² → S`; every formally smooth surjective presentation `P → S` admits such a section; some
formally smooth surjective presentation has split conormal sequence
`0 → J/J² → Ω[P⁄R] ⊗[P] S → Ω[S⁄R] → 0`; every formally smooth surjective presentation has split
conormal sequence; and the naive cotangent complex `NL_{S/R}` is quasi-isomorphic to a projective
`S`-module in degree `0`, i.e. `H¹(L_{S/R}) = 0` and `Ω[S⁄R]` is projective. -/
@[stacks 031J]
theorem formallySmooth_tfae_presentation_section_conormal_sequence_projective :
    List.TFAE
      [FormallySmooth R S,
        ∃ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring ∧
            ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
              (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S,
        ∀ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring →
            ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
              (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S,
        ∃ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring ∧
            ∃ τ : P.CotangentSpace →ₗ[S] P.Cotangent,
              τ ∘ₗ P.cotangentComplex = LinearMap.id,
        ∀ P : Extension.{max u v} R S,
          FormallySmooth R P.Ring →
            ∃ τ : P.CotangentSpace →ₗ[S] P.Cotangent,
              τ ∘ₗ P.cotangentComplex = LinearMap.id,
        Subsingleton (H1Cotangent R S) ∧ Module.Projective S Ω[S⁄R]] := by
  -- Clause (6) is exactly the owner characterization of formal smoothness, with the conjunction
  -- reordered to match the statement.
  tfae_have 1 ↔ 6 := by
    simpa [and_comm] using (Algebra.formallySmooth_iff (R := R) (A := S))
  -- A formally smooth target lifts across every formally smooth presentation to the
  -- infinitesimal thickening `P / J²`.
  tfae_have 1 → 3 := by
    intro hS P hP
    letI : FormallySmooth R P.Ring := hP
    simpa using
      (Algebra.FormallySmooth.iff_split_surjection
        (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mp hS
  -- For the existential infinitesimal-section clause, use the canonical polynomial presentation.
  tfae_have 3 → 2 := by
    intro h
    let P : Extension.{max u v} R S := (Generators.self R S).toExtension
    have hP : FormallySmooth R P.Ring := by
      simpa [P] using (self_generators_toExtension_formallySmooth (R := R) (S := S))
    refine ⟨P, ?_⟩
    refine ⟨hP, ?_⟩
    exact h P hP
  -- A single infinitesimal section for one formally smooth presentation already forces formal
  -- smoothness of `S`, and then the same presentation has a split conormal sequence.
  tfae_have 2 → 4 := by
    intro h
    rcases h with ⟨P, hP, σ, hσ⟩
    letI : FormallySmooth R P.Ring := hP
    have hS : FormallySmooth R S := by
      exact
        (Algebra.FormallySmooth.iff_split_surjection
          (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr ⟨σ, hσ⟩
    refine ⟨P, hP, ?_⟩
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS
  -- Once one section exists for a fixed presentation, it recovers formal smoothness of `S`, and
  -- then the same presentation has a split conormal sequence by the owner splitting criterion.
  tfae_have 3 → 5 := by
    intro h P hP
    letI : FormallySmooth R P.Ring := hP
    have hSection :
        ∃ σ : S →ₐ[R] P.infinitesimal.Ring,
          (IsScalarTower.toAlgHom R P.infinitesimal.Ring S).comp σ = AlgHom.id R S :=
      h P hP
    have hS : FormallySmooth R S := by
      exact
        (Algebra.FormallySmooth.iff_split_surjection
          (f := IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective).mpr hSection
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mp hS
  -- Again use the canonical polynomial presentation to forget the universal quantifier.
  tfae_have 5 → 4 := by
    intro h
    let P : Extension.{max u v} R S := (Generators.self R S).toExtension
    have hP : FormallySmooth R P.Ring := by
      simpa [P] using (self_generators_toExtension_formallySmooth (R := R) (S := S))
    refine ⟨P, ?_⟩
    refine ⟨hP, ?_⟩
    exact h P hP
  -- A split conormal sequence for one formally smooth presentation is the owner criterion for
  -- formal smoothness of the target.
  tfae_have 4 → 1 := by
    intro h
    rcases h with ⟨P, hP, τ, hτ⟩
    letI : FormallySmooth R P.Ring := hP
    exact (Algebra.Extension.formallySmooth_iff_split_injection P).mpr ⟨τ, hτ⟩
  tfae_finish

end

end Algebra
