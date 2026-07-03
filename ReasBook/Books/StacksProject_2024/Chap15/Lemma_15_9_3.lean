import StacksProject_2024.Chap15.Lemma_15_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum Set TopologicalSpace

universe u v

namespace Algebra

section

variable {A : Type u} [CommRing A]
variable {ι : Type v}

/- Domain-style sampling:
* primary domain: finite pairwise disjoint open covers of prime spectra and their étale lifting
  along quotient isomorphisms;
* sampled owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `PrimeSpectrum.isIdempotentElemEquivClopens`,
  `exists_etale_idempotent_lift_of_quotient`;
* `source-facing`: a finite pairwise disjoint open cover of `Spec(A ⧸ I)` and its étale lift;
* `core/canonical`: clopen subsets of `Spec` classified by idempotents, together with the
  single-idempotent lifting theorem from Lemma `15.9.2`;
* `bridge/view`: the finite `Clopens`-valued lifting step used internally after upgrading each open
  piece of the source cover to a clopen.

Primitive data for the lifting argument: the quotient ideal `I`, a family
`Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))` on a finite index type `[Finite ι]`, and the
hypotheses that these opens form a pairwise disjoint cover. Derived API: every member of such a
cover is automatically clopen, so the lifting step can run on the corresponding finite family in
`Clopens`. The output data are the lifted étale algebra `A'`, quotient isomorphism `eIso`, and
lifted clopen family `U' : ι → Clopens (PrimeSpectrum A')`.

This file keeps the textbook finite open-cover statement as the public `source-facing` theorem and
uses the finite `Clopens`-valued lifting step only as internal bridge data. No wrapper structure is
introduced. -/

private theorem isClopen_of_isOpenCover_of_pairwise_disjoint
    {X : Type*} [TopologicalSpace X] {U : ι → Opens X} (hCover : IsOpenCover U)
    (hDisjoint : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) (j : ι) :
    IsClopen (U j : Set X) := by
  refine ⟨IsClosed.mk ?_, (U j).isOpen⟩
  have hCompl :
      (U j : Set X)ᶜ = ⋃ i ∈ {i | i ≠ j}, (U i : Set X) := by
    ext x
    constructor
    · intro hx
      have hxCover : x ∈ ⋃ i, (U i : Set X) := by
        simpa [hCover.iSup_set_eq_univ] using (Set.mem_univ x)
      rcases mem_iUnion.mp hxCover with ⟨i, hxi⟩
      have hij : i ≠ j := by
        intro hij
        subst hij
        exact hx hxi
      exact mem_iUnion₂.mpr ⟨i, hij, hxi⟩
    · intro hx hxj
      rcases mem_iUnion₂.mp hx with ⟨i, hij, hxi⟩
      exact (Set.disjoint_right.mp (hDisjoint hij) hxj) hxi
  rw [hCompl]
  exact isOpen_biUnion fun i _ ↦ (U i).isOpen

section

variable [Finite ι]

-- Internal bridge: once the finite source cover is presented by clopens, the lifting step is a
-- finite family of clopens on the same index type.
private theorem exists_etale_lift_of_finite_disjoint_clopen_cover_of_spec_quotient
    (I : Ideal A) (Ubar : ι → Clopens (PrimeSpectrum (A ⧸ I)))
    (hCover : IsOpenCover fun j ↦ (Ubar j).toOpens)
    (hDisjoint :
      Pairwise fun i j ↦ Disjoint
        (Ubar i : Set (PrimeSpectrum (A ⧸ I))) (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
      (U' : ι → Clopens (PrimeSpectrum A')),
        (IsOpenCover fun j ↦ (U' j).toOpens) ∧
          (Pairwise fun i j ↦ Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
          ∀ j,
            comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
              comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                (U' j : Set (PrimeSpectrum A')) := by
  sorry

-- Proof sketch: upgrade the finite open family `Ubar` to a `Clopens`-valued family using
-- `isClopen_of_isOpenCover_of_pairwise_disjoint`, apply the internal finite clopen-family lifting
-- theorem above, and then forget back to `Opens` in the source-facing conclusion.
/-- Lemma 15.9.3: a pairwise disjoint open cover of `Spec(A ⧸ I)` lifts, after an étale extension
`A → A'` inducing an isomorphism on the quotient by `I`, to a pairwise disjoint clopen cover of
`Spec(A')`. The source hypothesis is a finite indexed cover, exposed here by `[Finite ι]`. -/
theorem exists_etale_lift_of_finite_disjoint_open_cover_of_spec_quotient
    (I : Ideal A) (Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))) (hCover : IsOpenCover Ubar)
    (hDisjoint :
      Pairwise fun i j ↦ Disjoint
        (Ubar i : Set (PrimeSpectrum (A ⧸ I))) (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
      (U' : ι → Clopens (PrimeSpectrum A')),
        (IsOpenCover fun j ↦ (U' j).toOpens) ∧
          (Pairwise fun i j ↦ Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
          ∀ j,
            comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
              comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                (U' j : Set (PrimeSpectrum A')) := by
  let UbarClopen : ι → Clopens (PrimeSpectrum (A ⧸ I)) := fun j ↦
    Clopens.mk (Ubar j) (isClopen_of_isOpenCover_of_pairwise_disjoint hCover hDisjoint j)
  have hCoverClopen : IsOpenCover fun j ↦ (UbarClopen j).toOpens := by
    simpa [UbarClopen]
  have hDisjointClopen :
      Pairwise fun i j ↦ Disjoint
        (UbarClopen i : Set (PrimeSpectrum (A ⧸ I)))
        (UbarClopen j : Set (PrimeSpectrum (A ⧸ I))) := by
    intro i j hij
    simpa [UbarClopen] using hDisjoint hij
  obtain ⟨A', hA'Ring, hA'Alg, hA'Etale, eIso, U', hCover', hDisjoint', hcomp⟩ :=
    exists_etale_lift_of_finite_disjoint_clopen_cover_of_spec_quotient
      I UbarClopen hCoverClopen hDisjointClopen
  refine ⟨A', hA'Ring, hA'Alg, hA'Etale, eIso, U', hCover', hDisjoint', ?_⟩
  intro j
  simpa [UbarClopen] using hcomp j

end

end

end Algebra
