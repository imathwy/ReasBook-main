import stacks_project.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology PrimeSpectrum
open scoped PrimeSpectrum
open Ideal.Quotient (eq_zero_iff_mem)

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: commutative algebra on `PrimeSpectrum`, zero loci, contraction ideals, and
  quotient elements;
- sampled owner declarations: `PrimeSpectrum.closure_image_comap_zeroLocus`,
  `PrimeSpectrum.zeroLocus_sup`, `PrimeSpectrum.zeroLocus_empty_iff_eq_top`,
  `stacks_project.Chap10.Definition_10_17_1`'s source-facing notation owner `V(-)`;
- source/core/bridge triage:
  * source-facing: this lemma extracts an element `r : R` from a disjointness statement on spectra;
  * core/canonical: the owner objects are `PrimeSpectrum.comap`, `PrimeSpectrum.zeroLocus`, and the
    ideal identity `I ⊔ J.comap φ = ⊤`;
  * bridge/view: `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_comap`, and quotienting the identity
    `g + r = 1` translate the ideal statement into the quotient and image conditions appearing in
    the source wording;
  * primitive data: `φ`, `I`, `J`, and the disjointness hypothesis;
  * derived API: the quotient equation and the membership condition on `φ r`, both recovered from the
    canonical ideal-top statement `I ⊔ J.comap φ = ⊤`.
-/
-- Proof sketch: by `PrimeSpectrum.closure_image_comap_zeroLocus`, the closure of the image of
-- `V(J)` in `Spec R` is `V(J.comap φ)`. Disjointness from `V(I)` then forces
-- `zeroLocus (I ⊔ J.comap φ)` to be empty, hence `I ⊔ J.comap φ = ⊤`. Writing
-- `1 = g + r` with `g ∈ I` and
-- `r ∈ J.comap φ`, the element `r` is `1` modulo `I` and its image lies in `J`.

/-- The owner-level ideal statement behind Lemma 15.9.8: disjointness of the closed subsets
`closure (comap φ '' V(J))` and `V(I)` forces the sum ideal `I ⊔ J.comap φ` to be the unit
ideal. -/
theorem sup_comap_eq_top_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    I ⊔ J.comap φ = ⊤ := by
  rw [← zeroLocus_empty_iff_eq_top, zeroLocus_sup, Set.inter_comm,
    ← closure_image_comap_zeroLocus φ J]
  simpa [Set.disjoint_iff_inter_eq_empty] using hdisj

/-- Lemma 15.9.8: if the closure of the image of `V(J)` in `Spec(R)` is disjoint from `V(I)`,
then there exists `r : R` whose image in `R ⧸ I` is `1` and whose image in `S` lies in `J`. -/
theorem exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    ∃ r : R, Ideal.Quotient.mk I r = 1 ∧ φ r ∈ J := by
  have hone : (1 : R) ∈ I ⊔ J.comap φ := by
    simpa [sup_comap_eq_top_of_disjoint_closure_image_zeroLocus φ I J hdisj]
  rcases Submodule.mem_sup.mp hone with ⟨g, hg, r, hr, hgr⟩
  refine ⟨r, ?_, Ideal.mem_comap.mp hr⟩
  simpa [map_add, map_one, eq_zero_iff_mem.mpr hg] using
    congrArg (Ideal.Quotient.mk I) hgr

end
