import StacksProject_2024.stacks_project.Chap10.Lemma_10_78_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsReduced R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: finite projective modules and the fiber-rank function on `Spec R`;
- sampled owner-style declarations of the same kind:
  `Module.Projective`,
  `Module.rankAtStalk`,
  `Module.isLocallyConstant_rankAtStalk`,
  `module_finite_projective_tfae`;
- owner abstraction: `Module.Projective R M` together with `Module.Finite R M`;
- primitive data: the reduced ring `R` and the module `M`;
- derived API: local constancy of the integer-valued fiber-rank function.

This item is a `bridge/view` lemma: under the reducedness hypothesis, it removes the extra
`Module.freeLocus R M = Set.univ` clause that appears in the owner-level TFAE from Lemma `10.78.2`.
Its public statement therefore uses the owner predicates directly, rather than parallel local
wrapper abbreviations for the same conditions.
-/

-- Proof sketch: after assuming `Module.Finite R M`, the forward implication is the local
-- constancy theorem for the rank function of a finite projective module. Conversely, over a
-- reduced ring a finite module with locally constant fiber rank is locally free on a standard-open
-- neighborhood of every prime, so Lemma `10.78.2` yields projectivity.
/-- Lemma 10.78.3: if `M` is a finite `R`-module over a reduced ring, then `M` is projective if
and only if the fiber-rank function `ρ_M : Spec(R) → ℤ`, `p ↦ dim_{κ(p)}(M ⊗[R] κ(p))`, is
locally constant. -/
theorem projective_iff_isLocallyConstant_rankAtStalk_of_finite
    (hM : Module.Finite R M) :
    Module.Projective R M ↔
      IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk M p : ℤ)) := sorry

end
