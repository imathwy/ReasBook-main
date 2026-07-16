import Mathlib.RingTheory.DedekindDomain.Dvr
import stacks_proof.stacks_project.Chap10.Definition_10_120_14
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: Dedekind domains in commutative algebra, viewed through the source-facing
  factorization criterion and the canonical local-DVR owner;
- sampled owner declarations:
  `IsDedekindDomainByFactorization`,
  `isDedekindDomain_iff_isDedekindDomainByFactorization`,
  `IsDedekindDomainDvr`,
  `isDedekindDomain_iff`,
  `isIntegrallyClosed_iff`;
- source-facing: `IsDedekindDomainByFactorization R`;
- core/canonical: `IsDedekindDomain R` and `IsDedekindDomainDvr R`;
- bridge/view: the passages from the factorization criterion to the canonical local-DVR owner and
  to the canonical Noetherian plus dimension-`≤ 1` plus integrally-closed characterization.

Primitive data belong to the source-facing factorization owner from Definition `10.120.14`.
Noetherianity, the local DVR criterion, Krull dimension `≤ 1`, and integral closedness are
derived owner-level API, so this file should expose them by reusing the canonical owners and
their equivalence theorems rather than by publishing a new `List.TFAE` wrapper.
-/

/-- Lemma 10.120.17: the factorization criterion from Definition `10.120.14` is equivalent to the
canonical Noetherian, dimension-`≤ 1`, and integrally-closed characterization of a Dedekind
domain. This is the source-facing bridge to `isDedekindDomain_iff`. -/
@[stacks 034X]
theorem isDedekindDomainByFactorization_iff :
    IsDedekindDomainByFactorization R ↔
      IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R := by
  rw [← isDedekindDomain_iff_isDedekindDomainByFactorization R,
    isDedekindDomain_iff R (FractionRing R),
    isIntegrallyClosed_iff (FractionRing R)]

section

variable [IsDomain R]

/-- Under the ambient domain hypothesis needed to speak about `IsDedekindDomainDvr`, the
source-facing factorization criterion is equivalent to the canonical local-DVR owner. -/
theorem isDedekindDomainByFactorization_iff_isDedekindDomainDvr :
    IsDedekindDomainByFactorization R ↔ IsDedekindDomainDvr R := by
  constructor
  · intro h
    letI : IsDedekindDomain R :=
      (isDedekindDomain_iff_isDedekindDomainByFactorization R).mpr h
    infer_instance
  · intro h
    letI : IsDedekindDomainDvr R := h
    exact (isDedekindDomain_iff_isDedekindDomainByFactorization R).mp inferInstance

end

/-- A ring satisfying the factorization criterion for Dedekind domains is Noetherian. -/
theorem isNoetherianRing_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : IsNoetherianRing R := by
  obtain ⟨-, hNoetherian, -, -⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hNoetherian

/-- A ring satisfying the factorization criterion for Dedekind domains has Krull dimension at most
`1`. -/
theorem ringDimensionLEOne_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : Ring.DimensionLEOne R := by
  obtain ⟨-, -, hDimensionLEOne, -⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hDimensionLEOne

/-- A ring satisfying the factorization criterion for Dedekind domains is integrally closed. -/
theorem isIntegrallyClosed_of_isDedekindDomainByFactorization
    (h : IsDedekindDomainByFactorization R) : IsIntegrallyClosed R := by
  obtain ⟨-, -, -, hIntegrallyClosed⟩ := (isDedekindDomainByFactorization_iff R).mp h
  exact hIntegrallyClosed

end
