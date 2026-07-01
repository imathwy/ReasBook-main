import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {m : Ideal R} [m.IsMaximal]

/-
Domain triage:
* primary domain: length and finite-length commutative algebra for modules annihilated by a
  maximal ideal;
* core/canonical owners: `Module.IsTorsionBySet R M m` for the annihilation hypothesis and
  `IsFiniteLength R M` / `Module.length R M` for the finiteness conclusion;
* layer split: the `...of_isTorsionBySet` results are the owner-facing core statements, while the
  `...of_smul_top_eq_bot` results are textbook companions for the source hypothesis `m • M = 0`;
* primitive data vs. derived API: the only primitive data are the `R`-module structure on `M`
  and the maximal ideal `m`; the quotient-field module structure is derived canonically from the
  torsion-by-`m` owner predicate, so no wrapper structure is introduced.
-/

omit [m.IsMaximal] in
/-- The condition `m • M = 0` is equivalent to every element of `m` annihilating every element
of `M`. -/
private theorem ideal_smul_top_eq_bot_iff_isTorsionBySet :
    m • (⊤ : Submodule R M) = ⊥ ↔ Module.IsTorsionBySet R M m := by
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top,
    Module.isTorsionBySet_iff_subset_annihilator]
  rfl

theorem module_length_eq_rank_quotient_of_isTorsionBySet
    (hM : Module.IsTorsionBySet R M m) :
    let _ := hM.module
    Module.length R M = (Module.rank (R ⧸ m) M).toENat := by
  letI := Ideal.Quotient.field m
  letI := hM.module
  calc
    Module.length R M = Module.length (R ⧸ m) M :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = (Module.rank (R ⧸ m) M).toENat := Module.length_eq_rank (R ⧸ m) M

/-- Lemma 10.52.6 (1) in textbook form: if `m • M = 0`, then the length of `M` as an
`R`-module agrees with its dimension over the field `R ⧸ m`. -/
theorem module_length_eq_rank_quotient_of_smul_top_eq_bot
    (h : m • (⊤ : Submodule R M) = ⊥) :
    let _ := (ideal_smul_top_eq_bot_iff_isTorsionBySet.mp h).module
    Module.length R M = (Module.rank (R ⧸ m) M).toENat := by
  let hM : Module.IsTorsionBySet R M m := ideal_smul_top_eq_bot_iff_isTorsionBySet.mp h
  exact module_length_eq_rank_quotient_of_isTorsionBySet hM

/-- Owner-level form of Lemma 10.52.6 (2): under the canonical hypothesis
`Module.IsTorsionBySet R M m`, finite length over `R` is equivalent to finite generation. -/
theorem isFiniteLength_iff_finite_of_isTorsionBySet
    (hM : Module.IsTorsionBySet R M m) :
    IsFiniteLength R M ↔ Module.Finite R M := by
  letI := Ideal.Quotient.field m
  letI := hM.module
  have hlen : Module.length R M = (Module.rank (R ⧸ m) M).toENat := by
    simpa using module_length_eq_rank_quotient_of_isTorsionBySet hM
  rw [← Module.length_ne_top_iff, ← lt_top_iff_ne_top, hlen, Cardinal.toENat_lt_top,
    Module.rank_lt_aleph0_iff]
  constructor
  · intro h
    letI := h
    exact Module.Finite.trans (R ⧸ m) M
  · intro h
    letI := h
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ m) M

/-- Textbook form of Lemma 10.52.6 (2): if `m • M = 0`, then `M` has finite length over `R`
if and only if it is a finite `R`-module. -/
theorem isFiniteLength_iff_finite_of_smul_top_eq_bot
    (h : m • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M ↔ Module.Finite R M := by
  exact isFiniteLength_iff_finite_of_isTorsionBySet
    (ideal_smul_top_eq_bot_iff_isTorsionBySet.mp h)

/-- Lemma 10.52.6 (2) in textbook form: if `m • M = 0`, then `M` has finite length over `R`
if and only if it is a finite `R`-module. -/
theorem module_length_lt_top_iff_finite_of_smul_top_eq_bot
    (h : m • (⊤ : Submodule R M) = ⊥) :
    Module.length R M < ⊤ ↔ Module.Finite R M := by
  simpa [Module.length_ne_top_iff, lt_top_iff_ne_top] using
    isFiniteLength_iff_finite_of_smul_top_eq_bot h

end Length
