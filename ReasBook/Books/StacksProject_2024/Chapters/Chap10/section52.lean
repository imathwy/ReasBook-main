import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_52_1 (from Chap10) -/
universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
* primary domain: module length and finite-length module theory over a ring;
* sampled owner API: `Module.length`, `Module.length_eq_coheight`,
  `Module.length_ne_top_iff`, and `Module.length_compositionSeries`;
* core/canonical owner: `Module.length R M`;
* layer split: the source-facing numerical invariant `length_R(M)` is the owner itself, while the
  coheight formula and finite-length criteria are derived API.
-/

/- Definition 10.52.1: for an `R`-module `M`, the Stacks-project length `length_R(M)` is the
canonical mathlib invariant `Module.length R M`. Mathlib defines this as the Krull dimension of
the lattice `Submodule R M`, packaging the textbook supremum over strict chains of submodules. -/
recall Module.length

/- Companion recall: the source formula
`sup {n | ∃ 0 = M₀ ⊂ M₁ ⊂ ⋯ ⊂ Mₙ = M}`
is the order-theoretic statement that `Module.length R M` is the coheight of `⊥` in
`Submodule R M`. -/
recall Module.length_eq_coheight

end Length

/-! ### Lemma_10_52_2 (from Chap10) -/
universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: finite-length modules and module length over a ring;
* sampled owner API: `Module.length`, `Module.length_ne_top_iff`,
  `isFiniteLength_iff_isNoetherian_isArtinian`, and `IsNoetherian.finite`;
* core/canonical owner: `IsFiniteLength R M`;
* layer split: the hypothesis `Module.length R M < ⊤` is the source-facing formulation,
  `IsFiniteLength R M` is the owner abstraction, and `Module.Finite R M` is derived API via the
  Noetherian half of the owner theorem.
-/

/- Owner bridge: finite module length is canonically expressed by `IsFiniteLength R M`. -/
recall Module.length_ne_top_iff

/-- Lemma 10.52.2: if `Module.length R M < ⊤`, then `M` is a finite `R`-module. This is the
Stacks-project formulation; the equivalent owner predicate in mathlib is `IsFiniteLength R M`. -/
theorem module_finite_of_length_lt_top (h : Module.length R M < ⊤) : Module.Finite R M := by
  have hFiniteLength : IsFiniteLength R M := Module.length_ne_top_iff.mp h.ne
  have hNoetherian : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hFiniteLength).1
  letI : IsNoetherian R M := hNoetherian
  exact Module.IsNoetherian.finite R M

end Length

/-! ### Lemma_10_52_3 (from Chap10) -/
/- Lemma 10.52.3: if `0 → M' → M → M'' → 0` is a short exact sequence of `R`-modules, then the
length of `M` is the sum of the lengths of `M'` and `M''`. This is exactly the canonical theorem
`Module.length_eq_add_of_exact`. -/
recall Module.length_eq_add_of_exact

/-! ### Lemma_10_52_4 (from Chap10) -/
open IsLocalRing

universe u v

section Length

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [IsLocalRing R]

/- Domain triage:
- primary domain: finite-length modules over a local ring, with the owner abstractions
  `IsFiniteLength R M`, `IsArtinian R M`, the canonical ideal `maximalIdeal R`, and Nakayama's
  lemma for finitely generated submodules;
- primitive data: the local ring `R`, the module `M`, and the finite-length hypothesis `hM`;
- derived API: the descending chain `((maximalIdeal R)^n) • ⊤` and the eventual vanishing claim. -/

-- Proof sketch: finite module length implies that `M` is Artinian, so the descending chain
-- `⊤ ≥ maximalIdeal R • ⊤ ≥ (maximalIdeal R)^2 • ⊤ ≥ ⋯` stabilizes. If the stable term were
-- nonzero, Nakayama's lemma over the local ring `R` would force it to vanish, a contradiction.
/-- Lemma 10.52.4: if an `R`-module over a local ring has finite length, then some power of the
maximal ideal annihilates it. -/
theorem exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength
    (hM : IsFiniteLength R M) :
    ∃ n : ℕ, ((maximalIdeal R) ^ n) • (⊤ : Submodule R M) = ⊥ := by
  obtain ⟨hNoeth, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  haveI : IsNoetherian R M := hNoeth
  haveI : IsArtinian R M := hArt
  let powers : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ (((maximalIdeal R) ^ n) • (⊤ : Submodule R M) : Submodule R M), fun _ _ h ↦
      Submodule.pow_smul_top_le (maximalIdeal R) M h⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes powers
  have hEq : ((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M) =
      maximalIdeal R • (((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M)) := by
    calc
      ((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M) =
          ((maximalIdeal R) ^ (n + 1) : Ideal R) • (⊤ : Submodule R M) := by
            simpa using hn (n + 1) n.le_succ
      _ = maximalIdeal R • (((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M)) := by
            rw [pow_succ', mul_smul]
  refine ⟨n, ?_⟩
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
    (IsNoetherian.noetherian _) hEq.le (IsLocalRing.maximalIdeal_le_jacobson _)

end Length

/-! ### Lemma_10_52_5 (from Chap10) -/
universe u v w

section Length

open Order

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [Ring S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable [Module R M] [IsScalarTower R S M]

namespace Module

/-- Lemma 10.52.5 (1), in the canonical library-facing scalar-tower form: if an `S`-module `M`
is also an `R`-module compatibly with `R → S`, then the length of `M` over `R` is at least its
length over `S`. Specializing to the induced `R`-module structure recovers the Stacks-project
statement for restriction of scalars along `R → S`. -/
-- Proof sketch: every chain of `S`-submodules of `M` is also a chain of `R`-submodules, so the
-- Krull dimension of `Submodule S M` is bounded above by that of `Submodule R M`.
theorem length_le_restrictScalars : length S M ≤ length R M := by
  let e := Submodule.restrictScalarsEmbedding R S M
  simpa [length_eq_height] using height_le_height_apply_of_strictMono e e.strictMono ⊤

end Module

/- Lemma 10.52.5 (2), in the same scalar-tower form: if `algebraMap R S` is surjective, then the
length of `M` is unchanged when passing between the compatible `R`- and `S`-module structures.
Specializing to the induced `R`-module structure recovers the Stacks-project statement. This is
exactly the canonical theorem `Module.length_eq_of_surjective`. -/
#check (Module.length_eq_of_surjective :
  Function.Surjective (algebraMap R S) → Module.length R M = Module.length S M)

end Length

/-! ### Lemma_10_52_6 (from Chap10) -/
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

/-! ### Lemma_10_52_7 (from Chap10) -/
universe u v

section Length

open Order Submodule

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: `Submodule.localized'gi` is the canonical Galois insertion between submodules of
-- `M` and submodules of `LocalizedModule S M`. Its upper adjoint is strictly monotone, so the
-- coheight of `⊥` in the localized submodule lattice is bounded by the coheight of its inverse
-- image in `Submodule R M`, which is in turn bounded by the coheight of `⊥`.
/-- Lemma 10.52.7: localizing an `R`-module at a multiplicative subset does not increase its
length. -/
theorem length_localizedModule_le :
    Module.length (Localization S) (LocalizedModule S M) ≤ Module.length R M := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  let u : Submodule (Localization S) (LocalizedModule S M) → Submodule R M :=
    comap (LocalizedModule.mkLinearMap S M) ∘ restrictScalars R
  have hu : StrictMono u := by
    simpa [u] using
      (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).strictMono_u
  calc
    coheight (⊥ : Submodule (Localization S) (LocalizedModule S M)) ≤ coheight (u ⊥) := by
      simpa [u] using
        coheight_le_coheight_apply_of_strictMono u hu
          (⊥ : Submodule (Localization S) (LocalizedModule S M))
    _ ≤ coheight (⊥ : Submodule R M) := coheight_anti bot_le

end Length

/-! ### Lemma_10_52_8 (from Chap10) -/
universe u v

section Length

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (m : Ideal R) [m.IsMaximal] [Module.Finite R M]

private theorem isFiniteLength_of_pow_smul_eq_bot_aux
    (hfg : m.FG) :
    ∀ {n : ℕ}, (m ^ n) • (⊤ : Submodule R M) = ⊥ → IsFiniteLength R M := by
  intro n
  induction n generalizing M with
  | zero =>
      intro hpow
      have htop : (⊤ : Submodule R M) = ⊥ := by simpa using hpow
      haveI : Subsingleton M := by
        have hsub : Subsingleton (Submodule R M) :=
          subsingleton_of_bot_eq_top <| by simpa [eq_comm] using htop
        exact (Submodule.subsingleton_iff R).mp hsub
      exact .of_subsingleton
  | succ n ih =>
      intro hpow
      let N : Submodule R M := (m ^ n) • (⊤ : Submodule R M)
      have hNfg : N.FG := by
        have htopfg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
        dsimp [N]
        exact Submodule.FG.smul (Ideal.FG.pow hfg) htopfg
      letI : Module.Finite R N := .of_fg_top ((Submodule.fg_top N).2 hNfg)
      have hsmulN : m • N = (⊥ : Submodule R M) := by
        dsimp [N]
        simpa [pow_succ', mul_smul] using hpow
      have hNtors : Module.IsTorsionBySet R N m := by
        intro x a
        apply Subtype.ext
        have hx : (a : R) • (x : M) ∈ m • N := Submodule.smul_mem_smul a.2 x.2
        have hx0 : (a : R) • (x : M) ∈ (⊥ : Submodule R M) := by
          simpa [hsmulN] using hx
        simpa using hx0
      have hN : IsFiniteLength R N := by
        exact (isFiniteLength_iff_finite_of_isTorsionBySet hNtors).2 inferInstance
      have hQpow : (m ^ n) • (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        have hQann : m ^ n ≤ Module.annihilator R (M ⧸ N) := by
          exact (Module.isTorsionBySet_iff_subset_annihilator R (M ⧸ N)).mp <| by
            rw [Module.isTorsionBySet_quotient_iff]
            intro x r hr
            change r • x ∈ N
            exact Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R M) by simp)
        refine (Submodule.le_annihilator_iff).mp ?_
        simpa [Submodule.annihilator_top] using hQann
      have hQ : IsFiniteLength R (M ⧸ N) := ih hQpow
      rw [isFiniteLength_iff_isNoetherian_isArtinian]
      exact ⟨(isNoetherian_iff_submodule_quotient N).mpr
          ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1,
            (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1⟩,
        (isArtinian_iff_submodule_quotient N).mpr
          ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2,
            (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).2⟩⟩

-- Proof sketch: use the finite filtration
-- `⊥ = m ^ n • ⊤ ⊆ m ^ (n - 1) • ⊤ ⊆ ⋯ ⊆ m • ⊤ ⊆ ⊤`. Since `m` is finitely generated and `M` is
-- finite, every submodule `m ^ i • ⊤` is finite, so each successive quotient is a finite module
-- annihilated by `m`; apply Lemma 10.52.6 to those quotients, then add the lengths with Lemma
-- 10.52.3.
/-
The owner abstraction for finite module length in mathlib is `IsFiniteLength R M`; the textbook
formulation `Module.length R M < ⊤` is the corresponding numerical specialization.
-/
/-- Lemma 10.52.8: if `m` is a finitely generated maximal ideal and a finite `R`-module `M` is
killed by a power of `m`, then `M` has finite length. This is the owner-level form of the
textbook statement `Module.length R M < ⊤`. -/
theorem isFiniteLength_of_pow_smul_eq_bot
    (hfg : m.FG) {n : ℕ} (hpow : (m ^ n) • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := by
  exact isFiniteLength_of_pow_smul_eq_bot_aux m hfg hpow

end Length

/-! ### Definition_10_52_9 (from Chap10) -/
universe u v

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: the textbook definition says a simple `R`-module has no nontrivial submodules.
- `core/canonical`: mathlib owns this notion as `IsSimpleModule R M`.
- `bridge/view`: the final theorem restates the owner class in the source wording
  `Nontrivial M ∧ ∀ N, N = ⊥ ∨ N = ⊤`.
- Primitive data vs derived API: there is no extra source-defined data here; the owner notion is
  primitive, and the source-text characterization is derived from `isSimpleModule_iff`.
-/

/- Definition 10.52.9: for an `R`-module `M`, the canonical mathlib notion of a simple module is
`IsSimpleModule R M`, expressing that `M` has no nontrivial submodules. -/
#check IsSimpleModule R M

/- Companion recall: the canonical structural form of simplicity is that the lattice
`Submodule R M` is a simple order. -/
recall isSimpleModule_iff

-- This is the source-text reformulation of `isSimpleModule_iff`, reduced to the standard
-- order-theoretic characterization `isSimpleOrder_iff` and the canonical equivalence
-- `Submodule.nontrivial_iff`.
/-- A module is simple exactly when it is nontrivial and every submodule is either `⊥` or `⊤`. -/
theorem isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top :
    IsSimpleModule R M ↔ Nontrivial M ∧ ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤ := by
  rw [isSimpleModule_iff, isSimpleOrder_iff, Submodule.nontrivial_iff]

/-! ### Lemma_10_52_10 (from Chap10) -/
universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: the lemma packages the textbook equivalence between simplicity, length `1`,
  and being a quotient by a maximal ideal.
- `core/canonical`: the owner abstraction is mathlib's `IsSimpleModule R M`.
- `bridge/view`: this file's theorem is the TFAE packaging of the two canonical characterizations
  `Module.length_eq_one_iff` and `isSimpleModule_iff_quot_maximal`.
- Primitive data vs derived API: there is no extra primitive data here beyond the owner notion;
  the length-one and quotient-by-a-maximal-ideal clauses are derived API.
-/
/-- Lemma 10.52.10: for an `R`-module `M`, the following are equivalent: `M` is simple,
`Module.length R M = 1`, and `M` is linearly isomorphic to `R ⧸ m` for some maximal ideal
`m` of `R`. -/
theorem isSimpleModule_tfae_length_eq_one_quotient_maximal :
    List.TFAE
      [IsSimpleModule R M,
        Module.length R M = 1,
        ∃ m : Ideal R, m.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ m)] := by
  tfae_have 1 ↔ 2 := Module.length_eq_one_iff.symm
  tfae_have 1 ↔ 3 := isSimpleModule_iff_quot_maximal
  tfae_finish

end Length

/-! ### Lemma_10_52_11 (from Chap10) -/
universe u v

section Length

open LocalizedModule

local notation "AtPrime" => LocalizedModule.AtPrime

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: finite-length modules and composition series of submodules;
- sampled owner API:
  `JordanHolderModule.instJordanHolderLattice`,
  `Module.length_compositionSeries`,
  `covBy_iff_quot_is_simple`,
  `IsSimpleModule.annihilator_isMaximal`;
- core/canonical owner: `CompositionSeries (Submodule R M)`;
- layer split: the quotient module `s.factor i` is a short reusable view of the owner quotient
  attached to the cover `s.step i`, while simplicity, annihilator, and localization statements are
  derived API.
-/

/- Lemma 10.52.11: for a maximal chain of submodules from `0` to `M`, the number of strict
inclusions is the length of `M`. This is exactly the canonical theorem
`Module.length_compositionSeries`. -/
recall Module.length_compositionSeries

namespace CompositionSeries

/-- The `i`-th successive quotient in a composition series of submodules. -/
abbrev factor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

-- Proof sketch: the step relation in a composition series says `s (Fin.castSucc i)` is maximal in
-- `s (Fin.succ i)`, and `covBy_iff_quot_is_simple` identifies such maximal submodule quotients with
-- simple modules.
/-- Each successive quotient in the chosen maximal chain is a simple `R`-module. -/
theorem factor_isSimpleModule (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (s.factor i) := by
  simpa [factor] using
    (covBy_iff_quot_is_simple (CovBy.le (s.step i))).mp (s.step i)

-- Proof sketch: apply clause (1) to see that the factor is simple. Over a commutative ring, a
-- simple module is canonically a quotient by its annihilator ideal, and that annihilator is
-- maximal.
/-- The annihilator of each successive factor is a maximal ideal. -/
theorem factor_annihilator_isMaximal (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (Module.annihilator R (s.factor i)).IsMaximal := by
  let _ : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  exact IsSimpleModule.annihilator_isMaximal

/-- Each successive factor is linearly isomorphic to the quotient of `R` by its annihilator. -/
theorem factor_isomorphic_quotient_annihilator
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nonempty (s.factor i ≃ₗ[R] R ⧸ Module.annihilator R (s.factor i)) := by
  have hsimple : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  obtain ⟨I, _, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hAnn : Module.annihilator R (s.factor i) = I := by
    rw [e.annihilator_eq, I.annihilator_quotient]
  exact ⟨e.trans <| Submodule.quotEquivOfEq _ _ hAnn.symm⟩

-- Proof sketch: localize the composition series at `m`; exactness of localization turns the
-- successive quotients into the localizations of the factors, and the localized factor is nonzero
-- exactly when the corresponding simple factor has annihilator `m`.
/-- For a maximal ideal `m`, the number of successive quotients whose annihilator is `m` is the
length of the localization of `M` at `m`. -/
theorem factor_count_eq_length_localizedModule
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (m : Ideal R) [m.IsMaximal] :
    ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m } =
      Module.length (Localization.AtPrime m) (AtPrime m M) := sorry

end CompositionSeries

end Length

/-! ### Lemma_10_52_12 (from Chap10) -/
open scoped BigOperators
open IsLocalRing LocalizedModule

universe u v w

noncomputable section

section Length

local notation "AtPrime" => LocalizedModule.AtPrime

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [Finite (MaximalSpectrum B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-
Domain triage:
* primary domain: finite-length modules over a semilocal algebra, decomposed by maximal ideals and
  the corresponding residue-field extensions;
* sampled owner API:
  `CompositionSeries.factor_count_eq_length_localizedModule`,
  `module_length_eq_rank_quotient_of_isTorsionBySet`,
  `Module.length_eq_add_of_exact`,
  `Module.length_ne_top_iff`;
* source-facing layer: the semilocal localization formula and its finite-length corollary;
* core/canonical owners: `CompositionSeries (Submodule B M)` for the localized factor counts and
  `IsFiniteLength` / `Module.IsTorsionBySet` for finite-length and residue-field computations;
* bridge/view: this file keeps the source-facing sum formula while routing its local simple-factor
  terms through the owner statements from `10.52.11` and `10.52.6` instead of duplicating those
  lower-level APIs.
-/

section ResidueFieldData

variable
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)

private abbrev residueFieldModule (m : MaximalSpectrum B) :
    Module κA (Ideal.ResidueField m.asIdeal) :=
  ((Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra).toModule

variable
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))

/-- Helper for Lemma 10.52.12: the maximal ideal attached to a simple factor in a composition
series. -/
def CompositionSeries.factor_maximalSpectrum (s : CompositionSeries (Submodule B M))
    (i : Fin s.length) : MaximalSpectrum B :=
  ⟨Module.annihilator B (s.factor i), s.factor_annihilator_isMaximal i⟩

namespace CompositionSeries

/-- Helper for Lemma 10.52.12: one step in the composition series adds the length of the
corresponding factor after restricting scalars from `B` to `A`. -/
theorem step_length_eq_add_factor_length_restrictScalars
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length) :
    Module.length A ↥((s i.succ).restrictScalars A) =
      Module.length A ↥((s i.castSucc).restrictScalars A) + Module.length A (s.factor i) := by
  let P : Submodule A M := (s i.succ).restrictScalars A
  let Q : Submodule A M := (s i.castSucc).restrictScalars A
  let N : Submodule A P := Q.comap P.subtype
  -- Compare the predecessor submodule with its comap inside the next term of the chain.
  have hN : Module.length A ↥N = Module.length A ↥(s i.castSucc) := by
    let e₀ := N.equivMapOfInjective P.subtype (Submodule.injective_subtype _)
    have hQP : Q ≤ P := by
      intro x hx
      exact CovBy.le (s.step i) hx
    have hmap : N.map P.subtype = Q := by
      rw [Submodule.map_comap_subtype, inf_of_le_right hQP]
    let e : N ≃ₗ[A] Q := e₀.trans <| LinearEquiv.ofEq _ _ hmap
    simpa using e.length_eq
  -- Apply additivity of length to the short exact sequence `0 → N → s i.succ → s.factor i → 0`.
  simpa [P, Q, N, hN, CompositionSeries.factor] using
    (Module.length_eq_add_of_exact N.subtype (Submodule.mkQ N)
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ N))

/-- Helper for Lemma 10.52.12: the `A`-length of `M` is the sum of the `A`-lengths of the factors
in any `B`-composition series from `0` to `M`. -/
theorem length_eq_sum_factor_length_restrictScalars
    (s : CompositionSeries (Submodule B M)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    Module.length A M = ∑ i : Fin s.length, Module.length A (s.factor i) := by
  -- Prove by induction that every stage of the chain has length equal to the sum of earlier factors.
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ s.length,
        Module.length A ↥((s ⟨n, Nat.lt_succ_of_le hn⟩).restrictScalars A) =
          ∑ i : Fin n, Module.length A (s.factor ⟨i, Nat.lt_of_lt_of_le i.isLt hn⟩) := by
    intro n
    induction n with
    | zero =>
        intro hn
        -- The chain starts at `0`, so the initial partial sum is zero.
        have hs0A : (s ⟨0, Nat.lt_succ_of_le hn⟩).restrictScalars A = ⊥ := by
          simpa using congrArg (Submodule.restrictScalars A) hs0
        rw [hs0A, Module.length_bot]
        simp
    | succ n ih =>
        intro hn
        have hn' : n ≤ s.length := Nat.le_of_succ_le hn
        let i : Fin s.length := ⟨n, Nat.lt_of_succ_le hn⟩
        -- Add the next factor using the one-step exact sequence.
        calc
          Module.length A ↥((s ⟨n + 1, Nat.lt_succ_of_le hn⟩).restrictScalars A)
              = Module.length A ↥((s ⟨n, Nat.lt_succ_of_le hn'⟩).restrictScalars A) +
                  Module.length A (s.factor i) := by
                  simpa [i] using s.step_length_eq_add_factor_length_restrictScalars (A := A) i
          _ = (∑ j : Fin n, Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn'⟩)) +
                Module.length A (s.factor i) := by
                  rw [ih hn']
          _ = ∑ j : Fin (n + 1),
                Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩) := by
                  symm
                  simpa [i] using
                    (Fin.sum_univ_castSucc
                      (f := fun j : Fin (n + 1) =>
                        Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩)))
  -- Evaluate the partial-sum formula at the last term of the composition series.
  have hlast : ((s (Fin.last s.length)).restrictScalars A : Submodule A M) = ⊤ := by
    simpa using congrArg (Submodule.restrictScalars A) hs1
  calc
    Module.length A M = Module.length A ↥((⊤ : Submodule A M)) := by
      simpa using (Module.length_top (R := A) (M := M)).symm
    _ = Module.length A ↥((s (Fin.last s.length)).restrictScalars A) := by
      rw [← hlast]
    _ = ∑ i : Fin s.length, Module.length A (s.factor i) := by
      simpa using hprefix s.length le_rfl

end CompositionSeries

/-- Helper for Lemma 10.52.12: after contracting `m` to `maximalIdeal A`, the `A`-length of the
residue field of `m` equals its `κ(maximalIdeal A)`-dimension. -/
theorem length_residueField_over_A_eq_finrank
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (m : MaximalSpectrum B) :
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    Module.length A (Ideal.ResidueField m.asIdeal) =
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
  let _ : Algebra κA (Ideal.ResidueField m.asIdeal) :=
    (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra
  let _ : IsScalarTower A κA (Ideal.ResidueField m.asIdeal) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    exact (IsScalarTower.algebraMap_apply A B (Ideal.ResidueField m.asIdeal) a).trans
      ((Ideal.ResidueField.map_algebraMap (maximalIdeal A) m.asIdeal (algebraMap A B)
        (hcomap m).symm a).symm)
  let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
  let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
  have hsurj : Function.Surjective (algebraMap A κA) := by
    intro x
    obtain ⟨y, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A)).surjective x
    obtain ⟨a, rfl⟩ := (Ideal.Quotient.mk_surjective (I := maximalIdeal A)) y
    exact ⟨a, by
      simpa using (Ideal.algebraMap_quotient_residueField_mk (I := maximalIdeal A) a)⟩
  -- First pass from `A` to its residue field, then compute length over the field `κA`.
  calc
    Module.length A (Ideal.ResidueField m.asIdeal)
      = Module.length κA (Ideal.ResidueField m.asIdeal) := by
          exact Module.length_eq_of_surjective (R := κA) (M := Ideal.ResidueField m.asIdeal) hsurj
    _ = (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
          simpa using (Module.length_eq_finrank κA (Ideal.ResidueField m.asIdeal))

namespace CompositionSeries

/-- Helper for Lemma 10.52.12: each simple factor in the chosen `B`-composition series contributes
the residue-field degree of the maximal ideal attached to that factor. -/
theorem factor_length_over_A_eq_residueField_degree
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length) :
    let m := s.factor_maximalSpectrum i
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    Module.length A (s.factor i) =
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
  let m := s.factor_maximalSpectrum i
  let _ : Algebra κA (Ideal.ResidueField m.asIdeal) :=
    (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra
  let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
  let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
  -- Identify the simple factor with the quotient by its annihilator and then with the residue field.
  have hfactor :
      Module.length A (s.factor i) = Module.length A (Ideal.ResidueField m.asIdeal) := by
    let J : Ideal B := Module.annihilator B (s.factor i)
    let _ : J.IsMaximal := s.factor_annihilator_isMaximal i
    let e₁ : s.factor i ≃ₗ[A] (B ⧸ J) := by
      let e := Classical.choice (s.factor_isomorphic_quotient_annihilator i)
      exact e.restrictScalars A
    let e₂ : (B ⧸ J) ≃ₗ[A] Ideal.ResidueField J := by
      let e : (B ⧸ J) ≃ₐ[B ⧸ J] Ideal.ResidueField J :=
        AlgEquiv.ofBijective
          (Algebra.ofId (B ⧸ J) (Ideal.ResidueField J))
          (Ideal.bijective_algebraMap_quotient_residueField J)
      exact e.toLinearEquiv.restrictScalars A
    simpa [m, J, CompositionSeries.factor_maximalSpectrum] using e₁.length_eq.trans e₂.length_eq
  -- Compute the `A`-length of the residue field using the finite `κA`-vector space structure.
  calc
    Module.length A (s.factor i) = Module.length A (Ideal.ResidueField m.asIdeal) := hfactor
    _ = (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
          simpa using length_residueField_over_A_eq_finrank
            (A := A) (B := B) hcomap hfinitek m

/-- Helper for Lemma 10.52.12: regrouping factor-by-factor contributions by maximal ideal turns the
sum over the composition-series factors into the sum of localization lengths. -/
theorem sum_factor_weights_eq_sum_localized_lengths
    [Fintype (MaximalSpectrum B)]
    (s : CompositionSeries (Submodule B M)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (w : MaximalSpectrum B → ENat) :
    ∑ i : Fin s.length, w (s.factor_maximalSpectrum i) =
      ∑ m : MaximalSpectrum B,
        w m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
  classical
  -- Regroup the factor contributions by the maximal ideal attached to each factor.
  rw [← Finset.sum_fiberwise' (s := Finset.univ) (fun i : Fin s.length ↦ s.factor_maximalSpectrum i) w]
  refine Finset.sum_congr rfl ?_
  intro m hm
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m), w m
      = ((Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m)).card : ENat) *
          w m := by
            simp
    _ = w m * ENat.card { i : Fin s.length // s.factor_maximalSpectrum i = m } := by
          have hcard :
              ((Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m)).card :
                ENat) = ENat.card { i : Fin s.length // s.factor_maximalSpectrum i = m } := by
            simp [ENat.card_eq_coe_fintype_card, Fintype.card_subtype]
          rw [hcard, mul_comm]
    _ = w m * ENat.card { i : Fin s.length //
          Module.annihilator B (s.factor i) = m.asIdeal } := by
          congr 1
          apply ENat.card_congr
          refine
            { toFun := fun i ↦
                ⟨i.1, by
                  simpa [CompositionSeries.factor_maximalSpectrum] using
                    congrArg MaximalSpectrum.asIdeal i.2⟩
              invFun := fun i ↦
                ⟨i.1, by
                  cases m with
                  | mk m hm =>
                      cases i with
                      | mk j hj =>
                          dsimp [CompositionSeries.factor_maximalSpectrum] at hj ⊢
                          cases hj
                          rfl⟩
              left_inv := by intro i; cases i; rfl
              right_inv := by intro i; cases i; rfl }
    _ = w m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
          rw [s.factor_count_eq_length_localizedModule hs0 hs1 m.asIdeal]

end CompositionSeries

-- Proof sketch: choose a composition series of the finite-length `B`-module `M`. By Lemma
-- 10.52.11, each factor is a residue field `J.ResidueField` for a unique maximal ideal `J` of
-- `B`, and the number of times `J.ResidueField` occurs is the length of `M` localized at `J`.
-- Restrict scalars to `A`, identify the `A`-length of each factor with the length of the induced
-- residue-field extension `κ(maximalIdeal A) → κ(J)` via Lemma 10.52.6, and sum the contributions
-- using additivity of length from Lemma 10.52.3.
/-- Lemma 10.52.12 (Tag `02M0`): if `A → B` maps the semilocal ring `B` to the local ring `A`
so that every maximal ideal of `B` lies over `maximalIdeal A`, every residue-field extension
`κ(m) / κ(maximalIdeal A)` is finite, and `M` has finite length as a `B`-module, then the
`A`-length of `M` is the sum of the residue-field degrees
`[κ(m) : κ(maximalIdeal A)]` times the lengths of the localizations `Mₘ`.

Canonical Lean form: the semilocal structure is expressed by `[Finite (MaximalSpectrum B)]`, the
finite-length hypothesis is the owner predicate `IsFiniteLength B M`, and the residue-field degree
is written as `Module.finrank`. -/
theorem length_eq_sum_residueFieldDegree_mul_length_localizedModule
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (hM : IsFiniteLength B M) :
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
      ∑ m : MaximalSpectrum B,
        let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
        let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
          Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  let weight : MaximalSpectrum B → ENat := fun m ↦
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat)
  -- Follow the source proof: sum the `A`-lengths of the factors and then regroup by maximal ideal.
  calc
    Module.length A M = ∑ i : Fin s.length, Module.length A (s.factor i) := by
      simpa using s.length_eq_sum_factor_length_restrictScalars (A := A) hs0 hs1
    _ = ∑ i : Fin s.length, weight (s.factor_maximalSpectrum i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [weight, CompositionSeries.factor_maximalSpectrum] using
        s.factor_length_over_A_eq_residueField_degree
          (A := A) hcomap hfinitek i
    _ = ∑ m : MaximalSpectrum B,
          weight m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
            exact s.sum_factor_weights_eq_sum_localized_lengths (B := B) (M := M) hs0 hs1 weight

-- Proof sketch: apply the semilocal localization formula above. Each summand is finite because the
-- residue-field factor is finite by hypothesis and the localized length is bounded by the original
-- finite `B`-length. A finite sum of finite `ENat` values is finite.
/-- Under the hypotheses of the semilocal localization formula, `M` has finite length over `A`. -/
theorem isFiniteLength_of_finiteLength_over_semilocal
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (hM : IsFiniteLength B M) :
    IsFiniteLength A M := by
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  -- The weighted localization formula expresses `Module.length A M` as a finite sum of finite terms.
  rw [← Module.length_ne_top_iff]
  rw [length_eq_sum_residueFieldDegree_mul_length_localizedModule (A := A) (B := B) (M := M)
    hcomap hfinitek hM]
  have hsum :
      (∑ m : MaximalSpectrum B,
          let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
          let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
            Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M)) ≠ ⊤ := by
    simpa using
      (ENat.sum_ne_top (s := Finset.univ) (f := fun m : MaximalSpectrum B ↦
        let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
        let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
          Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M))).2
        (fun m hm ↦ by
          let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
          let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
          -- Each coefficient is finite, and each localized length is a finite cardinality of factors.
          have hcoeff : (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) ≠ ⊤ := by
            simp
          have hloc : Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) ≠ ⊤ := by
            rw [← s.factor_count_eq_length_localizedModule hs0 hs1 m.asIdeal,
              ENat.card_eq_coe_fintype_card]
            simp
          exact WithTop.mul_ne_top hcoeff hloc)
  simpa using hsum

end ResidueFieldData

end Length

/-! ### Lemma_10_52_13 (from Chap10) -/
open scoped TensorProduct
open IsLocalRing

universe u v w

section Length

/-
Domain triage:
* primary domain: finite-length modules under flat local base change and the closed fiber of a
  local homomorphism;
* sampled owner API: `Ideal.Fiber`, `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `Module.length_ne_top_iff`, and `IsFiniteLength`;
* source-facing layer: the two textbook statements about the length of `B ⊗[A] M` and the finite
  length criterion after flat local base change;
* core/canonical owners: `Ideal.Fiber` for the closed fiber, `Module.FaithfullyFlat` for
  faithfulness of tensor base change, and `IsFiniteLength` for finiteness of length;
* bridge/view: the file keeps the source-facing length statements while deriving the ambient
  faithful-flat and finite-length notions from the owner abstractions already introduced earlier in
  the chapter.
-/

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
variable [AddCommGroup M] [Module A M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 10.52.13: base changing the residue field quotient `A / maximalIdeal A`
identifies with the closed fiber. -/
noncomputable def residue_baseChange_closedFiber_equiv :
    B ⊗[A] (A ⧸ maximalIdeal A) ≃ₐ[B] ClosedFiber :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (.ofBijective _
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A)))).trans <|
    Algebra.TensorProduct.commRight A B ((maximalIdeal A).ResidueField)

/-- Helper for Lemma 10.52.13: the closed fiber is the quotient `B / maximalIdeal A • B` as a
`B`-algebra. -/
noncomputable def closedFiber_quotient_equiv :
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ≃ₐ[B] ClosedFiber :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).trans <|
    residue_baseChange_closedFiber_equiv

/-- Helper for Lemma 10.52.13: under the quotient description of the closed fiber, the class of
`b : B` maps to the image of `b` in the closed fiber. -/
@[simp] lemma closedFiber_quotient_equiv_mk (b : B) :
    closedFiber_quotient_equiv
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) b) =
      algebraMap B ClosedFiber b := by
  -- Unfold the composite equivalence and evaluate each standard tensor-product component.
  simp [closedFiber_quotient_equiv, residue_baseChange_closedFiber_equiv,
    Algebra.TensorProduct.right_algebraMap_apply]

/-- Helper for Lemma 10.52.13: the canonical map `B → ClosedFiber` is surjective because the
closed fiber is the quotient `B / maximalIdeal A • B`. -/
lemma closedFiber_algebraMap_surjective :
    Function.Surjective (algebraMap B ClosedFiber) := by
  intro x
  obtain ⟨y, rfl⟩ := closedFiber_quotient_equiv.surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨b, (closedFiber_quotient_equiv_mk b).symm⟩

/-- Helper for Lemma 10.52.13: viewing the closed fiber as a `B`-module or as a module over
itself gives the same length. -/
lemma closedFiber_length_over_base_eq_self :
    Module.length B ClosedFiber = Module.length ClosedFiber ClosedFiber := by
  -- Compare the two scalar actions through the surjective algebra map `B → ClosedFiber`.
  exact Module.length_eq_of_surjective
    closedFiber_algebraMap_surjective

/-- Helper for Lemma 10.52.13: faithful flatness makes the natural map
`M → B ⊗[A] M` induce a strictly monotone map on submodules. -/
lemma tensor_product_mk_submodule_strictMono :
    StrictMono (fun N : Submodule A M => N.map (TensorProduct.mk A B M 1)) := by
  -- The local flat map is faithfully flat, so the tensor-product unit map is injective.
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Submodule.map_strictMono_of_injective
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M)

/-- Helper for Lemma 10.52.13: faithful flatness makes scalar extension
`N ↦ N.baseChange B` strictly monotone on submodules. -/
lemma submodule_baseChange_strictMono :
    StrictMono (fun N : Submodule A M => N.baseChange B) := by
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro N P hNP
  let NP : Submodule A P := N.comap P.subtype
  have hNPNeTop : NP ≠ ⊤ := by
    intro htop
    have hmap : NP.map P.subtype = N := by
      dsimp [NP]
      rw [Submodule.map_comap_subtype, inf_of_le_right hNP.le]
    rw [htop, Submodule.map_top] at hmap
    exact hNP.ne (by simpa [Submodule.range_subtype] using hmap.symm)
  have hTensorNontrivial : Nontrivial (B ⊗[A] (P ⧸ NP)) := by
    exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right A B).2
      (Submodule.Quotient.nontrivial_iff.mpr hNPNeTop)
  have hNPBaseChangeNeTop : NP.baseChange B ≠ ⊤ := by
    intro htop
    have hRangeTop : LinearMap.range (LinearMap.baseChange B NP.subtype) = ⊤ := by
      simpa [Submodule.baseChange] using htop
    have hExact : Function.Exact (LinearMap.baseChange B NP.subtype)
        (LinearMap.baseChange B NP.mkQ) := by
      simpa [LinearMap.baseChange_eq_ltensor] using
        (lTensor_exact B (LinearMap.exact_subtype_mkQ NP) (Submodule.mkQ_surjective NP))
    have hSurj : Function.Surjective (LinearMap.baseChange B NP.mkQ) := by
      simpa [LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective B (Submodule.mkQ_surjective NP))
    have hKerTop : LinearMap.ker (LinearMap.baseChange B NP.mkQ) = ⊤ := by
      rw [hExact.linearMap_ker_eq, hRangeTop]
    have hZero : LinearMap.baseChange B NP.mkQ = 0 := by
      rw [← LinearMap.ker_eq_top]
      exact hKerTop
    have hBotTop : (⊥ : Submodule B (B ⊗[A] (P ⧸ NP))) = ⊤ := by
      simpa [hZero] using (LinearMap.range_eq_top.2 hSurj)
    have hSubsingleton : Subsingleton (B ⊗[A] (P ⧸ NP)) := by
      rw [← Submodule.subsingleton_iff B, ← subsingleton_iff_bot_eq_top]
      simpa using hBotTop
    have : ¬ Subsingleton (B ⊗[A] (P ⧸ NP)) :=
      not_subsingleton_iff_nontrivial.mpr hTensorNontrivial
    exact this hSubsingleton
  let eNP :
      NP ≃ₗ[A] N :=
    (Submodule.equivMapOfInjective P.subtype Subtype.val_injective NP).trans <|
      LinearEquiv.ofEq _ _ (by
        dsimp [NP]
        rw [Submodule.map_comap_subtype, inf_of_le_right hNP.le])
  let iP : B ⊗[A] P →ₗ[B] B ⊗[A] M := LinearMap.baseChange B P.subtype
  have hiP : Function.Injective iP := by
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap P.subtype Subtype.val_injective)
  have hcomp :
      iP.comp (LinearMap.baseChange B NP.subtype) =
        (LinearMap.baseChange B N.subtype).comp (LinearMap.baseChange B eNP.toLinearMap) := by
    ext b
    rfl
  have hRangeTop :
      LinearMap.range (LinearMap.baseChange B eNP.toLinearMap) = ⊤ := by
    simpa using LinearEquiv.range (LinearEquiv.baseChange A B NP N eNP)
  have hMap :
      (NP.baseChange B).map iP = N.baseChange B := by
    rw [Submodule.baseChange, Submodule.baseChange, ← LinearMap.range_comp, hcomp,
      LinearMap.range_comp_of_range_eq_top _ hRangeTop]
  have hTopMap :
      (⊤ : Submodule B (B ⊗[A] P)).map iP = P.baseChange B := by
    rw [Submodule.map_top, Submodule.baseChange]
  have hltTop : NP.baseChange B < ⊤ := lt_of_le_of_ne le_top hNPBaseChangeNeTop
  have hmaplt :
      (NP.baseChange B).map iP < (⊤ : Submodule B (B ⊗[A] P)).map iP :=
    (Submodule.map_strictMono_of_injective hiP) hltTop
  rw [hMap, hTopMap] at hmaplt
  exact hmaplt

/-- Helper for Lemma 10.52.13: every strict chain of submodules in `M` remains strict after base
change to `B`, so the length can only increase. -/
lemma length_le_length_base_change :
    Module.length A M ≤ Module.length B (B ⊗[A] M) := by
  -- Convert strict monotonicity of base change on submodules into the height inequality.
  simpa [Module.length_eq_height, Submodule.baseChange_top] using
    Order.height_le_height_apply_of_strictMono
      (fun N : Submodule A M => N.baseChange B)
      submodule_baseChange_strictMono ⊤

/-- Helper for Lemma 10.52.13: base change carries every simple `A`-module to a `B`-module whose
length is the length of the closed fiber. -/
lemma simple_baseChange_length_eq_closedFiber_length
    {Q : Type*} [AddCommGroup Q] [Module A Q] [IsSimpleModule A Q] :
    Module.length B (B ⊗[A] Q) = Module.length ClosedFiber ClosedFiber := by
  obtain ⟨I, hImax, ⟨eQ⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A Q)
  have hI : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hImax
  subst hI
  -- Replace the simple module by the residue field quotient and then identify its base change
  -- with the closed fiber.
  calc
    Module.length B (B ⊗[A] Q) =
        Module.length B (B ⊗[A] (A ⧸ maximalIdeal A)) := by
          simpa using (LinearEquiv.baseChange A B Q (A ⧸ maximalIdeal A) eQ).length_eq
    _ = Module.length B ClosedFiber := by
          simpa using residue_baseChange_closedFiber_equiv.toLinearEquiv.length_eq
    _ = Module.length ClosedFiber ClosedFiber := closedFiber_length_over_base_eq_self

/-- Helper for Lemma 10.52.13: for modules of finite length, base change multiplies length by the
length of the closed fiber. -/
lemma length_base_change_eq_mul_closed_fiber_of_isFiniteLength
    (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) =
      Module.length A M * Module.length ClosedFiber ClosedFiber := by
  induction hM with
  | of_subsingleton =>
      -- The trivial module stays trivial after tensoring, so both lengths are zero.
      simp
  | @of_simple_quotient M _ _ N _ hN ih =>
      have hTensorInj : Function.Injective (LinearMap.baseChange B N.subtype) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective)
      have hTensorSurj : Function.Surjective (LinearMap.baseChange B N.mkQ) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N))
      have hTensorExact : Function.Exact (LinearMap.baseChange B N.subtype)
          (LinearMap.baseChange B N.mkQ) := by
        simpa [LinearMap.baseChange_eq_ltensor] using
          (lTensor_exact B (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N))
      have hTensorLength :
          Module.length B (B ⊗[A] M) =
            Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := by
        -- Tensor the short exact sequence `0 → N → M → M ⧸ N → 0`.
        simpa using
          (Module.length_eq_add_of_exact (LinearMap.baseChange B N.subtype)
            (LinearMap.baseChange B N.mkQ) hTensorInj hTensorSurj hTensorExact)
      have hSourceLength : Module.length A M = Module.length A N + 1 := by
        -- The simple quotient contributes exactly one to the source-side length.
        simpa using
          (Module.length_eq_add_of_exact N.subtype N.mkQ Subtype.val_injective
            (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N))
      -- Combine additivity with the simple-factor computation.
      calc
        Module.length B (B ⊗[A] M) =
            Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) :=
              hTensorLength
        _ = Module.length A N * Module.length ClosedFiber ClosedFiber +
              Module.length ClosedFiber ClosedFiber := by
              rw [ih, simple_baseChange_length_eq_closedFiber_length]
        _ = (Module.length A N + 1) * Module.length ClosedFiber ClosedFiber := by
              simp [add_mul]
        _ = Module.length A M * Module.length ClosedFiber ClosedFiber := by
              rw [hSourceLength]

-- Proof sketch: a flat local map of local rings is faithfully flat, so tensoring a composition
-- series of `M` with `B` preserves strict inclusions. Each simple quotient `A / maximalIdeal A`
-- becomes the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
-- `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, and additivity of `Module.length` gives the
-- multiplicative formula.
/-- Lemma 10.52.13 (1): for a flat local homomorphism `A → B`, the length of the base change
`B ⊗[A] M` is the length of `M` times the length of the closed fiber
`((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`. -/
theorem length_base_change_eq_length_mul_closed_fiber :
    Module.length B (B ⊗[A] M) =
      Module.length A M * Module.length ClosedFiber ClosedFiber := by
  by_cases htop : Module.length A M = ⊤
  · -- If `M` has infinite length, faithful flatness forces the base change to have infinite
    -- length as well, and multiplying by the positive closed-fiber length stays at `⊤`.
    have hTensorTop : Module.length B (B ⊗[A] M) = ⊤ := by
      exact top_le_iff.mp (htop ▸ length_le_length_base_change)
    have hMapLe :
        Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
      exact ((local_hom_TFAE (algebraMap A B)).out 0 2).mp
        (inferInstance : IsLocalHom (algebraMap A B))
    have hMapNeTop : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊤ := by
      intro htopMap
      exact (Ideal.IsPrime.ne_top (inferInstance : (maximalIdeal B).IsPrime))
        (top_le_iff.mp (htopMap ▸ hMapLe))
    letI : Nontrivial (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
      Ideal.Quotient.nontrivial_iff.mpr hMapNeTop
    letI : Nontrivial ClosedFiber := closedFiber_quotient_equiv.symm.toRingEquiv.toEquiv.nontrivial
    have hClosedFiberPos : 0 < Module.length ClosedFiber ClosedFiber := Module.length_pos
    rw [hTensorTop, htop, ENat.top_mul hClosedFiberPos.ne']
  · -- In the finite-length branch, use induction on the finite-length structure of `M`.
    exact length_base_change_eq_mul_closed_fiber_of_isFiniteLength
      ((Module.length_ne_top_iff).mp htop)

-- Proof sketch: use the length formula in (1) together with `Module.length_ne_top_iff`.
-- If the closed fiber has finite length, then multiplication by its length preserves finiteness of
-- the other factor, yielding the equivalence of finite-length conditions.
/-- Lemma 10.52.13 (2): if the closed fiber `((maximalIdeal A).Fiber B)`, equivalently
`B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)`, has finite length as a module over itself,
then `M` has finite length over `A` if and only if `B ⊗[A] M` has finite
length over `B`. -/
theorem finite_length_iff_finite_length_base_change
    (hclosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    IsFiniteLength A M ↔ IsFiniteLength B (B ⊗[A] M) := by
  constructor
  · intro hM
    -- Apply the length formula and use finiteness of both factors.
    rw [← Module.length_ne_top_iff] at hM hclosedFiber ⊢
    rw [length_base_change_eq_length_mul_closed_fiber (A := A) (B := B) (M := M)]
    exact WithTop.mul_ne_top hM hclosedFiber
  · intro hTensor
    -- Infinite source length would force infinite target length by faithful flatness.
    rw [← Module.length_ne_top_iff] at hTensor ⊢
    intro htop
    have hTensorTop : Module.length B (B ⊗[A] M) = ⊤ := by
      exact top_le_iff.mp (htop ▸ length_le_length_base_change)
    exact hTensor hTensorTop

end Length

/-! ### Lemma_10_52_14 (from Chap10) -/
open IsLocalRing
open scoped TensorProduct
universe u v w

section Length

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
variable [Module.Flat A B] [Module.Flat B C]

local notation "ClosedFiberAB" => Ideal.Fiber (maximalIdeal A) B
local notation "ClosedFiberBC" => Ideal.Fiber (maximalIdeal B) C
local notation "ClosedFiberAC" => Ideal.Fiber (maximalIdeal A) C

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-
Domain triage:
* primary domain: closed fibers of local ring maps, tensor base change, and finite module length;
* sampled owner API: `Ideal.Fiber`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`, `LinearEquiv.length_eq`, and
  `length_base_change_eq_length_mul_closed_fiber`;
* source-facing layer: the textbook multiplicativity formula for lengths of closed fibers in a
  composite of flat local maps;
* core/canonical owners: `Ideal.Fiber` for the closed fiber itself and the tensor-product
  base-change equivalences for identifying the composite closed fiber with the base change of the
  first closed fiber along `B → C`;
* bridge/view: the theorem remains source-facing, while the proof derives its two length rewrites
  and the composite-fiber identification from the owner abstractions already fixed in the previous
  item and in mathlib.
-/

-- Proof sketch: apply the base-change length formula of Lemma 10.52.13 to the flat local map
-- `B → C` and the `B`-module `ClosedFiberAB`. The tensor product of this closed fiber with `C`
-- identifies with `ClosedFiberAC`, giving the stated multiplicativity of closed-fiber lengths.
/-- Helper for Lemma 10.52.14: extending `maximalIdeal A` along `A → B → C` agrees with
extension along the composite `A → C`. -/
lemma map_map_maximalIdeal_eq :
    Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) (maximalIdeal A)) =
      Ideal.map (algebraMap A C) (maximalIdeal A) := by
  -- Collapse the iterated ideal extension using the scalar tower identity.
  simpa [IsScalarTower.algebraMap_eq A B C] using
    (Ideal.map_map (I := maximalIdeal A) (algebraMap A B) (algebraMap B C))

/-- Helper for Lemma 10.52.14: the quotient model `B / 𝔪_A B` has the same `B`-module length as
the canonical closed fiber of `A → B`. -/
lemma closedFiberAB_quotient_length_eq :
    Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) =
      Module.length ClosedFiberAB ClosedFiberAB := by
  -- First identify the quotient with the canonical closed fiber, then compare scalar actions.
  calc
    Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) =
        Module.length B ClosedFiberAB := by
          simpa using
            (closedFiber_quotient_equiv (A := A) (B := B)).toLinearEquiv.length_eq
    _ = Module.length ClosedFiberAB ClosedFiberAB :=
      closedFiber_length_over_base_eq_self (A := A) (B := B)

/-- Helper for Lemma 10.52.14: base changing the quotient model `B / 𝔪_A B` along `B → C`
produces the canonical closed fiber of the composite `A → C`, with the same `C`-module length. -/
lemma base_change_quotient_length_eq_closedFiberAC_length :
    Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
      Module.length ClosedFiberAC ClosedFiberAC := by
  letI : IsLocalHom (algebraMap A C) := by
    -- The composite of local maps is local, so the `A → C` closed-fiber API is available.
    simpa [IsScalarTower.algebraMap_eq A B C] using
      (RingHom.isLocalHom_comp (algebraMap B C) (algebraMap A B))
  letI : Module.Flat A C := Module.Flat.trans A B C
  -- Rewrite the tensor product as the quotient by the extended ideal.
  calc
    Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
        Module.length C
          (C ⧸ Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
          simpa using
            ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
              C (Ideal.map (algebraMap A B) (maximalIdeal A))).symm.toLinearEquiv.length_eq :
                Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
                  Module.length C
                    (C ⧸ Ideal.map (algebraMap B C)
                      (Ideal.map (algebraMap A B) (maximalIdeal A))))
    -- Collapse the iterated ideal extension to the composite one.
    _ = Module.length C (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) := by
          rw [map_map_maximalIdeal_eq]
    -- Identify that quotient with the canonical closed fiber of the composite map.
    _ = Module.length C ClosedFiberAC := by
          simpa using
            (closedFiber_quotient_equiv (A := A) (B := C)).toLinearEquiv.length_eq
    _ = Module.length ClosedFiberAC ClosedFiberAC :=
      closedFiber_length_over_base_eq_self (A := A) (B := C)

/-- Lemma 10.52.14: for flat local homomorphisms `A → B → C` of local rings, the length of the
closed fiber of `A → B` times the length of the closed fiber of `B → C` equals the length of the
closed fiber of the composite `A → C`. -/
theorem length_closed_fiber_mul_length_closed_fiber_eq_length_composite_closed_fiber :
    Module.length ClosedFiberAB ClosedFiberAB * Module.length ClosedFiberBC ClosedFiberBC =
      Module.length ClosedFiberAC ClosedFiberAC := by
  -- Apply Lemma 10.52.13 to `B → C` and the quotient model `B / 𝔪_A B`.
  have hbaseChange :
      Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
        Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) *
          Module.length ClosedFiberBC ClosedFiberBC :=
    length_base_change_eq_length_mul_closed_fiber
      (A := B) (B := C) (M := B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
  -- Rewrite the source quotient and its base change as the canonical closed fibers.
  calc
    Module.length ClosedFiberAB ClosedFiberAB * Module.length ClosedFiberBC ClosedFiberBC =
        Module.length B (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) *
          Module.length ClosedFiberBC ClosedFiberBC := by
          rw [← closedFiberAB_quotient_length_eq]
    _ = Module.length C (C ⊗[B] (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) := by
          exact hbaseChange.symm
    _ = Module.length ClosedFiberAC ClosedFiberAC :=
          base_change_quotient_length_eq_closedFiberAC_length

end Length
