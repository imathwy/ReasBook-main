import Mathlib
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_40_1 (from Chap10) -/
universe u v

/- Domain-style sampling for module support:
- primary domain: support of modules over a commutative ring, viewed on `PrimeSpectrum R`;
- sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff`,
  `Module.support_eq_empty_iff`,
  `Module.support_eq_zeroLocus`;
- best owner abstraction: `Module.support R M`;
- primitive data: the owner set of primes where the localized module is nontrivial;
- derived API: membership reformulations such as `Module.mem_support_iff`, together with
  closedness and zero-locus descriptions under stronger finiteness hypotheses.

Source/core/bridge triage:
- `source-facing`: the textbook support `Supp(M)` as a subset of `Spec R`;
- `core/canonical`: `Module.support R M`;
- `bridge/view`: `Module.mem_support_iff`, identifying membership with nontriviality of `M_𝔭`.

This numbered definition introduces no new mathematical data beyond the owner set
`Module.support R M`, so the main entry should remain a direct canonical recall rather than a
parallel local alias or a large restatement theorem.
-/

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/- Definition 10.40.1, canonical main form: the support of an `R`-module `M` is the mathlib
definition `Module.support R M`, the set of primes `𝔭 ∈ PrimeSpectrum R` such that the
localization `M_𝔭` is nontrivial. -/
recall Module.support

variable {R M} {p : PrimeSpectrum R}

/- Companion recall: membership in `Module.support R M` is exactly the textbook condition
`M_𝔭 ≠ 0`, formalized in Lean as nontriviality of the localized module at `𝔭`. -/
recall Module.mem_support_iff

end

/-! ### Lemma_10_40_2 (from Chap10) -/
/-
Domain-style sampling for module support and its emptiness criterion:
- primary domain: support of modules over a commutative ring, viewed as a subset of `Spec R`;
- sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff`,
  `Module.support_eq_empty_iff`,
  `Module.nonempty_support_iff`;
- best owner abstraction: `Module.support R M`;
- primitive data: the support set itself;
- derived API: membership and emptiness/nonemptiness characterizations, in particular
  `Module.support_eq_empty_iff`.

Source/core/bridge triage:
- `source-facing`: the statement that an `R`-module has empty support exactly when it is the zero
  module;
- `core/canonical`: `Module.support R M`;
- `bridge/view`: the canonical emptiness criterion `Module.support_eq_empty_iff`.

This lemma introduces no new data beyond the existing support owner and its derived emptiness API,
so the refined main entry should remain a direct recall of the canonical theorem rather than a
parallel local wrapper.
-/

section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- Lemma 10.40.2, source-facing through the support owner abstraction: an `R`-module `M` is
the zero module if and only if its support `Module.support R M` is empty. This is exactly the
canonical theorem `Module.support_eq_empty_iff`, where `M = (0)` is expressed as
`Subsingleton M`. -/
recall Module.support_eq_empty_iff

end

/-! ### Definition_10_40_3 (from Chap10) -/
universe u v

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/- Definition 10.40.3: given `m : M`, the annihilator of `m` is the canonical ideal
`Ideal.torsionOf R M m = {r : R | r • m = 0}`. -/
recall Ideal.torsionOf

/- Companion recall: membership in the annihilator of an element is exactly the textbook condition
`r • m = 0`. -/
recall Ideal.mem_torsionOf_iff

/- Companion recall: `Module.annihilator R M` is the canonical annihilator ideal of the module
`M`. -/
recall Module.annihilator

/- Companion recall: this is the standard membership characterization of the annihilator of a
module. -/
recall Module.mem_annihilator

end

/-! ### Lemma_10_40_4 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Domain triage: this file lies in the commutative-algebra domain of annihilators under flat base
change. The `source-facing` textbook content is the annihilator comparison in Lemma 10.40.4. The
owner abstractions are the canonical mathlib/project declarations `Ideal.torsionOf`,
`Module.annihilator`, and `Ideal.mapInfTopHom`; the file should derive its finite-intersection step
from that owner map rather than keep a parallel local ideal-map API. Primitive data are only the
flat algebra structure and the module. Derived API consists of the two public annihilator theorems
below. -/

namespace Ideal

private noncomputable def quotientTensorSingletonEquiv
    (m : M) :
    (S ⧸ Ideal.map (algebraMap R S) (torsionOf R M m)) ≃ₗ[S]
      S ∙ ((1 : S) ⊗ₜ[R] m) :=
  let I := torsionOf R M m
  let e₁ : (S ⧸ Ideal.map (algebraMap R S) I) ≃ₗ[S] S ⊗[R] (R ⧸ I) :=
    Ideal.qoutMapEquivTensorQout S
  let e₂ : S ⊗[R] (R ⧸ I) ≃ₗ[S] S ⊗[R] ↥(R ∙ m) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (Ideal.quotTorsionOfEquivSpanSingleton R M m)
  let e₃ : S ⊗[R] ↥(R ∙ m) ≃ₗ[S] (R ∙ m).baseChange S :=
    Submodule.toBaseChange.toLinearEquiv S (R ∙ m)
  let e₄ : (R ∙ m).baseChange S ≃ₗ[S] S ∙ ((1 : S) ⊗ₜ[R] m) :=
    LinearEquiv.ofEq ((R ∙ m).baseChange S) (S ∙ ((1 : S) ⊗ₜ[R] m))
      (by
        change (Submodule.span R ({m} : Set M)).baseChange S =
          S ∙ ((1 : S) ⊗ₜ[R] m)
        rw [Submodule.baseChange_span]
        congr
        ext x
        simp)
  e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Lemma 10.40.4 (Tag 07T8): for a flat ring map `R → S`, extending the annihilator ideal of
`m : M` agrees with the annihilator ideal of the base-changed element `1 ⊗ₜ[R] m`
in `S ⊗[R] M`.

This is the canonical Lean form of the first assertion in the textbook lemma, using
`Ideal.torsionOf` for the annihilator of an element. -/
-- Proof sketch: consider the exact sequence
-- `0 → Ideal.torsionOf R M m → R → M` sending `r` to `r • m`, tensor it with `S`, and identify
-- the kernel of `S → S ⊗[R] M` sending `s` to `s • (1 ⊗ₜ[R] m)` with
-- `Ideal.torsionOf S (S ⊗[R] M) (1 ⊗ₜ[R] m)`.
@[stacks 07T8 "element-annihilator assertion"]
theorem map_torsionOf_eq_torsionOf_baseChange_of_flat
    (m : M) :
    map (algebraMap R S) (torsionOf R M m) =
      torsionOf S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] m) := by
  let e :
      (S ⧸ map (algebraMap R S) (torsionOf R M m)) ≃ₗ[S]
        S ∙ ((1 : S) ⊗ₜ[R] m) :=
    quotientTensorSingletonEquiv m
  have hq :
      Module.annihilator S (S ⧸ map (algebraMap R S) (torsionOf R M m)) =
        map (algebraMap R S) (torsionOf R M m) :=
    annihilator_quotient
  rw [← hq, e.annihilator_eq]
  simpa [torsionOf] using
    (Submodule.annihilator_span_singleton ((1 : S) ⊗ₜ[R] m))

end Ideal

namespace Module

/-- Canonical Lean form of the finite-module assertion in Lemma 10.40.4: if `M` is finite over
`R`, then extending `annihilator R M` along a flat map `R → S` agrees with the annihilator of the
base-changed module `S ⊗[R] M`. -/
-- Proof sketch: choose finitely many generators of `M`, express both annihilators as
-- intersections of the annihilators of those generators, apply
-- `Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat` termwise, and then use Lemma 10.39.2 to
-- move extension of ideals across the finite intersection.
@[stacks 07T8 "finite-module assertion"]
theorem map_annihilator_eq_annihilator_baseChange_of_flat [Module.Finite R M] :
    Ideal.map (algebraMap R S) (annihilator R M) =
      annihilator S (S ⊗[R] M) := by
  have hsFinite : ∃ n : ℕ, ∃ s : Fin n → M, Submodule.span R (Set.range s) = ⊤ :=
    Module.Finite.exists_fin
  obtain ⟨n, s, hs⟩ := hsFinite
  have hsTensor : Submodule.span S (Set.range fun i : Fin n ↦ (1 : S) ⊗ₜ[R] s i) = ⊤ := by
    rw [← Submodule.baseChange_top, ← hs, Submodule.baseChange_span]
    congr
    ext x
    simp
  have hann :
      annihilator R M = ⨅ i : Fin n, Ideal.torsionOf R M (s i) := by
    rw [← Submodule.annihilator_top, ← hs, Submodule.annihilator_span]
    ext r
    simp [Ideal.torsionOf, Set.mem_range]
  have hbase :
      annihilator S (S ⊗[R] M) =
        ⨅ i : Fin n, Ideal.torsionOf S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] s i) := by
    rw [← Submodule.annihilator_top, ← hsTensor, Submodule.annihilator_span]
    ext r
    simp [Ideal.torsionOf, Set.mem_range]
  rw [hann, hbase]
  rw [show Ideal.map (algebraMap R S) (⨅ i, Ideal.torsionOf R M (s i)) =
      ⨅ i, Ideal.map (algebraMap R S) (Ideal.torsionOf R M (s i)) by
        simpa [Finset.inf_eq_iInf] using
          map_finset_inf Ideal.mapInfTopHom Finset.univ
            (fun i ↦ Ideal.torsionOf R M (s i))]
  ext x
  simp [Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat]

end Module

end

/-! ### Lemma_10_40_5 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.40.5, canonical main form: more precisely, if
`I = Module.annihilator R M`, then `PrimeSpectrum.zeroLocus I = Module.support R M`. -/
recall Module.support_eq_zeroLocus

/- Source-wording consequence: if `M` is finite, then `Module.support R M` is closed. -/
recall Module.isClosed_support

end

/-! ### Lemma_10_40_6 (from Chap10) -/
open scoped TensorProduct
open PrimeSpectrum
open TensorProduct.AlgebraTensorModule Module.FaithfullyFlat

universe u v w

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/-
Domain triage: this item lies in the commutative-algebra support/base-change domain.
- sampled canonical declarations: `Module.support`, `Module.support_subset_preimage_comap`,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`, and
  `AlgebraTensorModule.cancelBaseChange`;
- layer: `source-facing`, since the theorem identifies the support of the base-changed finite
  module inside the owner API `Module.support`.

Primitive data are only the algebra map `R → R'` and the finite `R`-module `M`. The forward
support equality itself is not yet present upstream, so the file keeps the minimal local bridge
that compares residue-field fibers after passing from `p = q.comap` to `q`.
-/

/-- Lemma 10.40.6 (Tag `0BUR`): let `R → R'` be a ring map and let `M` be a finite `R`-module.
Then the support of the canonical base change `R' ⊗[R] M` is the inverse image of
`support R M` along the induced map `Spec R' → Spec R`. -/
@[stacks 0BUR]
theorem Lemma_10_40_6 :
    support R' (R' ⊗[R] M) = comap (algebraMap R R') ⁻¹' support R M := by
  ext q
  change q ∈ support R' (R' ⊗[R] M) ↔ comap (algebraMap R R') q ∈ support R M
  let p : PrimeSpectrum R := comap (algebraMap R R') q
  let K := p.asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  let e : L ⊗[R'] (R' ⊗[R] M) ≃ₗ[L] L ⊗[K] (K ⊗[R] M) :=
    (cancelBaseChange R R' L L M).trans (cancelBaseChange R K L L M).symm
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  rw [mem_support_iff_nontrivial_residueField_tensorProduct,
    mem_support_iff_nontrivial_residueField_tensorProduct]
  simpa [p] using e.nontrivial_congr.trans (nontrivial_tensorProduct_iff_right K L)

end Module

end

/-! ### Lemma_10_40_7 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Owner-form of Lemma 10.40.7: a prime lies in the support of the cyclic module `R ∙ m`
precisely when the image of `m` in the localization `M_𝔭` is nonzero. -/
theorem mem_support_span_singleton_iff_localized_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ Module.support R (R ∙ m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  let S := p.asIdeal.primeCompl
  let e : (R ∙ m).localized S ≃ₗ[Localization S] LocalizedModule S (R ∙ m) :=
    Submodule.localizedEquiv S (R ∙ m)
  have hlocalized :
      (R ∙ m).localized S =
        (Localization S) ∙ LocalizedModule.mkLinearMap S M m := by
    simpa only [S, Submodule.localized, Set.image_singleton] using
      Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
        ({m} : Set M)
  rw [Module.mem_support_iff, ← e.toEquiv.nontrivial_congr, Submodule.nontrivial_iff_ne_bot,
    hlocalized]
  exact Submodule.span_singleton_eq_bot.not

/-- Lemma 10.40.7: a prime ideal lies in the zero locus of the annihilator of `m` precisely when
the image of `m` in the localization `M_𝔭` is nonzero.

This is a source-facing bridge from the owner abstraction `Module.support` for the cyclic module
`R ∙ m`, together with the canonical element-annihilator
`Ideal.torsionOf R M m = {r : R | r • m = 0}`. -/
theorem mem_zeroLocus_annihilator_span_singleton_iff_localized_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ PrimeSpectrum.zeroLocus (Ideal.torsionOf R M m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  simpa [Module.support_eq_zeroLocus, Ideal.torsionOf, Submodule.annihilator_span_singleton] using
    (mem_support_span_singleton_iff_localized_ne_zero p m)

end

/-! ### Lemma_10_40_8 (from Chap10) -/
universe u v

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Companion recall: the owner object for the textbook support of an `R`-module is
`Module.support R M`. -/
recall Module.support

/- Companion recall: for a finitely presented `R`-module, the canonical owner ideal cutting out
the support is the zeroth Fitting ideal `moduleFittingIdeal R M 0`. -/
recall moduleFittingIdeal

/- Companion recall: the support of a finite module is canonically the zero locus of its zeroth
Fitting ideal. This is the source-faithful bridge used in Lemma 10.40.8. -/
recall zeroLocus_moduleFittingIdeal_zero_eq_support

/- Companion recall: finite presentation makes the zeroth Fitting ideal finitely generated. -/
recall moduleFittingIdeal_fg_of_finitePresentation

/- Companion recall: finite modules have closed support. Since finitely presented modules are
finite, this supplies the closedness half of Lemma 10.40.8 directly from the owner abstraction
`Module.support`. -/
recall Module.isClosed_support

/- Companion recall: on `Spec R`, compact open subsets are exactly complements of zero loci of
finitely generated ideals. This is the ambient compact-open owner theorem used to package the
quasi-compactness conclusion. -/
recall PrimeSpectrum.isCompact_isOpen_iff_ideal

namespace Module

variable [FinitePresentation R M]

-- Proof sketch: rewrite `support R M` as the zero locus of the canonical zeroth Fitting ideal,
-- use finite presentation to make that ideal finitely generated, then apply
-- `PrimeSpectrum.isCompact_isOpen_iff_ideal`.
/-- Lemma 10.40.8: if `M` is a finitely presented `R`-module, then `Supp(M)` is closed and its
complement in `Spec R` is quasi-compact. In Lean, quasi-compactness of a subset of `Spec R` is
expressed by `IsCompact`. -/
theorem isClosed_support_and_isCompact_compl_support :
    IsClosed (support R M) ∧ IsCompact (support R M)ᶜ := by
  refine ⟨isClosed_support, ?_⟩
  simpa [zeroLocus_moduleFittingIdeal_zero_eq_support] using
    (isCompact_isOpen_iff_ideal.mpr
      ⟨moduleFittingIdeal R M 0, moduleFittingIdeal_fg_of_finitePresentation 0, rfl⟩).1

/-- Companion consequence of Lemma 10.40.8: for a finitely presented module, the complement of
`Supp(M)` is quasi-compact. -/
theorem isCompact_compl_support :
    IsCompact (support R M)ᶜ :=
  isClosed_support_and_isCompact_compl_support.2

end Module

/-! ### Lemma_10_40_9 (from Chap10) -/
/- Lemma 10.40.9 (1): if `M` is a finite `R`-module and `I` is an ideal of `R`, then the support
of the quotient `M / IM`, written in Lean as `M ⧸ (I • ⊤ : Submodule R M)`, is the intersection
`Module.support R M ∩ PrimeSpectrum.zeroLocus I`. This is exactly the canonical theorem
`Module.support_quotient`. -/
recall Module.support_quotient

/- Lemma 10.40.9 (2): if `N` is a submodule of an `R`-module `M`, then
`Module.support R N ⊆ Module.support R M`. This is the canonical theorem
`Module.support_subset_of_injective`, specialized to the subtype map `N.subtype`. -/
recall Module.support_subset_of_injective

/- Lemma 10.40.9 (3): if `Q` is a quotient module of an `R`-module `M`, then
`Module.support R Q ⊆ Module.support R M`. This is the canonical theorem
`Module.support_subset_of_surjective`, specialized to the quotient map onto `Q`. -/
recall Module.support_subset_of_surjective

/- Lemma 10.40.9 (4): for a short exact sequence `0 → N → M → Q → 0` of `R`-modules, the support
of `M` is the union of the supports of `N` and `Q`. This is exactly the canonical theorem
`Module.support_of_exact`. -/
recall Module.support_of_exact
