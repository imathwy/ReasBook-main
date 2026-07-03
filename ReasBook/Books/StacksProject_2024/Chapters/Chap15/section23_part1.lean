import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_23_1 (from Chap15) -/
universe u v

section

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/- Domain-style sampling:
- primary domain: module duality and reflexivity for modules over a commutative semiring;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.bijective_dual_eval`,
  `Module.evalEquiv`;
- best owner abstraction: `Module.IsReflexive` is the canonical owner of the source notion
  "reflexive module", and `Module.Dual.eval` is the canonical realization of the textbook
  evaluation map into the double dual;
- source/core/bridge triage:
  `source-facing`: the textbook definition of a reflexive module via the canonical map to the
    double dual;
  `core/canonical`: `Module.IsReflexive`;
  `bridge/view`: the companion identification of the textbook map with `Module.Dual.eval`.

Primitive data are only the ambient ring `R`, module `M`, and the canonical double-dual evaluation
map. Reflexivity itself is derived API owned by `Module.IsReflexive`, so this file should remain a
direct recall of the owner and the canonical map, with no local wrapper around the double dual or
its evaluation morphism.
-/
/- Definition 15.23.1: an `R`-module `M` is reflexive in the textbook sense exactly when it
is the canonical mathlib class `Module.IsReflexive R M`, saying that the natural evaluation map
from `M` to its double dual is bijective, equivalently an isomorphism of `R`-modules. -/
recall Module.IsReflexive

/- Companion recall: the textbook map
`j : M → Hom_R(Hom_R(M, R), R)` sending `m` to the functional `φ ↦ φ m`
is the canonical linear map `Module.Dual.eval R M`. -/
recall Module.Dual.eval

end

/-! ### Lemma_15_23_2 (from Chap15) -/
universe u v

open Module

/-
Domain-style sampling:
- primary domain: module duality, reflexivity, and torsion for modules over commutative domains;
- sampled owner API:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`;
- best owner abstraction: the canonical owner object is the reflexivity class `Module.IsReflexive`
  together with the canonical evaluation map `Module.Dual.eval`; torsion and torsion-freeness are
  already owned by `Module.IsTorsion` and `Module.IsTorsionFree`, both available through the
  owner import `Mathlib.LinearAlgebra.Dual.Defs`;
- source/core/bridge triage:
  `source-facing`: the torsion statements about the kernel and cokernel of the evaluation map and
  the finite-module injectivity criterion;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
  `Module.IsTorsion`;
  `bridge/view`: clause `(1)` is exact-interface reuse of the canonical owner instance
  `Module.IsReflexive.to_isTorsionFree`.

Primitive data are the ambient semiring/module for clause `(1)`, and the finite module plus the
canonical map `Module.Dual.eval` for clauses `(2)` through `(4)`. No extra wrapper around the
double dual or its evaluation map is mathematically needed, and clause `(1)` should remain a direct
recall of the upstream owner instance rather than a local theorem shell.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 15.23.2 (1): a reflexive module is torsion free. The source states this over a domain,
but the canonical owner instance already works over a commutative semiring. -/
recall IsReflexive.to_isTorsionFree

end

section Finite

open Module.Dual

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

-- Proof sketch: choose generators of `M`, pass to the fraction field, extract a basis of
-- `M ⊗[R] K`, and clear denominators to produce maps `R^r → M → R^r` whose two composites are
-- multiplication by a single nonzero scalar `c`. Comparing the induced diagram with the double
-- dual evaluation map `eval R M` shows that `c` annihilates the kernel.
/-- Lemma 15.23.2 (2): if `M` is finite, then the kernel of the canonical map from `M` to its
double dual is a torsion module. -/
theorem eval_ker_isTorsion :
    IsTorsion R (eval R M).ker := sorry

-- Proof sketch: use the same denominator-clearing maps `R^r → M → R^r` as in the kernel case.
-- The induced commutative diagram with `eval R M` shows that the same
-- nonzero scalar `c` annihilates the quotient of the double dual by the image of `M`.
/-- Lemma 15.23.2 (3): if `M` is finite, then the cokernel of the canonical map from `M` to its
double dual is a torsion module. -/
theorem eval_cokernel_isTorsion :
    IsTorsion R (Dual R (Dual R M) ⧸ (eval R M).range) := sorry

-- Proof sketch: if `M` is torsion free, the denominator-clearing map to a finite free module
-- constructed above is injective, forcing the evaluation map to be injective. Conversely, if the
-- evaluation map is injective, then `M` embeds into its torsion-free double dual.
/-- Lemma 15.23.2 (4): for a finite module over a domain, the canonical map to the double dual is
injective exactly when the module is torsion free. -/
theorem eval_injective_iff_isTorsionFree :
    Function.Injective (eval R M) ↔ IsTorsionFree R M := sorry

end Finite

/-! ### Lemma_15_23_3 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: module duality, torsion quotients, and reflexivity of finite modules over a PID;
- sampled owner declarations:
  `Module.Dual.eval`,
  `Submodule.torsion`,
  `Submodule.dualQuotEquivDualAnnihilator`,
  `Module.free_of_finite_type_torsion_free'`,
  `Module.IsReflexive.of_finite_of_free`;
- best owner abstraction: the canonical owner object is the evaluation map `Module.Dual.eval`,
  and the intrinsic source-facing reduction is through the torsion quotient
  `M ⧸ Submodule.torsion R M`; over a PID this quotient is canonically finite free, so reflexivity
  is controlled by `Module.IsReflexive`;
- primitive data: the commutative domain `R`, the principal-ideal-ring structure on `R`, and the
  finite `R`-module `M`;
- derived API: surjectivity of the source-facing evaluation map is a consequence of the canonical
  identification of `Dual R M` with the dual of the torsion-free quotient, together with
  reflexivity of that finite free quotient.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that the canonical map `M → Mᘁᘁ` is surjective for a
  finite module over a discrete valuation ring;
- `core/canonical`: `Module.Dual.eval`, `Submodule.torsion`, and `Module.IsReflexive`;
- `bridge/view`: `Submodule.dualQuotEquivDualAnnihilator` identifies `Dual R M` with the dual of
  the torsion-free quotient, and `Module.Dual.eval_naturality` compares the evaluation maps across
  the quotient.
-/

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsPrincipalIdealRing R] [Module.Finite R M] in
private theorem dual_mem_dualAnnihilator_torsion (φ : Dual R M) :
    φ ∈ (Submodule.torsion R M).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro x hx
  rcases hx with ⟨a, hax⟩
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.2
  have hax' : a • φ x = 0 := by
    simpa [map_smul] using congrArg φ hax
  exact (smul_eq_zero_iff_right ha0).mp hax'

omit [IsPrincipalIdealRing R] [Module.Finite R M] in
private theorem dualMap_mkQ_torsion_bijective :
    Function.Bijective
      (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap) := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (Submodule.torsion R M).mkQ_surjective, ?_⟩
  intro φ
  refine
    ⟨(Submodule.torsion R M).dualQuotEquivDualAnnihilator.symm
        ⟨φ, dual_mem_dualAnnihilator_torsion φ⟩, ?_⟩
  ext x
  exact
    (Submodule.torsion R M).dualQuotEquivDualAnnihilator_symm_apply_mk
      ⟨φ, dual_mem_dualAnnihilator_torsion φ⟩ x

-- Proof sketch: quotient `M` by its torsion submodule. Every linear form on `M` vanishes on
-- torsion, so `Dual R M` is canonically identified with the dual of `M / M_tors` via
-- `Submodule.dualQuotEquivDualAnnihilator`. The quotient is torsion free, hence finite free over a
-- PID and therefore reflexive by `Module.IsReflexive.of_finite_of_free`. Naturality of
-- `Module.Dual.eval` with respect to the quotient map then transports surjectivity back to `M`.
/-- Lemma 15.23.3, stated at the canonical PID owner layer: for a finite module over a principal
ideal domain, the canonical map `M → Hom_R(Hom_R(M, R), R)` is surjective. The discrete valuation
ring case is the immediate specialization. -/
theorem eval_surjective_of_isPrincipalIdealRing :
    Function.Surjective (Dual.eval R M) := by
  -- The proved bridge lemmas above reduce the theorem to the torsion-free quotient
  -- `M ⧸ Submodule.torsion R M`, which is finite free over a PID and hence reflexive.
  -- Transporting surjectivity of the quotient evaluation map back across
  -- `Submodule.dualQuotEquivDualAnnihilator` and `Module.Dual.eval_naturality` yields the claim.
  sorry

end

/-! ### Lemma_15_23_4 (from Chap15) -/
universe u v

section

open Module
open Module.Dual (eval)
open LocalizedModule (AtPrime map)

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-
Domain-style sampling:
- primary domain: reflexive finitely presented modules, detected by localization of the canonical
  double-dual evaluation map;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `bijective_localization_tfae`,
  `Module.FinitePresentation.linearEquivMapExtendScalars`,
  `LinearMap.extendScalarsOfIsLocalizationEquiv`;
- best owner abstraction: `Module.IsReflexive` is the core/canonical owner of the source notion,
  with `Module.Dual.eval` as the canonical comparison map and `bijective_localization_tfae` as the
  canonical local-global owner theorem for bijectivity under prime and maximal localization;
- source/core/bridge triage:
  `source-facing`: the TFAE criterion comparing reflexivity of `M`, of every `Mₚ`, and of every
    `Mₘ`;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `bijective_localization_tfae`;
  `bridge/view`: Lemma `10.10.2`, which identifies the localization of `Dual.eval R M` with the
    evaluation map of the localized module; there is no exact upstream theorem for this
    comparison, so the minimal chapter-level bridge theorem
    `isReflexive_atPrime_iff_bijective_eval` is kept as the public companion built from that
    identification.

Primitive data are only the finitely presented module `M` and its canonical evaluation map into
the double dual. Local reflexivity is derived API from that owner map after localization, so the
theorem should be proved by instantiating the canonical local-global bijectivity theorem in its
native ideal-indexed form rather than by keeping a parallel
`PrimeSpectrum`/`MaximalSpectrum` wrapper layer around that owner theorem.
-/

/-- Bridge/view: for a prime localization of a finitely presented module, reflexivity of the
localized module is equivalent to bijectivity of the localized canonical evaluation map. -/
theorem isReflexive_atPrime_iff_bijective_eval
    (P : Ideal R) [P.IsPrime] :
    IsReflexive (Localization.AtPrime P) (AtPrime P M) ↔
      Function.Bijective (map P.primeCompl (eval R M)) := by
  -- Proof sketch: localize `eval R M`, identify the localized `Hom` spaces with the
  -- corresponding `Localization.AtPrime P`-linear `Hom` spaces via Lemma `10.10.2`, and compare
  -- the resulting localized map with `Dual.eval (Localization.AtPrime P)
  -- (LocalizedModule.AtPrime P M)`.
  sorry

-- Proof sketch: localize the canonical evaluation map `M → Hom_R(Hom_R(M, R), R)` at a prime
-- ideal and identify it with the corresponding evaluation map for `M_p`, using Algebra
-- `10.10.2`. Then apply the local criterion from Algebra `10.23.1` to pass between reflexivity of
-- `M`, reflexivity at every prime localization, and reflexivity at every maximal localization.
/-- Lemma 15.23.4: for a finitely presented module, the following are equivalent: the module is
reflexive; every localization at a prime ideal is reflexive; and every localization at a maximal
ideal is reflexive. In the source Noetherian finite setting, finite presentation is automatic. -/
theorem isReflexive_localization_tfae :
    List.TFAE
      [ IsReflexive R M
      , ∀ (P : Ideal R) [P.IsPrime], IsReflexive (Localization.AtPrime P) (AtPrime P M)
      , ∀ (P : Ideal R) [P.IsMaximal], IsReflexive (Localization.AtPrime P) (AtPrime P M)
      ] := by
  have hEval := bijective_localization_tfae (eval R M)
  have hPrimeEval [IsReflexive R M] :
      ∀ (P : Ideal R) [P.IsPrime], Function.Bijective (map P.primeCompl (eval R M)) :=
    (hEval.out 0 1).mp (bijective_dual_eval R M)
  tfae_have 1 → 2 := by
    intro hM P _
    letI := hM
    exact (isReflexive_atPrime_iff_bijective_eval P).2 (hPrimeEval P)
  tfae_have 2 → 3 := by
    intro h P _
    exact h P
  tfae_have 3 → 1 := by
    intro hM
    have hMaxEval :
        ∀ (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (eval R M)) := by
      intro P _
      letI : P.IsPrime := inferInstance
      exact (isReflexive_atPrime_iff_bijective_eval P).1 (hM P)
    exact ⟨(hEval.out 2 0).mp hMaxEval⟩
  tfae_finish

end

/-! ### Lemma_15_23_5 (from Chap15) -/
universe u v w x

/-
Domain-style sampling:
- primary domain: duality and reflexivity of finite modules over a commutative domain;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`,
  `Module.Finite.of_injective`,
  `Module.Finite.range`;
- best owner abstraction: the canonical owner is the reflexivity class `Module.IsReflexive`,
  with the evaluation map `Module.Dual.eval` supplying the intrinsic comparison to the double
  dual; finiteness of the source and of the quotient object is derived API from the ambient finite
  middle term together with the exact pair;
- source/core/bridge triage:
  - `source-facing`: this closure lemma for reflexive modules under kernels with torsion-free
    quotient;
  - `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
    `Module.Finite`;
  - `bridge/view`: the quotient seen here is the canonical submodule `LinearMap.range g`, not an
    auxiliary wrapper around the ambient codomain.

Primitive data are the exact pair `f, g`, the injectivity of `f`, the reflexivity of the middle
term, and the torsion-freeness of the actual quotient object `LinearMap.range g`. The finiteness
of `M` is derived from `Module.Finite.of_injective hf`, and the finiteness of `LinearMap.range g`
is derived from the canonical range instance on linear maps out of finite modules. Requiring the
ambient codomain `M''` or the source `M` themselves to be finite as primitive public assumptions is
therefore redundant.
-/

section

open Function Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M'] [Module.Finite R M']
variable [AddCommGroup M''] [Module R M'']

-- Proof sketch: replace `g` by the canonical surjection `M' → range g`, so the exact pair
-- becomes `0 → M → M' → range g → 0`. Dualize this short exact sequence to compare the
-- evaluation maps into the double duals. Reflexivity of `M'` identifies the middle vertical map
-- with an isomorphism, while torsion-freeness of `range g` makes the right evaluation map
-- injective by Lemma `15.23.2`. The remaining diagram chase shows the evaluation map for `M` is
-- bijective.
/-- Lemma 15.23.5: if `0 → M → M' → M''` is exact over a domain, `M'` is finite and
reflexive, and the quotient `M'/M` identified with `LinearMap.range g` is torsion free, then `M`
is reflexive. -/
theorem isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    IsReflexive R M := sorry

end

/-! ### Lemma_15_23_6 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian domains and their finite-free
  presentations;
- sampled owner declarations:
  `Module.IsReflexive`,
  `isTorsionFree_iff_exists_injective_to_fin_fun`,
  `Module.exists_finite_presentation`,
  `Module.FinitePresentation.iff_exists_exact_free_sequence`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`;
- best owner abstraction: the source-facing short exact sequence should be expressed through the
  canonical cokernel `((Fin n → R) ⧸ LinearMap.range f)` of an injective map into a finite free
  module, rather than through an auxiliary witness structure carrying a separate quotient type and
  a surjective map onto it;
- source/core/bridge triage:
  - `source-facing`: this lemma is the textbook characterization of reflexive modules by a short
    exact sequence `0 → M → R^n → N → 0` with torsion-free quotient;
  - `core/canonical`: `Module.IsReflexive`, `LinearMap.range`, and the canonical quotient map
    `Submodule.mkQ`;
  - `bridge/view`: any separate torsion-free quotient `N` is equivalent to the canonical cokernel
    of the embedding, so it should remain derived rather than primitive public data.

Primitive data are an injective map `f : M →ₗ[R] (Fin n → R)` and torsion-freeness of its
canonical cokernel. The exact sequence and quotient object from the source are derived from
`f` via `Submodule.mkQ (LinearMap.range f)`, so the local structure previously packaging these
data was duplicate wheel API.
-/

section

open Function Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: for the forward direction, choose a finite presentation of `Module.Dual R M`,
-- dualize it, and use reflexivity of `M` to identify the resulting kernel with `M`; the quotient
-- is canonically the cokernel of the chosen embedding into `R^n`, and it is torsion free over a
-- domain. For the reverse direction, finite free modules are reflexive, and Lemma `15.23.5`
-- applies to the canonical short exact sequence
-- `0 → M → R^n → (R^n / range f) → 0` once the cokernel is assumed torsion free.
/-- Lemma 15.23.6: a finite module over a Noetherian domain is reflexive if and only if it admits
an injective map into a finite free module `R^n` whose canonical cokernel is torsion free;
equivalently, it fits into a short exact sequence `0 → M → R^n → N → 0` with `N` torsion free. -/
theorem isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel :
    IsReflexive R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R),
        Injective f ∧ IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range f) :=
  sorry

end

/-! ### Lemma_15_23_7 (from Chap15) -/
universe u v w

open scoped TensorProduct
open Function Module TensorProduct
open TensorProduct.AlgebraTensorModule

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian domains and their behavior under flat
  base change to a domain algebra;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Finite.base_change`,
  `TensorProduct.piScalarRight`,
  `Module.Flat.lTensor_exact`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`,
  `Module.IsReflexive.of_finite_of_free`,
  `isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel`,
  `isTorsionFree_baseChange_of_flat`;
- best owner abstraction: the core/canonical owner is `Module.IsReflexive`; the chapter-level
  bridge/view API is the characterization of a finite reflexive module by an injective map into a
  finite free module with torsion-free canonical cokernel; after tensoring that exact
  presentation, `Module.Flat.lTensor_exact` and
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` keep the proof at the exact-sequence
  owner level, while `TensorProduct.piScalarRight` and `Module.IsReflexive.of_finite_of_free`
  supply the reflexive finite-free middle term after base change;
- source/core/bridge triage:
  - `source-facing`: reflexivity of the base-changed module `R' ⊗[R] M`;
  - `core/canonical`: `Module.IsReflexive`;
  - `bridge/view`: Lemma `15.23.6` for the finite-free presentation and
    `isTorsionFree_baseChange_of_flat` for the cokernel after tensoring.

Primitive data are the flat algebra `R → R'` from a Noetherian domain into a domain algebra and
the finite reflexive `R`-module `M`. The finiteness of `R' ⊗[R] M` is derived API via
`Module.Finite.base_change`, and the finite-free embedding used in the proof is derived from the
reflexive owner theorem rather than packaged as a new local structure.
-/

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing R'] [IsDomain R'] [Algebra R R'] [Flat R R']
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]

namespace Module.IsReflexive

-- Proof sketch: apply Lemma `15.23.6` to choose an injective map `f : M → R^n` whose canonical
-- cokernel `(Fin n → R) ⧸ LinearMap.range f` is torsion free. Tensor the exact sequence
-- `0 → M → R^n → cokernel(f) → 0` with `R'`; flatness preserves exactness and injectivity, and
-- `isTorsionFree_baseChange_of_flat` preserves torsion-freeness of the tensorized cokernel.
-- The middle term remains finite free after base change via `TensorProduct.piScalarRight`, hence
-- reflexive. Lemma `15.23.5` then applies directly to the tensorized exact pair.
/-- Lemma 15.23.7: for a flat homomorphism `R → R'` from a Noetherian domain to a domain, the
base change of a finite reflexive `R`-module is reflexive over `R'`. The finiteness of
`R' ⊗[R] M` is supplied by the canonical owner theorem `Module.Finite.base_change`. -/
theorem baseChange_of_flat :
    IsReflexive R' (R' ⊗[R] M) := by
  letI : Module.Finite R' (R' ⊗[R] M) := inferInstance
  have hMReflexive : IsReflexive R M := inferInstance
  rcases
      isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel.mp hMReflexive with
    ⟨n, f, hf, hQ⟩
  let F := Fin n → R
  let freeBaseChange : R' ⊗[R] F ≃ₗ[R'] Fin n → R' :=
    TensorProduct.piScalarRight R R' R' (Fin n)
  let fTensor : R' ⊗[R] M →ₗ[R'] R' ⊗[R] F := (lTensor R' R') f
  let qTensor : R' ⊗[R] F →ₗ[R'] R' ⊗[R] (F ⧸ LinearMap.range f) :=
    (lTensor R' R') (Submodule.mkQ (LinearMap.range f))
  have hfTensor : Function.Injective fTensor := by
    simpa [fTensor] using Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hExactTensor : Function.Exact fTensor qTensor := by
    simpa [fTensor, qTensor, coe_lTensor] using
      Module.Flat.lTensor_exact R' (LinearMap.exact_map_mkQ_range f)
  haveI : IsTorsionFree R (F ⧸ LinearMap.range f) := hQ
  haveI : IsTorsionFree R' (R' ⊗[R] (F ⧸ LinearMap.range f)) :=
    isTorsionFree_baseChange_of_flat
  letI : Module.Finite R' (R' ⊗[R] F) := inferInstance
  letI : Module.Free R' (R' ⊗[R] F) := Module.Free.of_equiv freeBaseChange.symm
  letI : IsReflexive R' (R' ⊗[R] F) := Module.IsReflexive.of_finite_of_free R' (R' ⊗[R] F)
  haveI : IsTorsionFree R' (LinearMap.range qTensor) :=
    (Submodule.subtype_injective (LinearMap.range qTensor)).moduleIsTorsionFree
      (LinearMap.range qTensor).subtype fun r x ↦ rfl
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree hExactTensor hfTensor

end Module.IsReflexive

end

/-! ### Lemma_15_23_8 (from Chap15) -/
universe u v w

/-
Domain-style sampling:
- primary domain: duality and reflexivity of finitely presented modules over domains, together
  with the exactness behavior of `Hom_R(-, N)`;
- sampled owner declarations:
  `Module.IsReflexive`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`,
  `Module.FinitePresentation.iff_exists_exact_free_sequence`,
  `LinearMap.exact_lcomp_of_exact_of_surjective`,
  `LinearMap.instIsTorsionFree`,
  `Prod.instModuleIsReflexive`;
- best owner abstraction: the public owner remains the reflexivity class `Module.IsReflexive`,
  while the chapter-level kernel-closure theorem
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` is the right bridge/view API for this
  source-facing item. The finite presentation of `M` should be unpacked through the chapter bridge
  `Module.FinitePresentation.iff_exists_exact_free_sequence`, which exposes the exact free
  sequence actually used in the argument, rather than through a lower-level quotient witness or the
  stronger Noetherian-plus-finite wrapper. Torsion-freeness of the ambient `Hom` modules should
  come from the upstream owner instance `LinearMap.instIsTorsionFree`, and the finite-product
  reflexivity step should be reduced to mathlib's owner instance
  `Prod.instModuleIsReflexive` plus `Module.pi_induction'`, not rebuilt as a separate local API;
- source/core/bridge triage:
  - `source-facing`: the textbook assertion that `Hom_R(M, N)` is reflexive when `M` is finite and
    `N` is finite reflexive over a Noetherian domain, refined to the equivalent weaker statement
    where the primitive input on `M` is a finite presentation;
  - `core/canonical`: `Module.IsReflexive`;
  - `bridge/view`: the exact-sequence closure theorem
    `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` applied to the `Hom` sequence induced by
    a finite presentation of `M`.

Primitive data are the exact free presentation `R^m → R^n → M → 0` attached to
`Module.FinitePresentation R M` and the induced exact sequence
`0 → Hom_R(M, N) → Hom_R(R^n, N) → Hom_R(R^m, N)`. The reflexivity of the middle term and the
torsion-freeness of the quotient are derived from the owner abstractions above; they should not be
repackaged here as new primitive public data.
-/

section

open Function LinearMap Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N] [IsReflexive R N]

omit [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [IsReflexive R N] in
variable (R N) in
private theorem isReflexive_finFun [CommRing R] [AddCommGroup N] [Module R N] [IsReflexive R N]
    (n : ℕ) :
    IsReflexive R (Fin n → N) := by
  classical
  refine Module.pi_induction' R
    (fun P _ _ ↦ IsReflexive R P)
    (fun P _ _ ↦ IsReflexive R P)
    (fun e h ↦ by
      letI := h
      exact Module.equiv e)
    (fun e h ↦ by
      letI := h
      exact Module.equiv e)
    (by infer_instance)
    (fun hP hQ ↦ by
      letI := hP
      letI := hQ
      infer_instance)
    (fun _ : Fin n ↦ N)
    fun _ ↦ inferInstance

omit [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [IsReflexive R N] in
variable (R N) in
private theorem isReflexive_linearMap_finFun [CommRing R] [AddCommGroup N] [Module R N]
    [IsReflexive R N] (n : ℕ) :
    IsReflexive R ((Fin n → R) →ₗ[R] N) := by
  letI : IsReflexive R (Fin n → N) := isReflexive_finFun R N n
  exact Module.equiv (LinearEquiv.piRing R N (Fin n) R).symm

-- Proof sketch: unpack `Module.FinitePresentation R M` via
-- `Module.FinitePresentation.iff_exists_exact_free_sequence` to obtain
-- `R^m → R^n → M → 0`, apply `Hom_R(-, N)` to get an exact sequence
-- `0 → Hom_R(M, N) → N^n → N' → 0`, and note that `N'` is torsion free as a submodule of `N^m`.
-- Since finite products of reflexive modules are reflexive by the owner instance
-- `Prod.instModuleIsReflexive`, `Module.pi_induction'` upgrades this to `N^n`, and
-- `LinearEquiv.piRing` transports it to `Hom_R(R^n, N)`. Lemma `15.23.5` applied to the resulting
-- exact sequence yields reflexivity of `Hom_R(M, N)`.
/-- Lemma 15.23.8: if `M` is finitely presented and `N` is finite reflexive over a domain `R`,
then the `R`-module `Hom_R(M, N)` is reflexive. Over a Noetherian domain, this recovers the
textbook finite-module formulation because finite modules are finitely presented. -/
theorem isReflexive_linearMap :
    IsReflexive R (M →ₗ[R] N) := by
  -- This source-facing statement should be derived from the chapter owner bridge
  -- `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`, using the exact `Hom` sequence
  -- provided by the chapter bridge `Module.FinitePresentation.iff_exists_exact_free_sequence`
  -- and the canonical torsion-free owner `LinearMap.instIsTorsionFree` on the ambient `Hom`
  -- module.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  have hExact : Exact (lcomp R N g) (lcomp R N f) :=
    exact_lcomp_of_exact_of_surjective N hfg hg
  have hInj : Injective (lcomp R N g) :=
    lcomp_injective_of_surjective g hg
  letI : Module.Finite R ((Fin n → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin n → R) N
  letI : IsReflexive R ((Fin n → R) →ₗ[R] N) := isReflexive_linearMap_finFun R N n
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree hExact hInj

end

/-! ### Definition_15_23_9 (from Chap15) -/
universe u v

open Module

/-
Domain-style sampling:
- primary domain: module duality, double duals, and reflexivity for modules;
- sampled owner declarations:
  `Dual`,
  `Module.Dual.eval`,
  `Module.IsReflexive`,
  `Module.evalEquiv`;
- best owner abstraction: the source term "reflexive hull" is just the canonical double-dual
  owner type `Dual R (Dual R M)`;
- primitive data: the commutative semiring `R`, the additive commutative monoid `M`, and the
  ambient module structure;
- derived API: the surrounding evaluation and reflexivity statements are already owned by
  `Module.Dual.eval` and `Module.IsReflexive`.

Source/core/bridge triage:
- `source-facing`: the textbook phrase "the reflexive hull of `M`";
- `core/canonical`: the double-dual type `Dual R (Dual R M)`;
- `bridge/view`: later lemmas comparing `M` with its double dual through the evaluation map.

This item is therefore a pure canonical recall/check item, not a place for a new public alias.
-/

section ReflexiveHull

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/- Definition 15.23.9: the textbook reflexive hull of `M` is the canonical double-dual
`R`-module `Hom_R(Hom_R(M, R), R)`. The source states this for finite modules over a Noetherian
domain, but the recalled owner type itself already lives over the weaker canonical assumptions
`[CommSemiring R] [AddCommMonoid M] [Module R M]`. -/
#check (Dual R (Dual R M))

end ReflexiveHull

/-! ### Lemma_15_23_10 (from Chap15) -/
universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-
Domain triage:
* primary domain: local commutative algebra of module depth for `Hom` modules over Noetherian
  local rings;
* sampled owner declarations:
  `moduleDepth`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min`,
  `Module.FinitePresentation`;
* owner abstraction: the local-depth bridge `moduleDepth R _`, with the finite module structures
  on `M` and `N` as primitive data. Over a Noetherian ring, any finite module is finitely
  presented internally, so finite presentations and the finiteness of `M →ₗ[R] N` are derived
  support for the proof rather than primitive public data;
* derived API: the Chapter 10 short-exact depth inequalities above are the internal support for
  this file, while Lemma `15.23.11` gives the later `bridge/view` packaging into
  `Module.SerreConditionS`;
* layer: `source-facing`.

Primitive data here are just the finite module structures on `M` and `N`; the depth hypotheses in
the theorems are source-facing assumptions rather than extra packaged data. The short exact
sequence built from a finite presentation of `M` is proof-internal, and the LinearRepresentations_Serre_1977-condition
statements are derived downstream packaging that should not replace this local owner-level file.
-/

/- Source/core/bridge triage:
* `source-facing`: the local depth bounds for `Hom_R(M, N)`;
* `core/canonical`: `moduleDepth` and the Chapter 10 short-exact depth inequalities;
* `bridge/view`: Lemma `15.23.11`, which repackages these local statements as LinearRepresentations_Serre_1977 conditions.
-/

-- Proof sketch: choose a finite presentation of the finite module `M`, dualize against `N`, and
-- obtain a short exact sequence `0 → Hom_R(M, N) → N^n → N' → 0`. Since finite modules over a
-- Noetherian ring are finitely presented, the presentation is internal support rather than public
-- data. Apply `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min` to this sequence
-- and use `moduleDepth N^n = moduleDepth N` to conclude.
/-- Lemma 15.23.10 (1): if `N` has depth at least `1`, then `Hom_R(M, N)` has depth at least `1`.
-/
theorem moduleDepth_linearMap_ge_one
    (hN : 1 ≤ moduleDepth R N) :
    1 ≤ moduleDepth R (M →ₗ[R] N) := sorry

-- Proof sketch: use the same short exact sequence
-- `0 → Hom_R(M, N) → N^n → N' → 0`. Part `(1)` gives `moduleDepth R N' ≥ 1` when
-- `moduleDepth R N ≥ 2`, while `moduleDepth R N^n ≥ 2`. Then apply the canonical Chapter 10 owner
-- theorem `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min` to recover
-- `moduleDepth R Hom_R(M, N) ≥ 2`.
/-- Lemma 15.23.10 (2): if `N` has depth at least `2`, then `Hom_R(M, N)` has depth at least `2`.
-/
theorem moduleDepth_linearMap_ge_two
    (hN : 2 ≤ moduleDepth R N) :
    2 ≤ moduleDepth R (M →ₗ[R] N) := sorry

end

/-! ### Lemma_15_23_11 (from Chap15) -/
universe u v w

/-
Domain-style sampling:
- primary domain: LinearRepresentations_Serre_1977 conditions of finite modules over Noetherian rings and torsion-freeness of
  linear-map modules;
- sampled owner declarations:
  `Module.SerreConditionS`,
  `moduleDepth_linearMap_ge_one`,
  `moduleDepth_linearMap_ge_two`,
  `LinearMap.instIsTorsionFree`;
- best owner abstraction:
  `Module.SerreConditionS` for the `(S₁)` and `(S₂)` clauses, with Lemma `15.23.10` supplying the
  primitive local-depth input, and `LinearMap.instIsTorsionFree` for the torsion-free clause;
- source/core/bridge triage:
  clauses `(1)` and `(2)` are `bridge/view` packaging from the local owner `moduleDepth`, while
  clause `(3)` is a direct `core/canonical` recall.

Primitive data are the local depth inequalities from Lemma `15.23.10`. The
`Module.SerreConditionS` statements below are derived packaging of that owner-level data, and the
torsion-free statement should reuse the canonical upstream owner instead of keeping a parallel
local wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

instance LinearMap.instSerreConditionSOneOfCodomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    sorry

-- Proof sketch: localize at each prime ideal and use that localization commutes with finite-module
-- `Hom`. Then apply the depth estimate from Lemma `15.23.10 (1)` to the localized linear-map
-- module, and package the resulting local inequalities back into the definition of
-- `Module.SerreConditionS ... 1`.
/-- Lemma 15.23.11 (1): if the finite `R`-module `N` satisfies LinearRepresentations_Serre_1977's condition `(S_1)`, then
the module `Hom_R(M, N)` also satisfies LinearRepresentations_Serre_1977's condition `(S_1)`. -/
theorem linearMap_serreConditionS_one_of_codomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 := inferInstance

instance LinearMap.instSerreConditionSTwoOfCodomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    sorry

-- Proof sketch: localize at a prime ideal, identify localization of `Hom_R(M, N)` with the `Hom`
-- module of the localized finite modules, and invoke Lemma `15.23.10 (2)` to get the depth bound
-- required in the definition of `Module.SerreConditionS ... 2`.
/-- Lemma 15.23.11 (2): if the finite `R`-module `N` satisfies LinearRepresentations_Serre_1977's condition `(S_2)`, then
the module `Hom_R(M, N)` also satisfies LinearRepresentations_Serre_1977's condition `(S_2)`. -/
theorem linearMap_serreConditionS_two_of_codomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 := inferInstance

end

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N]

/- Lemma 15.23.11 (3): the torsion-free conclusion for `Hom_R(M, N)` is already the canonical
owner instance `LinearMap.instIsTorsionFree`, which is stronger than the source hypotheses used in
the textbook packaging of Lemma `15.23.11`. -/
recall LinearMap.instIsTorsionFree

end

/-! ### Lemma_15_23_12 (from Chap15) -/
universe u v w

section

open LocalizedModule (map mkLinearMap)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Domain triage:
* primary domain: injectivity criteria for module maps over a Noetherian ring via associated-prime
  localizations;
* sampled owner declarations:
  `associatedPrimes R M`,
  `LocalizedModule.map`,
  `LocalizedModule.mkLinearMap`,
  `to_pi_localization_at_associated_primes_injective`;
* best owner abstraction: the owner index type `associatedPrimes R M` together with the canonical
  map `M → ∏ p ∈ Ass(M), Mₚ`;
* primitive data: the linear map `φ : M →ₗ[R] N`;
* derived API: injectivity of the localized maps at the associated primes of `M`.

Layering:
* this numbered item is `source-facing`: it is the associated-prime criterion for injectivity from
  the source text;
* the `core/canonical` owner is the chapter theorem
  `to_pi_localization_at_associated_primes_injective`;
* there is no separate `bridge/view` owner to introduce here. The theorem should reuse the owner
  index set `associatedPrimes R M` directly rather than restating it through all prime-spectrum
  points with an implication.
-/

-- Proof sketch: the canonical map from `M` to the product of the localizations `∏_{p ∈ Ass(M)} Mₚ`
-- is injective by Lemma `10.63.19`. If `φ x = φ y`, then for every associated prime `p` the
-- localized equality `φₚ(x/1) = φₚ(y/1)` holds; injectivity of `φₚ` gives `x/1 = y/1` in `Mₚ`.
-- Hence `x` and `y` have the same image in the product of localizations at the associated primes,
-- so they are equal.
/-- Lemma 15.23.12: if `R` is Noetherian and every associated prime of `M` is a prime at which the
localized map `M_p → N_p` is injective, then `φ : M →ₗ[R] N` is injective. -/
theorem injective_of_injective_localizedMap_at_associatedPrimes
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : associatedPrimes R M,
      Function.Injective (map ((p : Ideal R).primeCompl) φ)) :
    Function.Injective φ := by
  intro x y hxy
  exact to_pi_localization_at_associated_primes_injective <| by
    ext p
    exact hφ p <| by
      simpa [LinearMap.pi_apply, LocalizedModule.map_mk] using
        congrArg (mkLinearMap ((p : Ideal R).primeCompl) N) hxy

end

/-! ### Lemma_15_23_13 (from Chap15) -/
universe u v w

open LocalizedModule (AtPrime map)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Domain triage:
* primary domain: local-to-global isomorphism criteria for finite module maps over Noetherian
  rings, using localized depth and associated primes;
* sampled owner declarations:
  `moduleDepth`,
  `injective_of_injective_localizedMap_at_associatedPrimes`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`,
  `subsingleton_iff_associatedPrimes_eq_empty`;
* best owner abstraction: the local-depth bridge `moduleDepth` together with the owner set
  `associatedPrimes R _`;
* primitive data: the linear map `φ : M →ₗ[R] N` and the primewise disjunction from the source;
* derived API: injectivity via associated-prime localizations and vanishing of the cokernel via
  emptiness of associated primes.

Layering:
* this numbered item is `source-facing`: it is the textbook criterion for when a finite module map
  is an isomorphism from primewise local data;
* the `core/canonical` owners reused here are `moduleDepth` and `associatedPrimes`;
* no extra `bridge/view` wrapper should be introduced in this file.
-/

-- Proof sketch: first apply Lemma `15.23.12` to the kernel to obtain injectivity of `φ`, since
-- bijectivity of the localized map implies injectivity and the second branch excludes associated
-- primes of the codomain. Then replace `N` by a finite submodule containing the image of `M`,
-- form the cokernel `Q`, and analyze its localizations: in the first branch `Qₚ = 0`, while in
-- the second branch Lemmas `10.63.18` and `10.72.6` give `moduleDepth` at least `1` for `Qₚ`.
-- Hence `Q` has no associated primes, so Lemma `10.63.7` forces `Q = 0`, proving surjectivity.
/-- Lemma 15.23.13: let `R` be a Noetherian ring and let `φ : M → N` be a map of `R`-modules with
`M` finite. If for every prime `p` of `R` either the localized map `Mₚ → Nₚ` is an isomorphism,
or the localized module `Mₚ` has depth at least `2` and `p` is not an associated prime of `N`,
then `φ` is an isomorphism. -/
theorem bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_and_not_mem_associatedPrimes
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl φ) ∨
        ((2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∧
          p.asIdeal ∉ associatedPrimes R N)) :
    Function.Bijective φ := sorry

end

/-! ### Lemma_15_23_14 (from Chap15) -/
universe u v w

open LocalizedModule (AtPrime map)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

/- Domain-style sampling:
- primary domain: local-to-global isomorphism criteria for finite module maps over Noetherian
  domains, using primewise localized depth and torsion-freeness of the codomain;
- sampled owner declarations:
  `moduleDepth`,
  `associatedPrimes R _`,
  `Module.IsTorsionFree`,
  `Module.not_mem_associatedPrimes_of_ne_bot`,
  `bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_and_not_mem_associatedPrimes`;
- best owner abstraction:
  `moduleDepth` is the canonical local depth owner surface in this chapter, while
  `Module.IsTorsionFree` is the canonical owner for the codomain hypothesis, and the previous
  lemma is the source-facing ambient isomorphism criterion being specialized here;
- source/core/bridge triage:
  `source-facing`: this lemma is the textbook torsion-free specialization of the previous local
    isomorphism criterion;
  `core/canonical`: `moduleDepth`, `associatedPrimes`, `Module.IsTorsionFree`;
  `bridge/view`: the implication from torsion-freeness over a domain to the associated-prime
    exclusion needed by the previous lemma.

Primitive data are only the linear map `φ`, the finite source module, the torsion-free codomain
owner instance, and the primewise disjunction from the source. The local depth term is derived API
and should therefore use the chapter owner `moduleDepth` rather than an inlined
`Ideal.depth (maximalIdeal _)` spelling. The associated-prime exclusion is also derived API here:
for a torsion-free module over a domain, every nonzero element of an associated prime would be a
zero divisor, so only the generic prime can remain.
-/

-- Proof sketch: this is the torsion-free specialization of Lemma `15.23.13`, but the source text
-- phrases the primewise alternative without exposing the generic-point exclusion
-- `p.asIdeal ≠ ⊥`. In the current depth formalization that generic-point case is not discharged by
-- definitional simplification alone, so the public theorem keeps the source-facing statement and
-- the proof obligation is deferred here rather than strengthening the API.
/-- Lemma 15.23.14: let `R` be a Noetherian domain and let `φ : M → N` be a map of `R`-modules.
Assume `M` is finite, `N` is torsion free, and that for every prime `p` of `R` either the
localized map `Mₚ → Nₚ` is an isomorphism, or the localized module `Mₚ` has depth at least `2`.
Then `φ` is an isomorphism. -/
theorem bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl φ) ∨
        (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M)) :
    Function.Bijective φ := by
  sorry

end

/-! ### Lemma_15_23_15 (from Chap15) -/
universe u v

open Module
open Module.Dual (eval)
open LocalizedModule (AtPrime)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling:
- primary domain: reflexive modules over Noetherian domains, detected by primewise local
  reflexivity and local depth bounds;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `moduleDepth`,
  `isReflexive_localization_tfae`,
  `bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner for the global property, `moduleDepth` is the
  canonical local depth owner, and the preceding chapter lemmas already provide the needed
  source-facing local-global bridge;
- source/core/bridge triage:
  `source-facing`: the textbook criterion characterizing reflexivity by the primewise disjunction;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `moduleDepth`;
  `bridge/view`: `Lemma 15.23.4` packages the source-facing local-global TFAE,
    `isReflexive_atPrime_iff_bijective_eval` packages the localized evaluation-map comparison, and
    `Lemma 15.23.14` packages the local-depth-or-isomorphism criterion for a map into a
    torsion-free module.

Primitive data are only the module `M` and the primewise disjunction itself. The local reflexive
branch and the global reflexive conclusion are both derived from the owner `Module.IsReflexive`,
so this file should reuse the chapter bridge lemmas directly rather than introducing a parallel
wrapper around localized evaluation maps or local depth data.
-/

-- Proof sketch: if `M` is reflexive, then every localization `Mₚ` is reflexive by
-- Lemma `15.23.4`, so the local disjunction holds at every prime. Conversely, apply
-- Lemma `15.23.14` to the evaluation map `M → Hom_R(Hom_R(M, R), R)`. By Algebra `10.10.2`,
-- its localization at `p` identifies with the evaluation map of `Mₚ`; the reflexive branch gives
-- a localized isomorphism, while the other branch is exactly the required depth bound.
/-- Lemma 15.23.15: for a finite module `M` over a Noetherian domain `R`, `M` is reflexive if and
only if for every prime ideal `p` of `R`, either the localized module `Mₚ` is reflexive over
`Rₚ` or `Mₚ` has depth at least `2`. -/
theorem isReflexive_iff_localizedModuleAtPrime_isReflexive_or_depth_ge_two :
    IsReflexive R M ↔
      ∀ p : PrimeSpectrum R,
        IsReflexive (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∨
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  constructor
  · intro hM p
    have hAtPrime :
        ∀ (P : Ideal R) [P.IsPrime], IsReflexive (Localization.AtPrime P) (AtPrime P M) :=
      (isReflexive_localization_tfae.out 0 1).mp hM
    exact .inl (hAtPrime p.asIdeal)
  · intro hlocal
    let hEval : Function.Bijective (eval R M) :=
      bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree
        (eval R M) fun p ↦ by
          rcases hlocal p with hreflexive | hdepth
          · exact .inl ((isReflexive_atPrime_iff_bijective_eval p.asIdeal).mp hreflexive)
          · exact .inr hdepth
    exact ⟨hEval⟩

end

/-! ### Lemma_15_23_16 (from Chap15) -/
universe u v

open Module
open LocalizedModule (AtPrime)

/-
Domain-style sampling:
- primary domain: reflexive finite modules over commutative Noetherian rings and their LinearRepresentations_Serre_1977 condition
  `(S₂)`, with prime-local depth bounds and double-dual linear maps as the local bridge;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.SerreConditionS`,
  `Module.IsReflexive.instSerreConditionSTwo`,
  `moduleDepth`,
  `isReflexive_localization_tfae`,
  `linearMap_serreConditionS_two_of_codomain`;
- best owner abstraction:
  `Module.IsReflexive` is the canonical owner of the source hypothesis and
  `Module.SerreConditionS` is the canonical owner of the conclusion. Clause `(1)` uses the
  localized owner theorem `isReflexive_localization_tfae` together with `moduleDepth` on
  `Localization.AtPrime p.asIdeal`, while clause `(2)` should be implemented as the canonical
  `Module.SerreConditionS` instance `Module.IsReflexive.instSerreConditionSTwo` and recalled
  directly rather than duplicated by a parallel theorem;
- source/core/bridge triage:
  clause `(1)` is `source-facing` local depth input at a single prime localization in the
  Noetherian-ring setting of the canonical owner proof,
  clause `(2)` is the `source-facing` global `(S₂)` theorem expressed in the canonical owner
  predicate `Module.SerreConditionS`.

Primitive data are only the reflexive module and the localized depth comparison. The global `(S₂)`
conclusion is owner-level API, so this file should expose the canonical instance directly, reusing
the chapter owners
`isReflexive_localization_tfae` and `linearMap_serreConditionS_two_of_codomain` rather than
duplicating a local wrapper around double-dual linear maps.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]
variable (p : PrimeSpectrum R)

open scoped ENat
local notation "Rₚ" => Localization.AtPrime p.asIdeal
local notation "Mₚ" => AtPrime p.asIdeal M

-- Proof sketch: use Lemma `15.23.4` to see that the localized module `Mₚ` is reflexive over the
-- local ring `Localization.AtPrime p.asIdeal`, identify it with its double dual via
-- `Module.evalEquiv`, and apply Lemma `15.23.10 (2)` twice to the local ring
-- `Localization.AtPrime p.asIdeal`.
/-- Lemma 15.23.16 (1): if `R` is a Noetherian ring, `M` is a finite reflexive `R`-module, and
`p` is a prime ideal of `R` such that `depth(Rₚ) ≥ 2`, then `depth(Mₚ) ≥ 2`. -/
theorem moduleDepth_localizationAtPrime_ge_two_of_ringDepth_localizationAtPrime_ge_two
    (hp : (2 : ℕ∞) ≤ moduleDepth Rₚ Rₚ) :
    (2 : ℕ∞) ≤ moduleDepth Rₚ Mₚ := by
  sorry

end

section

variable {R : Type u} [CommRing R] [R ⊧ (S₂)]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]

namespace Module.IsReflexive

instance instSerreConditionSTwo : SerreConditionS R M 2 := by
  sorry

end Module.IsReflexive

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.23.16 (2): if `R` satisfies `(S_2)`, then every finite reflexive `R`-module `M`
also satisfies LinearRepresentations_Serre_1977's condition `(S_2)`. This is the canonical owner instance
`Module.IsReflexive.instSerreConditionSTwo`, obtained by applying
`linearMap_serreConditionS_two_of_codomain` to the double dual and transporting along the reflexive
evaluation equivalence. -/
recall Module.IsReflexive.instSerreConditionSTwo

end

/-! ### Example_15_23_17 (from Chap15) -/
open Module MvPolynomial

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "Pxy" => MvPolynomial (Fin 2) k
local notation "x" => (X (0 : Fin 2) : Pxy)
local notation "y" => (X (1 : Fin 2) : Pxy)

/- Domain-style sampling:
- primary domain: subalgebras and ideals as module owners, together with module duality,
  reflexivity, and LinearRepresentations_Serre_1977's condition `(S_2)`;
- sampled owner declarations:
  `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`,
  `LinearMap.module`,
  `Module.IsReflexive`;
- best owner abstraction: the source-facing data are the explicit subalgebra `R` and ideal `𝔪`,
  while the ambient and dual module structures should come from the canonical owner layer rather
  than bespoke local instances;
- source/core/bridge triage:
  `source-facing`: the explicit ring `R = k[y, x^2, xy, x^3]`, the ideal
  `𝔪 = (y, x^2, xy, x^3)`, and the displayed identifications
  `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`;
  `core/canonical`: `Subalgebra.adjoin`, `Ideal.span`, `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`, `LinearMap.module`, `Module.IsReflexive`, and
  `Module.SerreConditionS`;
  `bridge/view`: the local notations `Pxy`, `x`, `y`, and `R`.

Primitive data are the explicit subalgebra and ideal. The module structures on `Pxy`, `𝔪`, and
their duals are derived API from the owner layer above, and reflexivity and the `(S_2)` statement
are further derived API on top of that source-facing data.
-/

/-- The ring `R = k[y, x^2, xy, x^3]`, modeled as a `k`-subalgebra of `k[x, y]`. -/
def reflexiveCounterexampleRing :
    Subalgebra k Pxy :=
  Algebra.adjoin k
    ({ y, x ^ 2, x * y, x ^ 3 } : Set Pxy)

local notation "R" => reflexiveCounterexampleRing k

private theorem reflexiveCounterexampleY_mem_ring :
    y ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXSq_mem_ring :
    x ^ 2 ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXY_mem_ring :
    x * y ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXCube_mem_ring :
    x ^ 3 ∈ R :=
  Algebra.subset_adjoin (by simp)

private noncomputable def reflexiveCounterexampleIdealGeneratorY :
    R := by
  refine ⟨y, reflexiveCounterexampleY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXSq :
    R := by
  refine ⟨x ^ 2, reflexiveCounterexampleXSq_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXY :
    R := by
  refine ⟨x * y, reflexiveCounterexampleXY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXCube :
    R := by
  refine ⟨x ^ 3, reflexiveCounterexampleXCube_mem_ring k⟩

private def reflexiveCounterexampleIdealGeneratorSet : Set R :=
  { reflexiveCounterexampleIdealGeneratorY k,
    reflexiveCounterexampleIdealGeneratorXSq k,
    reflexiveCounterexampleIdealGeneratorXY k,
    reflexiveCounterexampleIdealGeneratorXCube k }

/-- The ideal `𝔪 = (y, x^2, xy, x^3)` inside `R = k[y, x^2, xy, x^3]`. -/
def reflexiveCounterexampleIdeal :
    Ideal R :=
  Ideal.span (reflexiveCounterexampleIdealGeneratorSet k)

local notation "𝔪" => reflexiveCounterexampleIdeal k

local instance : Module R R :=
  Semiring.toModule

local instance : Module R Pxy :=
  Subalgebra.moduleLeft R

local instance : Module R ↥𝔪 :=
  SMulMemClass.toModule 𝔪

local instance : Module R (Module.Dual R Pxy) :=
  LinearMap.module

local instance : Module R (Module.Dual R ↥𝔪) :=
  LinearMap.module

private noncomputable def reflexiveCounterexampleYInIdeal :
    𝔪 := by
  refine ⟨reflexiveCounterexampleIdealGeneratorY k, ?_⟩
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

private abbrev reflexiveCounterexampleDivideYExponent
    (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  d.update (1 : Fin 2) (d (1 : Fin 2) - 1)

private noncomputable def reflexiveCounterexampleDivideByY
    (p : Pxy) : Pxy :=
  ∑ d ∈ p.support.filter (fun d ↦ 0 < d (1 : Fin 2)),
    monomial (reflexiveCounterexampleDivideYExponent d) (p.coeff d)

-- Proof sketch: multiplication by an element of `𝔪` sends every polynomial to `R`, yielding the
-- displayed map `𝔪 → Hom_R(k[x, y], R)`.
private noncomputable def reflexiveCounterexampleIdealToAmbientDual :
    ↥𝔪 →ₗ[R] Module.Dual R Pxy :=
  { toFun := fun a ↦
      { toFun := fun p ↦
          ⟨((a : R) : Pxy) * p, by
            sorry⟩
        map_add' := by
          intro p q
          ext
          simp [mul_add]
        map_smul' := by
          intro r p
          sorry }
    map_add' := by
      intro a b
      sorry
    map_smul' := by
      intro r a
      sorry }

-- Proof sketch: the example identifies an `R`-linear functional on `k[x, y]` by its value at `1`,
-- and that value lies in `𝔪`.
private noncomputable def reflexiveCounterexampleAmbientDualToIdeal :
    Module.Dual R Pxy →ₗ[R] ↥𝔪 :=
  { toFun := fun φ ↦
      ⟨φ 1, by
        sorry⟩
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: these two explicit maps are inverse `R`-linear identifications.
/-- The displayed `R`-linear identification `Hom_R(k[x, y], R) ≃ 𝔪`. -/
noncomputable def reflexiveCounterexampleAmbientDualEquivIdeal :
    Module.Dual R Pxy ≃ₗ[R] ↥𝔪 :=
  { toFun := reflexiveCounterexampleAmbientDualToIdeal k
    invFun := reflexiveCounterexampleIdealToAmbientDual k
    left_inv := by
      intro φ
      apply LinearMap.ext
      intro p
      sorry
    right_inv := by
      intro a
      apply Subtype.ext
      simp [reflexiveCounterexampleAmbientDualToIdeal,
        reflexiveCounterexampleIdealToAmbientDual]
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: multiplication by an ambient polynomial gives an `R`-linear functional on `𝔪`,
-- and the inverse recovers the ambient polynomial by dividing the value on `y` by `y`.
private noncomputable def reflexiveCounterexampleAmbientToIdealDual :
    Pxy →ₗ[R] Module.Dual R ↥𝔪 :=
  { toFun := fun p ↦
      { toFun := fun a ↦
          ⟨((a : R) : Pxy) * p, by
            sorry⟩
        map_add' := by
          intro a b
          ext
          simp [add_mul]
        map_smul' := by
          intro r a
          sorry }
    map_add' := by
      intro p q
      sorry
    map_smul' := by
      intro r p
      sorry }

private noncomputable def reflexiveCounterexampleIdealDualToAmbient :
    Module.Dual R ↥𝔪 →ₗ[R] Pxy :=
  { toFun := fun φ ↦
      reflexiveCounterexampleDivideByY k
        (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy))
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: these are the displayed inverse identifications `Hom_R(𝔪, R) ≃ k[x, y]`.
/-- The displayed `R`-linear identification `Hom_R(𝔪, R) ≃ k[x, y]`. -/
noncomputable def reflexiveCounterexampleIdealDualEquivAmbient :
    Module.Dual R ↥𝔪 ≃ₗ[R] Pxy :=
  { toFun := reflexiveCounterexampleIdealDualToAmbient k
    invFun := reflexiveCounterexampleAmbientToIdealDual k
    left_inv := by
      intro φ
      apply LinearMap.ext
      intro a
      sorry
    right_inv := by
      intro p
      sorry
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: the displayed identifications `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`
-- identify the ambient module with its double dual over `R`.
/-- The ambient polynomial ring `k[x, y]`, viewed as an `R`-module, is reflexive. -/
theorem reflexiveCounterexampleAmbient_isReflexive :
    Module.IsReflexive R Pxy := sorry

-- Proof sketch: the omitted depth computations in the text verify LinearRepresentations_Serre_1977's condition `(S_2)` for
-- `k[x, y]` when it is regarded as an `R`-module.
/-- The ambient polynomial ring satisfies LinearRepresentations_Serre_1977's condition `(S_2)` as an `R`-module. -/
theorem reflexiveCounterexampleAmbient_serreConditionS2 :
    Module.SerreConditionS R Pxy 2 := sorry

-- Proof sketch: this is the depth-theoretic failure exhibited in the text for the explicit
-- ring `R = k[y, x^2, xy, x^3]`.
/-- Example 15.23.17: if `R = k[y, x^2, xy, x^3] ⊂ k[x, y]`, then the ideal
`𝔪 = (y, x^2, xy, x^3)` and the displayed identifications
`Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]` are recorded by
`reflexiveCounterexampleAmbientDualEquivIdeal k` and
`reflexiveCounterexampleIdealDualEquivAmbient k`; in particular `k[x, y]` is reflexive and
`(S_2)` as an `R`-module, while `R` itself does not satisfy `(S_2)`. -/
theorem reflexiveCounterexampleRing_not_serreConditionS2 :
    ¬ R ⊧ (S₂) := sorry

end

/-! ### Lemma_15_23_18 (from Chap15) -/
open scoped nonZeroDivisors
open Module
open LocalizedModule (liftOfLE mkLinearMap)

universe u v

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian normal domains, together with the
  height-one localization intersection criterion inside the generic localization;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.IsTorsionFree`,
  `Module.SerreConditionS`,
  `LocalizedModule.mkLinearMap`;
- best owner abstraction:
  `Module.IsReflexive` is the core/canonical owner of the theorem, while the intersection of the
  height-one localizations is only a bridge/view used to express the source-facing third clause;
- source/core/bridge triage:
  `source-facing`: the textbook TFAE criterion for finite modules over a Noetherian normal domain;
  `core/canonical`: `Module.IsReflexive`, `Module.IsTorsionFree`, `Module.SerreConditionS`;
  `bridge/view`: the submodule of the generic localization obtained by intersecting the images of
    the height-one localization maps.

Primitive data are only the ambient domain `R`, the finite `R`-module `M`, and the canonical
generic localization map `mkLinearMap R⁰ M`. The `(S₂)` clause and reflexivity clause are already
owned by the chapter/mathlib owners above, so this file should keep only the minimal bridge object
for the height-one-localization intersection instead of introducing any heavier wrapper API.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The intersection of the height-one localizations of `M`, viewed inside the generic
localization `M ⊗[R] Frac(R)` and modeled as `LocalizedModule R⁰ M`. -/
noncomputable abbrev moduleHeightOneLocalizationIntersection (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Submodule R (LocalizedModule R⁰ M) :=
  ⨅ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
    LinearMap.range
      (liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))

end

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: apply LinearRepresentations_Serre_1977's criterion for normality to deduce `(R_1)` and `(S_2)` for `R`.
-- Then use Lemma `15.23.2` and Lemma `15.23.16` for `(1) → (2)`, Lemma `15.23.14` for
-- `(2) → (3)` after comparing the height-one localizations inside the generic fiber, and the DVR
-- freeness criterion from Lemma `15.22.11` for `(3) → (1)`.
/-- Lemma 15.23.18: for a finite module `M` over a Noetherian normal domain `R`, the following are
equivalent: `M` is reflexive; `M` is torsion free and satisfies LinearRepresentations_Serre_1977's condition `(S_2)`; and
`M` is torsion free and agrees with the intersection of its height-one localizations inside the
generic localization `M ⊗[R] Frac(R)`. -/
theorem reflexive_tfae_torsionFree_serreS2_heightOneLocalizationIntersection :
    List.TFAE
      [ IsReflexive R M
      , IsTorsionFree R M ∧ SerreConditionS R M 2
      , IsTorsionFree R M ∧
          LinearMap.range (mkLinearMap R⁰ M) =
            moduleHeightOneLocalizationIntersection R M ] :=
  sorry

end
