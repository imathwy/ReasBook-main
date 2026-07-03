import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Projective
import Mathlib.Order.Disjoint
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_129_1_Eilenberg_s_lemma (from Chap15) -/
universe u v w x

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommMonoid Q] [Module R Q]
variable {F : Type x} [AddCommMonoid F] [Module R F] [Module.Free R F]

/- Domain sampling:
- primary domain: infinitely generated free modules and absorption of direct summands;
- owner abstractions inspected upstream: `Module.Projective.iff_split`, `Module.Projective.of_split`,
  `LinearMap.inl`/`LinearMap.fst`, and `LinearEquiv.prodCongr`;
- source-facing layer: the complement-based hypothesis `(P × Q) ≃ₗ[R] F`;
- core/canonical layer: the retract data `i : P →ₗ[R] F`, `s : F →ₗ[R] P` with `s.comp i = id`;
- bridge/view below: recover that retract canonically from the given product equivalence. -/

/-- Canonical split-data form of Eilenberg absorption: a direct summand of a non-finitely generated
free module is absorbed by that free module. -/
theorem nonfinitely_generated_free_absorption_of_split
    (hF : ¬ Module.Finite R F) (i : P →ₗ[R] F) (s : F →ₗ[R] P)
    (hs : s.comp i = LinearMap.id) :
    Nonempty ((P × F) ≃ₗ[R] F) := sorry

-- Proof sketch: extract the canonical retract `P ↪ F ↠ P` from the chosen equivalence
-- `(P × Q) ≃ₗ[R] F`, then apply the split-data form above.
/-- Lemma 15.129.1 (Eilenberg's lemma): if `F` is a free `R`-module that is not finitely
generated and `P ⊕ Q ≅ F`, then `P ⊕ F ≅ F`; in Lean, the binary direct sums are modeled by the
product modules `P × Q` and `P × F`. -/
theorem prod_nonfinitely_generated_free_absorption
    (hF : ¬ Module.Finite R F) (e : (P × Q) ≃ₗ[R] F) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  let i : P →ₗ[R] F := e.toLinearMap ∘ₗ LinearMap.inl R P Q
  let s : F →ₗ[R] P := LinearMap.fst R P Q ∘ₗ e.symm.toLinearMap
  have hs : s.comp i = LinearMap.id := by
    ext p
    simp [i, s]
  simpa [i, s] using nonfinitely_generated_free_absorption_of_split hF i s hs

end

/-! ### Lemma_15_129_2 (from Chap15) -/
universe u v

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

open LinearMap

/- Domain sampling:
- primary domain: projective modules, their canonical lift into a free module, and Eilenberg
  absorption for non-finitely generated free modules;
- sampled owner declarations: `Module.Projective.iff_split`,
  `nonfinitely_generated_free_absorption_of_split`, `Module.Free.of_equiv`, and `LinearMap.inl`;
- source-facing layer: existence of a free `R`-module `F` for which `P ⊕ F` is free;
- core/canonical layer: the retract data `i : P →ₗ[R] M`, `r : M →ₗ[R] P` with `r.comp i = id`
  supplied by `Module.Projective.iff_split`, together with the free ambient module
  `M × (ℕ →₀ R)` on which Eilenberg absorption acts;
- bridge/view: `Module.Projective.iff_split` is semiring-level and therefore returns only
  `AddCommMonoid` data on the free witness. Over a ring, the source statement is about honest
  modules, so the public witness here is refined to an `AddCommGroup`; this is derived canonically
  from the ring-module structure and should not remain hidden behind the weaker semimodule-level
  interface. -/

-- Proof sketch: use `Module.Projective.iff_split` to realize `P` as a retract of some free module
-- `M`. Stabilize `M` by the countable free module `ℕ →₀ R`, whose non-finite generation is forced
-- unless `R` is subsingleton. Then apply the split-data form of Eilenberg's lemma from Lemma
-- `15.129.1` and transport freeness back along the resulting equivalence.
namespace Module.Projective

/-- Lemma 15.129.2: for a projective `R`-module `P`, there exists a free `R`-module `F` such that
`P ⊕ F` is free; in Lean, the binary direct sum is modeled by the product module `P × F`. -/
theorem exists_free_prod_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      Module.Free R (P × F) := by
  classical
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    letI : Subsingleton P := Module.subsingleton R P
    exact ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨M, _, _, _, i, r, hr⟩ := iff_split.mp (inferInstance : Module.Projective R P)
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let G := ℕ →₀ R
    have hG_not_finite : ¬ Module.Finite R G := by
      intro hG
      rcases Module.finite_finsupp_self_iff.1 hG with hsub | hfin
      · exact hR hsub
      · letI : Finite ℕ := hfin
        exact (inferInstance : Infinite ℕ).false
    have hMG_not_finite : ¬ Module.Finite R (M × G) := by
      intro hMG
      letI : Module.Finite R (M × G) := hMG
      have hG_finite : Module.Finite R G :=
        Module.Finite.of_surjective (snd R M G) snd_surjective
      exact hG_not_finite hG_finite
    let i' : P →ₗ[R] M × G := inl R M G ∘ₗ i
    let r' : M × G →ₗ[R] P := r ∘ₗ fst R M G
    have hr' : r'.comp i' = LinearMap.id := by
      ext p
      simpa [i', r'] using LinearMap.congr_fun hr p
    obtain ⟨e⟩ := nonfinitely_generated_free_absorption_of_split hMG_not_finite i' r' hr'
    exact ⟨M × G, inferInstance, inferInstance, inferInstance, Module.Free.of_equiv e.symm⟩

end Module.Projective

end

/-! ### Lemma_15_129_3 (from Chap15) -/
universe u v

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain sampling:
- primary domain: projective modules, free ambient modules, and complemented submodules;
- sampled owner declarations: `Module.Projective.exists_free_prod_free`,
  `Module.Free.chooseBasis`, `Finsupp.supported`, and `Complementeds (Submodule R M)`;
- source-facing layer: existence of a finite free direct summand of `F ⊕ P` containing `(0, s)`;
- core/canonical layer: the owner `Complementeds (Submodule R (F × P))` for the summand itself,
  with the finite-support submodule `Finsupp.supported R R S` as the canonical free finite model
  on basis coordinates;
- bridge/view: Lemma `15.129.2` provides the free ambient module `F₀ × P`, and a chosen basis of
  that free module identifies finite-support coordinate submodules with finite free complemented
  submodules in the ambient module.

Primitive data are the ambient finite free module `F` and the complemented submodule `K ≤ F × P`.
The properties `Module.Free R K` and `Module.Finite R K` are standard derived API on that owner
and should remain theorem-level output, not primitive wrapper fields. -/

-- Proof sketch: invoke `Module.Projective.exists_free_prod_free` to place `P` in a free ambient
-- module `F₀ × P`. In coordinates with respect to a chosen basis of that free module, the element
-- `(0, s)` has finite support, so it lies in the canonical finite-support submodule
-- `Finsupp.supported R R S`. Transport that finite free complemented submodule back to the ambient
-- module, then shrink the first factor of `F₀` to a finite free summand containing all first
-- coordinates occurring in this transported submodule so that the witness lives in some `F × P`.
/-- Lemma 15.129.3: for a projective `R`-module `P` and an element `s : P`, there exist a finite
free `R`-module `F` and a finite free direct summand `K` of `F ⊕ P`, modeled in Lean as a
complemented submodule `K ≤ F × P` together with the standard properties `Module.Free R K` and
`Module.Finite R K`, such that `(0, s) ∈ K`. -/
theorem exists_finiteFree_directSummand_prod_contains_zero_s (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F),
      ∃ K : Complementeds (Submodule R (F × P)),
        Module.Free R (K : Submodule R (F × P)) ∧
          Module.Finite R (K : Submodule R (F × P)) ∧ ((0 : F), s) ∈ (K : Submodule R (F × P)) :=
    sorry

end

/-! ### Lemma_15_129_4 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

/- Domain triage:
- primary domain: projective modules, cyclic submodules, and complemented direct summands;
  `exists_free_directSummand_submodule_containing`, `IsComplemented`, and the canonical finiteness
  API for cyclic spans;
- sampled maximal-local owner declaration: `MaximalSpectrum R`, the chapter-project owner for
  hypotheses indexed by maximal ideals and their canonical localizations;
- source-facing layer: perturb `s` by an element of `M` so that the cyclic submodule it generates
  becomes a free direct summand;
- core/canonical layer: the chapter owner abstraction is
  `Module.HasFiniteFreeComplementSummandProperty R P`, while the cyclic submodule `R ∙ (s + m)` is
  the canonical source-facing object produced in this perturbation step;
- bridge/view: the present theorem is the source-facing bridge feeding that owner-level story.
  Because the underlying submodule is canonically fixed as `R ∙ (s + m)`, the direct-summand datum
  is best expressed by `IsComplemented (R ∙ (s + m))` rather than by a separate complemented-owner
  witness plus an equality back to the cyclic span. Freeness is an ordinary property of that fixed
  submodule and finiteness is already a derived instance.

Primitive data are the perturbation `m : M` and the resulting cyclic submodule `R ∙ (s + m)`.
Complementedness and freeness are derived properties of that fixed cyclic span, and finiteness is
already supplied canonically because cyclic spans are finitely generated, so none of them should
remain bundled inside a separate existential owner witness in the public API. -/

-- Proof sketch: reduce modulo the Jacobson radical and work over the Noetherian quotient `R ⧸
-- Ring.jacobson R`, where a Noetherian-induction argument on closed subsets of `Spec R` produces a
-- perturbation `s + m` together with a splitting `P →ₗ[R] R`. That splitting identifies the cyclic
-- span of `s + m` with a free direct summand of `P`.
/-- Lemma 15.129.4: if `R ⧸ Ring.jacobson R` is Noetherian, `P` is a projective `R`-module whose
localizations at maximal ideals are not finitely generated, and `s` together with the submodule
`M` generates `P`, then there exists a perturbation `m : M` such that the cyclic submodule
generated by `s + m` is itself a free direct summand of `P`, expressed directly by the properties
`IsComplemented (R ∙ (s + m))` and `Module.Free R (R ∙ (s + m))`; its finiteness is the canonical
cyclic-span finiteness consequence and need not be carried as extra data. -/
theorem exists_perturbation_with_cyclicSpan_free_directSummand
    (M : Submodule R P) (s : P)
    (hP : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    (hspan : R ∙ s + M = ⊤) :
    ∃ m : M, IsComplemented (R ∙ (s + m)) ∧ Module.Free R (R ∙ (s + m)) := sorry

end

/-! ### Lemma_15_129_5 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

/- Domain triage:
- primary domain: projective modules, complemented direct summands, and finite stably free
  submodules;
- sampled owner declarations: `MaximalSpectrum R`, `IsComplemented`, `Module.Finite`,
  `Module.StablyFree`, and `exists_perturbation_with_cyclicSpan_free_directSummand`;
- `source-facing`: the numbered item says a chosen element `s : P` lies in a finite stably free
  direct summand of `P`;
- `core/canonical`: the ambient owner is the concrete submodule `M : Submodule R P` together with
  the standard predicates `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`,
  while maximal-local conditions are canonically indexed by `MaximalSpectrum R`;
- `bridge/view`: the theorem below is already the source-facing existence statement, so there is no
  additional owner-level bridge to a stronger free-summand property in this file.

Primitive data are only the ambient projective module `P`, the chosen element `s`, and the
submodule `M ≤ P` containing `s`. Complementedness, finiteness, and stable freeness are canonical
properties of that fixed submodule, so the public source-facing statement should expose `M`
directly instead of packaging it first as an element of `Complementeds (Submodule R P)`. -/

-- Proof sketch: first apply Lemma `15.129.3` to place `(0, s)` inside a finite free direct summand
-- of `F ⊕ P`. Induct on the finite free rank of `F`, reducing to a complemented finite stably free
-- submodule of `R ⊕ P` containing `(0, s)`. Then use Lemma `15.129.4` on the complement to split
-- off a free rank-one summand and identify the kernel of the resulting projection `P → K''` as a
-- complemented submodule of `P` containing `s`; this kernel is finite stably free because
-- `R ⊕ ker(π')` is isomorphic to the sum of the original finite stably free summand and a free
-- rank-one summand.
/-- Lemma 15.129.5: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a projective `R`-module
whose localizations at maximal ideals are not finitely generated, then every element `s : P` is
contained in a finite stably free direct summand of `P`, expressed directly by a submodule
`M ≤ P` together with `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`. -/
theorem exists_finiteStablyFree_directSummand_submodule_containing
    (s : P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M :=
  sorry

end

/-! ### Theorem_15_129_6 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

open Module

/- Domain triage:
- primary domain: projective modules, countable generation, and freeness criteria via free
  and stably free direct summands;
- sampled owner declarations:
  `Module.CountablyGenerated`,
  `exists_finiteStablyFree_directSummand_submodule_containing`,
  `exists_perturbation_with_cyclicSpan_free_directSummand`,
  and `Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty`;
- `source-facing`: the numbered theorem is the Chapter 15 freeness statement for one countably
  generated projective module under the maximal-localization infinite-rank hypothesis;
- `core/canonical`: the ambient owners are `Module.CountablyGenerated R P` and `Module.Free R P`;
- `bridge/view`: Lemma `15.129.5` gives the source-facing finite stably free summands, and
  Lemma `15.129.4` is the free rank-one splitting step used in the Stacks proof to upgrade those
  summands to a countable free decomposition.

Primitive data are the ambient projective module `P`, the countable-generation hypothesis, and the
local maximal-ideal non-finiteness condition. The Chapter 10 owner
`Module.HasFiniteFreeComplementSummandProperty R P` is stronger than Lemma `15.129.5` and is not
the direct output of Lemma `15.129.5`, so the source-facing theorem should remain the main public
entry while this file provides a separate bridge to that owner. The maximal-local condition should
still use the chapter’s canonical `MaximalSpectrum R` indexing rather than an `Ideal` parameter
with a hidden `[IsMaximal]` binder. -/

namespace Module

/-- Bridge from the Chapter 15 maximal-local hypothesis to the Chapter 10 owner
`HasFiniteFreeComplementSummandProperty`. This packages the repeated finite-summand splitting
argument needed to invoke Lemma `10.85.2`, while keeping the source-facing freeness theorem below
as the main public statement for Theorem `15.129.6`. -/
theorem hasFiniteFreeComplementSummandProperty_of_localizations_not_finite
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    HasFiniteFreeComplementSummandProperty R P := by
  sorry

end Module

-- Proof sketch: first pass from the maximal-local hypothesis to the Chapter 10 owner
-- `Module.HasFiniteFreeComplementSummandProperty R P` via the bridge theorem above, then apply
-- Lemma `10.85.2`.
/-- Theorem 15.129.6: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a countably generated
projective `R`-module whose localizations at maximal ideals are not finitely generated, then `P`
is free. This is the Lean rendering of the condition that each `P_𝔪` has infinite rank. -/
theorem free_of_countablyGenerated_projective_of_localizations_not_finite
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    Free R P := by
  exact Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty hcg
    (Module.hasFiniteFreeComplementSummandProperty_of_localizations_not_finite hnotFiniteAtMax)

end
