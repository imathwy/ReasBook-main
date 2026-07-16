import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Lemma_15_60_1
import stacks_proof.stacks_project.Chap15.Lemma_15_75_9

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.78.3:
- primary domain: perfectness and negative derived-fiber homology criteria for pseudo-coherent
  bounded-below objects of `D(R)` under localization at primes and maximal ideals;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra_isPerfect`,
  `primeResidueFieldDerivedHomology`,
  `K.IsPseudoCoherent`,
  `MaximalSpectrum`;
- best owner abstraction: this file is `source-facing` for the local/global `TFAE`, while the
  core/canonical owners are `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, the standard derived
  base-change notation `K ⊗[R]^L[S]`, the prime-fiber homology owner
  `primeResidueFieldDerivedHomology`, and the chapter-level maximal-local owner
  `MaximalSpectrum R`;
- primitive vs. derived:
  primitive data are `K`, the prime and maximal localization tests, the residue-field homology
  vanishing tests, and the bounded-below hypothesis in the final theorem;
  derived API is the fiber homology object itself, already owned upstream by
  `primeResidueFieldDerivedHomology`, so this file should reuse that owner instead of restating
  raw homology-functor applications, with maximal tests transported through the canonical bridge
  `m.toPrimeSpectrum : PrimeSpectrum R`;
- source/core/bridge triage:
  `source-facing`: the two `TFAE` theorems below;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `K.IsGE`, `derivedTensorWithAlgebra`,
    and `primeResidueFieldDerivedHomology`;
  `bridge/view`: the prime-localization specialization of `derivedTensorWithAlgebra_isPerfect`.
-/

/-- Helper for Lemma 15.78.3: the degree-`i` homology of the derived fiber
`K \otimes_R^{\mathbf L} \kappa(\mathfrak p)`. -/
abbrev primeResidueFieldDerivedHomology
    (𝔭 : PrimeSpectrum R) (K : DMod) (i : ℤ) :
    ModuleCat 𝔭.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat 𝔭.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[𝔭.asIdeal.ResidueField])

/-- The ideal underlying a point of `Spec R` is prime, viewed as a local typeclass instance. -/
local instance (𝔭 : PrimeSpectrum R) : 𝔭.asIdeal.IsPrime := 𝔭.isPrime

/-- Helper for Lemma 15.78.3: over a field, a zero module has rank `0`. -/
lemma module_rank_eq_zero_of_isZero
    {k : Type u} [Field k] {M : ModuleCat k} (hM : IsZero M) :
    Module.rank k M = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton] at hM
  classical
  let b := Module.Free.chooseBasis k M
  by_cases hι : Nonempty (Module.Free.ChooseBasisIndex k M)
  · rcases hι with ⟨i⟩
    have hne : b i ≠ 0 := b.ne_zero i
    exact False.elim (hne (hM.elim _ _))
  · have hempty : IsEmpty (Module.Free.ChooseBasisIndex k M) := not_nonempty_iff.mp hι
    calc
      Module.rank k M = Cardinal.mk (Module.Free.ChooseBasisIndex k M) := by
        simpa [b] using (Module.Basis.mk_eq_rank'' b).symm
      _ = 0 := Cardinal.mk_eq_zero_iff.mpr hempty

/-- Helper for Lemma 15.78.3: eventual vanishing of residue-field homology implies eventual
rank-`0` residue-field homology. -/
lemma eventually_module_rank_zero_of_eventually_isZero_primeResidueFieldDerivedHomology
    {K : DMod} (𝔭 : PrimeSpectrum R)
    (hzero :
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero (primeResidueFieldDerivedHomology 𝔭 K i)) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      Module.rank 𝔭.asIdeal.ResidueField (primeResidueFieldDerivedHomology 𝔭 K i) = 0 := by
  rcases hzero with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  -- Proof comment: over the residue field, each zero homology object has rank `0`.
  intro i hi
  exact module_rank_eq_zero_of_isZero (ha i hi)

/-- Helper for Lemma 15.78.3: bounded-below residue-field homology vanishing at a prime gives an
away-local perfectness witness via Lemma `15.78.1`. -/
lemma exists_away_isPerfect_of_eventually_zero_primeResidueFieldDerivedHomology
    {K : DMod} (𝔭 : PrimeSpectrum R) (hK : K.IsPseudoCoherent)
    (hboundedBelow : ∃ n : ℤ, K.IsGE n)
    (hzero :
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero (primeResidueFieldDerivedHomology 𝔭 K i)) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      (K ⊗[R]^L[Localization.Away f]).IsPerfect := by
  have hrank :
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        Module.rank 𝔭.asIdeal.ResidueField (primeResidueFieldDerivedHomology 𝔭 K i) = 0 := by
    -- Proof comment: reduce the source hypothesis to the rank-zero form used by Lemma `15.78.1`.
    exact
      eventually_module_rank_zero_of_eventually_isZero_primeResidueFieldDerivedHomology
        (K := K) 𝔭 hzero
  -- Route correction: the proof skeleton is now reduced to the exact owner theorem from
  -- Lemma `15.78.1` after the local rank-zero translation above.
  -- TODO: import and apply
  -- `exists_away_isPerfect_of_primeResidueFieldDerivedHomology_vanishing_below`
  -- once the missing owner `.olean` is available in the Lake state.
  let _ := hK
  let _ := hboundedBelow
  let _ := hrank
  sorry

/-- Helper for Lemma 15.78.3: maximal-local away-perfect witnesses can be reduced to one finite
principal-open cover whose generators span the unit ideal. -/
lemma exists_finite_unitIdeal_family_of_awayPerfect_of_maximal_witnesses
    {K : DMod}
    (hmax :
      ∀ 𝔪 : MaximalSpectrum R,
        ∃ f : R, f ∉ 𝔪.asIdeal ∧
          (K ⊗[R]^L[Localization.Away f]).IsPerfect) :
    ∃ n : ℕ, ∃ g : Fin n → R,
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ j, (K ⊗[R]^L[Localization.Away (g j)]).IsPerfect := by
  classical
  let S : Set R := {f : R | (K ⊗[R]^L[Localization.Away f]).IsPerfect}
  have hspan : Ideal.span S = ⊤ := by
    -- Proof comment: if the span were proper, a maximal ideal containing it would also contain
    -- every chosen maximal-local witness, contradicting the defining `f ∉ 𝔪`.
    by_contra hspan'
    obtain ⟨mIdeal, hmmax, hSm⟩ := Ideal.exists_le_maximal (Ideal.span S) hspan'
    let 𝔪 : MaximalSpectrum R := ⟨mIdeal, hmmax⟩
    rcases hmax 𝔪 with ⟨f, hfm, hfperfect⟩
    have hfmem : f ∈ Ideal.span S := Ideal.subset_span hfperfect
    exact hfm (hSm hfmem)
  obtain ⟨s, hsS, hsTop⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
  let t : Finset R := s
  let g : Fin t.card → R := fun i ↦ (t.equivFin.symm i : R)
  have hg_range : Set.range g = (↑t : Set R) := by
    -- Proof comment: reindex the finite chosen subset by a finite type suitable for
    -- `isPerfect_of_localizationAway_unitIdeal`.
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (t.equivFin.symm i).2
    · intro hx
      exact ⟨t.equivFin ⟨x, hx⟩, by simp [g]⟩
  refine ⟨t.card, g, ?_, ?_⟩
  · simpa [hg_range] using hsTop
  · intro i
    exact (hsS (t.equivFin.symm i).2 : (K ⊗[R]^L[Localization.Away (g i)]).IsPerfect)

/-- Helper for Lemma 15.78.3: sufficiently negative vanishing of the maximal residue-field fiber
forces perfectness after localizing at that maximal ideal. -/
lemma isPerfect_localizationAtMaximal_of_eventually_zero_primeResidueFieldDerivedHomology
    {K : DMod} (hK : K.IsPseudoCoherent) (𝔪 : MaximalSpectrum R)
    (hzero :
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)) :
    (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect := by
  -- Route correction: this is the source-faithful local-ring step using Lemma `15.77.4`,
  -- pseudo-coherence of the lower truncation, finiteness of its top cohomology, and Nakayama.
  -- TODO: formalize that local argument and expose it here as the exact `(4) → (2)` bridge.
  let _ := hK
  let _ := hzero
  sorry

/-- Helper for Lemma 15.78.3: perfectness descends from a finite family of away-local perfect
witnesses whose generators span the unit ideal. -/
lemma isPerfect_of_localizationAway_unitIdeal_family
    {K : DMod} {n : ℕ} (g : Fin n → R)
    (hspan : Ideal.span (Set.range g) = ⊤)
    (hgperfect : ∀ j, (K ⊗[R]^L[Localization.Away (g j)]).IsPerfect) :
    K.IsPerfect := by
  -- Route correction: this wrapper should collapse immediately to the owner theorem from
  -- Lemma `15.75.12`.
  -- TODO: apply `isPerfect_of_localizationAway_unitIdeal (ι := Fin n)` once the missing owner
  -- `.olean` is available in the Lake state.
  let _ := hspan
  let _ := hgperfect
  sorry

-- Proof sketch: specialize derived base change of perfect complexes to the algebra maps
-- `R → R_𝔭` for prime localizations.
/-- A perfect derived `R`-complex remains perfect after localization at any prime ideal. -/
theorem isPerfect_localizationAtPrime_of_isPerfect
    {K : DMod} (hK : K.IsPerfect) (𝔭 : PrimeSpectrum R) :
    (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect := by
  have hloc : (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect :=
    derivedTensorWithAlgebra_isPerfect K hK
  exact hloc

/-- Helper for Lemma 15.78.3: over a field, a perfect complex is bounded below, so all
sufficiently negative homology groups vanish. -/
lemma eventually_isZero_homology_of_isPerfect_over_field
    {k : Type u} [Field k]
    (L : DerivedCategory (ModuleCat k)) (hL : L.IsPerfect) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) i).obj L) := by
  -- Proof comment: unfold perfectness to a bounded finite-projective representative and read off
  -- the lower `t`-structure bound from that representative.
  rcases hL with ⟨P, e, hP⟩
  rcases hP.bounded with ⟨a, _b, hPge, _hPle⟩
  have hQge : (DerivedCategory.Q.obj P).IsGE a := by
    let _ : P.IsStrictlyGE a := hPge
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  let _ : (DerivedCategory.Q.obj P).IsGE a := hQge
  have hLge : L.IsGE a := t.isGE_of_iso e.symm a
  refine ⟨a, ?_⟩
  intro i hi
  let _ : L.IsGE a := hLge
  exact DerivedCategory.isZero_of_isGE L a i hi

/-- Helper for Lemma 15.78.3: perfectness at a maximal localization descends further to any
smaller prime localization. -/
lemma isPerfect_localizationAtPrime_of_isPerfect_localizationAtMaximal
    {K : DMod} (𝔭 : PrimeSpectrum R) (𝔪 : MaximalSpectrum R)
    (hpm : 𝔭.asIdeal ≤ 𝔪.asIdeal)
    (hK𝔪 : (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect) :
    (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect := by
  -- Route correction: the intended source route is still "choose a prime over `𝔭` in `Spec R_𝔪`,
  -- localize the perfect `R_𝔪`-complex there, then identify that localization with `R_𝔭`".
  -- TODO: use the localization-over-specialization API from Lemma `15.50.7` to build the
  -- comparison `R_𝔪 → R_𝔭` without the failing ad hoc algebra-instance transport.
  let _ := hpm
  let _ := hK𝔪
  sorry

/-- Helper for Lemma 15.78.3: if the localization of `K` at `𝔭` is perfect, then the derived
fiber over `𝔭` has vanishing homology in all sufficiently negative degrees. -/
lemma eventually_isZero_primeResidueFieldDerivedHomology_of_isPerfect_localizationAtPrime
    {K : DMod} (𝔭 : PrimeSpectrum R)
    (hK𝔭 : (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero (primeResidueFieldDerivedHomology 𝔭 K i) := by
  -- Route correction: the proof should again be pure base change: extend the perfect
  -- localization from `R_𝔭` to its residue field, compare the iterated tensor with the direct
  -- derived fiber, and then apply the field case.
  -- TODO: follow the stable comparison pattern from Lemma `15.76.7`, using a named residue-field
  -- comparison object to avoid the current universe/elaboration mismatch at
  -- `derivedTensorWithAlgebraCompIso`.
  let _ := hK𝔭
  sorry

-- Proof sketch: `(2) ⇒ (3)` is immediate. For `(3) ⇒ (2)`, localize further from a maximal ideal
-- containing the given prime. The implications `(2) ⇒ (4)` and `(3) ⇒ (5)` come from base change
-- to residue fields. For `(4) ⇒ (2)` and `(5) ⇒ (3)`, reduce to the local case and use the gap
-- splitting statement of Lemma `15.77.4` together with Nakayama to force the lower truncation to
-- vanish.
/-- For a pseudo-coherent object of `D(R)`, perfectness after localization at primes, perfectness
after localization at maximal ideals, and vanishing of sufficiently negative residue-field
homology at primes or maximal ideals are equivalent conditions. -/
theorem prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h𝔭 𝔪
      -- Proof comment: maximal-local perfectness is the prime-local condition applied to the
      -- corresponding prime `𝔪.toPrimeSpectrum`.
      exact h𝔭 𝔪.toPrimeSpectrum
    · intro h𝔪 𝔭
      -- Proof comment: choose a maximal ideal containing `𝔭`, then localize the perfect
      -- `R_𝔪`-complex once more to recover the `R_𝔭`-localization.
      obtain ⟨mIdeal, hmmax, hpm⟩ := 𝔭.asIdeal.exists_le_maximal 𝔭.2.1
      let 𝔪 : MaximalSpectrum R := ⟨mIdeal, hmmax⟩
      exact
        isPerfect_localizationAtPrime_of_isPerfect_localizationAtMaximal
          (K := K) 𝔭 𝔪 hpm (h𝔪 𝔪)
  tfae_have 1 → 3 := by
    intro h𝔭 𝔭
    -- Proof comment: a perfect localization stays perfect after passing to `κ(𝔭)`, and over a
    -- field that forces sufficiently negative homology to vanish.
    exact
      eventually_isZero_primeResidueFieldDerivedHomology_of_isPerfect_localizationAtPrime
        (K := K) 𝔭 (h𝔭 𝔭)
  tfae_have 3 → 4 := by
    intro h𝔭 𝔪
    -- Proof comment: a maximal ideal is in particular a prime ideal, so the prime-fiber
    -- vanishing witness specializes directly.
    simpa using h𝔭 𝔪.toPrimeSpectrum
  tfae_have 4 → 2 := by
    intro h𝔪 𝔪
    -- Route correction: the remaining source-faithful step is the local criterion over
    -- `R_𝔪`. One must combine Lemma `15.77.4` with pseudo-coherence and Nakayama to show that
    -- sufficiently negative vanishing of the `κ(𝔪)`-fiber forces `K ⊗_R^L R_𝔪` to be perfect.
    exact
      isPerfect_localizationAtMaximal_of_eventually_zero_primeResidueFieldDerivedHomology
        (K := K) hK 𝔪 (h𝔪 𝔪)
  tfae_finish

-- Proof sketch: perfection implies perfectness after prime localization by the first theorem.
-- The bounded-below hypothesis and Lemma `15.78.1` upgrade the residue-field vanishing conditions
-- to local perfectness near each maximal ideal, and the previous TFAE then yields equivalence of
-- all five conditions.
/-- Lemma 15.78.3: for a pseudo-coherent bounded-below object `K` of `D(R)`, the following are
equivalent: `K` is perfect, all prime localizations `K \otimes_R^{\mathbf L} R_\mathfrak p` are
perfect, all maximal localizations `K \otimes_R^{\mathbf L} R_\mathfrak m` are perfect, and the
derived fibers over primes or maximal ideals have vanishing homology in all sufficiently negative
degrees. -/
@[stacks 068W]
theorem perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE
    (K : DMod) (hK : K.IsPseudoCoherent) (hboundedBelow : ∃ n : ℤ, K.IsGE n) :
    List.TFAE
      [ K.IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
      , ∀ 𝔪 : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
      , ∀ 𝔭 : PrimeSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
      , ∀ 𝔪 : MaximalSpectrum R,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
      ] := by
  have hLocal :
      List.TFAE
        [ ∀ 𝔭 : PrimeSpectrum R,
            (K ⊗[R]^L[Localization.AtPrime 𝔭.asIdeal]).IsPerfect
        , ∀ 𝔪 : MaximalSpectrum R,
            (K ⊗[R]^L[Localization.AtPrime 𝔪.asIdeal]).IsPerfect
        , ∀ 𝔭 : PrimeSpectrum R,
            ∃ a : ℤ, ∀ i : ℤ, i < a →
              IsZero (primeResidueFieldDerivedHomology 𝔭 K i)
        , ∀ 𝔪 : MaximalSpectrum R,
            ∃ a : ℤ, ∀ i : ℤ, i < a →
              IsZero (primeResidueFieldDerivedHomology 𝔪.toPrimeSpectrum K i)
        ] :=
    prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent K hK
  tfae_have 1 → 2 := by
    intro hKperfect 𝔭
    -- Proof comment: perfect complexes remain perfect after localization at every prime.
    exact isPerfect_localizationAtPrime_of_isPerfect (K := K) hKperfect 𝔭
  tfae_have 2 ↔ 3 := by
    -- Proof comment: the four-way local TFAE already identifies prime-local and maximal-local
    -- perfectness.
    exact hLocal.out 0 1
  tfae_have 3 ↔ 4 := by
    -- Proof comment: reuse the same local TFAE to move from maximal-local perfectness to the
    -- prime-fiber vanishing condition.
    exact hLocal.out 1 2
  tfae_have 4 ↔ 5 := by
    -- Proof comment: the final leg of the local TFAE compares prime and maximal residue-field
    -- vanishing directly.
    exact hLocal.out 2 3
  tfae_have 5 → 1 := by
    intro h𝔪
    have hmax :
        ∀ 𝔪 : MaximalSpectrum R,
          ∃ f : R, f ∉ 𝔪.asIdeal ∧
            (K ⊗[R]^L[Localization.Away f]).IsPerfect := by
      intro 𝔪
      -- Proof comment: apply the bounded-below primewise theorem of Lemma `15.78.1` to the
      -- maximal prime `𝔪.toPrimeSpectrum`.
      exact
        exists_away_isPerfect_of_eventually_zero_primeResidueFieldDerivedHomology
          (K := K) 𝔪.toPrimeSpectrum hK hboundedBelow (h𝔪 𝔪)
    rcases
        exists_finite_unitIdeal_family_of_awayPerfect_of_maximal_witnesses
          (K := K) hmax with
      ⟨n, g, hspan, hgperfect⟩
    -- Proof comment: once a finite principal-open cover with perfect localizations is available,
    -- the local-global perfection theorem closes the proof.
    exact isPerfect_of_localizationAway_unitIdeal_family (K := K) g hspan hgperfect
  tfae_finish

end

end CategoryTheory
