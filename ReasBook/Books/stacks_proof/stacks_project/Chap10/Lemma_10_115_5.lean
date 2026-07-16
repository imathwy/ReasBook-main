import Mathlib
import stacks_proof.stacks_project.Chap05.Definition_5_10_1
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap10.Lemma_10_115_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace Topology

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Source/core/bridge triage:
* primary domain: Noether normalization for finite-type algebras over a field, localized on a
  basic open neighborhood of a point of `Spec(S)`;
* sampled owner API:
  `topologicalKrullDimAt` and
  `exists_openNhdsOf_topologicalKrullDimAt_eq` from `Definition 5.10.1`,
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
  Lemma `10.115.4`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField` from
  Lemma `10.116.3`;
* source-facing: the existence of a basic open neighborhood of `x` whose coordinate ring realizes
  the local dimension at `x` and admits Noether normalization;
* core/canonical: finite injective polynomial-algebra maps and the local-dimension owner formula;
* bridge/view: this lemma specializes those owners to a localization away from one element
  `g ∉ x.asIdeal`.

Primitive data are the basic-open witness `g` and the finite injective algebra map into
`Localization.Away g`. The polynomial source still needs a literal `ℕ` index, so the statement
keeps the minimal witness `d : ℕ` only to record that the canonical owners
`ringKrullDim (Localization.Away g)` and `topologicalKrullDimAt x` are realized by a finite
number of variables.
-/

/-- A witness that `Localization.Away g` realizes the local dimension at `x` and admits a finite
injective Noether normalization by a polynomial ring in `d` variables. -/
structure IsNoetherNormalizationLocalizationAwayAtPoint
    (x : PrimeSpectrum S) (g : S) (d : ℕ)
    (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g) : Prop where
  not_mem_asIdeal : g ∉ x.asIdeal
  ringKrullDim_eq : ringKrullDim (Localization.Away g) = d
  topologicalKrullDimAt_eq : topologicalKrullDimAt x = d
  injective : Function.Injective f
  finite : AlgHom.Finite f

-- Proof sketch: choose a basic open `D(g)` with `g ∉ x.asIdeal` whose dimension equals the local
-- dimension at `x`. Apply Lemma `10.115.4` to a polynomial presentation of `Localization.Away g`.
-- The number of variables is then the canonical owner `ringKrullDim (Localization.Away g)`, and
-- the local-dimension equality identifies this with `topologicalKrullDimAt x`.
/-- Lemma 10.115.5: for a point `x` of `X = Spec(S)`, where `S` is a finite type `k`-algebra,
there exists `g ∉ x.asIdeal` such that the localization `S_g`, formalized as
`Localization.Away g`, has Krull dimension equal to the local dimension at `x`; writing this
common finite value as `d`, there is a finite injective `k`-algebra map from
`MvPolynomial (Fin d) k` to `Localization.Away g`. -/
@[stacks 00OZ]
lemma exists_noether_normalization_localizationAway_at_point (x : PrimeSpectrum S) :
    ∃ (g : S) (d : ℕ) (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      IsNoetherNormalizationLocalizationAwayAtPoint x g d f := by
  -- First realize the local dimension on an actual open neighborhood of `x`.
  obtain ⟨U, hU⟩ := exists_openNhdsOf_topologicalKrullDimAt_eq x
  have hxU : x ∈ (U : Set (PrimeSpectrum S)) := U.2
  -- Then refine that neighborhood to a basic open through `x`.
  obtain ⟨V, ⟨g, rfl⟩, hxV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.2 x hxU
  have hg_not_mem : g ∉ x.asIdeal := by
    simpa using hxV
  have hbasic_le :
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ (U : Set (PrimeSpectrum S)) := hVU
  have hbasic_dim_le :
      topologicalKrullDim (PrimeSpectrum.basicOpen g) ≤ topologicalKrullDim U := by
    -- Compare `D(g)` with its image as a subspace of the minimizing neighborhood `U`.
    let e₁ :
        PrimeSpectrum.basicOpen g ≃ₜ
          (((U : Set (PrimeSpectrum S)) ∩
              (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) :=
      Homeomorph.setCongr <| by
        ext y
        constructor
        · intro hy
          exact ⟨hbasic_le hy, hy⟩
        · intro hy
          exact hy.2
    let e₂ :
        { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } ≃ₜ
          (((U : Set (PrimeSpectrum S)) ∩
              (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) :=
      (Homeomorph.setCongr <| by
          ext y
          constructor
          · intro hy
            exact ⟨y.2, hy⟩
          · intro hy
            exact hy.2).trans
        (IsEmbedding.subtypeVal.homeomorphOfSubsetRange fun y hy ↦
          ⟨⟨y, hy.1⟩, rfl⟩)
    have hsubspace :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } ≤
          topologicalKrullDim U :=
      topologicalKrullDim_subspace_le U
        { y : U | y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) }
    have heq₁ :
        topologicalKrullDim (PrimeSpectrum.basicOpen g) =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum S)) ∩
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) := by
      simpa [e₁] using
        IsHomeomorph.topologicalKrullDim_eq e₁ e₁.isHomeomorph
    have heq₂ :
        topologicalKrullDim
            { y : U // y.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) } =
          topologicalKrullDim
            (((U : Set (PrimeSpectrum S)) ∩
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) : Set (PrimeSpectrum S)) := by
      simpa [e₂] using
        IsHomeomorph.topologicalKrullDim_eq e₂ e₂.isHomeomorph
    rw [heq₁, ← heq₂]
    exact hsubspace
  have hdim_basic :
      topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum.basicOpen g) := by
    refine le_antisymm ?_ ?_
    · -- Any neighborhood bounds the local dimension from above.
      exact topologicalKrullDimAt_le x ⟨PrimeSpectrum.basicOpen g, hxV⟩
    · -- The chosen neighborhood `U` already realizes the minimum, so the smaller basic open has
      -- the same dimension.
      rw [hU]
      exact hbasic_dim_le
  have hdim_localization :
      topologicalKrullDimAt x = ringKrullDim (Localization.Away g) := by
    -- Identify `D(g)` with `Spec(S_g)` and transport topological Krull dimension across that
    -- homeomorphism.
    have hhomeo :
        topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
          topologicalKrullDim (PrimeSpectrum.basicOpen g) := by
      simpa using
        IsHomeomorph.topologicalKrullDim_eq
          (primeSpectrum_localizationAway_homeomorph_D g)
          (primeSpectrum_localizationAway_homeomorph_D g).isHomeomorph
    calc
      topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum.basicOpen g) := hdim_basic
      _ = topologicalKrullDim (PrimeSpectrum (Localization.Away g)) := hhomeo.symm
      _ = ringKrullDim (Localization.Away g) := by
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  -- Finally apply Noether normalization to the finite type `k`-algebra `Localization.Away g`.
  let xg : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨x, hxV⟩
  let _ : Nontrivial (Localization.Away g) := PrimeSpectrum.nontrivial xg
  have hfiniteTypeLoc : Algebra.FiniteType k (Localization.Away g) := inferInstance
  obtain ⟨d, f, hf_injective, hf_finite⟩ :=
    exists_finite_inj_algHom_of_fg k (Localization.Away g)
  have hring :
      ringKrullDim (Localization.Away g) = d := by
    let _ : Algebra (MvPolynomial (Fin d) k) (Localization.Away g) := f.toAlgebra
    -- A finite algebra map is integral, hence preserves Krull dimension under injectivity.
    have hf_integral :
        (algebraMap (MvPolynomial (Fin d) k) (Localization.Away g)).IsIntegral := by
      simpa [RingHom.algebraMap_toAlgebra] using hf_finite.to_isIntegral
    let _ : Algebra.IsIntegral (MvPolynomial (Fin d) k) (Localization.Away g) :=
      algebraMap_isIntegral_iff.mp hf_integral
    have hdim :
        ringKrullDim (MvPolynomial (Fin d) k) =
          ringKrullDim (Localization.Away g) :=
      ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
        (by simpa [RingHom.algebraMap_toAlgebra] using hf_injective)
    have hpoly : ringKrullDim (MvPolynomial (Fin d) k) = d := by
      -- Polynomial rings over a field have Krull dimension equal to the number of variables.
      simp
    exact hdim.symm.trans hpoly
  have htop : topologicalKrullDimAt x = d := by
    rw [hdim_localization, hring]
  refine ⟨g, d, f, ?_⟩
  exact
    { not_mem_asIdeal := hg_not_mem
      ringKrullDim_eq := hring
      topologicalKrullDimAt_eq := htop
      injective := hf_injective
      finite := hf_finite }

end
