import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_3_1

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u v

namespace Representation

section

variable {F : Type u} [Field F]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 16-16.1-2: the quotient factor attached to one step of a composition
series of the regular `F[G]`-module. -/
private abbrev regularCompositionSeriesFactor
    (s : CompositionSeries (Submodule F[G] F[G])) (i : Fin s.length) :=
  (s (Fin.succ i)) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype

/-- Helper for Theorem 16-16.1-2: quotienting inside the top submodule is linearly equivalent to
quotienting the ambient regular module. -/
private theorem nonempty_topSubmoduleQuotientLinearEquiv
    (N : Submodule F[G] F[G]) :
    Nonempty
      (((⊤ : Submodule F[G] F[G]) ⧸ N.comap (⊤ : Submodule F[G] F[G]).subtype) ≃ₗ[F[G]]
        F[G] ⧸ N) := by
  -- The top submodule is equivalent to the ambient module, and this equivalence sends the
  -- restricted copy of `N` exactly onto `N`.
  refine ⟨Submodule.Quotient.equiv
    (N.comap (⊤ : Submodule F[G] F[G]).subtype) N Submodule.topEquiv ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, by simp⟩, hx, rfl⟩

/-- Helper for Theorem 16-16.1-2: an equivalence between the underlying `F[G]`-modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep F G`. -/
private theorem fdRep_nonemptyIso_of_asModuleLinearEquiv
    {σ τ : FDRep F G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[F[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the module equivalence as a `Rep` isomorphism, then reflect it through the faithful
  -- forgetful functor from finite-dimensional representations.
  let eRep : ((forget₂ (FDRep F G) (Rep F G)).obj σ) ≅
      ((forget₂ (FDRep F G) (Rep F G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep F G) (Rep F G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep F G) (Rep F G)).obj τ)).symm
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep F G) (Rep F G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep F G) (Rep F G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Theorem 16-16.1-2: a simple finite-dimensional representation is a quotient of the
regular module by a maximal submodule. -/
private theorem exists_maximal_regular_quotient_equiv_simple
    (τ : FDRep F G) [Simple τ] :
    ∃ K : Submodule F[G] F[G],
      K ⋖ (⊤ : Submodule F[G] F[G]) ∧ Nonempty ((F[G] ⧸ K) ≃ₗ[F[G]] asModule τ.ρ) := by
  classical
  let ρ : Representation F G τ := τ.ρ
  letI : Module F[G] τ := by
    simpa using (inferInstance : Module F[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule F[G] τ := by
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial τ :=
    IsSimpleModule.nontrivial (R := F[G]) (M := τ)
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  let φ : F[G] →ₗ[F[G]] τ :=
    LinearMap.toSpanSingleton F[G] τ v
  have hφ_surj : Function.Surjective φ :=
    IsSimpleModule.toSpanSingleton_surjective F[G] hv
  let K : Submodule F[G] F[G] := LinearMap.ker φ
  refine ⟨K, ?_, ?_⟩
  · have hquot_simple : IsSimpleModule F[G] (F[G] ⧸ K) :=
      (LinearMap.quotKerEquivOfSurjective φ hφ_surj).isSimpleModule_iff.mpr inferInstance
    -- A quotient of the regular module is simple exactly when its kernel is maximal below `⊤`.
    rw [covBy_iff_quot_is_simple le_top]
    exact (Classical.choice (nonempty_topSubmoduleQuotientLinearEquiv (F := F) (G := G) K))
      |>.isSimpleModule_iff.mpr hquot_simple
  · let eQuot : (F[G] ⧸ K) ≃ₗ[F[G]] τ :=
      LinearMap.quotKerEquivOfSurjective φ hφ_surj
    let eAsModule : τ ≃ₗ[F[G]] asModule τ.ρ := LinearEquiv.refl F[G] τ
    -- The quotient by the kernel recovers the original simple owner.
    exact ⟨eQuot.trans eAsModule⟩

/-- Helper for Theorem 16-16.1-2: a fixed regular composition series contains the factor
corresponding to any maximal quotient of the regular module. -/
private theorem regularCompositionSeries_factor_equiv_top_quotient
    (s : CompositionSeries (Submodule F[G] F[G])) (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (K : Submodule F[G] F[G]) (hKmax : K ⋖ (⊤ : Submodule F[G] F[G])) :
    ∃ i : Fin s.length,
      Nonempty
        (regularCompositionSeriesFactor (F := F) (G := G) s i ≃ₗ[F[G]]
          ((⊤ : Submodule F[G] F[G]) ⧸
            K.comap (⊤ : Submodule F[G] F[G]).subtype)) := by
  have hKmaxLast : K ⋖ s.last := by
    simpa [hs_last] using hKmax
  have hhead_le : s.head ≤ K := by
    simpa [hs_head] using (bot_le : (⊥ : Submodule F[G] F[G]) ≤ K)
  obtain ⟨t, _ht_head, _ht_len, hKlast, hequiv⟩ :=
    CompositionSeries.exists_last_eq_snoc_equivalent s K hKmaxLast hhead_le
  let u : CompositionSeries (Submodule F[G] F[G]) :=
    t.snoc s.last (show t.last ⋖ s.last from hKlast.symm ▸ hKmaxLast)
  let j : Fin u.length := Fin.last t.length
  let i : Fin s.length := hequiv.choose.symm j
  have hji : hequiv.choose i = j :=
    hequiv.choose.apply_symm_apply j
  have hIso := hequiv.choose_spec i
  rw [hji] at hIso
  rcases hIso with ⟨eFactor⟩
  have eFactor' :
      regularCompositionSeriesFactor (F := F) (G := G) s i ≃ₗ[F[G]]
        regularCompositionSeriesFactor (F := F) (G := G) u j := by
    -- Jordan-Hölder equivalence identifies the selected factor with the final factor of the
    -- modified series ending in `K < ⊤`.
    simpa [regularCompositionSeriesFactor, u, hji] using eFactor
  have eLast :
      regularCompositionSeriesFactor (F := F) (G := G) u j ≃ₗ[F[G]]
        ((⊤ : Submodule F[G] F[G]) ⧸
          K.comap (⊤ : Submodule F[G] F[G]).subtype) := by
    let A : Submodule F[G] F[G] := u j.succ
    let B : Submodule F[G] F[G] := u (Fin.castSucc j)
    have hA : A = (⊤ : Submodule F[G] F[G]) := by
      simp [A, u, j, hs_last]
    have hB : B = K := by
      simpa [B, u, j, RelSeries.last] using hKlast
    let eA : A ≃ₗ[F[G]] (⊤ : Submodule F[G] F[G]) := LinearEquiv.ofEq _ _ hA
    have hmap : Submodule.map (eA : A →ₗ[F[G]] (⊤ : Submodule F[G] F[G]))
        (B.comap A.subtype) = K.comap (⊤ : Submodule F[G] F[G]).subtype := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact by simpa [B, hB, A, hA, eA] using hy
      · intro hx
        refine ⟨⟨x, ?_⟩, ?_, ?_⟩
        · simpa [A, hA] using x.2
        · simpa [B, hB, A, hA] using hx
        · ext
          rfl
    -- Transport the last quotient of the snoc series to the ambient top quotient.
    exact Submodule.Quotient.equiv (B.comap A.subtype)
      (K.comap (⊤ : Submodule F[G] F[G]).subtype) eA hmap
  exact ⟨i, ⟨eFactor'.trans eLast⟩⟩

/-- Helper for Theorem 16-16.1-2: every simple finite-dimensional representation occurs as a
composition factor of the regular `F[G]`-module. -/
private theorem simple_asModule_occurs_as_regular_factor
    (s : CompositionSeries (Submodule F[G] F[G])) (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (τ : FDRep F G) [Simple τ] :
    ∃ i : Fin s.length,
      Nonempty (regularCompositionSeriesFactor (F := F) (G := G) s i ≃ₗ[F[G]] asModule τ.ρ) := by
  classical
  obtain ⟨K, hKmax, ⟨eKτ⟩⟩ :=
    exists_maximal_regular_quotient_equiv_simple (F := F) (G := G) τ
  obtain ⟨i, ⟨eFactorTop⟩⟩ :=
    regularCompositionSeries_factor_equiv_top_quotient
      (F := F) (G := G) s hs_head hs_last K hKmax
  let eTop :
      ((⊤ : Submodule F[G] F[G]) ⧸
        K.comap (⊤ : Submodule F[G] F[G]).subtype) ≃ₗ[F[G]] F[G] ⧸ K :=
    Classical.choice (nonempty_topSubmoduleQuotientLinearEquiv (F := F) (G := G) K)
  -- Compose the regular factor equivalence with the ambient quotient and the simple quotient model.
  exact ⟨i, ⟨eFactorTop.trans (eTop.trans eKτ)⟩⟩

/-- Helper for Theorem 16-16.1-2: any complete pairwise nonisomorphic simple family of
finite-dimensional representations of a finite group over a field has a finite index type. -/
theorem finiteOfCompletePairwiseNonisomorphicSimpleFamily
    {ι : Type v} (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  classical
  letI : Module.Finite F F[G] := MonoidAlgebra.moduleFinite
  have hfl : IsFiniteLength F[G] F[G] := by
    -- The regular module is finite-dimensional over `F`, hence noetherian and artinian as an
    -- `F[G]`-module.
    exact (isFiniteLength_iff_isNoetherian_isArtinian).2
      ⟨isNoetherian_of_tower F inferInstance, isArtinian_of_tower F inferInstance⟩
  obtain ⟨s, hs_head, hs_last⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfl
  have hocc :
      ∀ i : ι, ∃ j : Fin s.length,
        Nonempty
          (regularCompositionSeriesFactor (F := F) (G := G) s j ≃ₗ[F[G]]
            asModule (π i).ρ) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    -- Completeness and simplicity put each family member among the regular module factors.
    exact simple_asModule_occurs_as_regular_factor
      (F := F) (G := G) s hs_head hs_last (π i)
  let factorIndex : ι → Fin s.length := fun i ↦ Classical.choose (hocc i)
  have hfactorIndex_injective : Function.Injective factorIndex := by
    intro i j hij
    rcases Classical.choose_spec (hocc i) with ⟨ei⟩
    rcases Classical.choose_spec (hocc j) with ⟨ej⟩
    have ej' :
        regularCompositionSeriesFactor (F := F) (G := G) s (factorIndex i) ≃ₗ[F[G]]
          asModule (π j).ρ := by
      have hij_choose : Classical.choose (hocc i) = Classical.choose (hocc j) := by
        simpa [factorIndex] using hij
      change
        regularCompositionSeriesFactor (F := F) (G := G) s (Classical.choose (hocc i)) ≃ₗ[F[G]]
          asModule (π j).ρ
      rw [hij_choose]
      exact ej
    have hij_iso : Nonempty (π i ≅ π j) :=
      fdRep_nonemptyIso_of_asModuleLinearEquiv (F := F) (G := G) ⟨ei.symm.trans ej'⟩
    by_contra hne
    exact hπ_pairwise hne hij_iso
  -- The family injects into the finite set of factors of a regular composition series.
  exact Finite.of_injective factorIndex hfactorIndex_injective

end

end Representation
