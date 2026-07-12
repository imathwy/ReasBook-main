import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1

noncomputable section

open CategoryTheory
open Module
open scoped MonoidAlgebra Representation

universe u

namespace Representation

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

/-- Helper for Corollary 16-16.1-6: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_basis_support :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Corollary 16-16.1-6: the quotient factor attached to one step of a composition
series. -/
private abbrev compositionSeriesFactor_basis_support
    {M : Type*} [AddCommGroup M] [Module k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :=
  (s (Fin.succ i)) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype

/-- Helper for Corollary 16-16.1-6: quotienting inside the top submodule is the same as
quotienting the ambient module. -/
private noncomputable def topSubmoduleQuotientEquiv_basis_support
    {M : Type*} [AddCommGroup M] [Module k[G] M] (N : Submodule k[G] M) :
    ((⊤ : Submodule k[G] M) ⧸ N.comap (⊤ : Submodule k[G] M).subtype) ≃ₗ[k[G]] M ⧸ N :=
  Submodule.Quotient.equiv
    (N.comap (⊤ : Submodule k[G] M).subtype) N Submodule.topEquiv
    (by
      -- The top-submodule equivalence sends the restricted submodule exactly onto `N`.
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by simp⟩, hx, rfl⟩)

/-- Helper for Corollary 16-16.1-6: a `k[G]`-linear equivalence between owner modules upgrades
to an isomorphism of finite-dimensional representations. -/
private theorem fdRep_nonempty_iso_of_asModuleLinearEquiv_basis_support
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the module equivalence as a `Rep` isomorphism and use faithfulness of `FDRep → Rep`.
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Corollary 16-16.1-6: a simple finite-dimensional representation is a quotient of
the regular module by a maximal submodule. -/
private theorem exists_maximal_regular_quotient_equiv_simple_basis_support
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ K : Submodule k[G] k[G],
      K ⋖ (⊤ : Submodule k[G] k[G]) ∧ Nonempty ((k[G] ⧸ K) ≃ₗ[k[G]] asModule τ.ρ) := by
  classical
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial τ :=
    IsSimpleModule.nontrivial (R := k[G]) (M := τ)
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  let φ : k[G] →ₗ[k[G]] τ :=
    LinearMap.toSpanSingleton k[G] τ v
  have hφ_surj : Function.Surjective φ := by
    exact IsSimpleModule.toSpanSingleton_surjective k[G] hv
  let K : Submodule k[G] k[G] := LinearMap.ker φ
  refine ⟨K, ?_, ?_⟩
  · have hquot_simple : IsSimpleModule k[G] (k[G] ⧸ K) := by
      exact (LinearMap.quotKerEquivOfSurjective φ hφ_surj).isSimpleModule_iff.mpr inferInstance
    -- The quotient by the cyclic map's kernel is simple, so the kernel is maximal under `⊤`.
    rw [covBy_iff_quot_is_simple le_top]
    exact (topSubmoduleQuotientEquiv_basis_support (k := k) (G := G) K).isSimpleModule_iff.mpr
      hquot_simple
  · -- The quotient by the kernel is linearly equivalent to the original simple module.
    let eQuot : (k[G] ⧸ K) ≃ₗ[k[G]] τ :=
      LinearMap.quotKerEquivOfSurjective φ hφ_surj
    let eAsModule : τ ≃ₗ[k[G]] asModule τ.ρ := LinearEquiv.refl k[G] τ
    exact ⟨eQuot.trans eAsModule⟩

/-- Helper for Corollary 16-16.1-6: a fixed regular composition series contains the factor
corresponding to any maximal quotient of the regular module. -/
private theorem regular_compositionSeries_factor_equiv_top_quotient_basis_support
    (s : CompositionSeries (Submodule k[G] k[G])) (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (K : Submodule k[G] k[G]) (hKmax : K ⋖ (⊤ : Submodule k[G] k[G])) :
    ∃ i : Fin s.length,
      Nonempty
        (compositionSeriesFactor_basis_support (k := k) (G := G) s i ≃ₗ[k[G]]
          ((⊤ : Submodule k[G] k[G]) ⧸
            K.comap (⊤ : Submodule k[G] k[G]).subtype)) := by
  have hKmaxLast : K ⋖ s.last := by
    simpa [hs_last] using hKmax
  have hhead_le : s.head ≤ K := by
    simpa [hs_head] using (bot_le : (⊥ : Submodule k[G] k[G]) ≤ K)
  obtain ⟨t, _ht_head, _ht_len, hKlast, hequiv⟩ :=
    CompositionSeries.exists_last_eq_snoc_equivalent s K hKmaxLast hhead_le
  let u : CompositionSeries (Submodule k[G] k[G]) :=
    t.snoc s.last (show t.last ⋖ s.last from hKlast.symm ▸ hKmaxLast)
  let j : Fin u.length := Fin.last t.length
  let i : Fin s.length := hequiv.choose.symm j
  have hji : hequiv.choose i = j := by
    exact hequiv.choose.apply_symm_apply j
  have hIso := hequiv.choose_spec i
  rw [hji] at hIso
  rcases hIso with ⟨eFactor⟩
  have eFactor' :
      compositionSeriesFactor_basis_support (k := k) (G := G) s i ≃ₗ[k[G]]
        compositionSeriesFactor_basis_support (k := k) (G := G) u j := by
    -- The Jordan-Hölder equivalence identifies the chosen factor of `s` with the final factor.
    simpa [compositionSeriesFactor_basis_support, u, hji] using eFactor
  have eLast :
      compositionSeriesFactor_basis_support (k := k) (G := G) u j ≃ₗ[k[G]]
        ((⊤ : Submodule k[G] k[G]) ⧸
          K.comap (⊤ : Submodule k[G] k[G]).subtype) := by
    let A : Submodule k[G] k[G] := u j.succ
    let B : Submodule k[G] k[G] := u (Fin.castSucc j)
    have hA : A = (⊤ : Submodule k[G] k[G]) := by
      simp [A, u, j, hs_last]
    have hB : B = K := by
      simpa [B, u, j, RelSeries.last] using hKlast
    let eA : A ≃ₗ[k[G]] (⊤ : Submodule k[G] k[G]) := LinearEquiv.ofEq _ _ hA
    have hmap : Submodule.map (eA : A →ₗ[k[G]] (⊤ : Submodule k[G] k[G]))
        (B.comap A.subtype) = K.comap (⊤ : Submodule k[G] k[G]).subtype := by
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
    -- Transport the final quotient of the snoc series along the equality with `⊤ / K`.
    exact Submodule.Quotient.equiv (B.comap A.subtype)
      (K.comap (⊤ : Submodule k[G] k[G]).subtype) eA hmap
  refine ⟨i, ?_⟩
  exact ⟨eFactor'.trans eLast⟩

/-- Helper for Corollary 16-16.1-6: every simple finite-dimensional representation occurs as a
composition factor of the regular `k[G]`-module. -/
private theorem simple_asModule_occurs_as_regular_factor_basis_support
    (s : CompositionSeries (Submodule k[G] k[G])) (hs_head : s.head = ⊥) (hs_last : s.last = ⊤)
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ i : Fin s.length,
      Nonempty (compositionSeriesFactor_basis_support (k := k) (G := G) s i ≃ₗ[k[G]] asModule τ.ρ) := by
  classical
  obtain ⟨K, hKmax, ⟨eKτ⟩⟩ :=
    exists_maximal_regular_quotient_equiv_simple_basis_support (k := k) (G := G) τ
  obtain ⟨i, ⟨eFactorTop⟩⟩ :=
    regular_compositionSeries_factor_equiv_top_quotient_basis_support
      (k := k) (G := G) s hs_head hs_last K hKmax
  let eTop :
      ((⊤ : Submodule k[G] k[G]) ⧸
        K.comap (⊤ : Submodule k[G] k[G]).subtype) ≃ₗ[k[G]] k[G] ⧸ K :=
    topSubmoduleQuotientEquiv_basis_support (k := k) (G := G) K
  -- Compose the factor equivalence with the ambient top-quotient and the simple quotient model.
  exact ⟨i, ⟨eFactorTop.trans (eTop.trans eKτ)⟩⟩

/-- Helper for Corollary 16-16.1-6: any complete pairwise nonisomorphic simple family is finite,
because its members inject into the finite set of composition factors of the regular module. -/
private theorem finite_index_of_complete_pairwise_nonisomorphic_simple_family_basis_support
    {ι : Type (u + 1)} (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  classical
  letI : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  have hfl : IsFiniteLength k[G] k[G] := by
    -- The regular module is finite-dimensional over `k`, hence finite length over `k[G]`.
    exact (isFiniteLength_iff_isNoetherian_isArtinian).2
      ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  obtain ⟨s, hs_head, hs_last⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfl
  have hocc :
      ∀ i : ι, ∃ j : Fin s.length,
        Nonempty
          (compositionSeriesFactor_basis_support (k := k) (G := G) s j ≃ₗ[k[G]]
            asModule (π i).ρ) := by
    intro i
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    exact simple_asModule_occurs_as_regular_factor_basis_support (k := k) (G := G)
      s hs_head hs_last (π i)
  let factorIndex : ι → Fin s.length := fun i ↦ Classical.choose (hocc i)
  have hfactorIndex_injective : Function.Injective factorIndex := by
    intro i j hij
    rcases Classical.choose_spec (hocc i) with ⟨ei⟩
    rcases Classical.choose_spec (hocc j) with ⟨ej⟩
    have ej' :
        compositionSeriesFactor_basis_support (k := k) (G := G) s (factorIndex i) ≃ₗ[k[G]]
          asModule (π j).ρ := by
      have hij_choose : Classical.choose (hocc i) = Classical.choose (hocc j) := by
        simpa [factorIndex] using hij
      change
        compositionSeriesFactor_basis_support (k := k) (G := G) s
            (Classical.choose (hocc i)) ≃ₗ[k[G]] asModule (π j).ρ
      rw [hij_choose]
      exact ej
    have hij_iso : Nonempty (π i ≅ π j) := by
      exact fdRep_nonempty_iso_of_asModuleLinearEquiv_basis_support (k := k) (G := G)
        ⟨ei.symm.trans ej'⟩
    by_contra hne
    exact hπ_pairwise hne hij_iso
  -- The complete pairwise family injects into the finite set of regular composition factors.
  exact Finite.of_injective factorIndex hfactorIndex_injective

/-- Helper for Corollary 16-16.1-6: the source of a projective envelope of a simple module is
cyclic, hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_basis_support
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using this
  have hmap_top : N.map f = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Corollary 16-16.1-6: every simple finite-dimensional representation admits a finite
projective envelope in the category of `k[G]`-modules. -/
private theorem exists_finite_projectiveEnvelope_of_simple_basis_support
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Translate simplicity of the representation owner to simplicity of the underlying module.
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_basis_support
      (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  simpa [P, ρ] using hf'

/-- Helper for Corollary 16-16.1-6: `R₀[k](G)` has a finite `ℤ`-basis coming from a complete
simple family. -/
theorem finiteRepGrothendieck_basis_support :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι),
      Nonempty (Module.Basis ι ℤ (R₀[k](G))) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  letI : Finite ι :=
    finite_index_of_complete_pairwise_nonisomorphic_simple_family_basis_support
      (k := k) (G := G) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  exact ⟨ι, inferInstance, ⟨b⟩⟩

/-- Helper for Corollary 16-16.1-6: both Cartan source and target admit `ℤ`-bases indexed by the
same complete simple family. -/
theorem cartan_source_target_bases_support :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι),
      Nonempty (Module.Basis ι ℤ (P₀[k](G))) ∧
        Nonempty (Module.Basis ι ℤ (R₀[k](G))) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  letI : Finite ι :=
    finite_index_of_complete_pairwise_nonisomorphic_simple_family_basis_support
      (k := k) (G := G) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  have hP_exists :
      ∀ i, ∃ P : FiniteProjectiveGroupAlgebraModule k G,
        ∃ f : P.V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope := by
    intro i
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    exact exists_finite_projectiveEnvelope_of_simple_basis_support (k := k) (G := G) (τ := π i)
  choose P hP using hP_exists
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP
  let bR : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  exact ⟨ι, inferInstance, ⟨bP⟩, ⟨bR⟩⟩

/-- Helper for Corollary 16-16.1-6: the canonical Cartan source and target owners are free finite
`ℤ`-modules once the common-index basis package has been chosen. -/
theorem cartan_source_target_free_and_finite_support :
    Module.Free ℤ (P₀[k](G)) ∧ Module.Finite ℤ (P₀[k](G)) ∧
      Module.Free ℤ (R₀[k](G)) ∧ Module.Finite ℤ (R₀[k](G)) := by
  classical
  obtain ⟨ι, _, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases_support (k := k) (G := G)
  -- Reuse the common-index basis pair directly on the canonical owners.
  exact ⟨Module.Free.of_basis bP, Module.Finite.of_basis bP,
    Module.Free.of_basis bR, Module.Finite.of_basis bR⟩

/-- Helper for Corollary 16-16.1-6: the canonical Cartan source and target have the same
`ℤ`-rank because the support file produces bases indexed by the same finite type. -/
theorem cartan_source_target_finrank_eq_support :
    Module.finrank ℤ (P₀[k](G)) = Module.finrank ℤ (R₀[k](G)) := by
  classical
  obtain ⟨ι, hι, ⟨bP⟩, ⟨bR⟩⟩ := cartan_source_target_bases_support (k := k) (G := G)
  letI : Fintype ι := hι
  -- Serre's rank count is exactly the common cardinal of the simple-family index type.
  rw [Module.finrank_eq_card_basis bP, Module.finrank_eq_card_basis bR]

end

end Representation
