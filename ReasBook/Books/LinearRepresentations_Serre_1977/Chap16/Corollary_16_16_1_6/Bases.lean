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
  letI : NeZero (Nat.card G : k) := by sorry
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
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
  letI : NeZero (Nat.card G : k) := by sorry
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
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
  -- LinearRepresentations_Serre_1977's rank count is exactly the common cardinal of the simple-family index type.
  rw [Module.finrank_eq_card_basis bP, Module.finrank_eq_card_basis bR]

end

end Representation
