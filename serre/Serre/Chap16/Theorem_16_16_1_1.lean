import Mathlib
import Serre.Chap02.Theorem_2_2_3_5
import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap14.Proposition_14_14_3_1
import Serre.Chap16.Remark_16_16_3_5
import Serre.Chap15.Theorem_15_15_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped Representation
open scoped MonoidAlgebra
open scoped TensorProduct
open CategoryTheory

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for Theorem 16-16.1-1:
* source-facing layer: Serre's large-field surjectivity statement for the decomposition map.
* core/canonical owner already defined upstream in Chapter 15:
  `decompositionHom A K G : R₀[K](G) →+ R₀[k](G)`.
* same-domain project declarations inspected before refining:
  `stableLatticeReduction_grothendieckClass_eq`,
  `decompositionHom`,
  `decompositionHom_finiteRepClass_eq`,
  `simple_finiteRep_classes_basis_of_complete_family`,
  `isRealizableOver_of_hasEnoughRootsOfUnity`.

Primitive data belongs to the owner `decompositionHom A K G`; this file contributes only the theorem
that the existing owner is surjective under the standard large-field hypothesis. -/

-- Proof sketch: under the standard large-field hypothesis on `K`, every simple
-- `(A / 𝔪_A)[G]`-representation lifts to a `K[G]`-representation. Since the simple classes form a
-- `ℤ`-basis of `R_k(G)`, the image of the decomposition homomorphism contains a basis and is
-- therefore all of `R_k(G)`.
omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Theorem 16-16.1-1: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local [Finite G] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
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
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot admit an isomorphism.
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
      have hq : Nonempty ((Quotient.out q).1 ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 16-16.1-1: the simple classes attached to a complete simple family form the
canonical basis of `R₀[k](G)`. -/
private abbrev simple_class_basis_local {ι : Type*} (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι ℤ (R₀[k](G)) :=
  simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Theorem 16-16.1-1: the basis vector indexed by `i` is the class of `π i`. -/
@[simp] private theorem simple_class_basis_local_apply {ι : Type*} (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    simple_class_basis_local π hπ_pairwise hπ_complete i = [π i]₀ := by
  simp [simple_class_basis_local, simple_finiteRep_classes_basis_of_complete_family_apply]

/-- Helper for Theorem 16-16.1-1: if every simple residue-field class is the reduction of some
characteristic-zero class, then the decomposition map is onto. -/
private theorem decompositionHom_surjective_of_basis_vectors_mem_range
    [Finite G]
    {ι : Type*} (b : Module.Basis ι ℤ (R₀[k](G)))
    (hb : ∀ i, b i ∈ Set.range (decompositionHom A K G)) :
    Function.Surjective (decompositionHom A K G) := by
  classical
  choose x hx using hb
  intro y
  refine ⟨(b.repr y).sum fun i a ↦ a • x i, ?_⟩
  -- Expand `y` in the chosen basis and lift each basis vector separately.
  calc
    decompositionHom A K G ((b.repr y).sum fun i a ↦ a • x i)
        = (b.repr y).sum fun i a ↦ a • decompositionHom A K G (x i) := by
            simp [Finsupp.sum, map_sum, map_zsmul]
    _ = (b.repr y).sum fun i a ↦ a • b i := by
          simp [Finsupp.sum, hx]
    _ = y := by
          simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr y

/-- Helper for Theorem 16-16.1-1: any residue-field class coming from the reduction of a stable
characteristic-zero lattice already lies in the range of `decompositionHom A K G`. -/
private theorem finiteRep_class_mem_range_decompositionHom_of_exists_lift
    [Finite G]
    (S : FDRep k G)
    (hS :
      ∃ X : FDRep K G, ∃ L : StableLattice A X.ρ,
        Nonempty (FDRep.of L.reductionRepresentation ≅ S)) :
    [S]₀ ∈ Set.range (decompositionHom A K G) := by
  rcases hS with ⟨X, L, hReduction⟩
  rcases hReduction with ⟨e⟩
  refine ⟨[X]₀, ?_⟩
  -- Evaluate `decompositionHom` on the chosen characteristic-zero witness and then transport
  -- the reduction class across the supplied isomorphism with `S`.
  calc
    decompositionHom A K G [X]₀ = [FDRep.of L.reductionRepresentation]₀ := by
      simpa using decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L
    _ = [S]₀ := by
      simpa using
        (finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
          (V := FDRep.of L.reductionRepresentation) (W := S) ⟨e⟩)

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Theorem 16-16.1-1: the source of a projective envelope of a simple `k[G]`-module
is finitely generated over the group algebra. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    [Finite G]
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen generator maps to a nonzero vector, so the image cannot be trivial.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    -- Once the cyclic span is all of `P`, the canonical map from `k[G]` onto that span is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Helper for Theorem 16-16.1-1: every simple finite-dimensional `k[G]`-representation admits a
finite projective envelope in the canonical owner category of projective modules. -/
private theorem exists_finite_projective_envelope_of_simple_local
    [Finite G]
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule.{u, u} k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    -- Expose the ambient `k[G]`-module structure carried by the owner `S`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Convert categorical simplicity of `S` into irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    -- The projective-envelope theorem is stated for modules, so move to `k[G]`-modules here.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] S
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (G := G) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    -- Repackage the projective-envelope source as a finitely generated `k[G]`-module.
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    -- Projectivity is already part of the projective-envelope structure.
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule.{u, u} k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Theorem 16-16.1-1: for a finite group `G`, under the standard large-field hypothesis on `K`,
Serre's decomposition homomorphism `d = decompositionHom A K G : R₀[K](G) → R₀[k](G)` is
surjective. -/
theorem decompositionHom_surjective
    [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective (decompositionHom A K G) := by
  classical
  -- Route correction: the dedicated Chapter 16 infra module is unavailable here as a compiled
  -- dependency, so use the already-built `(R')` packaging of the same Serre lifting step.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (A := A) (G := G)
  have hRPrime : SatisfiesConditionRPrime A K G :=
    satisfiesConditionRPrime_of_sufficiently_large (A := A) (K := K) (G := G)
  let b : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_class_basis_local π hπ_pairwise hπ_complete
  -- Serre's basis argument reduces surjectivity to lifting the simple basis vectors.
  have hb : ∀ i, b i ∈ Set.range (decompositionHom A K G) := by
    intro i
    letI : Simple (π i) := hπ_complete.isSimple i
    rcases hRPrime (π i) inferInstance with ⟨X, _hX_simple, L, hReduction⟩
    simpa [b] using
      finiteRep_class_mem_range_decompositionHom_of_exists_lift
        (A := A) (K := K) (G := G) (S := π i) ⟨X, L, hReduction⟩
  -- Once the canonical simple basis lies in the image, surjectivity is purely formal.
  exact
    decompositionHom_surjective_of_basis_vectors_mem_range
      (A := A) (K := K) (G := G) b hb

end

end Representation
