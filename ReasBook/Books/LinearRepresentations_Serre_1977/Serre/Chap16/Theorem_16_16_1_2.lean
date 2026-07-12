import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.MatrixPrimeToP
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Infra_16_1_DecompositionSurjectivity
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.BrauerMultiplicity
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.EntryBridge
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.SimpleFamilyFinite
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.SubgroupInductionLocal
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w z

namespace Representation

open CategoryTheory
open scoped MonoidAlgebra
open scoped Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 16-16.1-2: a fraction-field realization into a field gives the local
coefficient ring the domain structure needed by the DVR-shaped decomposition-map API. -/
private theorem isDomain_of_isFractionRing_field_local
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDomain A := by
  -- The algebra map into the fraction field is injective, and injective maps into fields reflect
  -- the domain structure back to the source ring.
  exact (IsFractionRing.injective A K).isDomain

/-- Helper for Theorem 16-16.1-2: over any field, one can choose a finite complete family of
pairwise nonisomorphic simple finite-dimensional `G`-representations. -/
private theorem existsCompletePairwiseNonisomorphicSimpleFamilyFieldLocal
    {F : Type u} [Field F] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep F G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F G // Simple τ }
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
  let π : ι → FDRep F G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot contain isomorphic representatives.
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

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: once Serre's comparison identifies the image of each chosen
source basis vector with the matching target basis vector, the matrix of the map in those bases is
the identity matrix. -/
private theorem basis_toMatrix_eq_of_basis_images_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (bM : Module.Basis ι ℤ M) (bN : Module.Basis ι ℤ N)
    (f : M →ₗ[ℤ] N)
    (himage : ∀ i, f (bM i) = bN i) :
    LinearMap.toMatrix bM bN f = 1 := by
  ext i j
  -- Evaluate the matrix entry on the source basis and use the assumed basis-image formula.
  rw [LinearMap.toMatrix_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simpa [himage] using bN.repr_self i
  · have hrepr := bN.repr_self j
    simpa [himage, hij] using congrArg (fun c : ι →₀ ℤ ↦ c i) hrepr

/-- Helper for Theorem 16-16.1-2: if each basis vector of the target has a chosen preimage, the
linear map built from those preimages is a right inverse. -/
private theorem basis_constr_rightInverse_of_basis_preimages_local
    {ι : Type*}
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (b : Module.Basis ι ℤ M)
    (d : N →ₗ[ℤ] M)
    (v : ι → N)
    (hv : ∀ i, d (v i) = b i) :
    Function.RightInverse (b.constr ℕ v) d := by
  have hcomp :
      d.comp (b.constr ℕ v) = LinearMap.id := by
    -- It suffices to check the composite on the chosen basis of `R₀[k](G)`.
    apply b.ext
    intro i
    simpa using hv i
  intro x
  -- Evaluate the identity `f ∘ b.constr = id` at the point `x`.
  exact congrArg (fun g : M →ₗ[ℤ] M ↦ g x) hcomp

/-- Helper for Theorem 16-16.1-2: once a complete simple residue family has basiswise preimages
under `decompositionHom`, those chosen lifts assemble into an additive right inverse. -/
private theorem decomposition_rightInverse_of_complete_simple_family_local
    {ι : Type*}
    [IsDomain A] [IsDiscreteValuationRing A]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_range : ∀ i, [π i]₀ ∈ Set.range (decompositionHom A K G)) :
    ∃ r : R₀[k](G) →+ R₀[K](G), Function.RightInverse r (decompositionHom A K G) := by
  classical
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hpreimage :
      ∀ i, ∃ x : R₀[K](G), (decompositionHom A K G).toIntLinearMap x = bk i := by
    intro i
    rcases hπ_range i with ⟨x, hx⟩
    -- Rewrite the chosen range witness as a lift of the corresponding simple-basis vector.
    refine ⟨x, ?_⟩
    simpa [bk, simple_finiteRep_classes_basis_of_complete_family_apply] using hx
  choose x hx using hpreimage
  let rL : R₀[k](G) →ₗ[ℤ] R₀[K](G) := bk.constr ℕ x
  have hrL : Function.RightInverse rL (decompositionHom A K G).toIntLinearMap := by
    -- The basis-built section is a right inverse because every chosen column maps back to the
    -- matching simple-basis vector.
    simpa [rL] using
      basis_constr_rightInverse_of_basis_preimages_local bk
        (decompositionHom A K G).toIntLinearMap x hx
  -- Package the linear section as the additive right inverse used in the matrix endgame.
  exact ⟨rL.toAddMonoidHom, hrL⟩

/-- Helper for Theorem 16-16.1-2: any genuine surjectivity theorem for Serre's decomposition map
produces the additive section needed by the transpose-matrix argument. -/
private theorem decomposition_rightInverse_of_surjective_local
    [IsDomain A] [IsDiscreteValuationRing A]
    (hsurj : Function.Surjective (decompositionHom A K G)) :
    ∃ r : R₀[k](G) →+ R₀[K](G), Function.RightInverse r (decompositionHom A K G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyFieldLocal (F := k) (G := G)
  have hπ_range : ∀ i, [π i]₀ ∈ Set.range (decompositionHom A K G) := by
    intro i
    -- Surjectivity gives the required preimage for each simple basis vector.
    exact hsurj [π i]₀
  -- The basiswise section construction is the only linear algebra needed after surjectivity.
  exact
    decomposition_rightInverse_of_complete_simple_family_local
      (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete hπ_range

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: the source of a projective envelope of a simple `k[G]`-module
is finitely generated over `k[G]`. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
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
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: every simple finite-dimensional `k[G]`-representation admits a
finite projective envelope in the canonical projective owner category. -/
private theorem exists_finite_projective_envelope_of_simple_local
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    -- Expose the ambient `k[G]`-module structure carried by the owner `S`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Convert categorical simplicity of `S` into irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    -- Move the simple owner into the `k[G]`-module API used by projective envelopes.
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
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Theorem 16-16.1-2: the coordinates of `f x` are obtained by expanding `x` in the
source basis and summing the coordinates of the basis images. -/
private theorem basis_repr_linearMap_apply_eq_sum_local
    {ι κ : Type*} [Fintype ι] [Finite κ]
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (bM : Module.Basis ι ℤ M) (bN : Module.Basis κ ℤ N)
    (f : M →ₗ[ℤ] N) (x : M) (i : κ) :
    bN.repr (f x) i = ∑ j, bM.repr x j * bN.repr (f (bM j)) i := by
  -- Read the standard matrix identity `toMatrix(f) * repr(x) = repr(f x)` in the `i`th target
  -- coordinate and then unfold the matrix-vector product.
  classical
  let h :=
    congrArg (fun g : κ → ℤ ↦ g i)
      (LinearMap.toMatrix_mulVec_repr (v₁ := bM) (v₂ := bN) f x)
  simpa [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, mul_comm] using h.symm

/-- Helper for Theorem 16-16.1-2: a basiswise right inverse forces the corresponding square
matrix product to be the identity. -/
private theorem toMatrix_mul_eq_one_of_rightInverse_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Rk RK : Type*}
    [AddCommGroup Rk] [Module ℤ Rk]
    [AddCommGroup RK] [Module ℤ RK]
    (bk : Module.Basis ι ℤ Rk)
    (bK : Module.Basis κ ℤ RK)
    (d : RK →ₗ[ℤ] Rk)
    (r : Rk →ₗ[ℤ] RK)
    (hrightInv : Function.RightInverse r d) :
    LinearMap.toMatrix bK bk d * LinearMap.toMatrix bk bK r = 1 := by
  have hcomp : d.comp r = LinearMap.id := by
    -- Convert the pointwise right-inverse identity into an equality of linear maps.
    ext x
    exact hrightInv x
  -- Read the identity `d ∘ r = id` through the chosen bases.
  rw [← LinearMap.toMatrix_comp bk bK bk d r, hcomp]
  simp

/-- Helper for Theorem 16-16.1-2: once Brauer reciprocity identifies the scalar-extension matrix
with the transpose of the decomposition matrix, transposing a basiswise right inverse of
`decompositionHom A K G` yields the desired section of
`projectiveGrothendieckScalarExtensionHom A K`. -/
private theorem left_inverse_of_transpose_section_henselian_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Pk Rk RK : Type*}
    [AddCommGroup Pk] [Module ℤ Pk]
    [AddCommGroup Rk] [Module ℤ Rk]
    [AddCommGroup RK] [Module ℤ RK]
    (bP : Module.Basis ι ℤ Pk)
    (bk : Module.Basis ι ℤ Rk)
    (bK : Module.Basis κ ℤ RK)
    (e : Pk →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk)
    (r : Rk →ₗ[ℤ] RK)
    (hrightInv : Function.RightInverse r d)
    (hmatrix :
      LinearMap.toMatrix bP bK e =
        (LinearMap.toMatrix bK bk d).transpose) :
    ∃ s : RK →ₗ[ℤ] Pk, Function.LeftInverse s e := by
  let s : RK →ₗ[ℤ] Pk :=
    Matrix.toLin bK bP ((LinearMap.toMatrix bk bK r).transpose)
  have hsMatrix :
      LinearMap.toMatrix bK bP s = (LinearMap.toMatrix bk bK r).transpose := by
    -- The matrix-built linear map is definitionally the one we started from.
    simp [s]
  have hrightInvMatrix :
      LinearMap.toMatrix bK bk d * LinearMap.toMatrix bk bK r = 1 := by
    -- The chosen right inverse already identifies the decomposition-side square matrix product.
    exact toMatrix_mul_eq_one_of_rightInverse_local bk bK d r hrightInv
  have hcompMatrix :
      LinearMap.toMatrix bP bP (s.comp e) = 1 := by
    -- Multiply the transpose matrices and rewrite through the right-inverse relation `d ∘ r = id`.
    calc
      LinearMap.toMatrix bP bP (s.comp e)
          = LinearMap.toMatrix bK bP s * LinearMap.toMatrix bP bK e := by
              simpa using LinearMap.toMatrix_comp bP bK bP s e
      _ = (LinearMap.toMatrix bk bK r).transpose *
            (LinearMap.toMatrix bK bk d).transpose := by
              rw [hsMatrix, hmatrix]
      _ =
          (LinearMap.toMatrix bK bk d * LinearMap.toMatrix bk bK r).transpose := by
            simpa using
              (Matrix.transpose_mul
                (LinearMap.toMatrix bK bk d)
                (LinearMap.toMatrix bk bK r)).symm
      _ = (1 : Matrix ι ι ℤ).transpose := by
            rw [hrightInvMatrix]
      _ = 1 := by
            simp
  have hcomp : s.comp e = LinearMap.id := by
    -- The square matrix of `s ∘ e` is the identity in the basis `bP`, so the map itself is `id`.
    apply (LinearMap.toMatrix bP bP).injective
    simpa using hcompMatrix
  refine ⟨s, ?_⟩
  intro x
  -- Evaluate the recovered identity `s ∘ e = id` at the point `x`.
  exact congrArg (fun f : Pk →ₗ[ℤ] Pk ↦ f x) hcomp

/-- Helper for Theorem 16-16.1-2: after choosing projective envelopes `P_i`, projective lifts
`Q_i`, and stable lattices `L_j` for the generic simples, Serre's common-owner comparison
packages as the transpose identity between the scalar-extension and decomposition matrices. -/
private theorem projective_scalar_extension_toMatrix_eq_decomposition_transpose_henselian_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Pk Rk RK : Type*}
    [AddCommGroup Pk] [Module ℤ Pk]
    [AddCommGroup Rk] [Module ℤ Rk]
    [AddCommGroup RK] [Module ℤ RK]
    (bP : Module.Basis ι ℤ Pk)
    (bk : Module.Basis ι ℤ Rk)
    (bK : Module.Basis κ ℤ RK)
    (e : Pk →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk)
    (hentry : ∀ (j : κ) (i : ι), bK.repr (e (bP i)) j = bk.repr (d (bK j)) i) :
    LinearMap.toMatrix bP bK e =
      (LinearMap.toMatrix bK bk d).transpose := by
  ext j i
  -- Once the `(i,j)` entries are identified basiswise, the whole matrix equality is immediate.
  simpa [LinearMap.toMatrix_apply, Matrix.transpose_apply] using hentry j i

/-- Helper for Theorem 16-16.1-2: a right inverse for `decompositionHom` and the entrywise
Brauer-reciprocity transpose identity assemble into an additive left inverse for scalar extension. -/
private theorem split_injective_of_decomposition_section_and_entries_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsDomain A] [IsDiscreteValuationRing A]
    (bP : Module.Basis ι ℤ (P₀[k](G)))
    (bk : Module.Basis ι ℤ (R₀[k](G)))
    (bK : Module.Basis κ ℤ (R₀[K](G)))
    (r : R₀[k](G) →+ R₀[K](G))
    (hrightInv : Function.RightInverse r (decompositionHom A K G))
    (hentry :
      ∀ (j : κ) (i : ι),
        bK.repr
            ((projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap (bP i)) j =
          bk.repr ((decompositionHom A K G).toIntLinearMap (bK j)) i) :
    ∃ s : R₀[K](G) →+ P₀[k](G),
      Function.LeftInverse s (projectiveGrothendieckScalarExtensionHom A K) := by
  have hmatrix :
      LinearMap.toMatrix bP bK
          (projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap =
        (LinearMap.toMatrix bK bk (decompositionHom A K G).toIntLinearMap).transpose := by
    -- Package the entrywise Brauer reciprocity comparison as a matrix-transpose identity.
    exact
      projective_scalar_extension_toMatrix_eq_decomposition_transpose_henselian_local
        bP bk bK (projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap
        (decompositionHom A K G).toIntLinearMap hentry
  have hrightInvL :
      Function.RightInverse r.toIntLinearMap (decompositionHom A K G).toIntLinearMap := by
    -- Move the additive right inverse to the integer-linear map layer used by matrices.
    intro x
    exact hrightInv x
  obtain ⟨sL, hsL⟩ :=
    left_inverse_of_transpose_section_henselian_local bP bk bK
      (projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap
      (decompositionHom A K G).toIntLinearMap r.toIntLinearMap hrightInvL hmatrix
  refine ⟨sL.toAddMonoidHom, ?_⟩
  intro x
  -- Return from the linear-map section to the additive homomorphism statement.
  exact hsL x

/-- Helper for Theorem 16-16.1-2: the decomposition-map coordinate of a generic simple class is
the fixed-simple multiplicity of the reduction of the chosen stable lattice. -/
private theorem decomposition_coord_eq_stableLatticeMultiplicity_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain A] [IsDiscreteValuationRing A]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ j, StableLattice A (πK j).ρ)
    (i : ι) (j : κ) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
        ((decompositionHom A K G).toIntLinearMap
          ((simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete) j)) i =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        [FDRep.of (L j).reductionRepresentation]₀ := by
  classical
  let bk :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bK :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  -- First rewrite the generic simple-basis vector and evaluate the canonical decomposition map
  -- through the chosen stable lattice.
  calc
    bk.repr ((decompositionHom A K G).toIntLinearMap (bK j)) i =
        bk.repr (decompositionHom A K G [πK j]₀) i := by
          simp [bK, simple_finiteRep_classes_basis_of_complete_family_apply,
            AddMonoidHom.coe_toIntLinearMap]
    _ = bk.repr [FDRep.of (L j).reductionRepresentation]₀ i := by
          rw [decompositionHom_finiteRepClass_eq
            (A := A) (K := K) (G := G) (πK j) (L j)]
    _ = simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
          [FDRep.of (L j).reductionRepresentation]₀ := by
          -- The residue simple-basis coordinate is exactly the fixed-simple multiplicity
          -- functional at the chosen residue simple `π i`.
          simpa [bk] using
            simple_basis_coord_eq_fixed_simple_multiplicity_local
              (A := A) (G := G) (S := π i) π hπ_pairwise hπ_complete
              i ⟨Iso.refl _⟩ [FDRep.of (L j).reductionRepresentation]₀

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: on the projective-envelope basis, fixed-simple multiplicities of
`cartanHom` recover the corresponding Cartan-matrix entries, not a Kronecker delta. -/
private theorem cartan_projectiveEnvelope_basis_fixedMultiplicity_eq_cartanMatrix_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i j : ι) :
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        (cartanHom k G
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) j)) =
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete)
        i j := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let b :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  -- Read the multiplicity through the residue simple basis and then identify that coordinate with
  -- the defining `(i,j)` Cartan entry.
  calc
    simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        (cartanHom k G (bP j)) =
      b.repr (cartanHom k G (bP j)) i := by
        simpa [b] using
          (simple_basis_coord_eq_fixed_simple_multiplicity_local
            (A := A) (G := G) (S := π i) π hπ_pairwise hπ_complete i ⟨Iso.refl _⟩
            (cartanHom k G (bP j))).symm
    _ = cartanMatrix k G bP b i j := by
        simp [cartanMatrix, LinearMap.toMatrix_apply]

/-- Helper for Theorem 16-16.1-2: a complete pairwise-nonisomorphic family of simple
finite-dimensional representations of a finite group over any field has a finite index type. -/
private theorem finite_index_of_complete_pairwise_nonisomorphic_simple_family_local
    {F : Type u} [Field F] {ι : Type*}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  -- Inject the complete simple family into the finite list of regular-module composition factors;
  -- this avoids the semisimple/algebraically closed finite-index theorem, whose side conditions
  -- are not available in the modular residue setting.
  exact
    finiteOfCompletePairwiseNonisomorphicSimpleFamily
      (F := F) (G := G) π hπ_pairwise hπ_complete

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: a sufficiently large coefficient field has nonzero group order.
-/
private theorem nat_card_neZero_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    NeZero (Nat.card G : K) := by
  let p := ringChar K
  refine NeZero.of_not_dvd K (p := p) ?_
  intro hp_card
  by_cases hp_zero : p = 0
  · have hcard_zero : Nat.card G = 0 := by
      apply zero_dvd_iff.mp
      rw [← hp_zero]
      exact hp_card
    exact Nat.card_pos.ne' hcard_zero
  · haveI : NeZero p := ⟨hp_zero⟩
    haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hp_card
    have hp_exp : p ∣ Monoid.exponent G := by
      simpa [hg] using Monoid.order_dvd_exponent g
    letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent G)
    have hne_exp : NeZero ((Monoid.exponent G : ℕ) : K) := hζ.neZero'
    exact (NeZero.not_char_dvd (R := K) p (Monoid.exponent G)) hp_exp

/-- Helper for Theorem 16-16.1-2: a finite subgroup-induction decomposition lifts through
`decompositionHom` once each subgroup summand has a preimage and `decompositionHom` commutes with
those subgroup inductions. -/
private theorem finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition_local
    [IsDomain A] [IsDiscreteValuationRing A]
    {ι : Type u} [Fintype ι]
    (H : ι → Subgroup G)
    (y : ∀ i, R₀[k](H i))
    (z : R₀[k](G))
    (hdecomp :
      z =
        ∑ i,
          finiteRepGrothendieckGroupInduction_splitInjective k (H i) (y i))
    (hRange : ∀ i, y i ∈ Set.range (decompositionHom A K (H i)))
    (hcompat :
      ∀ i (x : R₀[K](H i)),
        decompositionHom A K G
            (finiteRepGrothendieckGroupInduction_splitInjective K (H i) x) =
          finiteRepGrothendieckGroupInduction_splitInjective k (H i)
            (decompositionHom A K (H i) x)) :
    z ∈ Set.range (decompositionHom A K G) := by
  classical
  choose x hx using hRange
  refine
    ⟨∑ i, finiteRepGrothendieckGroupInduction_splitInjective K (H i) (x i), ?_⟩
  -- Push `decompositionHom` through the finite sum, then replace every summand by its chosen
  -- subgroup preimage and finally fold the given induction decomposition back to `z`.
  calc
    decompositionHom A K G
        (∑ i, finiteRepGrothendieckGroupInduction_splitInjective K (H i) (x i)) =
        ∑ i,
          decompositionHom A K G
            (finiteRepGrothendieckGroupInduction_splitInjective K (H i) (x i)) := by
          simp [map_sum]
    _ =
        ∑ i,
          finiteRepGrothendieckGroupInduction_splitInjective k (H i)
            (decompositionHom A K (H i) (x i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact hcompat i (x i)
    _ =
        ∑ i,
          finiteRepGrothendieckGroupInduction_splitInjective k (H i) (y i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hx i]
    _ = z := hdecomp.symm

/-- Helper for Theorem 16-16.1-2: a source theorem giving finite subgroup-induction
decompositions with subgroup preimages immediately implies surjectivity of `decompositionHom`. -/
private theorem decompositionHom_surjective_of_induction_decomposition_local
    [IsDomain A] [IsDiscreteValuationRing A]
    (hInd :
      ∀ z : R₀[k](G),
        ∃ ι : Type u,
          ∃ hι : Fintype ι,
            ∃ H : ι → Subgroup G,
              ∃ y : ∀ i, R₀[k](H i),
                z =
                    (@Finset.univ ι hι).sum
                      (fun i ↦
                        finiteRepGrothendieckGroupInduction_splitInjective k (H i)
                          (y i)) ∧
                  (∀ i, Function.Surjective (decompositionHom A K (H i))) ∧
                    (∀ i (x : R₀[K](H i)),
                      decompositionHom A K G
                          (finiteRepGrothendieckGroupInduction_splitInjective K (H i) x) =
                        finiteRepGrothendieckGroupInduction_splitInjective k (H i)
                          (decompositionHom A K (H i) x))) :
    Function.Surjective (decompositionHom A K G) := by
  intro z
  rcases hInd z with ⟨ι, hι, H, y, hdecomp, hsurj, hcompat⟩
  letI : Fintype ι := hι
  have hRange : ∀ i, y i ∈ Set.range (decompositionHom A K (H i)) := by
    intro i
    exact hsurj i (y i)
  -- Apply the formal range bridge to the source-provided induction decomposition of `z`.
  exact
    finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition_local
      (A := A) (K := K) (G := G) H y z hdecomp hRange hcompat

/-- Helper for Theorem 16-16.1-2: the active same-field form of Serre's decomposition theorem
for a sufficiently large complete DVR modular system. -/
private theorem decompositionHom_rightInverse_of_orderPrimeToResidueChar_local
    {p : ℕ} [CharP k p]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hpG : ¬ p ∣ Nat.card G) :
    ∃ s : R₀[k](G) →+ R₀[K](G),
      Function.RightInverse s (decompositionHom A K G) := by
  classical
  obtain ⟨ι, πK, hπK_pairwise, hπK_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyFieldLocal (F := K) (G := G)
  let L : ∀ i, StableLattice A (πK i).ρ :=
    fun i ↦ Classical.choice (Representation.exists_stableLattice (A := A) (ρ := (πK i).ρ))
  let bK : Module.Basis ι ℤ (R₀[K](G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hpG πK hπK_pairwise hπK_complete L
  have hbasis :
      ∀ i, (decompositionHom A K G).toIntLinearMap (bK i) = bk i := by
    intro i
    -- Chapter 15 proves that, when `p ∤ |G|`, reducing a stable lattice sends the chosen
    -- generic simple basis vector to the corresponding residue simple basis vector.
    rw [simple_finiteRep_classes_basis_of_complete_family_apply,
      simple_finiteRep_classes_basis_of_complete_family_apply]
    simpa [bK, bk, reduction_family_of_order_prime_to_p_local] using
      decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)
  let sL : R₀[k](G) →ₗ[ℤ] R₀[K](G) := bk.constr ℕ (fun i ↦ bK i)
  have hsL :
      Function.RightInverse sL (decompositionHom A K G).toIntLinearMap := by
    -- A linear map built by sending each residue basis vector to its generic lift is a right
    -- inverse because the decomposition map returns every basis vector.
    exact
      basis_constr_rightInverse_of_basis_preimages_local
        bk (decompositionHom A K G).toIntLinearMap (fun i ↦ bK i) hbasis
  -- Package the linear section as the additive section used by the Grothendieck-group API.
  exact ⟨sL.toAddMonoidHom, hsL⟩

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: a fraction field of a local domain has either characteristic
zero or the same prime characteristic as the residue field. -/
private theorem fractionField_charZero_or_charP_residue_local
    {p : ℕ} [Fact p.Prime] [hpChar : CharP k p]
    [IsDomain A] [IsDiscreteValuationRing A] :
    CharZero K ∨ CharP K p := by
  by_cases hchar0 : ringChar K = 0
  · -- The zero `ringChar` branch is the ordinary characteristic-zero instance.
    exact Or.inl ((CharP.ringChar_zero_iff_CharZero (R := K)).mp hchar0)
  · let q := ringChar K
    have hqprime : Nat.Prime q := by
      rcases CharP.char_is_prime_or_zero K q with hqprime | hqzero
      · exact hqprime
      · exact (hchar0 hqzero).elim
    letI : Fact q.Prime := ⟨hqprime⟩
    letI : CharP K q := ringChar.charP (R := K)
    letI : CharP A q :=
      RingHom.charP (algebraMap A K) (IsFractionRing.injective A K) q
    have hq0 : (q : k) = 0 := by
      -- Push the characteristic-`q` equality from `A` to the residue-field quotient.
      change
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q : A) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) 0
      exact congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
        (CharP.cast_eq_zero (R := A) q)
    letI : CharP k q :=
      ringChar.of_eq
        (CharP.ringChar_of_prime_eq_zero (R := k) hqprime hq0)
    have hpchar : ringChar k = p := @ringChar.eq k _ p hpChar
    have hqchar : ringChar k = q := ringChar.eq (R := k) q
    have hqp : q = p := by
      -- A field cannot have two distinct prime characteristics.
      calc
        q = ringChar k := hqchar.symm
        _ = p := hpchar
    exact Or.inr (hqp ▸ (inferInstance : CharP K q))

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: in the branch `p ∣ |G|`, enough roots rule out the
equal-characteristic fraction-field case, so the generic field has characteristic zero. -/
private theorem charZero_of_hasEnoughRoots_dvd_natCard_local
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsDomain A] [IsDiscreteValuationRing A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hpG : p ∣ Nat.card G) :
    CharZero K := by
  rcases fractionField_charZero_or_charP_residue_local
      (A := A) (K := K) (p := p) with hzero | hcharp
  · exact hzero
  · letI : CharP K p := hcharp
    have hcard_zero : (Nat.card G : K) = 0 :=
      (CharP.cast_eq_zero_iff K p (Nat.card G)).2 hpG
    letI : NeZero (Nat.card G : K) :=
      nat_card_neZero_of_hasEnoughRoots_local (K := K) (G := G)
    exact False.elim ((NeZero.ne (Nat.card G : K)) hcard_zero)

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: a sufficiently large characteristic-zero field receives the full
cyclotomic field of the group exponent. -/
private noncomputable def cyclotomicFieldExponentAlgHom_of_hasEnoughRoots_local
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] K := by
  classical
  let m := Monoid.exponent G
  let Lexp := CyclotomicField m ℚ
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {m} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := m) (K := ℚ)
  have hprim :
      ∀ n ∈ ({m} : Set ℕ), n ≠ 0 → ∃ r : K, IsPrimitiveRoot r n := by
    intro n hn _hn0
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K m
  let M : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {x : K | ∃ n ∈ ({m} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  let e : Lexp ≃ₐ[ℚ] M :=
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
        (S := {m}) ℚ Lexp K hprim)
  -- Include the cyclotomic subfield of `K` into `K` itself.
  exact (IsScalarTower.toAlgHom ℚ M K).comp e.toAlgHom

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: the top intermediate cyclotomic field also maps into any
sufficiently large characteristic-zero coefficient field. -/
private noncomputable def cyclotomicTopAlgHom_of_hasEnoughRoots_local
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ↥(⊤ : IntermediateField ℚ (CyclotomicField (Monoid.exponent G) ℚ)) →ₐ[ℚ] K :=
  (cyclotomicFieldExponentAlgHom_of_hasEnoughRoots_local (K := K) (G := G)).comp
    (IntermediateField.topEquiv (F := ℚ)
      (E := CyclotomicField (Monoid.exponent G) ℚ)).toAlgHom

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: scalar extension of a representation changes its character by
applying the chosen coefficient homomorphism. -/
private theorem scalarExtension_character_eq_algHom_map_local
    {F : Type} [Field F] {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    {H : Type u} [Group H]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) :
    letI : Algebra F E := f.toRingHom.toAlgebra
    (Representation.scalarExtension ρ).character = fun h ↦ f (ρ.character h) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  ext h
  exact LinearMap.trace_baseChange (ρ h) E

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: coefficientwise field homomorphisms send virtual character
rings into virtual character rings. -/
private theorem map_mem_characterRingOverField_algHom_local
    {F : Type} [Field F] {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    {H : Type u} [Group H] [Finite H]
    (χ : H → F)
    (hχ : χ ∈ R[F](H)) :
    (f.compLeft H) χ ∈ R[E](H) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  -- Check honest characters by scalar extension and then close under the algebra operations
  -- defining the virtual character ring.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    let ρE : Rep E H := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (f.compLeft H) ρ.ρ.character = ρE.ρ.character := by
      ext h
      simpa [ρE] using
        (congrFun
          (scalarExtension_character_eq_algHom_map_local
            (f := f) (H := H) (ρ := ρ.ρ))
          h).symm
    exact hchar.symm ▸
      Representation.rep_character_mem_characterRingOverField
        (K := E) (G := H) (Rep.of (Representation.scalarExtension ρ.ρ))
  · intro n
    change (fun _ : H ↦ f (algebraMap ℤ F n)) ∈ R[E](H)
    have hconst : (fun _ : H ↦ f (algebraMap ℤ F n)) = algebraMap ℤ (H → E) n := by
      ext h
      simpa using (f.commutes n)
    rw [hconst]
    exact (R[E](H)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](H)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](H)).mul_mem hφ hψ

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: coefficientwise field homomorphisms induce additive maps on
virtual character rings. -/
private noncomputable def characterRingMapAlgHom_local
    {F : Type} [Field F] {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    (H : Type u) [Group H] [Finite H] :
    R[F](H) →+ R[E](H) where
  toFun χ :=
    ⟨(f.compLeft H) (χ : H → F),
      map_mem_characterRingOverField_algHom_local f (χ : H → F) χ.property⟩
  map_zero' := by
    ext h
    simp
  map_add' χ ψ := by
    ext h
    simp

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: the coefficientwise map on virtual character rings preserves
the unit character. -/
private theorem characterRingMapAlgHom_one_local
    {F : Type} [Field F] {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    {H : Type u} [Group H] [Finite H] :
    characterRingMapAlgHom_local f H 1 = 1 := by
  ext h
  simp [characterRingMapAlgHom_local]

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: coefficientwise maps commute with subgroup induction on
virtual character rings. -/
private theorem characterRingMapAlgHom_subgroupInduction_local
    {F : Type} [Field F] [CharZero F]
    {E : Type u} [Field E] [CharZero E]
    (f : F →ₐ[ℤ] E)
    {H₀ : Type u} [Group H₀] [Finite H₀]
    (H : Subgroup H₀) (χ : R[F](H)) :
    characterRingMapAlgHom_local f H₀
        (H.characterRingOverFieldInduction F χ) =
      H.characterRingOverFieldInduction E
        (characterRingMapAlgHom_local f H χ) := by
  classical
  ext h
  simp only [characterRingMapAlgHom_local, Subgroup.characterRingOverFieldInduction_apply,
    Subtype.coe_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Subgroup.inducedClassFunction]
  change
    f (((Nat.card ↥H : F)⁻¹) *
        ∑ s : H₀,
          if hsg : s⁻¹ * h * s ∈ H then
            (χ : H → F) ⟨s⁻¹ * h * s, hsg⟩
          else 0) =
      (Nat.card ↥H : E)⁻¹ *
        ∑ x : H₀,
          if hsg : x⁻¹ * h * x ∈ H then
            f ((χ : H → F) ⟨x⁻¹ * h * x, hsg⟩)
          else 0
  rw [map_mul]
  have hcoeff : f ((Nat.card ↥H : F)⁻¹) = (Nat.card ↥H : E)⁻¹ := by
    simp
  have hsum :
      f (∑ s : H₀,
          if hsg : s⁻¹ * h * s ∈ H then
            (χ : H → F) ⟨s⁻¹ * h * s, hsg⟩
          else 0) =
        ∑ x : H₀,
          if hsg : x⁻¹ * h * x ∈ H then
            f ((χ : H → F) ⟨x⁻¹ * h * x, hsg⟩)
          else 0 := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    by_cases hxH : x⁻¹ * h * x ∈ H
    · simp [hxH]
    · simp [hxH]
  rw [hcoeff, hsum]

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: coefficientwise maps commute with finite sums of subgroup
inductions on virtual character rings. -/
private theorem characterRingMapAlgHom_sum_subgroupInduction_local
    {F : Type} [Field F] [CharZero F]
    {E : Type u} [Field E] [CharZero E]
    (f : F →ₐ[ℤ] E)
    {H₀ : Type u} [Group H₀] [Finite H₀]
    {ι : Type u} [Fintype ι]
    (H : ι → Subgroup H₀) (χ : ∀ i, R[F](H i)) :
    characterRingMapAlgHom_local f H₀
        (∑ i, (H i).characterRingOverFieldInduction F (χ i)) =
      ∑ i, (H i).characterRingOverFieldInduction E
        (characterRingMapAlgHom_local f (H i) (χ i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact characterRingMapAlgHom_subgroupInduction_local f (H i) (χ i)

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: over a sufficiently large characteristic-zero field, the unit
ordinary character-ring unit is an integral sum of inductions from elementary subgroups. -/
private theorem one_eq_sum_elementary_characterRingInduction_of_hasEnoughRoots_local
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (ι : Type u) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ χ : ∀ i, R[K](H i),
          (1 : R[K](G)) =
            ∑ i, (H i).characterRingOverFieldInduction K (χ i) := by
  classical
  let Lexp := CyclotomicField (Monoid.exponent G) ℚ
  let Ktop : IntermediateField ℚ Lexp := ⊤
  letI : NumberField Lexp := inferInstance
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  let ι : Type u :=
    { H : Subgroup G //
      Subgroup.IsGammaElementary (Representation.gammaSubgroup (Monoid.exponent G) Ktop) H }
  letI : Fintype ι := inferInstance
  letI : DecidableEq ι := Classical.decEq ι
  let φℚ : ↥Ktop →ₐ[ℚ] K :=
    cyclotomicTopAlgHom_of_hasEnoughRoots_local (K := K) (G := G)
  let φ : ↥Ktop →ₐ[ℤ] K := φℚ.restrictScalars ℤ
  obtain ⟨χ, hχ⟩ :=
    gammaElementarySubgroupInductionOverField_surjective
      (K := Ktop) (G := G) (L := Lexp) (1 : R[↥Ktop](G))
  have hχ_sum :
      (1 : R[↥Ktop](G)) =
        χ.sum fun H ↦
          (H.1.characterRingOverFieldInduction (↥Ktop)).toAddMonoidHom := by
    have happly :
        (gammaElementarySubgroupInductionOverField (↥Ktop)
            (Representation.gammaSubgroup (Monoid.exponent G) Ktop)) χ =
          χ.sum fun H ↦
            (H.1.characterRingOverFieldInduction (↥Ktop)).toAddMonoidHom := by
      unfold gammaElementarySubgroupInductionOverField
      exact
        DFinsupp.sumAddHom_apply
          (fun H : ι ↦ (H.1.characterRingOverFieldInduction (↥Ktop)).toAddMonoidHom) χ
    exact hχ.symm.trans happly
  have hχ_fin :
      (1 : R[↥Ktop](G)) =
        ∑ H : ι, H.1.characterRingOverFieldInduction (↥Ktop) (χ H) := by
    calc
      (1 : R[↥Ktop](G)) =
          χ.sum fun H ↦
            (H.1.characterRingOverFieldInduction (↥Ktop)).toAddMonoidHom := hχ_sum
      _ =
          ∑ H : ι, H.1.characterRingOverFieldInduction (↥Ktop) (χ H) := by
            exact
              DFinsupp.sum_eq_sum_fintype
                (v := χ)
                (f := fun H ψH ↦ H.1.characterRingOverFieldInduction (↥Ktop) ψH)
                (hf := fun H ↦ by simp)
  have hχK_sum :
      (1 : R[K](G)) =
        ∑ H : ι,
          H.1.characterRingOverFieldInduction K
            (characterRingMapAlgHom_local φ H.1 (χ H)) := by
    calc
      (1 : R[K](G)) =
          characterRingMapAlgHom_local φ G (1 : R[↥Ktop](G)) := by
            exact (characterRingMapAlgHom_one_local φ (H := G)).symm
      _ =
          characterRingMapAlgHom_local φ G
            (∑ H : ι, H.1.characterRingOverFieldInduction (↥Ktop) (χ H)) := by
            rw [hχ_fin]
      _ =
          ∑ H : ι,
            H.1.characterRingOverFieldInduction K
              (characterRingMapAlgHom_local φ H.1 (χ H)) := by
            exact
              characterRingMapAlgHom_sum_subgroupInduction_local
                (E := K) φ (fun H : ι ↦ H.1) (fun H : ι ↦ χ H)
  refine ⟨ι, inferInstance, (fun H : ι ↦ H.1), ?_,
    (fun H ↦ characterRingMapAlgHom_local φ H.1 (χ H)), hχK_sum⟩
  intro H
  have hΓbot :
      Representation.gammaSubgroup (Monoid.exponent G) Ktop =
        (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
    simpa [Ktop, Lexp] using gammaSubgroup_top_eq_bot_bridge (G := G)
  have hHbot :
      Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H.1 := by
    rw [← hΓbot]
    exact H.2
  rcases hHbot with ⟨q, hq⟩
  exact ⟨q, (Subgroup.IsGammaPElementary.bot_iff_isPElementary q H.1).1 hq⟩

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: over a sufficiently large characteristic-zero field, the unit
ordinary Grothendieck class is an integral sum of inductions from elementary subgroups. -/
private theorem one_eq_sum_elementary_finiteRepGrothendieckInduction_of_hasEnoughRoots_local
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (ι : Type u) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[K](H i),
          (1 : R₀[K](G)) =
            ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i) := by
  classical
  obtain ⟨ι, hι, H, hH, χK, hχK_sum⟩ :=
    one_eq_sum_elementary_characterRingInduction_of_hasEnoughRoots_local
      (K := K) (G := G)
  letI : Fintype ι := hι
  let y : ∀ i : ι, R₀[K](H i) :=
    fun i ↦ (finiteRepGrothendieckCharacterAddEquiv' (K := K) (G := H i)).symm (χK i)
  have hGroth :
      (1 : R₀[K](G)) =
        ∑ i : ι, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i) := by
    apply (finiteRepGrothendieckCharacter_bijective' (K := K) (G := G)).1
    calc
      finiteRepGrothendieckCharacter K G (1 : R₀[K](G)) =
          (1 : R[K](G)) := finiteRepGrothendieckCharacter_one (K := K) (G := G)
      _ = ∑ i : ι, (H i).characterRingOverFieldInduction K (χK i) := hχK_sum
      _ =
          ∑ i : ι,
            finiteRepGrothendieckCharacter K G
              (Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [finiteRepGrothendieckCharacter_subgroupInduction]
            have hy :
                finiteRepGrothendieckCharacter K (H i) (y i) = χK i := by
              exact
                (finiteRepGrothendieckCharacterAddEquiv' (K := K) (G := H i)).apply_symm_apply
                  (χK i)
            rw [hy]
      _ =
          finiteRepGrothendieckCharacter K G
            (∑ i : ι,
              Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i)) := by
            simp [map_sum]
  exact ⟨ι, hι, H, hH, y, hGroth⟩

/-- Helper for Theorem 16-16.1-2: the mixed-characteristic branch of Serre's decomposition theorem
for the active complete-DVR modular system. -/
private theorem decompositionHom_surjective_of_mixedResidueChar_hasEnoughRoots_local
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hpG : p ∣ Nat.card G) :
    Function.Surjective (decompositionHom A K G) := by
  classical
  haveI : CharZero K :=
    charZero_of_hasEnoughRoots_dvd_natCard_local
      (A := A) (K := K) (G := G) (p := p) hpG
  obtain ⟨ι, hι, H, hH, y, hunitK⟩ :=
    one_eq_sum_elementary_finiteRepGrothendieckInduction_of_hasEnoughRoots_local
      (K := K) (G := G)
  letI : Fintype ι := hι
  intro z
  let yk : ∀ i, R₀[k](H i) := fun i ↦ decompositionHom A K (H i) (y i)
  have hunitk :
      (1 : R₀[k](G)) =
        ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yk i) := by
    calc
      (1 : R₀[k](G)) = decompositionHom A K G (1 : R₀[K](G)) := by
        rw [decompositionHom_one (A := A) (K := K) (G := G)]
      _ =
          decompositionHom A K G
            (∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i)) := by
            rw [← hunitK]
      _ =
          ∑ i,
            decompositionHom A K G
              (Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i)) := by
            simp [map_sum]
      _ =
          ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yk i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact
              decompositionHom_subgroupInduction_of_bridge
                (A := A) (K := K) (G := G) (H i)
                (hind_complete (A := A) (K := K) (G := G) (H i)) (y i)
  let yr : ∀ i, R₀[k](H i) :=
    fun i ↦ yk i *
      Representation.Subgroup.finiteRepGrothendieckGroupRestriction k (H i) z
  have hzdecomp :
      z =
        ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yr i) := by
    calc
      z = (1 : R₀[k](G)) * z := by rw [one_mul]
      _ =
          (∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yk i)) *
            z := by
            rw [hunitk]
      _ =
          ∑ i,
            Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yk i) * z := by
            rw [Finset.sum_mul]
      _ =
          ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (yr i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact
              Representation.finiteRepGrothendieckGroupInduction_mul (H i) (yk i) z
  have hRange : ∀ i, yr i ∈ Set.range (decompositionHom A K (H i)) := by
    intro i
    exact
      decompositionHom_surjective_of_isElementary
        (A := A) (K := K) (G := G) (p := p) (H i) (hH i) (yr i)
  exact
    finiteRepGrothendieckClass_mem_range_decompositionHom_of_induction_decomposition'
      (A := A) (K := K) (G := G) H yr z hzdecomp hRange

/-- Helper for Theorem 16-16.1-2: the active same-field form of Serre's decomposition theorem
for a sufficiently large complete DVR modular system. -/
private theorem decompositionHom_surjective_of_hasEnoughRoots_sameField_local
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective (decompositionHom A K G) := by
  -- Route correction: split off the `p ∤ |G|` branch instead of keeping Theorem 33 as a single
  -- subgroup-induction placeholder.  Chapter 15 gives a basis-level right inverse in that branch;
  -- only the mixed-characteristic active-field theorem remains as a source input.
  classical
  let p := ringChar k
  letI : CharP k p := ringChar.charP (R := k)
  by_cases hpG : p ∣ Nat.card G
  · by_cases hp0 : p = 0
    · have hcard_zero : Nat.card G = 0 := by
        have hpG0 : 0 ∣ Nat.card G := by
          rw [hp0] at hpG
          exact hpG
        exact Nat.zero_dvd.mp hpG0
      exact (Nat.card_pos.ne' hcard_zero).elim
    · haveI : NeZero p := ⟨hp0⟩
      haveI : Fact p.Prime := CharP.char_is_prime_of_pos k p
      exact
        decompositionHom_surjective_of_mixedResidueChar_hasEnoughRoots_local
          (A := A) (K := K) (G := G) (p := p) hpG
  · obtain ⟨s, hs⟩ :=
      decompositionHom_rightInverse_of_orderPrimeToResidueChar_local
        (A := A) (K := K) (G := G) (p := p) hpG
    exact Function.RightInverse.surjective hs

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: adjoining a Laurent-series uniformizer preserves the chosen
primitive roots of unity. -/
private theorem hasEnoughRootsOfUnity_laurentSeries_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := by
  classical
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent G)
  have hprim : (primitiveRoots (Monoid.exponent G) K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos (Monoid.exponent G))]
    exact hζ
  exact
    MulEquiv.hasEnoughRootsOfUnity
      (rootsOfUnityEquivOfPrimitiveRoots
        (S := LaurentSeries K)
        (f := algebraMap K (LaurentSeries K))
        (algebraMap K (LaurentSeries K)).injective
        hprim)

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] [Group G] [Finite G] in
/-- Helper for Theorem 16-16.1-2: replacing a field by an isomorphic coefficient field does not
change finite dimension. -/
private theorem finrank_compHom_ringEquiv_eq_local
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    (M : Type u) [AddCommGroup M] [Module K M] [FiniteDimensional K M] :
    @Module.finrank F M _ _ (Module.compHom M e.toRingHom) = Module.finrank K M := by
  classical
  letI : Module F M := Module.compHom M e.toRingHom
  let bK : Module.Basis (Module.Free.ChooseBasisIndex K M) K M := Module.Free.chooseBasis K M
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K M) F M :=
    bK.mapCoeffs e.symm (by
      intro c x
      change e (e.symm c) • x = c • x
      simp)
  rw [Module.finrank_eq_card_basis bF, Module.finrank_eq_card_basis bK]

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: transport a `K`-representation to an isomorphic coefficient
field, keeping the same underlying additive group and group action. -/
private noncomputable def repOverRingEquiv_local
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation F G S := by
  letI : Module F S := Module.compHom S e.toRingHom
  exact
    { toFun := fun g ↦
        { toFun := fun x ↦ S.ρ g x
          map_add' := by intro x y; exact (S.ρ g).map_add x y
          map_smul' := by
            intro a x
            change S.ρ g (e a • x) = e a • S.ρ g x
            exact (S.ρ g).map_smul (e a) x }
      map_one' := by
        ext x
        change S.ρ 1 x = x
        simp
      map_mul' := by
        intro g h
        ext x
        change S.ρ (g * h) x = S.ρ g (S.ρ h x)
        simp }

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: simplicity is preserved by transport across an isomorphic
coefficient field. -/
private theorem transported_irreducible_of_ringEquiv_local
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) [Simple S] :
    letI : Module F S := Module.compHom S e.toRingHom
    Representation.IsIrreducible (repOverRingEquiv_local e S) := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  change Representation.IsIrreducible (repOverRingEquiv_local e S)
  have hSK : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  have hS_nontriv : Nontrivial S := by
    by_contra h
    letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp h
    have hzero : (𝟙 S : S ⟶ S) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero S hzero
  let ρF : Representation F G S := repOverRingEquiv_local e S
  have hbot_ne_top : (⊥ : Subrepresentation ρF) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    have hsub := congrArg Subrepresentation.toSubmodule h
    have hxbot : x ∈ (⊥ : Submodule F S) := by
      change x ∈ (⊥ : Subrepresentation ρF).toSubmodule
      rw [hsub]
      exact Submodule.mem_top
    exact hx (by simpa using hxbot)
  letI : Nontrivial (Subrepresentation ρF) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro N
  let NK : Subrepresentation S.ρ :=
    { toSubmodule :=
        { carrier := N.toSubmodule
          zero_mem' := N.toSubmodule.zero_mem'
          add_mem' := N.toSubmodule.add_mem'
          smul_mem' := by
            intro c x hx
            have hx' : (e.symm c) • x ∈ N.toSubmodule := N.toSubmodule.smul_mem (e.symm c) hx
            convert hx' using 1
            change c • x = e (e.symm c) • x
            simp }
      apply_mem_toSubmodule := by
        intro g x hx
        exact N.apply_mem_toSubmodule g hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top NK with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊥ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊥ : Subrepresentation S.ρ).toSubmodule := by
      rw [hbot]
    exact hmem
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ N.toSubmodule ↔ x ∈ (⊤ : Subrepresentation ρF).toSubmodule
    have hmem : x ∈ NK.toSubmodule ↔ x ∈ (⊤ : Subrepresentation S.ρ).toSubmodule := by
      rw [htop]
    exact hmem

omit [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [Algebra A K]
  [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: transport self-intertwining maps across an isomorphic
coefficient field. -/
private noncomputable def intertwiningMap_ringEquiv_linearEquiv_local
    {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
    {G : Type u} [Group G] (S : FDRep K G) :
    letI : Module F S := Module.compHom S e.toRingHom
    let ρF : Representation F G S := repOverRingEquiv_local e S
    letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
      Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
    Representation.IntertwiningMap ρF ρF ≃ₗ[F]
      Representation.IntertwiningMap S.ρ S.ρ := by
  classical
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv_local e S
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  exact
    { toFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by intro x y; exact f.map_add x y
              map_smul' := by
                intro c x
                have h := f.toLinearMap.map_smul (e.symm c) x
                change f (e (e.symm c) • x) = e (e.symm c) • f x at h
                simpa using h }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv_local] using
              (Representation.IntertwiningMap.isIntertwining
                (repOverRingEquiv_local e S) (repOverRingEquiv_local e S) f g x) }
      invFun := fun f ↦
        { toLinearMap :=
            { toFun := fun x ↦ f x
              map_add' := by intro x y; exact f.map_add x y
              map_smul' := by
                intro a x
                change f (e a • x) = e a • f x
                exact f.map_smul (e a) x }
          isIntertwining' := by
            intro g
            ext x
            simpa [ρF, repOverRingEquiv_local] using
              (Representation.IntertwiningMap.isIntertwining S.ρ S.ρ f g x) }
      left_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      right_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        rfl
      map_add' := by
        intro f g
        apply Representation.IntertwiningMap.ext
        rfl
      map_smul' := by
        intro a f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl }

/-- Helper for Theorem 16-16.1-2: sufficiently large generic fields are splitting fields for
simple finite-dimensional `K[G]`-representations. -/
private theorem genericSimple_selfIntertwining_finrank_eq_one_of_hasEnoughRoots_local
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep K G) [Simple S] :
    Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  classical
  let F := IsLocalRing.ResidueField (PowerSeries K)
  let e : F ≃+* K := PowerSeries.residueFieldOfPowerSeries
  haveI : CharZero F := (RingHom.charZero_iff e.toRingHom.injective).2 inferInstance
  letI : Module F S := Module.compHom S e.toRingHom
  let ρF : Representation F G S := repOverRingEquiv_local e S
  haveI : FiniteDimensional F S := by
    let bK : Module.Basis (Module.Free.ChooseBasisIndex K S) K S := Module.Free.chooseBasis K S
    let bF : Module.Basis (Module.Free.ChooseBasisIndex K S) F S :=
      bK.mapCoeffs e.symm (by
        intro c x
        change e (e.symm c) • x = c • x
        simp)
    exact bF.finiteDimensional_of_finite
  let SF : FDRep F G := FDRep.of ρF
  haveI : Representation.IsIrreducible SF.ρ := by
    simpa [SF, ρF] using transported_irreducible_of_ringEquiv_local e S
  haveI : Simple SF := FDRep.simple_of_isIrreducible SF
  have hroots : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_laurentSeries_local (K := K) (G := G)
  have hHom : Module.finrank F (SF ⟶ SF) = 1 := by
    letI : HasEnoughRootsOfUnity (LaurentSeries K) (Monoid.exponent G) := hroots
    exact
      simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
        (A := PowerSeries K) (K := LaurentSeries K) (G := G) SF
  let eHom : (SF ⟶ SF) ≃ₗ[F] Representation.IntertwiningMap ρF ρF :=
    ((FDRep.forget₂HomLinearEquiv SF SF).symm).trans
      (Rep.homLinearEquiv
        ((forget₂ (FDRep F G) (Rep F G)).obj SF)
        ((forget₂ (FDRep F G) (Rep F G)).obj SF))
  have hIF : Module.finrank F (Representation.IntertwiningMap ρF ρF) = 1 := by
    simpa [hHom] using (LinearEquiv.finrank_eq eHom).symm
  letI : Module F (Representation.IntertwiningMap S.ρ S.ρ) :=
    Module.compHom (Representation.IntertwiningMap S.ρ S.ρ) e.toRingHom
  have hIKF : Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
    let E := intertwiningMap_ringEquiv_linearEquiv_local e S
    simpa [hIF, ρF] using (LinearEquiv.finrank_eq E).symm
  have hfinrank_eq :
      Module.finrank F (Representation.IntertwiningMap S.ρ S.ρ) =
        Module.finrank K (Representation.IntertwiningMap S.ρ S.ρ) := by
    exact finrank_compHom_ringEquiv_eq_local e (Representation.IntertwiningMap S.ρ S.ρ)
  rw [← hfinrank_eq]
  exact hIKF

/-- Helper for Theorem 16-16.1-2: sufficiently large complete DVR modular systems make the
residue field split all simple `k[G]`-representations. -/
private theorem residueSimple_selfIntertwining_finrank_eq_one_of_hasEnoughRootsDVR_local
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep k G) [Simple S] :
    Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) = 1 := by
  let e :
      (S ⟶ S) ≃ₗ[k] Representation.IntertwiningMap S.ρ S.ρ :=
    ((FDRep.forget₂HomLinearEquiv S S).symm).trans
      (Rep.homLinearEquiv
        ((forget₂ (FDRep k G) (Rep k G)).obj S)
        ((forget₂ (FDRep k G) (Rep k G)).obj S))
  calc
    Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) =
        Module.finrank k (S ⟶ S) := (LinearEquiv.finrank_eq e).symm
    _ = 1 :=
        simple_finiteRep_endomorphism_finrank_eq_one_of_sufficiently_large
          (A := A) (K := K) (G := G) S

omit [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: if an `A[G]`-projective module reduces to a residue-field
projective module, scalar extension of the residue projective class is the class of the lifted
generic module. -/
private theorem projectiveScalarExtension_liftClass_eq_local
    {K' : Type u} [Field K'] [Algebra A K']
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    projectiveGrothendieckScalarExtensionHom A K' [F]ₚ₀ = [Q.scalarExtension K']₀ := by
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
    -- The chosen reduction isomorphism gives equality after applying the reduction equivalence.
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [F]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [F]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred.symm
  -- Evaluate Serre's scalar-extension map through the inverse reduction equivalence.
  calc
    projectiveGrothendieckScalarExtensionHom A K' [F]ₚ₀ =
        projectiveGrothendieckBaseChangeHom K' [Q]ₚ₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
    _ = [Q.scalarExtension K']₀ := by
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K') Q

/-- Helper for Theorem 16-16.1-2: the split-field consequences needed by the Brauer-reciprocity
readback are exactly the residue-side and generic-side self-Hom dimensions being one. -/
private theorem schurWeights_eq_one_of_hasEnoughRootsDVR_local
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι κ : Type*}
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK) :
    (∀ i, Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1) ∧
      (∀ j, Module.finrank K (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) = 1) := by
  constructor
  · intro i
    -- The residue-field split Schur theorem supplies the diagonal Schur weight for `π i`.
    letI : Simple (π i) := hπ_complete.isSimple i
    exact
      residueSimple_selfIntertwining_finrank_eq_one_of_hasEnoughRootsDVR_local
        (A := A) (K := K) (G := G) (π i)
  · intro j
    -- The generic-field split Schur theorem supplies the diagonal Schur weight for `πK j`.
    letI : Simple (πK j) := hπK_complete.isSimple j
    exact
      genericSimple_selfIntertwining_finrank_eq_one_of_hasEnoughRoots_local
        (K := K) (G := G) (πK j)

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Theorem 16-16.1-2: a representation whose action is the ambient group-algebra
generator action is equivalent to the canonical `ofModule'` representation. -/
private lemma nonempty_ofModulePrimeEquivOfActionEqComm_local
    {R : Type u} [CommRing R] {G : Type u} [Group G]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R G) M]
    [IsScalarTower R (MonoidAlgebra R G) M]
    (ρ : Representation R G M)
    (hρ : ∀ (g : G) (x : M), ρ g x = MonoidAlgebra.of R G g • x) :
    Nonempty ((show Representation R G M from Representation.ofModule' M).Equiv ρ) := by
  -- Conjugation by the identity linear equivalence is enough once the two actions agree on each
  -- group-algebra generator.
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl R M) fun g ↦ ?_⟩
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe]
  rw [hρ g x]
  simp [Representation.ofModule', MonoidAlgebra.of]

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Theorem 16-16.1-2: the exact lattice owner representation is the same as the
canonical representation attached to its `A[G]`-module structure. -/
private lemma stableLattice_toRepresentation_ofModule_equiv_local
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation A G L.toSubmodule from Representation.ofModule' L.toSubmodule).Equiv
        L.toRepresentation) := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  -- Reduce the comparison to the generator-action formula for the lattice representation.
  refine nonempty_ofModulePrimeEquivOfActionEqComm_local L.toRepresentation ?_
  intro g x
  rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
  rfl

omit [IsLocalRing A] [HenselianLocalRing A] [IsFractionRing A K] in
/-- Helper for Theorem 16-16.1-2: the finite-projective scalar-extension owner has the expected
underlying scalar-extended representation. -/
private lemma finiteProjective_scalarExtension_rep_equiv_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      ((show Representation K G (TensorProduct A K Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv
          (Q.scalarExtension K).ρ) := by
  -- This owner is an abbrev around `FDRep.of` of the same scalar-extended representation.
  exact ⟨Representation.Equiv.refl _⟩

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: scalar-extending the exact lattice owner recovers the ambient
generic representation. -/
private lemma stableLattice_scalarExtension_ofModule_equiv_local
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation K G (TensorProduct A K L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv X.ρ) := by
  rcases stableLattice_toRepresentation_ofModule_equiv_local
      (A := A) (K := K) (G := G) L with
    ⟨eA⟩
  let eScalar :
      (show Representation K G (TensorProduct A K L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
        (Representation.scalarExtension L.toRepresentation) :=
    Representation.scalarExtensionEquiv (A := A) (F := K) (G := G) eA
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) L with
    ⟨eFD⟩
  let eFDRep :
      (Representation.scalarExtension L.toRepresentation).Equiv X.ρ := by
    simpa using Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso eFD)
  -- Compose the scalar-extension functoriality bridge with the exact-owner lattice theorem.
  exact ⟨eScalar.trans eFDRep⟩

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: a chosen projective lift identifies the residue scalar
extension of its owner with the target residue projective representation. -/
private lemma projectiveLift_residue_scalarExtension_equiv_local
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ P)) :
    Nonempty
      ((show Representation k G (TensorProduct A k Q.V) from
        Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv P.toRep.ρ) := by
  rcases hQ with ⟨eQP⟩
  let ρred : Rep k G :=
    Rep.of (show Representation k G (TensorProduct A k Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V))
  have eSrcIso : ρred ≅ Q.residueFieldReduction.toRep := by
    simpa [ρred, FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρred)
  have hlin : Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] P.V) := by
    exact (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) Q.residueFieldReduction P).1 ⟨eQP⟩
  rcases hlin with ⟨elin⟩
  let eRedP : Q.residueFieldReduction.toRep ≅ P.toRep :=
    Rep.ofModuleMonoidAlgebra.mapIso elin.toModuleIso
  let eρ : (show Representation k G (TensorProduct A k Q.V) from
      Representation.scalarExtension (Representation.ofModule' Q.V)).Equiv P.toRep.ρ :=
    (Representation.equivOfIso eSrcIso).trans (Representation.equivOfIso eRedP)
  -- The residue reduction isomorphism supplies the source-side transport for the Hom fiber.
  exact ⟨eρ⟩

omit [HenselianLocalRing A] [IsFractionRing A K] [Finite G] in
/-- Helper for Theorem 16-16.1-2: the residue scalar extension of the exact lattice owner is the
reduction representation used in the stable-lattice multiplicity. -/
private lemma stableLattice_reduction_scalarExtension_equiv_local
    [IsDomain A] [IsDiscreteValuationRing A]
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Nonempty
      ((show Representation k G (TensorProduct A k L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
          (FDRep.of L.reductionRepresentation).ρ) := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  have hred :=
    StableLattice.reduction_mkQ_isResidueFieldReduction_local
      (A := A) (K := K) (G := G) L
  have hact : ∀ (g : G) (x : L.toSubmodule),
      L.toRepresentation g x = MonoidAlgebra.of A G g • x := by
    intro g x
    rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
    rfl
  let ρL : Representation A G L.toSubmodule := Representation.ofModule' L.toSubmodule
  let ρLk : Representation k G (TensorProduct A k L.toSubmodule) :=
    Representation.scalarExtension ρL
  let eσ : ρLk.Equiv L.reductionRepresentation :=
    Representation.Equiv.mk hred.1.equiv fun g ↦ by
      apply LinearMap.ext
      intro y
      -- Check equivariance on pure tensors and extend additively across the tensor product.
      induction y using TensorProduct.induction_on with
      | zero =>
          simp [ρLk]
      | tmul c x =>
          have hsource : ρLk g (c ⊗ₜ[A] x) = c ⊗ₜ[A] (ρL g x) := by
            change (LinearMap.baseChange k (ρL g)) (c ⊗ₜ[A] x) = c ⊗ₜ[A] (ρL g x)
            rw [LinearMap.baseChange_tmul]
          have hsrc_action : ρL g x = L.toRepresentation g x := by
            change MonoidAlgebra.of A G g • x = L.toRepresentation g x
            rw [← hact g x]
          calc
            hred.1.equiv (ρLk g (c ⊗ₜ[A] x))
                = hred.1.equiv (c ⊗ₜ[A] (ρL g x)) := by rw [hsource]
            _ = c • (Submodule.mkQ L.maximalIdealSubmodule :
                  L.toSubmodule →ₗ[A] L.reduction) (ρL g x) := by
                    exact IsBaseChange.equiv_tmul hred.1 c (ρL g x)
            _ = c • (Submodule.mkQ L.maximalIdealSubmodule :
                  L.toSubmodule →ₗ[A] L.reduction) (L.toRepresentation g x) := by
                    rw [hsrc_action]
            _ = c • L.reductionRepresentation g
                  ((Submodule.mkQ L.maximalIdealSubmodule :
                    L.toSubmodule →ₗ[A] L.reduction) x) := by
                    exact congrArg (fun z ↦ c • z)
                      (StableLattice.reductionRepresentation_apply_mk (L := L) g x).symm
            _ = L.reductionRepresentation g (c •
                  ((Submodule.mkQ L.maximalIdealSubmodule :
                    L.toSubmodule →ₗ[A] L.reduction) x)) := by
                    rw [LinearMap.map_smul]
            _ = L.reductionRepresentation g (hred.1.equiv (c ⊗ₜ[A] x)) := by
                    rw [IsBaseChange.equiv_tmul hred.1 c x]
      | add y z hy hz =>
          simpa only [map_add, LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hy hz
  have eσ' :
      (show Representation k G (TensorProduct A k L.toSubmodule) from
        Representation.scalarExtension (Representation.ofModule' L.toSubmodule)).Equiv
          (FDRep.of L.reductionRepresentation).ρ := by
    simpa [ρL, ρLk] using eσ
  -- The quotient map is a residue-field base change, so its base-change equivalence is the
  -- target-side Hom-fiber transport.
  exact ⟨eσ'⟩

omit [HenselianLocalRing A] in
/-- Helper for Theorem 16-16.1-2: the chosen projective lift and stable lattice identify the
generic and residue Hom dimensions appearing in Brauer reciprocity. -/
private theorem homFiber_projectiveLift_stableLattice_finrank_eq_local
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (_hQ : Nonempty (Q.residueFieldReduction ≅ P))
    {X : FDRep K G} (L : StableLattice A X.ρ) :
    Module.finrank K (Representation.IntertwiningMap (Q.scalarExtension K).ρ X.ρ) =
      Module.finrank k
        (Representation.IntertwiningMap P.toRep.ρ (FDRep.of L.reductionRepresentation).ρ) := by
  letI : Module.Projective A[G] Q.V := Q.projective
  letI : Module.Free A Q.V := Q.free
  letI : Module.Finite A Q.V := inferInstance
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module.Free A L.toSubmodule := inferInstance
  letI : Module.Finite A L.toSubmodule := inferInstance
  have hbase :
      Module.finrank K (scalarExtIntertwiner A G Q.V L.toSubmodule K) =
        Module.finrank k (scalarExtIntertwiner A G Q.V L.toSubmodule k) := by
    -- The common-owner Hom-fiber theorem computes both field fibers as the same `A`-rank.
    exact scalarExtIntertwiner_finrank_eq
      (A := A) (G := G) (Q := Q.V) (T := L.toSubmodule) (S₁ := K) (S₂ := k)
  rcases finiteProjective_scalarExtension_rep_equiv_local (A := A) (K := K) (G := G) Q with
    ⟨eQK⟩
  rcases stableLattice_scalarExtension_ofModule_equiv_local (A := A) (K := K) (G := G) L with
    ⟨eLK⟩
  have hK :
      Module.finrank K (scalarExtIntertwiner A G Q.V L.toSubmodule K) =
        Module.finrank K (Representation.IntertwiningMap (Q.scalarExtension K).ρ X.ρ) := by
    -- Transport the generic fiber from the raw scalar-extension owners to the projective module
    -- and stable-lattice owners used in the theorem statement.
    exact Representation.IntertwiningMap.finrank_eq_of_equiv eQK eLK
  rcases projectiveLift_residue_scalarExtension_equiv_local (A := A) (G := G) P Q _hQ with
    ⟨eQk⟩
  rcases stableLattice_reduction_scalarExtension_equiv_local (A := A) (K := K) (G := G) L with
    ⟨eLk⟩
  have hk :
      Module.finrank k (scalarExtIntertwiner A G Q.V L.toSubmodule k) =
        Module.finrank k
          (Representation.IntertwiningMap P.toRep.ρ (FDRep.of L.reductionRepresentation).ρ) := by
    -- Transport the residue fiber using the chosen projective lift and the residue-lattice
    -- base-change equivalence.
    exact Representation.IntertwiningMap.finrank_eq_of_equiv eQk eLk
  -- Route correction: first compare the two raw Hom fibers, then transport both sides to the
  -- theorem-facing owners; no Schur-weight arithmetic is hidden in this Hom-fiber step.
  exact hK.symm.trans (hbase.trans hk)

/-- Helper for Theorem 16-16.1-2: once the Hom-fiber dimensions agree and the simple owners have
Schur weight one, the scalar-extension coordinate is the fixed-simple multiplicity of the
stable-lattice reduction. -/
private theorem projectiveScalarExtension_coord_eq_multiplicity_of_homFinrank_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NeZero (Nat.card G : K)]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ_absIrr :
      ∀ i, Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1)
    (πK : κ → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (hπK_absIrr :
      ∀ j, Module.finrank K (Representation.IntertwiningMap (πK j).ρ (πK j).ρ) = 1)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (i : ι) (j : κ) (L : StableLattice A (πK j).ρ)
    (hHom :
      Module.finrank K (Representation.IntertwiningMap (Q.scalarExtension K).ρ (πK j).ρ) =
        Module.finrank k
          (Representation.IntertwiningMap (P i).toRep.ρ
            (FDRep.of L.reductionRepresentation).ρ)) :
    (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
        [Q.scalarExtension K]₀ j =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        [FDRep.of L.reductionRepresentation]₀ := by
  -- Read the generic simple-basis coordinate as a K-side Hom dimension.
  have hcoord :
      (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
          [Q.scalarExtension K]₀ j =
        (Module.finrank K
          (Representation.IntertwiningMap (Q.scalarExtension K).ρ (πK j).ρ) : ℤ) := by
    exact
      simpleK_basis_coord_eq_hom_finrank_commonOwner
        (K := K) (G := G) πK hπK_pairwise hπK_complete hπK_absIrr
        (Q.scalarExtension K) j
  have hHomInt :
      (Module.finrank K
          (Representation.IntertwiningMap (Q.scalarExtension K).ρ (πK j).ρ) : ℤ) =
        (Module.finrank k
          (Representation.IntertwiningMap (P i).toRep.ρ
            (FDRep.of L.reductionRepresentation).ρ) : ℤ) := by
    exact_mod_cast hHom
  have hProjectiveHom :
      (Module.finrank k
          (Representation.IntertwiningMap (P i).toRep.ρ
            (FDRep.of L.reductionRepresentation).ρ) : ℤ) =
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
          [FDRep.of L.reductionRepresentation]₀ := by
    exact
      projectiveEnvelope_hom_finrank_eq_multiplicity_of_absIrr_commonOwner
        (A := A) (G := G) π hπ_pairwise hπ_complete hπ_absIrr
        P hP_envelope i (FDRep.of L.reductionRepresentation)
  -- Compose the coordinate readback, Hom-fiber equality, and projective-envelope readback.
  exact hcoord.trans (hHomInt.trans hProjectiveHom)

/-- Helper for Theorem 16-16.1-2: the left scalar-extension matrix entry is the multiplicity of
the fixed residue simple in the reduction of a chosen stable lattice for the target generic simple.
-/
private theorem projectiveScalarExtension_coord_eq_stableLatticeMultiplicity_local
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (j : κ) (L : StableLattice A (πK j).ρ) (i : ι) :
    (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
        ((projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) i)) j =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        [FDRep.of L.reductionRepresentation]₀ := by
  classical
  obtain ⟨Q, hQ⟩ := exists_projective_lift_of_residueField_projective (A := A) (G := G) (P i)
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bK : Module.Basis κ ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  have hliftClass :
      projectiveGrothendieckScalarExtensionHom A K [P i]ₚ₀ = [Q.scalarExtension K]₀ :=
    projectiveScalarExtension_liftClass_eq_local
      (A := A) (G := G) (K' := K) (F := P i) Q hQ
  have hcoord :
      bK.repr [Q.scalarExtension K]₀ j =
        simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
          [FDRep.of L.reductionRepresentation]₀ := by
    haveI : NeZero (Nat.card G : K) :=
      nat_card_neZero_of_hasEnoughRoots_local (K := K) (G := G)
    have hweights :=
      schurWeights_eq_one_of_hasEnoughRootsDVR_local
        (A := A) (K := K) (G := G) π hπ_complete πK hπK_complete
    have hHom :
        Module.finrank K
            (Representation.IntertwiningMap (Q.scalarExtension K).ρ (πK j).ρ) =
          Module.finrank k
            (Representation.IntertwiningMap (P i).toRep.ρ
              (FDRep.of L.reductionRepresentation).ρ) :=
      homFiber_projectiveLift_stableLattice_finrank_eq_local
        (A := A) (K := K) (G := G) (P i) Q hQ L
    -- The remaining formal readback is now independent of the DVR source theorem: the two
    -- source-facing placeholders provide exactly the Hom-fiber equality and the Schur weights.
    exact
      projectiveScalarExtension_coord_eq_multiplicity_of_homFinrank_local
        (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete hweights.1
        πK hπK_pairwise hπK_complete hweights.2 P hP_envelope Q i j L hHom
  -- The projective lift reduces the original coordinate goal to the single Hom-fiber comparison.
  simpa [bP, bK, projectiveEnvelope_classes_basis_of_complete_family_apply,
    AddMonoidHom.coe_toIntLinearMap, hliftClass] using hcoord

/-- Helper for Theorem 16-16.1-2: Brauer reciprocity identifies each scalar-extension matrix
entry on projective-envelope classes with the transposed decomposition-map entry. -/
private theorem projectiveScalarExtension_decomposition_transpose_entries_local
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (j : κ) (i : ι) :
    (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
        ((projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) i)) j =
      (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
        ((decompositionHom A K G).toIntLinearMap
          ((simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete) j)) i := by
  classical
  let L : ∀ j, StableLattice A (πK j).ρ :=
    fun j ↦ Classical.choice (Representation.exists_stableLattice (A := A) (ρ := (πK j).ρ))
  -- Normalize the scalar-extension entry to the same fixed-simple multiplicity that already
  -- computes the decomposition-map coordinate through the chosen stable lattice.
  calc
    (simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete).repr
        ((projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap
          ((projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope) i)) j =
      simple_factor_multiplicity_hom_fixed_local (A := A) (G := G) (π i)
        [FDRep.of (L j).reductionRepresentation]₀ := by
          exact
            projectiveScalarExtension_coord_eq_stableLatticeMultiplicity_local
              (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
              πK hπK_pairwise hπK_complete P hP_envelope j (L j) i
    _ =
      (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr
        ((decompositionHom A K G).toIntLinearMap
          ((simple_finiteRep_classes_basis_of_complete_family
            πK hπK_pairwise hπK_complete) j)) i := by
          exact
            (decomposition_coord_eq_stableLatticeMultiplicity_local
              (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
              πK hπK_pairwise hπK_complete L i j).symm

/-- Helper for Theorem 16-16.1-2: with the projective-envelope basis attached to a complete
residue simple family, the Cartan matrix is the Gram matrix of the decomposition matrix. -/
theorem cartanMatrix_eq_decomposition_toMatrix_transpose_mul_decomposition_toMatrix
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (πK : κ → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    let bP :=
      projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
    cartanMatrix k G bP bk =
      LinearMap.toMatrix bK bk (decompositionHom A K G).toIntLinearMap *
        (LinearMap.toMatrix bK bk (decompositionHom A K G).toIntLinearMap).transpose := by
  classical
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bK : Module.Basis κ ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  let eL : P₀[k](G) →ₗ[ℤ] R₀[K](G) :=
    (projectiveGrothendieckScalarExtensionHom (G := G) A K).toIntLinearMap
  let dL : R₀[K](G) →ₗ[ℤ] R₀[k](G) :=
    (decompositionHom A K G).toIntLinearMap
  have hentry :
      ∀ (j : κ) (i : ι), bK.repr (eL (bP i)) j = bk.repr (dL (bK j)) i := by
    intro j i
    simpa [bP, bk, bK, eL, dL] using
      projectiveScalarExtension_decomposition_transpose_entries_local
        (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
        πK hπK_pairwise hπK_complete P hP_envelope j i
  have heMatrix :
      LinearMap.toMatrix bP bK eL =
        (LinearMap.toMatrix bK bk dL).transpose :=
    projective_scalar_extension_toMatrix_eq_decomposition_transpose_henselian_local
      bP bk bK eL dL hentry
  have htriangle :
      dL.comp eL = (cartanHom k G).toIntLinearMap := by
    ext x
    simpa [dL, eL] using
      decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
        (A := A) (K := K) (G := G) x
  calc
    cartanMatrix k G bP bk =
        LinearMap.toMatrix bP bk (dL.comp eL) := by
          rw [htriangle]
          ext i j
          simp [cartanMatrix, LinearMap.toMatrix_apply]
    _ = LinearMap.toMatrix bK bk dL * LinearMap.toMatrix bP bK eL := by
          rw [LinearMap.toMatrix_comp bP bK bk dL eL]
    _ = LinearMap.toMatrix bK bk dL * (LinearMap.toMatrix bK bk dL).transpose := by
          rw [heMatrix]

/-- Theorem 16-16.1-2: the scalar-extension homomorphism
`projectiveGrothendieckScalarExtensionHom A K : P_k(G) → R_K(G)` is a split injection.

Faithful framing: Serre's `(A, K, k)` is a complete discrete valuation modular system with `K`
sufficiently large.  The proof route is Serre's: Brauer reciprocity identifies `e` with the
transpose of the decomposition map, and surjectivity of the decomposition map makes that transpose
a split injection. -/
theorem projectiveGrothendieckScalarExtensionHom_split_injective
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ s : finiteRepGrothendieckGroup K G →+
        finiteProjectiveGroupAlgebraGrothendieckGroup (IsLocalRing.ResidueField A) G,
      Function.LeftInverse s (projectiveGrothendieckScalarExtensionHom A K) := by
  -- With the DVR modular-system structure available, the proof route is: surjectivity of
  -- `decompositionHom A K G` (th. 33) gives a right inverse of `d`; Brauer reciprocity identifies
  -- the scalar-extension matrix `e` with the transpose `ᵗd`; then the transpose-section endgame
  -- (`decomposition_rightInverse_of_surjective_local` /
  -- `left_inverse_of_transpose_section_henselian_local`) produces the split left inverse `s`.
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyFieldLocal (F := k) (G := G)
  letI : Finite ι :=
    finite_index_of_complete_pairwise_nonisomorphic_simple_family_local
      π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨κ, πK, hπK_pairwise, hπK_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyFieldLocal (F := K) (G := G)
  letI : Finite κ :=
    finite_index_of_complete_pairwise_nonisomorphic_simple_family_local
      πK hπK_pairwise hπK_complete
  letI : Fintype κ := Fintype.ofFinite κ
  letI : DecidableEq κ := Classical.decEq κ
  have hP_exists :
      ∀ i, ∃ P : FiniteProjectiveGroupAlgebraModule k G,
        ∃ f : (P).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope := by
    intro i
    -- Each residue simple in the chosen complete family has a finite projective envelope.
    letI : Simple (π i) := hπ_complete.isSimple i
    exact exists_finite_projective_envelope_of_simple_local (A := A) (G := G) (S := π i)
  choose P hP_envelope using hP_exists
  let bk : Module.Basis ι ℤ (R₀[k](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bP : Module.Basis ι ℤ (P₀[k](G)) :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
  let bK : Module.Basis κ ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family πK hπK_pairwise hπK_complete
  have hd_surj : Function.Surjective (decompositionHom A K G) := by
    -- Serre's Theorem 33 supplies the decomposition-map section used by the linear-algebra
    -- transpose argument.
    exact
      decompositionHom_surjective_of_hasEnoughRoots_sameField_local
        (A := A) (K := K) (G := G)
  obtain ⟨r, hrightInv⟩ :=
    decomposition_rightInverse_of_surjective_local (A := A) (K := K) (G := G) hd_surj
  have hentry :
      ∀ (j : κ) (i : ι),
        bK.repr
            ((projectiveGrothendieckScalarExtensionHom A K).toIntLinearMap (bP i)) j =
          bk.repr ((decompositionHom A K G).toIntLinearMap (bK j)) i := by
    intro j i
    -- The matrix entries are precisely the Brauer-reciprocity comparison for the chosen bases.
    simpa [bP, bk, bK] using
      projectiveScalarExtension_decomposition_transpose_entries_local
        (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
        πK hπK_pairwise hπK_complete P hP_envelope j i
  -- Apply the formal transpose-section lemma to the chosen bases and right inverse of `d`.
  exact
    split_injective_of_decomposition_section_and_entries_local
      (A := A) (K := K) (G := G) bP bk bK r hrightInv hentry

end

end Representation
