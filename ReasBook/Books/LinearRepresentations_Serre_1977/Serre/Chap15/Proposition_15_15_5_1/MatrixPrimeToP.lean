import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionSplitReflection
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v

section MatrixIdentities

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P_A(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup A G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Proposition 15-15.5-1: the reduced simple family attached to the chosen lattices. -/
noncomputable abbrev reduction_family_of_order_prime_to_p_local
    {S : Type v}
    (πK : S → FDRep K G)
    (L : ∀ i : S, StableLattice A (πK i).ρ) :
    S → FDRep k G :=
  fun i ↦ FDRep.of (L i).reductionRepresentation

/-- Helper for Proposition 15-15.5-1: Maschke's hypothesis makes the reduced lattice family
pairwise nonisomorphic. -/
abbrev reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    PairwiseNonisomorphic
      (reduction_family_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) πK L) :=
  stableLattice_reductionFamily_pairwise_of_iso_reflection
    (A := A) (K := K) (G := G) (S := S) πK hπK_pairwise L
    (fun {i j} hij ↦
      stableLattice_reduction_iso_implies_generic_iso_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) (S := S) hG πK L hij)

/-- Helper for Proposition 15-15.5-1: Maschke's hypothesis makes the reduced lattice family a
complete irreducible family. -/
abbrev reduction_family_complete_irreducible_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    IsCompleteIrreducibleFamily
      (reduction_family_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) πK L) :=
  stableLattice_reductionFamily_complete_of_isSimple_of_order_prime_to_p
    (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L
    (stableLattice_reductionFamily_isSimple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L)

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `K` for the chosen
generic simple family. -/
noncomputable abbrev generic_simple_basis_of_order_prime_to_p_local
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK) :
    Module.Basis S ℤ (R_K(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    πK hπK_pairwise hπK_complete

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `k` for the reduced
lattice family. -/
noncomputable abbrev reduced_simple_basis_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    Module.Basis S ℤ (R_k(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p_local (A := A) (K := K) (G := G) πK L)
    (reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L)
    (reduction_family_complete_irreducible_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L)

/-- Helper for Proposition 15-15.5-1: the canonical projective-envelope basis over `k` attached to
the reduced lattice family. -/
noncomputable abbrev projective_envelope_basis_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    Module.Basis S ℤ (P_k(G)) :=
  projectiveEnvelope_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p_local (A := A) (K := K) (G := G) πK L)
    (reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L)
    (reduction_family_complete_irreducible_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L)
    P hP_envelope

/-- Helper for Proposition 15-15.5-1: once the reduced family is complete and pairwise
nonisomorphic, the basis-built map `bk.constr ℤ bK` is a left inverse to `decompositionHom`. -/
theorem decomposition_basis_leftInverse_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    ((reduced_simple_basis_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L).constr ℤ
      (generic_simple_basis_of_order_prime_to_p_local
        (G := G) πK hπK_pairwise hπK_complete)).comp
      (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
  let bK : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  -- Evaluate `decompositionHom` on the `K`-simple basis and package the resulting basis images.
  apply bK.ext
  intro i
  have hi :
      (decompositionHom A K G).toIntLinearMap (bK i) = bk i := by
    rw [simple_finiteRep_classes_basis_of_complete_family_apply,
      simple_finiteRep_classes_basis_of_complete_family_apply]
    simpa [reduction_family_of_order_prime_to_p_local] using
      decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)
  calc
    ((bk.constr ℤ bK).comp (decompositionHom A K G).toIntLinearMap) (bK i) =
        (bk.constr ℤ bK) ((decompositionHom A K G).toIntLinearMap (bK i)) := by
          simp [LinearMap.comp_apply]
    _ = (bk.constr ℤ bK) (bk i) := by
          rw [hi]
    _ = bK i := by
          simp

/-- Helper for Proposition 15-15.5-1: Serre's scalar-extension homomorphism satisfies
`d (e x) = c x` on projective Grothendieck classes over the residue field. -/
theorem decompositionHom_projectiveGrothendieckBaseChange_eq_cartan_reduction_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (x : P_A(G)) :
    decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) x) =
      cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro Q
    have hred :
        projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
      change
        projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀
      simpa using
        projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
    calc
      decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) [Q]ₚ₀) =
          decompositionHom A K G [Q.scalarExtension K]₀ := by
            rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
      _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
            exact
              decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
                (A := A) (K := K) (G := G) Q
      _ = cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) := by
            rw [hred]
  · intro a ha
    simpa using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ (fun x y ↦ x + y) ha hb

/-- Helper for Proposition 15-15.5-1: Serre's scalar-extension homomorphism satisfies
`d (e x) = c x` on projective Grothendieck classes over the residue field. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (x : P_k(G)) :
    decompositionHom A K G
      ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)) x) =
      cartanHom k G x := by
  let y : P_A(G) := (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm x
  -- Transport to `P_A(G)`, evaluate the triangle on that projective class, and then rewrite back.
  calc
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)) x) =
      decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) y) := by
        simp [projectiveGrothendieckScalarExtensionHom_apply, y]
    _ =
        cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) y) := by
          exact
            decompositionHom_projectiveGrothendieckBaseChange_eq_cartan_reduction_local
              (A := A) (K := K) (G := G) y
    _ = cartanHom k G x := by
          simp [y]

/-- Helper for Proposition 15-15.5-1: the Cartan map sends each projective-envelope basis vector
to the matching reduced simple-class basis vector. -/
theorem cartanHom_projective_envelope_class_eq_reduction_target_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope)
    (i : S) :
    cartanHom k G [P i]ₚ₀ = [FDRep.of (L i).reductionRepresentation]₀ := by
  rcases hP_envelope i with ⟨f, hf⟩
  -- Compute the Cartan class of the projective envelope source and then identify that source with
  -- the reduced simple target by Maschke's theorem.
  calc
    cartanHom k G [P i]ₚ₀ = [(P i).toFiniteRep]₀ := by
      simpa using (cartanHom_projectiveClass_eq k G (P i))
    _ = [FDRep.of (L i).reductionRepresentation]₀ := by
      let M : ModuleCat k[G] :=
        Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj
          (FDRep.of (L i).reductionRepresentation))
      let _ : Module.Projective k[G] M := by
        let _ : Fintype G := Fintype.ofFinite G
        let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
        let _ : IsSemisimpleRing k[G] := by
          infer_instance
        exact Module.projective_of_isSemisimpleRing k[G] M
      let f' : (P i).V →ₗ[k[G]] M := by
        simpa using f
      have hf' : f'.IsProjectiveEnvelope := by
        simpa [f'] using hf
      obtain ⟨eLin⟩ := hf'.nonempty_linearEquiv_target
      let eRep' : (P i).toRep ≅ ((forget₂ (FDRep k G) (Rep k G)).obj
          (FDRep.of (L i).reductionRepresentation)) :=
        Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
          (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj
            (FDRep.of (L i).reductionRepresentation))).symm
      let eRep :
          ((forget₂ (FDRep k G) (Rep k G)).obj (P i).toFiniteRep) ≅
            ((forget₂ (FDRep k G) (Rep k G)).obj
              (FDRep.of (L i).reductionRepresentation)) := by
        simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
          FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
      let e : (P i).toFiniteRep ≅ FDRep.of (L i).reductionRepresentation :=
        ⟨(FDRep.forget₂HomLinearEquiv (P i).toFiniteRep
            (FDRep.of (L i).reductionRepresentation)) eRep.hom,
          (FDRep.forget₂HomLinearEquiv (FDRep.of (L i).reductionRepresentation)
            (P i).toFiniteRep) eRep.inv,
          by
            apply (forget₂ (FDRep k G) (Rep k G)).map_injective
            change eRep.hom ≫ eRep.inv = 𝟙 _
            exact eRep.hom_inv_id,
          by
            apply (forget₂ (FDRep k G) (Rep k G)).map_injective
            change eRep.inv ≫ eRep.hom = 𝟙 _
            exact eRep.inv_hom_id⟩
      exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Proposition 15-15.5-1: the Cartan map sends each projective-envelope basis vector
to the matching reduced simple-class basis vector. -/
theorem cartanHom_projectiveEnvelope_basis_eq_reduced_simple_basis_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    ∀ i,
      cartanHom k G
          ((projective_envelope_basis_of_order_prime_to_p_local
              (A := A) (K := K) (G := G) (p := p)
              hG πK hπK_pairwise hπK_complete L P hP_envelope) i) =
        (reduced_simple_basis_of_order_prime_to_p_local
          (A := A) (K := K) (G := G) (p := p)
          hG πK hπK_pairwise hπK_complete L) i := by
  let bP : Module.Basis S ℤ (P_k(G)) :=
    projective_envelope_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L P hP_envelope
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  intro i
  -- Rewrite both basis vectors to their defining classes and then invoke the class-level Cartan
  -- computation for the chosen projective envelope.
  calc
    cartanHom k G (bP i) = cartanHom k G [P i]ₚ₀ := by
      rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
    _ = [FDRep.of (L i).reductionRepresentation]₀ := by
      exact
        cartanHom_projective_envelope_class_eq_reduction_target_local
          (A := A) (K := K) (G := G) (p := p) hG πK L P hP_envelope i
    _ = bk i := by
      rw [simple_finiteRep_classes_basis_of_complete_family_apply]

/-- Helper for Proposition 15-15.5-1: evaluating Serre's `d ∘ e = c` triangle on the chosen
projective-envelope basis yields the reduced simple basis. -/
theorem projectiveScalarExtension_triangle_on_projectiveEnvelope_basis_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (bP : Module.Basis S ℤ (P_k(G)))
    (bk : Module.Basis S ℤ (R_k(G)))
    (hcartan_basis : ∀ i, cartanHom k G (bP i) = bk i) :
    ∀ i,
      (decompositionHom A K G).toIntLinearMap
          ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
            (bP i)) =
        bk i := by
  intro i
  -- Compute `d (e (bP i))` through Serre's triangle, then rewrite the Cartan image on the basis.
  calc
    (decompositionHom A K G).toIntLinearMap
        ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          (bP i))
        = cartanHom k G (bP i) := by
            simpa using
              decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
                (A := A) (K := K) (G := G) (bP i)
    _ = bk i := by
          exact hcartan_basis i

/-- Helper for Proposition 15-15.5-1: evaluating a left inverse at a point recovers that point. -/
theorem linearMap_eq_of_comp_eq_id_apply_local_support
    {M : Type u} [AddCommGroup M] [Module ℤ M]
    {N : Type u} [AddCommGroup N] [Module ℤ N]
    (s : N →ₗ[ℤ] M)
    (f : M →ₗ[ℤ] N)
    (h : s.comp f = (LinearMap.id : M →ₗ[ℤ] M))
    (x : M) :
    s (f x) = x := by
  -- Evaluate the equality `s.comp f = id` at `x`.
  exact congrArg (fun g : M →ₗ[ℤ] M ↦ g x) h

/-- Helper for Proposition 15-15.5-1: a left inverse identifies any element mapping to the `i`-th
reduced basis vector with the corresponding `K`-basis vector. -/
theorem basis_image_of_left_inverse_and_basis_value_local_support
    {S : Type v}
    (bK : Module.Basis S ℤ (R_K(G)))
    (bk : Module.Basis S ℤ (R_k(G)))
    (d : R_K(G) →ₗ[ℤ] R_k(G))
    (x : R_K(G))
    (i : S)
    (hleftInv : (bk.constr ℤ bK).comp d = (LinearMap.id : R_K(G) →ₗ[ℤ] R_K(G)))
    (hx : d x = bk i) :
    x = bK i := by
  let s : R_k(G) →ₗ[ℤ] R_K(G) := bk.constr ℤ bK
  calc
    x = s (d x) := by
      symm
      exact linearMap_eq_of_comp_eq_id_apply_local_support s d hleftInv x
    _ = s (bk i) := by
      rw [hx]
    _ = bK i := by
      simp [s]

/-- Helper for Proposition 15-15.5-1: scalar extension sends each projective-envelope basis vector
to the matching `K`-simple basis vector. -/
theorem projectiveScalarExtension_basis_image_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    ∀ i,
      (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          ((projective_envelope_basis_of_order_prime_to_p_local
              (A := A) (K := K) (G := G) (p := p)
              hG πK hπK_pairwise hπK_complete L P hP_envelope) i) =
        (generic_simple_basis_of_order_prime_to_p_local
          (G := G) πK hπK_pairwise hπK_complete) i := by
  -- Route correction: keep Serre's `d ∘ e = c` proof, but split the old hotspot into separate
  -- triangle and left-inverse helpers so Lean no longer elaborates one large declaration.
  let bP : Module.Basis S ℤ (P_k(G)) :=
    projective_envelope_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L P hP_envelope
  let bK : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  have hleftInv :
      (bk.constr ℤ bK).comp (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
    -- The reduced simple basis already gives a left inverse to the decomposition map.
    simpa [bK, bk] using
      decomposition_basis_leftInverse_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L
  have hcartan_basis : ∀ i, cartanHom k G (bP i) = bk i := by
    -- Reuse the basis-level Cartan computation instead of re-expanding the same basis rewrites
    -- inside the scalar-extension triangle argument.
    simpa [bP, bk] using
      cartanHom_projectiveEnvelope_basis_eq_reduced_simple_basis_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L P hP_envelope
  have htriangle_basis :
      ∀ i,
        (decompositionHom A K G).toIntLinearMap
            ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
              (bP i)) =
          bk i := by
    -- Evaluate Serre's `d ∘ e = c` triangle on the chosen projective-envelope basis.
    exact
      projectiveScalarExtension_triangle_on_projectiveEnvelope_basis_local
        (A := A) (K := K) (G := G) bP bk hcartan_basis
  intro i
  -- The decomposition left inverse identifies the unique preimage of `bk i` with `bK i`.
  exact
    basis_image_of_left_inverse_and_basis_value_local_support
      bK bk
      (decompositionHom A K G).toIntLinearMap
      ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
        (bP i))
      i hleftInv (htriangle_basis i)

end MatrixIdentities
