import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {G : Type u} [Group G] [Finite G]

omit [IsLocalRing R] [Finite G] in
/-- Helper for Corollary 16-16.1-8: the sum of two actual projective classes is again represented
by an actual finite projective module. -/
private theorem exists_projective_class_sum_rep_local
    (P Q : FiniteProjectiveGroupAlgebraModule R G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule R G, [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  let W0 : ModuleCat (MonoidAlgebra R G) := ModuleCat.of (MonoidAlgebra R G) (P.V × Q.V)
  have hfinite : Module.Finite (MonoidAlgebra R G) W0 := by
    -- Finite generation is preserved by the binary product module.
    change Module.Finite (MonoidAlgebra R G) (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat (MonoidAlgebra R G) := ⟨W0, hfinite⟩
  have hproj : Module.Projective (MonoidAlgebra R G) Wfg := by
    -- Projectivity is inherited by binary products.
    change Module.Projective (MonoidAlgebra R G) (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule R G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk
      (ConcreteCategory.ofHom (LinearMap.inl (MonoidAlgebra R G) P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk
      (ConcreteCategory.ofHom (LinearMap.snd (MonoidAlgebra R G) P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk
      (ConcreteCategory.ofHom (LinearMap.fst (MonoidAlgebra R G) P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk
      (ConcreteCategory.ofHom (LinearMap.inr (MonoidAlgebra R G) P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule R G) :=
    ShortComplex.mk f g (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.snd (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inl (MonoidAlgebra R G) P.V Q.V) x) =
          0
      simp)
  have hsplit : T.Splitting := by
    -- The standard inclusions and projections split the product short complex.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.fst (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inl (MonoidAlgebra R G) P.V Q.V) x) =
          x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.snd (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inr (MonoidAlgebra R G) P.V Q.V) x) =
          x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl (MonoidAlgebra R G) P.V Q.V
              ((LinearMap.fst (MonoidAlgebra R G) P.V Q.V) (x, y)) +
            LinearMap.inr (MonoidAlgebra R G) P.V Q.V
              ((LinearMap.snd (MonoidAlgebra R G) P.V Q.V) (x, y))) =
          (x, y)
      simp
  refine ⟨W, ?_⟩
  -- Translate the split short exact sequence into the Grothendieck relation.
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := R) (G := G) T hsplit.shortExact

omit [IsLocalRing R] [Finite G] in
/-- Helper for Corollary 16-16.1-8: every class in `P₀[R](G)` is a difference of two actual
finite projective classes. This is the Grothendieck-level difference presentation needed before
the source-faithful `d ∘ e = c` triangle can be proved on arbitrary projective classes. -/
theorem exists_projective_class_difference_rep_local
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup R G) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule R G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is represented by the zero projective module minus itself.
    refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule R G),
        (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    simp
  · intro P
    -- A generator class is already a difference with zero.
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := R) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    -- Negation swaps the two witnesses in the formal difference.
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, hW⟩ := exists_projective_class_sum_rep_local (R := R) (G := G) P P'
    obtain ⟨Z, hZ⟩ := exists_projective_class_sum_rep_local (R := R) (G := G) Q Q'
    refine ⟨W, Z, ?_⟩
    -- Add the two difference presentations and compress the positive parts again.
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) (a + b)
          =
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) a +
              QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) b := by
              rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

/-- Helper for Corollary 16-16.1-8: on an actual lifted projective generator, LinearRepresentations_Serre_1977's
`d ∘ e = c` triangle should identify the decomposition class with the Cartan class of the reduced
projective module. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (V : FDRep K G)
    (hV : [V]₀ = [Q.scalarExtension K]₀)
    (L : StableLattice A V.ρ)
    (hL : [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- First rewrite the scalar-extension class through the chosen characteristic-zero model `V`.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ = decompositionHom A K G [V]₀ := by
      rw [hV]
    -- Then evaluate the decomposition map using the supplied stable lattice `L`.
    _ = [FDRep.of L.reductionRepresentation]₀ :=
      decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L
    -- The remaining input is precisely the promised comparison with the reduced projective class.
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := hL
    -- Finally translate the reduced projective class back through the Cartan generator formula.
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
      symm
      exact (cartanHom_projectiveClass_eq k G Q.residueFieldReduction)

/-- Helper for Corollary 16-16.1-8: the literal scalar-extension map sends `x` to the pure tensor
`1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Corollary 16-16.1-8: on an actual lifted projective generator, LinearRepresentations_Serre_1977's
`d ∘ e = c` triangle identifies the decomposition class of the scalar extension with the
Cartan class of the reduced projective module.

This is the exact root bridge needed from the source text: a projective `A[G]`-module `Q`
contributes `K ⊗_A Q` to `R_K(G)`, and reducing the same lattice gives the projective
`k[G]`-module `k ⊗_A Q`.  The previous local attempt expanded this into a literal image
lattice; that made Lean infer the wrong owner module for the lattice submodule.  Keep the
source-faithful bridge as the proof target and avoid encoding a false owner choice. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- Source route, LinearRepresentations_Serre_1977 16.1: this is the projective-generator case of the c-d-e triangle.
  -- The stable lattice is `Q` itself inside its scalar extension, and its reduction is
  -- `Q.residueFieldReduction`.
  exact
    decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Corollary 16-16.1-8: once the honest-projective generator case is known, LinearRepresentations_Serre_1977's
`d ∘ e = c` triangle follows on all of `P₀[k](G)` by transporting to `P₀[A](G)` and expanding the
pulled-back class as a difference of actual projective generators. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local
    [HenselianLocalRing A]
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup k G) :
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom A K) x) =
      cartanHom k G x := by
  exact
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
      (A := A) (K := K) (G := G) x

end

end Representation
