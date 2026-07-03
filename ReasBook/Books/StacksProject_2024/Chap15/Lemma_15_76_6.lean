import Mathlib
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open IsLocalRing
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "κ" => ResidueField R
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "FiniteFreeClass" => (fun M : ModuleCat R ↦ Module.Free R M ∧ Module.Finite R M)
local notation "BoundedFiniteFreeCpx" => CochainComplex.MinusWithTermsIn FiniteFreeClass

/- Domain-style sampling for Lemma 15.76.6:
- primary domain: pseudo-coherent derived complexes over a local ring and bounded-above finite-free
  representatives controlled by residue-field homology;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`,
  `exists_boundedAbove_termwiseFiniteFree_quasiIso`;
- best owner abstraction: the bounded-above finite-free model should be carried by the existing
  owner `CochainComplex.MinusWithTermsIn FiniteFreeClass`, while the source-facing residue-field
  homology and prescribed rank function remain bridge data on top of that owner;
- primitive vs. derived:
  primitive data are the derived residue-field homology objects and the rank function `d : ℤ → ℕ`;
  derived API is the existence and uniqueness of owner-level bounded-above finite-free models with
  those prescribed ranks;
- source/core/bridge triage:
  `source-facing`: the three clauses of Lemma `15.76.6`;
  `core/canonical`: `K.IsPseudoCoherent`, `CochainComplex.MinusWithTermsIn`, and
    `CochainComplex.IsTermwiseFiniteFree`;
  `bridge/view`: `residueFieldDerivedHomology` and the pointwise rank condition on the owner
    complex terms.
-/

/-- The degree-`i` homology of the derived residue-field base change `K ⊗_R^L κ`. -/
abbrev residueFieldDerivedHomology (K : DModR) (i : ℤ) : ModuleCat κ :=
  (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj (K ⊗[R]^L[κ])

-- Proof sketch: apply pseudo-coherence preservation under derived tensoring with the residue field,
-- then use the standard characterization of pseudo-coherent derived complexes over the field `κ`,
-- where every pseudo-coherent object is represented by a bounded-above complex of finite free
-- `κ`-modules. Such a complex has finite-dimensional homology in each degree and vanishes in all
-- sufficiently large degrees.
/-- Lemma 15.76.6 (1): if `K` is pseudo-coherent over the local ring `R`, then the cohomology of
`K ⊗_R^L κ` is finite-dimensional over the residue field `κ` in every degree and vanishes in
sufficiently large degrees. -/
theorem residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
    (K : DModR) (hK : K.IsPseudoCoherent) :
    (∀ i : ℤ, FiniteDimensional κ (residueFieldDerivedHomology K i)) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (residueFieldDerivedHomology K i) := sorry

-- Proof sketch: combine part `(1)` with `hd` to deduce that `d i = 0` for all sufficiently large
-- `i`, then choose the zero-differential complex over `κ` with term `κ^{d i}` in degree `i` and
-- identify it with the derived residue-field base change of `K`. Apply the lifting statement of
-- Lemma `15.76.5` at the maximal ideal of the local ring to obtain a bounded-above free
-- `R`-complex representing `K` with the prescribed ranks.
/-- Lemma 15.76.6 (2): if `d i` is the dimension of the degree-`i` residue-field cohomology of
`K`, then `K` is represented by a bounded-above cochain complex whose degree-`i` term is free of
rank `d i`. -/
theorem exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
    (K : DModR) (hK : K.IsPseudoCoherent) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ))) :
    ∃ P : BoundedFiniteFreeCpx,
      (∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R))) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)) := sorry

-- Proof sketch: let `β : P ⟶ Q` be a morphism in the derived category representing the identity of
-- `K`. After tensoring with `κ`, the complexes `P ⊗_R κ` and `Q ⊗_R κ` have zero differentials
-- because their terms already realize the residue-field homology dimensions `d i`. Hence `β ⊗ 1`
-- is degreewise an isomorphism, so each component `β^i` is an isomorphism by Nakayama's lemma for
-- finite free modules over the local ring `R`.
/-- Lemma 15.76.6 (3): a bounded-above free representative of `K` whose degree-`i` term has rank
equal to the dimension of `H^i(K ⊗_R^L κ)` is unique up to isomorphism of complexes. -/
theorem boundedAbove_termwiseFree_representative_unique_of_residueFieldDerivedHomology
    (K : DModR) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((residueFieldDerivedHomology K i) ≃ₗ[κ] (Fin (d i) → κ)))
    {P P' : BoundedFiniteFreeCpx}
    (hP : ∀ i : ℤ, Nonempty (((P : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hPK : Nonempty (K ≅ DerivedCategory.Q.obj (P : CpxR)))
    (hP' : ∀ i : ℤ, Nonempty (((P' : CpxR).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hP'K : Nonempty (K ≅ DerivedCategory.Q.obj (P' : CpxR))) :
    Nonempty ((P : CpxR) ≅ (P' : CpxR)) := sorry

end

end CategoryTheory
