import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SmithDiagonal
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance instFintypeGExercise181832 : Fintype G := Fintype.ofFinite G

/-- Exercise 18-18.3-2 (1): an element of the canonical Chapter `12` owner `A ⊗R[K](G)` belongs
to the projective-character span
`projectiveCharacterSubmodule` if and only if it vanishes on the `p`-singular elements and each
value at a `p`-regular element is divisible in `A` by the order of a `p`-Sylow subgroup of the
centralizer of that element, in the standard Chapter `18` ordinary-character regime
`[CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]`. Here
`k = IsLocalRing.ResidueField A`. -/
theorem
    mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regular_values_divisible
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        ∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g = algebraMap A K ((centralizerPPart p g : A) * a) :=
  by
    have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
      intro s _hs
      haveI : HasEnoughRootsOfUnity K (orderOf s) :=
        HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
    -- Route correction: the projective-span image theorem now lives in the theorem-local support
    -- owner, so part `(1)` only translates its regular-restriction lattice into pointwise values.
    rw [mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
      (p := p) (A := A) (K := K) (G := G) hω Φ]
    constructor
    · rintro ⟨hzero, hreg⟩
      refine ⟨hzero, ?_⟩
      intro g hg
      rcases
            (mem_regularValueDivisibilitySubmodule_iff
              (p := p) (A := A) (K := K) (G := G)
              (regularRestriction (p := p) Φ)).1 hreg
            (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) with
        ⟨a, ha⟩
      refine ⟨a, ?_⟩
      -- Evaluate the regular restriction on the representative `g`.
      simpa [regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha
    · rintro ⟨hzero, hdiv⟩
      refine ⟨hzero, ?_⟩
      refine
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)
          (regularRestriction (p := p) Φ)).2 ?_
      intro c
      rcases c with ⟨c, hc⟩
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      have hg : IsPRegular p g := hc g (by simp [ConjClasses.mem_carrier_iff_mk_eq])
      have hsubtype :
          (⟨ConjClasses.mk g, hc⟩ : PRegularConjClass G p) =
            PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩ := by
        apply Subtype.ext
        rfl
      rcases hdiv g hg with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      -- Move from the chosen class representative back to the coordinate of the restriction.
      simpa [hsubtype, regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha

end ProjectiveCharacterCriterion

section CartanCokernel

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable {ι : Type x}

local instance :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: centralizer `p`-parts are positive. -/
theorem ConjClasses.centralizerPPart_pos
    (c : ConjClasses G) :
    0 < ConjClasses.centralizerPPart p c := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  -- On representatives the `p`-part is a positive power of the prime `p`.
  simp [ConjClasses.centralizerPPart_mk, Representation.centralizerPPart,
    pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p))]

/-- Helper for Exercise 18-18.3-2: the cyclic modulus attached to a regular class is nonzero. -/
theorem ConjClasses.centralizerPPart_neZero
    (c : ConjClasses G) :
    NeZero (ConjClasses.centralizerPPart p c) := by
  -- Positivity of the centralizer `p`-part supplies the `NeZero` instance needed by `ZMod`.
  exact ⟨(ConjClasses.centralizerPPart_pos (p := p) (G := G) c).ne'⟩

/-- Helper for Exercise 18-18.3-2: a complete simple family has finite index because its
Grothendieck classes form a basis of the finite `ℤ`-module `R₀[k](G)`. -/
private theorem finite_index_of_complete_family_from_simpleBasis
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  letI : Module.Finite ℤ (R₀[k](G)) :=
    (cartan_source_target_free_and_finite_support (k := k) (G := G)).2.2.2
  -- A basis of a finite module can only have finitely many basis vectors.
  exact Module.Finite.finite_basis bR

/-- Helper for Exercise 18-18.3-2: a finite-index Cartan range and matching finite bases force
the Cartan homomorphism to be injective. -/
private theorem cartanHom_injective_of_finiteIndexRange_and_bases
    [Fintype ι]
    (bP : Module.Basis ι ℤ (P₀[k](G)))
    (bR : Module.Basis ι ℤ (R₀[k](G)))
    [((cartanHom k G).range).FiniteIndex] :
    Function.Injective (cartanHom k G) := by
  letI : Module.Free ℤ (P₀[k](G)) := Module.Free.of_basis bP
  letI : Module.Finite ℤ (P₀[k](G)) := Module.Finite.of_basis bP
  letI : Module.Free ℤ (R₀[k](G)) := Module.Free.of_basis bR
  letI : Module.Finite ℤ (R₀[k](G)) := Module.Finite.of_basis bR
  have hRangeRank :
      Module.finrank ℤ ↥((cartanHom k G).range) =
        Module.finrank ℤ (R₀[k](G)) := by
    -- A finite-index subgroup of a finite free abelian group has the full ambient rank.
    simpa using AddSubgroup.finrank_eq_of_finiteIndex (M := R₀[k](G)) ((cartanHom k G).range)
  have hQuotRank :
      Module.finrank ℤ (P₀[k](G) ⧸ (cartanHom k G).ker) =
        Module.finrank ℤ ↥((cartanHom k G).range) := by
    -- The additive first isomorphism theorem identifies the quotient by the kernel with the range.
    simpa using
      (AddEquiv.toIntLinearEquiv
        (QuotientAddGroup.quotientKerEquivRange (cartanHom k G))).finrank_eq
  have hSourceTargetRank :
      Module.finrank ℤ (P₀[k](G)) = Module.finrank ℤ (R₀[k](G)) := by
    -- The chosen projective and simple bases use the same finite index type.
    rw [Module.finrank_eq_card_basis bP, Module.finrank_eq_card_basis bR]
  have hKerZero : Module.finrank ℤ ↥((cartanHom k G).ker) = 0 := by
    -- Rank-nullity over `ℤ` leaves no rank for the kernel.
    have hnull :
        Module.finrank ℤ (P₀[k](G) ⧸ (cartanHom k G).ker) +
          Module.finrank ℤ ↥((cartanHom k G).ker) =
            Module.finrank ℤ (P₀[k](G)) := by
      simpa using
        (Submodule.finrank_quotient_add_finrank (R := ℤ) (M := P₀[k](G))
          (((cartanHom k G).ker).toIntSubmodule))
    rw [hQuotRank, hRangeRank, hSourceTargetRank] at hnull
    omega
  have hKerBot : (cartanHom k G).ker = ⊥ := by
    -- A finite `ℤ`-submodule with finrank zero is trivial.
    exact AddSubgroup.toIntSubmodule.injective
      (Submodule.finrank_eq_zero.mp (show
        Module.finrank ℤ (((cartanHom k G).ker).toIntSubmodule) = 0 from hKerZero))
  -- Injectivity is exactly vanishing of the additive kernel.
  exact (AddMonoidHom.ker_eq_bot_iff (cartanHom k G)).mp hKerBot

/-- Helper for Exercise 18-18.3-2: a global Smith-coordinate identification of the Cartan image
immediately quotients to the corresponding regular-class diagonal quotient. -/
private theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_coordinate_equiv
    (hcoord :
      ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
        (cartanHom k G).range.map e.toAddMonoidHom =
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  rcases hcoord with ⟨e, he⟩
  -- Quotient the global coordinate equivalence by the Cartan image and the diagonal lattice.
  exact
    ⟨by
      simpa [cartanCokernel] using
        (QuotientAddGroup.congr (cartanHom k G).range
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup e he)⟩

/-- Helper for Exercise 18-18.3-2: Smith coefficients that match the centralizer `p`-parts up to
permutation still produce the correct existential coordinate change for the Cartan image. -/
private theorem cartanRange_existsCoordinateEquiv_regularIntegerDiagonal_of_smithCoeffs_perm
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G)))
    (σ : PRegularConjClass G p ≃ PRegularConjClass G p)
    (hcoeff :
      ∀ c : PRegularConjClass G p,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := (cartanHom k G).range.toIntSubmodule)
            (Classical.choose
              (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G)))
            hfull c) =
          ConjClasses.centralizerPPart p (σ c).1) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)) :=
    Classical.choose (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G))
  obtain ⟨e, he⟩ :=
    exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
      (N := (cartanHom k G).range.toIntSubmodule)
      (b := b) (h := hfull)
      (d := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
      σ
      (by
        intro c
        simpa [b] using hcoeff c)
  -- The Smith-coordinate diagonal lattice is definitionally the regular integer diagonal lattice.
  refine ⟨e, ?_⟩
  simpa [regularIntegerDiagonalSubmodule] using he

/-- Helper for Exercise 18-18.3-2: the Cartan image has full ambient `ℤ`-rank. -/
private theorem cartanRange_toIntSubmodule_finrank_eq :
    Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
      Module.finrank ℤ (R₀[k](G)) := by
  let hfreeFinite := cartan_source_target_free_and_finite_support (k := k) (G := G)
  letI : Module.Free ℤ (P₀[k](G)) := hfreeFinite.1
  letI : Module.Finite ℤ (P₀[k](G)) := hfreeFinite.2.1
  letI : Module.Free ℤ (R₀[k](G)) := hfreeFinite.2.2.1
  letI : Module.Finite ℤ (R₀[k](G)) := hfreeFinite.2.2.2
  let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
    AddMonoidHom.ofInjective (cartanHom_injective (k := k) (G := G))
  have hRangeSource :
      Module.finrank ℤ ↥((cartanHom k G).range) =
        Module.finrank ℤ (P₀[k](G)) := by
    -- Injectivity identifies the source lattice with the additive Cartan image.
    simpa using (AddEquiv.toIntLinearEquiv eRange.symm).finrank_eq
  -- The public Chapter 16 support API gives equal ranks for the source and target lattices.
  calc
    Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ ↥((cartanHom k G).range) := rfl
    _ = Module.finrank ℤ (P₀[k](G)) := hRangeSource
    _ = Module.finrank ℤ (R₀[k](G)) :=
      cartan_source_target_finrank_eq_support (k := k) (G := G)

/-- Helper for Exercise 18-18.3-2: Serre's projective-character divisibility theorem should
produce a coordinate equivalence that identifies the full Cartan image with the diagonal
regular-integer lattice. -/
private theorem
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_regularValueSource
      (p := p) (k := k) (G := G) hregular

/-- Helper for Exercise 18-18.3-2: Serre's projective-character divisibility theorem identifies
the Cartan cokernel with the diagonal quotient of integer functions on the `p`-regular classes. -/
private theorem cartanCokernel_addEquiv_regularIntegerQuotient_via_projectiveCharacterLattice
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  -- Route correction: the fixed-coordinate projective-envelope generator route would diagonalize
  -- the Cartan matrix.  The source-faithful route instead needs the whole projective-character
  -- lattice quotient from Exercise 18.5(a), transported through `c = d ∘ e`.
  exact
      cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_coordinate_equiv
        (p := p) (k := k) (G := G)
        (existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_via_projectiveCharacterLattice
          (p := p) (k := k) (G := G) hregular)

/-- Helper for Exercise 18-18.3-2: Serre's projective-character divisibility theorem identifies
the Cartan cokernel directly with the product of cyclic groups indexed by the `p`-regular
classes. -/
private theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_source
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  -- Once the source-level diagonal quotient is available, the coordinatewise cyclic product is the
  -- already proved formal split of that quotient.
  rcases
        cartanCokernel_addEquiv_regularIntegerQuotient_via_projectiveCharacterLattice
          (p := p) (k := k) (G := G) hregular with
    ⟨e⟩
  exact
    ⟨e.trans
      (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))⟩

/-- Helper for Exercise 18-18.3-2: a coordinate-normalized projective-envelope generator
formula is already enough to identify the Cartan cokernel with the diagonal regular-class
quotient. -/
private theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_generator_formula
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hgen :
      ∀ c : PRegularConjClass G p,
        cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
          scaled_regular_integer_indicator (p := p) (G := G) c) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  -- The generator formula gives the desired coordinate description of the Cartan image.
  refine cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_coordinate_equiv ?_
  refine
    ⟨regularClassCoordinateAddEquiv (p := p) (k := k) (G := G), ?_⟩
  -- Quotienting that coordinate description is handled by the existing formal cokernel helper.
  exact
    cartan_range_map_eq_regularIntegerDiagonal_of_generator_formula
      (p := p) (k := k) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hgen

/-- Helper for Exercise 18-18.3-2: the whole-lattice Cartan range equality is the exact input
needed to identify the Cartan cokernel with the diagonal regular-class quotient. -/
private theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_regularClassCoordinate_range
    (hrange :
      (cartanHom k G).range.map
          (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  -- The formal quotient step only needs the canonical regular-class coordinate equivalence and
  -- the range equality supplied by the source-facing lattice bridge.
  exact
    cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_of_coordinate_equiv
      (p := p) (k := k) (G := G)
      ⟨regularClassCoordinateAddEquiv (p := p) (k := k) (G := G), hrange⟩

/-- Helper for Exercise 18-18.3-2: a product decomposition of the Cartan cokernel formally
composes with the inverse of the diagonal quotient splitting. -/
private theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_from_pi
    (h :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  rcases h with ⟨e⟩
  -- The diagonal quotient API already identifies the regular integer quotient with the same
  -- product of cyclic groups, so invert that splitting and compose.
  exact
    ⟨e.trans
      (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G)).symm⟩

/-- Helper for Exercise 18-18.3-2: once the Cartan image is identified with the diagonal lattice,
the cokernel becomes the corresponding quotient of regular-class functions. -/
theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) →
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  intro hregular
  -- Serre 18.5(b) first gives the cyclic product decomposition; the diagonal quotient form is the
  -- already proved coordinatewise splitting read backwards.
  exact
    cartanCokernel_nonempty_addEquiv_regularIntegerQuotient_from_pi
      (p := p) (k := k) (G := G)
      (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_source
        (p := p) (k := k) (G := G) hregular)

/-- Helper for Exercise 18-18.3-2: the diagonal regular-integer quotient description already
makes the Cartan cokernel finite. -/
private theorem finite_cartanCokernel_of_regularIntegerQuotient
    (h :
      Nonempty
        (cartanCokernel k G ≃+
          ((PRegularConjClass G p → ℤ) ⧸
            regularIntegerDiagonalSubmodule (p := p) (G := G)))) :
    Finite (cartanCokernel k G) := by
  rcases h with ⟨e⟩
  let eProd :
      cartanCokernel k G ≃+
        (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    e.trans (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))
  letI :
      ∀ c : PRegularConjClass G p,
        NeZero (ConjClasses.centralizerPPart p c.1) := fun c ↦
    ConjClasses.centralizerPPart_neZero (p := p) (G := G) c.1
  letI :
      Fintype
        (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    inferInstance
  letI :
      Finite
        (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
    Finite.of_fintype _
  -- Transport finiteness across the quotient splitting into coordinatewise cyclic groups.
  exact Finite.of_equiv
    (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))
    eProd.toEquiv.symm

/-- Helper for Exercise 18-18.3-2: a Cartan-cokernel equivalence with the diagonal quotient
formally composes with the coordinatewise cyclic splitting. -/
private theorem cartanCokernel_nonempty_addEquiv_pi_of_regularIntegerQuotient
    (h :
      Nonempty
        (cartanCokernel k G ≃+
          ((PRegularConjClass G p → ℤ) ⧸
            regularIntegerDiagonalSubmodule (p := p) (G := G)))) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
  rcases h with ⟨e⟩
  -- Compose the quotient-level Cartan equivalence with the explicit diagonal quotient splitting.
  exact
    ⟨e.trans
      (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))⟩

-- Proof sketch: part `(1)` computes the invariant factors of the Cartan map on the canonical
-- owner `PRegularConjClass G p` by evaluating projective characters classwise on the `p`-regular
-- conjugacy classes. Passing to Smith normal form gives a decomposition of the cokernel into the
-- corresponding cyclic groups.
/-- Exercise 18-18.3-2 (2): the cokernel of the Cartan homomorphism `c : P_k(G) → R_k(G)` is
isomorphic to the product, over the canonical owner `PRegularConjClass G p`, of the cyclic groups
`ℤ / ConjClasses.centralizerPPart p c.1 ℤ`. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart :
    fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G) →
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  by
    intro hregular
    -- Consume Serre's source-level product decomposition directly; the quotient version above is
    -- now derived from this product equivalence instead of the other way around.
    exact
      cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_source
        (p := p) (k := k) (G := G) hregular

/-- Helper for Exercise 18-18.3-2: a product decomposition of the Cartan cokernel immediately
computes its cardinality as the product of the centralizer `p`-parts. -/
private theorem card_cartanCokernel_eq_prod_centralizerPPart_of_piEquiv
    (h :
      Nonempty
        (cartanCokernel k G ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))) :
    Nat.card (cartanCokernel k G) =
      ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
  classical
  rcases h with ⟨e⟩
  -- Transport cardinality across the product equivalence, then evaluate the finite product of
  -- cyclic factors coordinatewise.
  calc
    Nat.card (cartanCokernel k G) =
        Nat.card
          (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
        exact Nat.card_congr e.toEquiv
    _ =
        ∏ c : PRegularConjClass G p,
          Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)) := by
        simpa using (Nat.card_pi : Nat.card
          (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) =
            ∏ c : PRegularConjClass G p,
              Nat.card (ZMod (ConjClasses.centralizerPPart p c.1)))
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
        simp [Nat.card_zmod]

-- Proof sketch: the previous cokernel decomposition identifies the invariant factors of the
-- distinguished Cartan matrix with the centralizer `p`-parts attached to the `p`-regular
-- conjugacy classes of `G`.
/-- Helper for Exercise 18-18.3-2: once the Cartan cokernel is transported to the diagonal
regular-class quotient, the absolute value of the distinguished Cartan determinant is the product
of the centralizer `p`-parts. -/
private theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_regularValueSource
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hregular :
      fullMixedModelRegularValueSourceStatement
        (p := p) (k := k) (G := G)) :
    by
      letI : Finite ι :=
        finite_index_of_complete_family_from_simpleBasis
          (k := k) (G := G) π hπ_pairwise hπ_complete
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
      letI : DecidableEq (PRegularConjClass G p) := Classical.decEq (PRegularConjClass G p)
      exact
        Int.natAbs
          (Matrix.det
            (cartanMatrix k G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
          ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1
  := by
    letI : Finite ι :=
      finite_index_of_complete_family_from_simpleBasis
        (k := k) (G := G) π hπ_pairwise hπ_complete
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    let bP :=
      projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope
    let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
    have hCokernelFinite : Finite (cartanCokernel k G) := by
      rcases
          cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_source
            (p := p) (k := k) (G := G) hregular with
        ⟨e⟩
      letI :
          ∀ c : PRegularConjClass G p,
            NeZero (ConjClasses.centralizerPPart p c.1) := fun c ↦
        ConjClasses.centralizerPPart_neZero (p := p) (G := G) c.1
      letI :
          Fintype
            (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
        inferInstance
      letI :
          Finite
            (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
        Finite.of_fintype _
      exact Finite.of_equiv
        (∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1))
        e.toEquiv.symm
    letI : (cartanHom k G).range.FiniteIndex := by
      have hquot :
          Finite (R₀[k](G) ⧸ (cartanHom k G).range) := by
        simpa [cartanCokernel] using hCokernelFinite
      exact AddSubgroup.finiteIndex_of_finite_quotient
    have hdet_card :
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G) := by
      have hcartan : Function.Injective (cartanHom k G) :=
        cartanHom_injective_of_finiteIndexRange_and_bases
          bP bR
      let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
        AddMonoidHom.ofInjective hcartan
      let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
        Module.Basis.map bP eRange.toIntLinearEquiv
      have hindex :
          (cartanHom k G).range.index =
            Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) := by
        -- Compare the range index with the determinant in the distinguished Cartan bases.
        rw [AddSubgroup.index_eq_natAbs_det bR (cartanHom k G).range bRange]
        congr 1
        have hbRange :
            (fun i ↦ ((bRange i : (cartanHom k G).range) : R₀[k](G))) =
              (cartanHom k G) ∘ bP := by
          ext i
          change ↑(eRange (bP i)) = cartanHom k G (bP i)
          simpa [eRange] using
            (AddMonoidHom.ofInjective_apply (f := cartanHom k G) hcartan (x := bP i))
        rw [hbRange, Module.Basis.det_apply]
        congr
        ext i j
        simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
      -- The Cartan cokernel is exactly the quotient by the Cartan-image subgroup.
      calc
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
            (cartanHom k G).range.index := hindex.symm
        _ = Nat.card (cartanCokernel k G) := by
          simpa [cartanCokernel] using
            (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))
    -- Replace the Cartan-cokernel cardinality by the imported diagonal quotient size.
    calc
      Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G) := hdet_card
      _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
          exact
              card_cartanCokernel_eq_prod_centralizerPPart_of_piEquiv
                (p := p) (k := k) (G := G)
                (cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_source
                  (p := p) (k := k) (G := G) hregular)

theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart
      (π : ι → FDRep k G)
      (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
      (hπ_complete : IsCompleteIrreducibleFamily π)
      (P : ι → FiniteProjectiveGroupAlgebraModule k G)
      (hP_envelope :
        ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
      (hregular :
        fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
      by
        letI : Finite ι :=
          finite_index_of_complete_family_from_simpleBasis
            (k := k) (G := G) π hπ_pairwise hπ_complete
        letI : Fintype ι := Fintype.ofFinite ι
        letI : DecidableEq ι := Classical.decEq ι
        letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
        letI : DecidableEq (PRegularConjClass G p) := Classical.decEq (PRegularConjClass G p)
        exact
          Int.natAbs
            (Matrix.det
              (cartanMatrix k G
                (projectiveEnvelope_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete P hP_envelope)
                (simple_finiteRep_classes_basis_of_complete_family
                  π hπ_pairwise hπ_complete))) =
            ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1
    := by
      exact
        cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_regularValueSource
          (p := p) (k := k) (G := G) (ι := ι)
          π hπ_pairwise hπ_complete P hP_envelope hregular

/-- Helper for Exercise 18-18.3-2: once the determinant is known to be nonnegative, the
corresponding `Int.natAbs` identity upgrades to an equality in `ℤ`. -/
theorem int_eq_natAbs_of_nonneg {z : ℤ} {n : ℕ}
    (hnatAbs : Int.natAbs z = n) (hz : 0 ≤ z) :
    z = n := by
  -- Replace `Int.natAbs z` by `z` using nonnegativity, then rewrite the absolute-value formula.
  calc
    z = (Int.natAbs z : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = n := by rw [hnatAbs]

/-- Helper for Exercise 18-18.3-2: any integral Gram matrix has nonnegative determinant. -/
private theorem Matrix.int_gram_det_nonneg
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (E : Matrix κ η ℤ) :
    0 ≤ Matrix.det (E.transpose * E) := by
  let Eℝ : Matrix κ η ℝ := E.map (Int.castRingHom ℝ)
  have hpsd : Matrix.PosSemidef (Eℝ.transpose * Eℝ) := by
    -- After casting to `ℝ`, a Gram matrix is visibly positive semidefinite.
    simpa [Eℝ] using Matrix.posSemidef_conjTranspose_mul_self Eℝ
  have hmap :
      (E.transpose * E).map (Int.castRingHom ℝ) = Eℝ.transpose * Eℝ := by
    -- Entrywise casting commutes with transpose and matrix multiplication.
    ext i j
    simp [Eℝ, Matrix.mul_apply]
  have hdet_nonneg : 0 ≤ Matrix.det (Eℝ.transpose * Eℝ) :=
    Matrix.PosSemidef.det_nonneg hpsd
  have hcast :
      (((Matrix.det (E.transpose * E) : ℤ)) : ℝ) =
        Matrix.det (Eℝ.transpose * Eℝ) := by
    -- Rewrite the determinant after casting the integral entries to `ℝ`.
    rw [Int.cast_det]
    simpa [hmap] using congrArg Matrix.det hmap
  have hreal : 0 ≤ (((Matrix.det (E.transpose * E) : ℤ)) : ℝ) := by
    rw [hcast]
    exact hdet_nonneg
  exact_mod_cast hreal

/-- Helper for Exercise 18-18.3-2: once the source-faithful Cartan argument produces a Gram
factorization `C = Eᵀ * E`, determinant nonnegativity is a pure integral matrix fact. -/
private theorem Matrix.int_det_nonneg_of_eq_transpose_mul_self
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (C : Matrix η η ℤ) (E : Matrix κ η ℤ)
    (hC : C = E.transpose * E) :
    0 ≤ Matrix.det C := by
  -- Replace `C` by the exhibited Gram matrix and apply the previous determinant-sign lemma.
  simpa [hC] using Matrix.int_gram_det_nonneg E

/-- Helper for Exercise 18-18.3-2: existential integral Gram data already implies nonnegative
determinant. -/
private theorem Matrix.int_det_nonneg_of_exists_eq_transpose_mul_self
    {η : Type*} [Fintype η] [DecidableEq η]
    (C : Matrix η η ℤ)
    (hC :
      ∃ (κ : Type*) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ η ℤ),
        C = E.transpose * E) :
    0 ≤ Matrix.det C := by
  rcases hC with ⟨κ, _, _, E, hE⟩
  -- Expose the Gram witness and reuse the pure matrix determinant-sign lemma.
  exact Matrix.int_det_nonneg_of_eq_transpose_mul_self C E hE

omit [IsAlgClosed k] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 18-18.3-2: existential Gram data for the distinguished Cartan matrix
implies the Cartan determinant is nonnegative. -/
private theorem cartanMatrix_det_nonneg_of_gram_data
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hGramData :
      ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
        cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete) =
          E.transpose * E) :
    0 ≤
      Matrix.det
        (cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)) := by
  -- Once the representation-theoretic bridge has produced a Gram factorization, the determinant
  -- sign is the pure integral matrix lemma above.
  exact
    Matrix.int_det_nonneg_of_exists_eq_transpose_mul_self
      (C :=
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete))
      hGramData

include p in
/-- Helper for Exercise 18-18.3-2: the Chapter `16` Gram factorization should be transportable
directly to an algebraically closed residue field `k` of characteristic `p`. -/
private theorem cartanMatrix_source_faithful_gram_data_via_mixed_character_model
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  exact
    cartanMatrix_source_faithful_gram_data_via_mixed_character_model_support
      (k := k) (G := G) π hπ_pairwise hπ_complete P hP_envelope

include p in
/-- Helper for Exercise 18-18.3-2: the Chapter `16` Gram factorization should be transportable
directly to an algebraically closed residue field `k` of characteristic `p`. -/
private theorem cartanMatrix_source_faithful_gram_data_over_algClosed_residueField
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  -- Delegate to the mixed-character transport front so the public determinant argument only sees
  -- the final Gram identity it needs.
  exact
    cartanMatrix_source_faithful_gram_data_via_mixed_character_model
      (p := p) (k := k) (G := G) π hπ_pairwise hπ_complete P hP_envelope

include p in
/-- Helper for Exercise 18-18.3-2: the distinguished Cartan determinant is nonnegative. -/
theorem cartanMatrix_det_nonneg
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    0 ≤
      Matrix.det
        (cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)) := by
  have hGramData :
      ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
        cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete) =
          E.transpose * E :=
    cartanMatrix_source_faithful_gram_data_over_algClosed_residueField
      (p := p) (k := k) (G := G) π hπ_pairwise hπ_complete P hP_envelope
  -- Once the mixed-character bridge exposes existential Gram data, determinant nonnegativity is a
  -- pure integral matrix argument.
  exact
    cartanMatrix_det_nonneg_of_gram_data
      (k := k) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope
      hGramData

/-- Helper for Exercise 18-18.3-2: the product of the centralizer `p`-parts in `ℤ` is just the
coercion of the corresponding product in `ℕ`. -/
theorem int_prod_centralizerPPart_eq_natCast :
    (∏ c : PRegularConjClass G p, (ConjClasses.centralizerPPart p c.1 : ℤ)) =
      ((∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 : ℕ) : ℤ) := by
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  -- Move the coercion across the finite product coordinatewise.
  symm
  simpa using
    (Nat.cast_prod (R := ℤ) (s := Finset.univ)
      (f := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1))

/-- Helper for Exercise 18-18.3-2: the final determinant identity follows formally from the
absolute-value formula and the Gram-data nonnegativity bridge. -/
private theorem cartanMatrix_det_eq_prod_centralizerPPart_of_natAbs_and_nonneg
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hnatAbs :
      Int.natAbs
          (Matrix.det
            (cartanMatrix k G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
        ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1)
    (hnonneg :
      0 ≤
        Matrix.det
          (cartanMatrix k G
            (projectiveEnvelope_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete P hP_envelope)
            (simple_finiteRep_classes_basis_of_complete_family
              π hπ_pairwise hπ_complete))) :
    Matrix.det
        (cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)) =
      ∏ c : PRegularConjClass G p, (ConjClasses.centralizerPPart p c.1 : ℤ) := by
  -- First express the integer product as the cast of the natural product from the cokernel count.
  rw [int_prod_centralizerPPart_eq_natCast (p := p) (G := G)]
  -- The nonnegative determinant is equal to its `Int.natAbs`, so the `natAbs` formula closes.
  exact int_eq_natAbs_of_nonneg hnatAbs hnonneg

/-- Exercise 18-18.3-2 (3): the determinant of the distinguished Cartan matrix written in the
canonical simple and projective-envelope bases is the product, over the canonical owner
`PRegularConjClass G p`, of the centralizer `p`-parts of the `p`-regular conjugacy classes of
`G`. -/
theorem cartanMatrix_det_eq_prod_centralizerPPart
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hregular :
      fullMixedModelRegularValueSourceStatement (p := p) (k := k) (G := G)) :
    by
      letI : Finite ι :=
        finite_index_of_complete_family_from_simpleBasis
          (k := k) (G := G) π hπ_pairwise hπ_complete
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
      letI : DecidableEq (PRegularConjClass G p) := Classical.decEq (PRegularConjClass G p)
      exact
        Matrix.det
            (cartanMatrix k G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete)) =
          ∏ c : PRegularConjClass G p, (ConjClasses.centralizerPPart p c.1 : ℤ)
  := by
    letI : Finite ι := by
      -- The determinant matrix is formed after installing the finite index supplied by the
      -- Grothendieck-basis helper.
      exact
        finite_index_of_complete_family_from_simpleBasis
          (k := k) (G := G) π hπ_pairwise hπ_complete
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    -- Assemble the two representation-theoretic inputs using the formal integer cast helper.
    exact
      cartanMatrix_det_eq_prod_centralizerPPart_of_natAbs_and_nonneg
        (p := p) (k := k) (G := G) (ι := ι)
        π hπ_pairwise hπ_complete P hP_envelope
        (cartanMatrix_det_natAbs_eq_prod_centralizerPPart_of_regularValueSource
          (p := p) (k := k) (G := G) (ι := ι)
          π hπ_pairwise hπ_complete P hP_envelope hregular)
        (cartanMatrix_det_nonneg
          π hπ_pairwise hπ_complete P hP_envelope)

end CartanCokernel

end Representation
