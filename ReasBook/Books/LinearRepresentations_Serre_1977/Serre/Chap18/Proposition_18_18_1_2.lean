import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.QuotientCharpoly
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RealizationCore
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2.TensorMultiplicativity
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation
open scoped TensorProduct

universe u v x y

namespace Representation


section BasicProperties

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v}
variable {G : Type u}
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

section One

variable [CommSemiring A]
variable [Group G]

-- Proof sketch: evaluate the characteristic polynomial of `ρ 1`, whose only root is `1`, and sum
-- the lifted copies of that root counted with multiplicity `Module.finrank k V`.
/-- Clause (1) of Proposition 18-18.1-2: the modular character of a finite-dimensional
`k[G]`-module takes
the identity to the dimension of the module. -/
theorem modularCharacter_one_eq_finrank
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) :
    φ[lift](ρ) ⟨(1 : G), isPRegular_one p⟩ =
      Module.finrank k V :=
  -- Rewrite the characteristic roots of `ρ 1 = 1` as `finrank` many copies of the root `1`.
  by
    classical
    have hroots :
        (ρ (1 : G)).charpoly.roots =
          Multiset.replicate (Module.finrank k V) (1 : k) := by
      calc
        (LinearMap.charpoly (ρ (1 : G))).roots =
            ((Polynomial.X - Polynomial.C (1 : k)) ^ Module.finrank k V).roots := by
              simp [LinearMap.charpoly_one]
        _ = Module.finrank k V • (Polynomial.X - Polynomial.C (1 : k)).roots := by
              rw [Polynomial.roots_pow]
        _ = Multiset.replicate (Module.finrank k V) (1 : k) := by
              rw [Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]
    have hcard :
        (LinearMap.charpoly (1 : Module.End k V)).roots.card = Module.finrank k V := by
      simpa using congrArg Multiset.card hroots
    -- Every packaged root on the identity element is the distinguished unit root `1`.
    change
      (Multiset.map
        (fun μ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦
          (lift : PrimeToPRoot p k → A)
            (charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2))
        (ρ (1 : G)).charpoly.roots.attach).sum =
        Module.finrank k V
    have hmap :
        Multiset.map
          (fun μ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦
            (lift : PrimeToPRoot p k → A)
              (charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2))
          (ρ (1 : G)).charpoly.roots.attach =
        Multiset.map (fun _ : { x // x ∈ (ρ (1 : G)).charpoly.roots } ↦ (1 : A))
          (ρ (1 : G)).charpoly.roots.attach := by
      apply Multiset.map_congr rfl
      intro μ _
      have hval_mem : (μ : k) ∈ Multiset.replicate (Module.finrank k V) (1 : k) := by
        rw [← hroots]
        exact μ.2
      have hval : (μ : k) = 1 := Multiset.eq_of_mem_replicate hval_mem
      have hroot :
          charpolyRoot_primeToPRoot (p := p) (k := k) ρ (isPRegular_one p) μ.2 =
            (1 : PrimeToPRoot p k) := by
        ext
        simp [hval]
      simp [hroot]
    rw [hmap]
    -- Summing the constant value `1` over the attached roots gives the root-count, hence the
    -- dimension.
    simp only [Multiset.map_const', Multiset.card_attach, map_one, Multiset.sum_replicate,
      nsmul_eq_mul, mul_one]
    exact congrArg (fun n : ℕ ↦ (n : A)) hcard

end One

section Conjugation

variable [AddCommMonoid A]
variable [Group G]

-- Proof sketch: `ρ (t * s * t⁻¹)` is conjugate to `ρ s`, so their characteristic polynomials and
-- hence the defining multisets of lifted roots agree.
/-- Clause (2) of Proposition 18-18.1-2: the modular character is constant on conjugacy classes of
`p`-regular elements. -/
theorem modularCharacter_conj
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V) (s t : G)
    (hs : IsPRegular p s) :
    φ[lift](ρ) ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      φ[lift](ρ) ⟨s, hs⟩ :=
  -- Package `ρ t` as a linear equivalence so that `ρ (t * s * t⁻¹)` appears as a conjugate of
  -- `ρ s`.
  by
    let e : V ≃ₗ[k] V :=
      LinearEquiv.ofLinear (ρ t) (ρ t⁻¹)
        (by
          ext x
          simp)
        (by
          ext x
          simp)
    have hconj : e.conj (ρ s) = ρ (t * s * t⁻¹) := by
      ext x
      simp [e, LinearEquiv.conj_apply_apply, LinearEquiv.ofLinear_apply,
        LinearEquiv.ofLinear_symm_apply, mul_assoc]
    have hchar : (ρ (t * s * t⁻¹)).charpoly = (ρ s).charpoly := by
      simpa [hconj] using (LinearEquiv.charpoly_conj e (ρ s))
    have hroots : (ρ (t * s * t⁻¹)).charpoly.roots = (ρ s).charpoly.roots := by
      simpa using congrArg Polynomial.roots hchar
    change
      (Multiset.map
        (fun μ : { x // x ∈ (ρ (t * s * t⁻¹)).charpoly.roots } ↦
          lift
            (charpolyRoot_primeToPRoot (p := p) (k := k) ρ
              (isPRegular_conj p s t hs) μ.2))
        (ρ (t * s * t⁻¹)).charpoly.roots.attach).sum =
        (Multiset.map
          (fun μ : { x // x ∈ (ρ s).charpoly.roots } ↦
            lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ hs μ.2))
          (ρ s).charpoly.roots.attach).sum
    exact attached_sum_eq_of_eq hroots
      (fun μ ↦ lift
        (charpolyRoot_primeToPRoot (p := p) (k := k) ρ
          (isPRegular_conj p s t hs) μ.2))
      (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ hs μ.2))
      (fun μ ↦ by
        apply congrArg lift
        ext
        simp [charpolyRoot_primeToPRoot_coe])

end Conjugation

section Exactness

variable [AddCommMonoid A]
variable [Group G]

-- block-upper-triangular, so the characteristic roots and their lifted sums split additively.
/-- Clause (3) of Proposition 18-18.1-2: the modular character is additive on short exact
sequences of
finite-dimensional `k[G]`-representations. -/
-- TODO: vendor the Chapter `9` charpoly factorization for an invariant submodule and apply it to
-- the short exact sequence at the chosen `p`-regular element, then split the root sum with
-- `Polynomial.roots_mul`.
theorem modularCharacter_add_of_shortExactSequence
    (lift : PrimeToPRoot p k → A)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) (s : { t : G // IsPRegular p t }) :
    φ[lift](S.X₂.ρ) s =
      φ[lift](S.X₁.ρ) s +
        φ[lift](S.X₃.ρ) s := by
  exact modularCharacter_add_of_shortExactSequence_bridge (p := p) (lift := lift) S hS s

end Exactness

section Tensor

variable [CommSemiring A]
variable [Group G]
variable {W : Type y} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

-- Proof sketch: tensoring eigenvectors multiplies eigenvalues, so on a `p`-regular element the
-- lifted eigenvalue sum for `tprod ρ σ` factors as the product of the two lifted sums.
/-- Clause (4) of Proposition 18-18.1-2: the modular character is multiplicative under tensor
products.
As in the source, `p` is the prime characteristic of `k`, so that `p`-regular elements act
diagonalizably. -/
theorem modularCharacter_tensor [Fact p.Prime] [CharP k p]
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) (σ : Representation k G W)
    (s : { t : G // IsPRegular p t }) :
    φ[lift](tprod ρ σ) s =
      φ[lift](ρ) s *
        φ[lift](σ) s := by
  -- The theorem-local support file owns the eigenbasis/root-sum proof so later projective
  -- helpers can reuse tensor multiplicativity without importing this target file.
  exact modularCharacter_tensor_bridge (p := p) (k := k) (A := A) (G := G) lift ρ σ s

end Tensor

end BasicProperties

section TraceReduction

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type v} [CommRing A]
variable {G : Type u} [Group G] [Fact p.Prime] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Clause (5) of Proposition 18-18.1-2: the trace of `t` is the reduction of the modular character
evaluated at the chosen `p`-regular component `pRegularComponent p t`. -/
-- TODO: first compare the reduction of the modular-character root sum with the trace on the
-- `p`-regular locus, then show the `p`-unipotent component contributes a nilpotent trace-zero
-- correction.
theorem trace_eq_reduction_modularCharacter_pRegularComponent
    (lift : PrimeToPRoot p k →* A) (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (ρ : Representation k G V) (t : G) :
    LinearMap.trace k V (ρ t) =
      red
        (φ[lift](ρ)
          ⟨pRegularComponent p t, isPRegular_pRegularComponent t⟩) := by
  exact trace_eq_reduction_modularCharacter_pRegularComponent_bridge
    (p := p) (lift := lift) (red := red) hred ρ t
end TraceReduction

section StableReduction

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable [FiniteDimensional K E]

local notation "k" => IsLocalRing.ResidueField A

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

open Polynomial in
-- Proof sketch (after the source): choose a basis of the stable lattice; it is simultaneously a
-- `K`-basis upstairs and reduces to a basis of the reduction, so the two characteristic
-- polynomials are the two scalar images of one polynomial over `A`.  Over a sufficiently large
-- `K` the upstairs polynomial splits into root-of-unity linear factors lying in `A`; reducing the
-- factorization identifies the reduced eigenvalues, and the compatibility of the lift with the
-- residue map recovers each upstairs eigenvalue from its reduction.
/-- Clause (6) of Proposition 18-18.1-2: the modular character of the reduction of a
`G`-stable lattice is
the restriction of the ordinary character of the ambient `K[G]`-representation to the `p`-regular
elements.

Following the source, the coefficient field is sufficiently large for the element in question
(`hω`) and the eigenvalue lift is the canonical one determined by the reduction of `A`
(`hred`); without the latter compatibility the statement is false for general injective lifts. -/
theorem modularCharacter_stableLatticeReduction_eq_character_restriction
    [IsDomain A] [IsDiscreteValuationRing A] [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (ρ : Representation K G E) (L : StableLattice A ρ)
    (s : { t : G // IsPRegular p t })
    (hω : ∃ ω : K, IsPrimitiveRoot ω (orderOf s.1)) :
    φ[PrimeToPRoot.toFieldLift lift](L.reductionRepresentation) s =
      ρ.character s.1 := by
  exact stableLatticeReduction_modularCharacter_eq_character_restriction
    (p := p) (A := A) (K := K) (G := G) lift hred ρ L s hω

end StableReduction

section ProjectiveFormulas

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance finiteGroupFintypeTarget : Fintype G := Fintype.ofFinite G

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]


-- Proof sketch: on the `p`-regular locus use clause `(6)` on a projective lift, and away from
-- that locus use the vanishing of projective characters on `p`-singular elements.
/-- Clause (7) of Proposition 18-18.1-2: for a finite-dimensional `k[G]`-representation `E`
and a finite projective `k[G]`-representation `F`, the projective lift character of `E ⊗ F`
agrees on `p`-regular elements with the product of the modular character of `E` and the
projective lift character of `F`, and vanishes on `p`-singular elements. -/
-- TODO: split by `IsPRegular p g`; on the regular branch, rewrite through clause `(6)` and
-- ordinary character multiplicativity, and on the singular branch use the projective-character
-- vanishing criterion.
-- The eigenvalue lift must be the CANONICAL one compatible with the reduction `A → k` (`hred`)
-- and `K` must contain the relevant roots of unity (`hω`); without `hred` the identity is false for
-- a general monoid-hom `lift` (the `p`-regular factor `φ_E` depends on the chosen lift while the
-- left side does not).  These are exactly the guards carried by the neighbouring helper
-- `projectiveLiftCharacter_eq_modularCharacterZeroExtension_toFiniteRep_of_isPRegular_local`.
theorem projectiveLiftCharacter_tensor_eq_modularCharacter_mul
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G)
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (E ⊗ₚ F) e =
      FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) *
        FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e :=
  by
    -- The theorem-local bridge contains the regular/singular pointwise decomposition; its
    -- remaining support obligations are isolated in `GrothendieckProjectiveBridge`.
    exact projectiveLiftCharacter_tensor_eq_modularCharacter_mul_bridge
      (A := A) (K := K) (G := G) (p := p) lift hred hω E F

-- Proof sketch: rewrite the multiplicity pairing as the ordinary projective-character pairing and
-- substitute clause `(7)` to express the ordinary factor through the Brauer character on the
-- `p`-regular locus.
/- Clause (8) of Proposition 18-18.1-2: the source-facing bridge remains in the target file so the
pipeline's active declaration is the planned theorem, while its support stays in the local API. -/
/-- Clause (8) of Proposition 18-18.1-2: the projective Brauer pairing formula in expanded finite
sum form. -/
theorem intertwining_finrank_eq_projectiveLiftCharacter_pairing_bridge
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G) (F : FiniteProjectiveGroupAlgebraModule k G) :
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
            FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s := by
  -- Expand the named normalized pairing bridge into Serre's source-facing finite sum.
  calc
    (Module.finrank k
        (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) =
        ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e,
          FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift)⟫ := by
          exact
            (projectiveLiftCharacter_pairing_eq_intertwining_finrank
              (A := A) (K := K) (G := G) (p := p) lift hred hω E F).symm
    _ =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
              FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s := by
          rfl

/-- Clause (8) of Proposition 18-18.1-2: the multiplicity pairing of `E` with a finite projective
`k[G]`-representation `F` is the average over the `p`-regular elements of the product
`Φ_F(s⁻¹) φ_E(s)`. -/
-- As in clause (7), the lift must be the canonical reduction-compatible one (`hred`) with `K`
-- large enough (`hω`); for a general `lift` the right-hand pairing depends on the lift while the
-- left-hand multiplicity does not, so the identity fails.
theorem intertwining_finrank_eq_projectiveLiftCharacter_pairing
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : FDRep k G)
    (F : FiniteProjectiveGroupAlgebraModule k G) :
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap (FDRep.ρ E)) : K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
            FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s :=
  by
    -- The theorem-local bridge is the source-facing expanded pairing formula; the missing
    -- multiplicity bridge is kept as the explicit frontier in the support file.
    exact intertwining_finrank_eq_projectiveLiftCharacter_pairing_bridge
      (A := A) (K := K) (G := G) (p := p) lift hred hω E F

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Finite G] [CharP k p] in
/-- Helper for Proposition 18-18.1-2: the zero-extended modular character of the trivial
representation is exactly the indicator of the `p`-regular locus. -/
private theorem modularCharacterZeroExtension_trivial_local
    (lift : PrimeToPRoot p k →* Kˣ) :
    FDRep.modularCharacterZeroExtension (FDRep.of (Representation.trivial k G k))
      (PrimeToPRoot.toFieldLift lift) =
      fun s : G ↦ if IsPRegular p s then (1 : K) else 0 := by
  -- On the regular locus the trivial representation contributes the constant modular character
  -- `1`, and away from that locus both zero-extensions vanish by definition.
  funext s
  by_cases hsp : IsPRegular p s
  · -- The trivial action is the identity on the one-dimensional module, so its modular character
    -- is `1` at every `p`-regular element.
    have hmod :
        φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ = (1 : K) := by
      have hroots :
          (Representation.trivial k G k s).charpoly.roots =
            (Representation.trivial k G k (1 : G)).charpoly.roots := by
        simp [Representation.trivial]
      have hsame :
          φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ =
            φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k)
              ⟨(1 : G), isPRegular_one p⟩ := by
        unfold Representation.modularCharacter
        exact attached_sum_eq_of_eq hroots _ _ (by
          intro μ
          apply congrArg (fun z ↦ ((Units.coeHom K).comp lift) z)
          ext
          simp [Representation.trivial])
      have hone :
          φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k)
              ⟨(1 : G), isPRegular_one p⟩ = (1 : K) := by
        convert (modularCharacter_one_eq_finrank (p := p)
          (lift := (Units.coeHom K).comp lift) (ρ := Representation.trivial k G k)) using 1
        simp
      exact hsame.trans hone
    simp [FDRep.modularCharacterZeroExtension, hmod]
  · -- Outside the regular locus the zero-extension is definitionally zero.
    simp [FDRep.modularCharacterZeroExtension, hsp]

-- Proof sketch: specialize clause `(8)` to the trivial representation, whose modular character is
-- `1` on the `p`-regular locus and `0` elsewhere after zero extension.
/-- Proposition 18-18.1-2 (9): the multiplicity of the trivial representation in a finite
projective `k[G]`-representation `F` is the average of its projective lift character over the
`p`-regular elements of `G`. -/
theorem trivialMultiplicity_eq_projectiveLiftCharacter_average
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    (Module.finrank k
        (F.toRep.ρ.IntertwiningMap
          (Representation.trivial k G k)) :
        K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          if IsPRegular p s then
            FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s
          else 0 :=
  by
    -- Apply clause `(8)` to the trivial representation, using the supplied compatible lift.
    calc
      (Module.finrank k
        (F.toRep.ρ.IntertwiningMap
          (Representation.trivial k G k)) :
        K) =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹) *
                FDRep.modularCharacterZeroExtension
                  (FDRep.of (Representation.trivial k G k))
                  (PrimeToPRoot.toFieldLift lift) s := by
            -- The pairing formula with `E` equal to the trivial representation gives the target
            -- multiplicity on the left-hand side.
            simpa using
              intertwining_finrank_eq_projectiveLiftCharacter_pairing
                (p := p) (A := A) (K := K) (lift := lift) hred hω
                (E := FDRep.of (Representation.trivial k G k)) F
      _ = (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              if IsPRegular p s then
                FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e (s⁻¹)
              else 0 := by
            -- Replace the trivial modular character by the indicator of the `p`-regular locus.
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            have htriv :=
              congrFun
                (modularCharacterZeroExtension_trivial_local (p := p) (A := A) (K := K)
                  (G := G) lift) s
            by_cases hsp : IsPRegular p s
            · have hzero :
                  FDRep.modularCharacterZeroExtension (FDRep.of (Representation.trivial k G k))
                    (PrimeToPRoot.toFieldLift lift) s = (1 : K) := by
                  rw [htriv]
                  simp [hsp]
              have hmod :
                  φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, hsp⟩ =
                    (1 : K) := by
                  have hzero' :
                      (if h : IsPRegular p s then
                        φ[PrimeToPRoot.toFieldLift lift](Representation.trivial k G k) ⟨s, h⟩
                      else 0) = (1 : K) := by
                    simpa [FDRep.modularCharacterZeroExtension] using hzero
                  rw [dif_pos hsp] at hzero'
                  exact hzero'
              simp [FDRep.modularCharacterZeroExtension, hmod]
            · simp [FDRep.modularCharacterZeroExtension, hsp]
      _ = (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              if IsPRegular p s then
                FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e s
              else 0 := by
            -- Reindex the finite sum by inversion, which preserves the `p`-regular locus.
            congr 1
            simpa [Function.comp, IsPRegular, orderOf_inv] using
              (Equiv.sum_comp (Equiv.inv G)
                (fun t : G ↦ if IsPRegular p t then
                  FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter F e t
                else 0))

end ProjectiveFormulas

end Representation
