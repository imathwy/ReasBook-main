import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularClasses
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FieldTransport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FDRepTransport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveTransport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.LocalGramSupport
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.FullMixedCharacteristicModel
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.DiagonalQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

/-- Helper: transport of `ℤ`-basis coordinates across a `ℤ`-linear map carrying one basis to
another. If `Φ (bM i) = bN i` for all `i`, then the `bN`-coordinates of `Φ x` equal the
`bM`-coordinates of `x`. -/
private theorem repr_transport_aux {ι : Type*} {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (bM : Module.Basis ι ℤ M) (bN : Module.Basis ι ℤ N)
    (Φ : M →ₗ[ℤ] N) (h : ∀ i, Φ (bM i) = bN i) (x : M) (i : ι) :
    bN.repr (Φ x) i = bM.repr x i := by
  have key : (bN.repr.toLinearMap.comp Φ) = bM.repr.toLinearMap := by
    apply bM.ext
    intro j
    simp [h j, Module.Basis.repr_self]
  have hx := congrArg (fun L : M →ₗ[ℤ] (ι →₀ ℤ) => L x) key
  simpa using congrArg (fun f : ι →₀ ℤ => f i) hx

section CartanCokernelRingEquivTransport

variable {F K : Type u} [Field F] [Field K]
variable (e : F ≃+* K)
variable {G : Type u} [Group G] [Finite G]

/-- Restrict a split-product equivalence of finite projective `K[G]`-modules along a coefficient
field isomorphism. -/
def transProjProdLinearEquiv
    {X Y Z : FiniteProjectiveGroupAlgebraModule K G}
    (h : Y.V ≃ₗ[K[G]] X.V × Z.V) :
    (transProj e Y).V ≃ₗ[F[G]] (transProj e X).V × (transProj e Z).V where
  toFun y := ((h y).1, (h y).2)
  invFun yz := h.symm (yz.1, yz.2)
  left_inv y := by
    simp
  right_inv yz := by
    cases yz
    simp
  map_add' y y' := by
    simpa only using h.map_add y y'
  map_smul' a y := by
    have hs := h.map_smul (mapMonoidAlgebraRingEquiv e G a) (y : Y.V)
    simpa only [transProj] using hs

/-- Free-abelian lift used to transport projective Grothendieck groups across a coefficient-field
isomorphism. -/
private abbrev projectiveGrothendieckTransportLift :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule K G) →+
      P₀[F](G) :=
  FreeAbelianGroup.lift fun P ↦ ([transProj e P]ₚ₀ : P₀[F](G))

omit [Finite G] in
/-- The projective Grothendieck transport lift kills the defining split-exact relations. -/
theorem projectiveGrothendieckTransport_generator_eq_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule K G))
    (hS : Nonempty (S.X₂.V ≃ₗ[K[G]] S.X₁.V × S.X₃.V)) :
    projectiveGrothendieckTransportLift e
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0 := by
  rcases hS with ⟨hS⟩
  have hrel :
      ([transProj e S.X₂]ₚ₀ : P₀[F](G)) =
        [transProj e S.X₁]ₚ₀ + [transProj e S.X₃]ₚ₀ := by
    exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_add_of_linearEquiv_prod
      (A := F) (G := G)
      (transProj e S.X₁) (transProj e S.X₂) (transProj e S.X₃)
      (transProjProdLinearEquiv e hS)
  simp only [projectiveGrothendieckTransportLift, map_sub, FreeAbelianGroup.lift_apply_of]
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm]
  exact hrel

variable (G) in
/-- Transport the projective Grothendieck group across a coefficient-field isomorphism. -/
def projectiveGrothendieckTransport :
    P₀[K](G) →+ P₀[F](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations K G)
    (projectiveGrothendieckTransportLift e)
    (by
      rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
      rintro _ ⟨⟨S, hS⟩, rfl⟩
      exact projectiveGrothendieckTransport_generator_eq_zero e S hS)

omit [Finite G] in
@[simp] theorem projectiveGrothendieckTransport_class
    (P : FiniteProjectiveGroupAlgebraModule K G) :
    projectiveGrothendieckTransport e G ([P]ₚ₀ : P₀[K](G)) =
      ([transProj e P]ₚ₀ : P₀[F](G)) :=
  rfl

/-- Transporting finite-representation Grothendieck groups across a field isomorphism and then back
is the identity. -/
theorem finiteRepGrothendieckTransport_left_inv
    (x : R₀[K](G)) :
    grothendieckTransport e.symm G (grothendieckTransport e G x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    simpa [grothendieckTransport_class] using
      (finiteRepGrothendieckClass_eq_of_nonempty_iso
        (L := K) (G := G)
        (V := fdRepOverRingEquiv e.symm (fdRepOverRingEquiv e V)) (W := V)
        ⟨fdRepOverRingEquiv_roundtrip e V⟩)
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

/-- Transporting finite-representation Grothendieck groups back across a field isomorphism and then
forward is the identity. -/
theorem finiteRepGrothendieckTransport_right_inv
    (x : R₀[F](G)) :
    grothendieckTransport e G (grothendieckTransport e.symm G x) = x := by
  simpa using
    (finiteRepGrothendieckTransport_left_inv (e := e.symm) (G := G) x)

/-- The finite-representation Grothendieck group is transported by an additive equivalence across a
field isomorphism. -/
noncomputable def finiteRepGrothendieckTransportAddEquiv :
    R₀[K](G) ≃+ R₀[F](G) where
  toFun := grothendieckTransport e G
  invFun := grothendieckTransport e.symm G
  left_inv := finiteRepGrothendieckTransport_left_inv (e := e) (G := G)
  right_inv := finiteRepGrothendieckTransport_right_inv (e := e) (G := G)
  map_add' := (grothendieckTransport e G).map_add

@[simp] theorem finiteRepGrothendieckTransportAddEquiv_apply
    (x : R₀[K](G)) :
    finiteRepGrothendieckTransportAddEquiv (e := e) (G := G) x =
      grothendieckTransport e G x :=
  rfl

/-- Transport of `R₀` sends the finite-representation class underlying a projective module to the
finite-representation class underlying the transported projective module. -/
theorem grothendieckTransport_projective_toFiniteRep
    (P : FiniteProjectiveGroupAlgebraModule K G) :
    grothendieckTransport e G ([(P.toFiniteRep)]₀ : R₀[K](G)) =
      ([(transProj e P).toFiniteRep]₀ : R₀[F](G)) := by
  rw [grothendieckTransport_class]
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso
    (L := F) (G := G) ⟨(transProj_toFiniteRep_iso e P).symm⟩

/-- Transporting `R₀` after the Cartan homomorphism is the same as first transporting `P₀` and then
applying the Cartan homomorphism. -/
theorem cartanHom_transport_commute
    (x : P₀[K](G)) :
    grothendieckTransport e G (cartanHom K G x) =
      cartanHom F G (projectiveGrothendieckTransport e G x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro P
    change grothendieckTransport e G (cartanHom K G ([P]ₚ₀ : P₀[K](G))) =
      cartanHom F G (projectiveGrothendieckTransport e G ([P]ₚ₀ : P₀[K](G)))
    rw [cartanHom_projectiveClass_eq, projectiveGrothendieckTransport_class,
      cartanHom_projectiveClass_eq]
    exact grothendieckTransport_projective_toFiniteRep (e := e) (G := G) P
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

/-- Transport of `R₀` carries the Cartan image into the Cartan image. -/
theorem grothendieckTransport_cartanHom_mem_range
    (x : P₀[K](G)) :
    grothendieckTransport e G (cartanHom K G x) ∈ (cartanHom F G).range := by
  exact ⟨projectiveGrothendieckTransport e G x, (cartanHom_transport_commute e x).symm⟩

/-- The finite-representation transport equivalence carries the Cartan-image subgroup to the
Cartan-image subgroup. -/
theorem cartanHom_range_map_finiteRepGrothendieckTransportAddEquiv :
    (cartanHom K G).range.map
        (finiteRepGrothendieckTransportAddEquiv (e := e) (G := G)).toAddMonoidHom =
      (cartanHom F G).range := by
  ext y
  constructor
  · intro hy
    rcases AddSubgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    exact ⟨projectiveGrothendieckTransport e G x, (cartanHom_transport_commute e x).symm⟩
  · intro hy
    rcases hy with ⟨x, rfl⟩
    refine AddSubgroup.mem_map.2 ?_
    refine ⟨cartanHom K G (projectiveGrothendieckTransport e.symm G x), ⟨_, rfl⟩, ?_⟩
    have hcomm := cartanHom_transport_commute e.symm x
    calc
      grothendieckTransport e G
          (cartanHom K G (projectiveGrothendieckTransport e.symm G x)) =
        grothendieckTransport e G (grothendieckTransport e.symm G (cartanHom F G x)) := by
          rw [hcomm]
      _ = cartanHom F G x :=
        finiteRepGrothendieckTransport_right_inv (e := e) (G := G) (cartanHom F G x)

/-- The Cartan cokernel is invariant, as an additive group, under field isomorphism. -/
noncomputable def cartanCokernel_addEquiv_transport_of_ringEquiv :
    cartanCokernel K G ≃+ cartanCokernel F G := by
  simpa [cartanCokernel] using
    QuotientAddGroup.congr
      (cartanHom K G).range
      (cartanHom F G).range
      (finiteRepGrothendieckTransportAddEquiv (e := e) (G := G))
      (cartanHom_range_map_finiteRepGrothendieckTransportAddEquiv (e := e) (G := G))

end CartanCokernelRingEquivTransport

section CartanCokernelProductRingEquivTransport

variable {p : ℕ}
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Product decompositions of the Cartan cokernel transport across an isomorphism of algebraically
closed coefficient fields. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_transport_of_ringEquiv
    {k0 k : Type u} [Field k0] [Field k]
    [IsAlgClosed k0] [IsAlgClosed k] [CharP k0 p] [CharP k p]
    (e0 : k0 ≃+* k)
    (h0 :
      Nonempty
        (cartanCokernel k0 G ≃+
          ((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1)))) :
    Nonempty
      (cartanCokernel k G ≃+
        ((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1))) := by
  rcases h0 with ⟨h0⟩
  exact ⟨(cartanCokernel_addEquiv_transport_of_ringEquiv (e := e0) (G := G)).trans h0⟩

end CartanCokernelProductRingEquivTransport

section CartanRangeCoordinateRingEquivTransport

variable {p : ℕ}
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Coordinate descriptions of the Cartan image transport across an isomorphism of coefficient
fields. This is the range-level analogue of
`cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_transport_of_ringEquiv`. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_transport_of_ringEquiv
    {k0 k : Type u} [Field k0] [Field k]
    (e0 : k0 ≃+* k)
    (h0 :
      ∃ e : R₀[k0](G) ≃+ (PRegularConjClass G p → ℤ),
        (cartanHom k0 G).range.map e.toAddMonoidHom =
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rcases h0 with ⟨coord0, hcoord0⟩
  let T := finiteRepGrothendieckTransportAddEquiv (e := e0) (G := G)
  refine ⟨T.trans coord0, ?_⟩
  have hT :
      (cartanHom k G).range.map T.toAddMonoidHom =
        (cartanHom k0 G).range := by
    simpa [T] using
      cartanHom_range_map_finiteRepGrothendieckTransportAddEquiv
        (e := e0) (G := G)
  have hcomp :
      (cartanHom k G).range.map (T.trans coord0).toAddMonoidHom =
        ((cartanHom k G).range.map T.toAddMonoidHom).map coord0.toAddMonoidHom := by
    ext f
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨T x, AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases AddSubgroup.mem_map.1 hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hcomp, hT, hcoord0]

end CartanRangeCoordinateRingEquivTransport

/-- Exercise 18-18.3-2 (ring-equiv transport): if the algebraically closed field `k` is isomorphic
to the residue field of the mixed-characteristic local ring `A`, then the distinguished Cartan
matrix of `G` over `k` is the Gram matrix `Eᵀ E` of an integer decomposition matrix. The result is
obtained by transporting the complete simple family and its projective envelopes across the ring
isomorphism `e0 : ResidueField A ≃+* k` to the residue field, where the mixed-characteristic engine
applies. -/
theorem cartanMatrix_transport_to_residueField
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    {k : Type u} [Field k] [IsAlgClosed k]
    (e0 : IsLocalRing.ResidueField A ≃+* k)
    {G : Type u} [Group G] [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope : ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  classical
  haveI : IsCompleteIrreducibleFamily π := hπ_complete
  -- Transport the simple family to the residue field via `e0`.
  set π' : ι → FDRep (IsLocalRing.ResidueField A) G := fun i => fdRepOverRingEquiv e0 (π i) with hπ'
  have hπ'_pairwise : PairwiseNonisomorphic π' :=
    fdRepOverRingEquiv_pairwise e0 π hπ_pairwise
  haveI hπ'_complete : IsCompleteIrreducibleFamily π' :=
    fdRepOverRingEquiv_complete e0 π
  -- Transport the projective envelopes to the residue field.
  set P' : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G :=
    fun i => transProj e0 (P i) with hP'
  have hP'_envelope :
      ∀ i, ∃ f : (P' i).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π' i).ρ,
        f.IsProjectiveEnvelope := by
    intro i
    obtain ⟨f, hf⟩ := hP_envelope i
    exact transProj_envelope e0 (P i) f hf
  -- The residue field is algebraically closed because `k` is.
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField A) e0.symm
  -- Apply the mixed-characteristic engine over the residue field.
  obtain ⟨κ, hκ_fin, hκ_dec, E, hE⟩ :=
    cartanMatrix_source_faithful_gram_eq_of_support
      (A := A) (K := K) (G := G)
      π' hπ'_pairwise hπ'_complete P' hP'_envelope
  refine ⟨κ, hκ_fin, hκ_dec, E, ?_⟩
  -- It now suffices to identify the two Cartan matrices.
  refine Eq.trans ?_ hE
  -- Notation for the four bases.
  set bP := projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
    with hbP
  set bk := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete with hbk
  set bP' := projectiveEnvelope_classes_basis_of_complete_family π' hπ'_pairwise hπ'_complete P'
    hP'_envelope with hbP'
  set bk' := simple_finiteRep_classes_basis_of_complete_family π' hπ'_pairwise hπ'_complete with hbk'
  -- The `ℤ`-linear Grothendieck transport carrying `[V]₀ ↦ [fdRepOverRingEquiv e0 V]₀`.
  set Φ : R₀[k](G) →ₗ[ℤ] R₀[IsLocalRing.ResidueField A](G) :=
    (grothendieckTransport e0 G).toIntLinearMap with hΦ
  -- `Φ` carries the simple basis `bk` to the residue-field simple basis `bk'`.
  have hΦbk : ∀ i, Φ (bk i) = bk' i := by
    intro i
    have h1 : bk i = [π i]₀ := by
      simp [hbk, simple_finiteRep_classes_basis_of_complete_family_apply]
    have h2 : bk' i = [π' i]₀ := by
      simp [hbk', simple_finiteRep_classes_basis_of_complete_family_apply]
    rw [h1, h2, hπ']
    simp [hΦ, grothendieckTransport_class]
  -- Prove the two Cartan matrices agree entrywise.
  ext i j
  -- Reduce both entries to basis coordinates of `toFiniteRep` classes.
  have lhs : cartanMatrix k G bP bk i j = bk.repr [(P j).toFiniteRep]₀ i := by
    rw [hbP, hbk]
    simp [cartanMatrix, LinearMap.toMatrix_apply,
      projectiveEnvelope_classes_basis_of_complete_family_apply,
      cartanHom_projectiveClass_eq]
  have rhs : cartanMatrix (IsLocalRing.ResidueField A) G bP' bk' i j
      = bk'.repr [(P' j).toFiniteRep]₀ i := by
    rw [hbP', hbk']
    simp [cartanMatrix, LinearMap.toMatrix_apply,
      projectiveEnvelope_classes_basis_of_complete_family_apply,
      cartanHom_projectiveClass_eq]
  rw [lhs, rhs]
  -- Transport coordinates of the `k`-side class to the residue-field side.
  have htrans :
      bk.repr [(P j).toFiniteRep]₀ i
        = bk'.repr (Φ [(P j).toFiniteRep]₀) i :=
    (repr_transport_aux bk bk' Φ hΦbk [(P j).toFiniteRep]₀ i).symm
  rw [htrans]
  -- Identify the transported class with the residue-field projective `toFiniteRep` class.
  have hclass :
      Φ [(P j).toFiniteRep]₀ = [(P' j).toFiniteRep]₀ := by
    have hΦval : Φ [(P j).toFiniteRep]₀ = [fdRepOverRingEquiv e0 ((P j).toFiniteRep)]₀ := by
      simp [hΦ, grothendieckTransport_class]
    rw [hΦval, hP']
    refine (finiteRepGrothendieckClass_eq_of_nonempty_iso ?_).symm
    exact ⟨transProj_toFiniteRep_iso e0 (P j)⟩
  rw [hclass]

section AlgClosedResidueGramBridge

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable {ι : Type x}

include p in
/-- Support bridge for Exercise 18-18.3-2: the full mixed-characteristic source model and Chapter
`16` decomposition-matrix identity provide a Gram factorization of the distinguished Cartan matrix
over an arbitrary algebraically closed residue field of characteristic `p`. -/
theorem cartanMatrix_source_faithful_gram_data_via_mixed_character_model_support
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
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
  classical
  obtain ⟨A, instComm, instLocal, instHenselian, instDomain, instDVR, instNoeth, instComplete,
      K, instField, instAlg, instFrac, instCharZero, instRoots, ⟨e0⟩⟩ :=
    existsFullMixedCharacteristicModel_with_all_roots (p := p) (k := k) (G := G)
  letI : CommRing A := instComm
  letI : IsLocalRing A := instLocal
  letI : HenselianLocalRing A := instHenselian
  letI : IsDomain A := instDomain
  letI : IsDiscreteValuationRing A := instDVR
  letI : IsNoetherianRing A := instNoeth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := instComplete
  letI : Field K := instField
  letI : Algebra A K := instAlg
  letI : IsFractionRing A K := instFrac
  letI : CharZero K := instCharZero
  letI : HasEnoughRootsOfUnity K (Monoid.exponent G) := instRoots
  exact
    cartanMatrix_transport_to_residueField
      (A := A) (K := K) (G := G) (k := k) (ι := ι)
      e0 π hπ_pairwise hπ_complete P hP_envelope

end AlgClosedResidueGramBridge

end Representation
