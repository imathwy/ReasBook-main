import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_12_12_2_7 (from Chap12) -/
noncomputable section

open scoped Representation
open scoped BigOperators

universe u x

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type u} [Field L] [CharZero L] [Algebra K L] [FiniteDimensional K L]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local instance : Fintype G := Fintype.ofFinite G

omit [Finite G] in
/-- Helper for Exercise 12-12.2-7: scalar extension transports a character by applying the
coefficient map to each value. -/
private theorem scalarExtension_character_eq_map_local
    {F : Type u} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F G V) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap F E (τ.character g) := by
  -- Trace commutes with base change, so scalar extension only changes coefficients.
  ext g
  exact LinearMap.trace_baseChange (τ g) E

omit [Finite G] in
/-- Helper for Exercise 12-12.2-7: coefficientwise extension of a virtual character stays inside
the target character ring. -/
private theorem map_mem_characterRingOverField_local
    {F : Type u} [Field F]
    {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    (χ : G → F)
    (hχ : χ ∈ R[F](G)) :
    (f.compLeft G) χ ∈ R[E](G) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  -- Check the claim on honest characters and then extend across the algebra generation.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    let ρE : Rep E G := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (f.compLeft G) ρ.ρ.character = ρE.ρ.character := by
      -- The generator becomes the character of the scalar-extended representation.
      ext g
      simpa [ρE] using
        (congrFun (scalarExtension_character_eq_map_local (E := E) (τ := ρ.ρ)) g).symm
    exact hchar.symm ▸ by
      simpa using
        (Representation.rep_character_mem_characterRingOverField
          (K := E) (G := G) (Rep.of (Representation.scalarExtension ρ.ρ)))
  · intro n
    change (fun _ : G ↦ f (algebraMap ℤ F n)) ∈ R[E](G)
    have hconst : (fun _ : G ↦ f (algebraMap ℤ F n)) = algebraMap ℤ (G → E) n := by
      ext g
      simpa using (f.commutes n)
    rw [hconst]
    exact (R[E](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).mul_mem hφ hψ

/-- Helper for Exercise 12-12.2-7: every `FDRep` object is canonically isomorphic to the object
rebuilt from its underlying unbundled representation. -/
private noncomputable def fdRepIsoOfRho_local (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Exercise 12-12.2-7: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft_local
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V₁} {σ : Representation K G V₂}
    (e : ρ.Equiv σ) (τ : Representation K G W) :
    Representation.IntertwiningMap σ τ ≃ₗ[K] Representation.IntertwiningMap ρ τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-7: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
private noncomputable def directSumIntertwiningMapEquivPi_local
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    Representation.IntertwiningMap (Representation.directSum π) τ ≃ₗ[K]
      ∀ i, Representation.IntertwiningMap (π i) τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-7: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. -/
private theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- A nonzero intertwiner between irreducibles would be bijective, hence a representation
  -- equivalence, contradicting the nonisomorphism hypothesis.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_left
      (fun hf ↦ hρ ⟨f.ofBijective hf⟩)

/-- Helper for Exercise 12-12.2-7: choose a finite complete pairwise nonisomorphic family of
simple finite-dimensional `K`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular K G)
  let e :
      (Representation.directSum fun i ↦ (σ i).toRepresentation).Equiv (leftRegular K G) :=
    directSum_equiv_of_iSupIndep_of_iSup_eq_top (ρ := leftRegular K G) σ hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨f⟩
            exact ⟨f.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨f⟩
            rcases hjk with ⟨g⟩
            exact ⟨f.trans g⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep K G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot label isomorphic simple summands.
    intro q q' hqq' hIso
    rcases hIso with ⟨f⟩
    have hclasses :
        (⟦Quotient.out q⟧ : Quotient r) = ⟦Quotient.out q'⟧ := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso f)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : Quotient r) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hσ_complete :
      ∀ (τ : FDRep K G) [Simple τ], ∃ i : κ, Nonempty (τ ≅ FDRep.of ((σ i).toRepresentation)) := by
    intro τ _
    letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero τ hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : τ)
    let f : Representation.IntertwiningMap (leftRegular K G) τ.ρ :=
      (Representation.leftRegularMapEquiv τ.ρ).symm v
    have hf_nonzero : f ≠ 0 := by
      intro hf
      apply hv
      have hf' := congrArg (Representation.leftRegularMapEquiv τ.ρ) hf
      simpa [f] using hf'
    let F :
        Representation.IntertwiningMap
          (Representation.directSum fun i ↦ (σ i).toRepresentation) τ.ρ :=
      intertwiningMapCongrLeft_local (K := K) (G := G) e τ.ρ f
    have hF_nonzero : F ≠ 0 := by
      intro hF
      exact hf_nonzero ((intertwiningMapCongrLeft_local (K := K) (G := G) e τ.ρ).injective hF)
    have hcomponent :
        ∃ i, (directSumIntertwiningMapEquivPi_local
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) ≠ 0 := by
      by_contra hnone
      have hnone' := not_exists.mp hnone
      apply hF_nonzero
      apply (directSumIntertwiningMapEquivPi_local
        (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ)).injective
      ext i x
      have hi0 :
          (directSumIntertwiningMapEquivPi_local
            (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) = 0 := by
        simpa using hnone' i
      simp [hi0]
    rcases hcomponent with ⟨i, hi⟩
    have hi_iso : Nonempty (((σ i).toRepresentation).Equiv τ.ρ) := by
      by_contra hnot
      let ρ1 := (σ i).toRepresentation
      let ρ2 := τ.ρ
      let fi : Representation.IntertwiningMap ((σ i).toRepresentation) τ.ρ :=
        directSumIntertwiningMapEquivPi_local
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i
      letI : Representation.IsIrreducible ((σ i).toRepresentation) := by
        exact hσ_irr i
      have hnot' : ¬ Nonempty (Representation.Equiv ((σ i).toRepresentation) τ.ρ) := hnot
      have hnot'' : ¬ Nonempty (ρ1.Equiv ρ2) := by
        simpa [ρ1, ρ2] using hnot'
      -- In the nonisomorphic case Schur's lemma forces the chosen coordinate intertwiner to vanish.
      have hfi_zero : fi = 0 := by
        let f' : ρ1.IntertwiningMap ρ2 := fi
        simpa [ρ1, ρ2, f'] using
          intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
            (K := K) (G := G) (V1 := ↥(σ i).toSubmodule) (V2 := ↥τ)
            (ρ1 := ρ1) (ρ2 := ρ2) (f := f') hnot''
      exact hi hfi_zero
    rcases hi_iso with ⟨eτ⟩
    -- A nonzero coordinate map between irreducibles yields the desired `FDRep` isomorphism.
    refine ⟨i, ?_⟩
    exact ⟨(fdRepIsoOfRho_local (K := K) (G := G) τ).trans eτ.symm.toFDRepIso⟩
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := ?_
        exists_iso := ?_ }
    · intro q
      letI : Representation.IsIrreducible (π q).ρ := by
        simpa [π] using hσ_irr (Quotient.out q)
      exact FDRep.simple_of_isIrreducible (π q)
    · intro τ _
      obtain ⟨i, hi⟩ := hσ_complete τ
      refine ⟨(⟦i⟧ : Quotient r), ?_⟩
      have hout :
          Nonempty (((σ (Quotient.out (⟦i⟧ : Quotient r))).toRepresentation).Equiv
            ((σ i).toRepresentation)) := by
        exact Quotient.exact (Quotient.out_eq (⟦i⟧ : Quotient r))
      rcases hout with ⟨hout⟩
      rcases hi with ⟨hi⟩
      simpa [π] using ⟨hi.trans hout.toFDRepIso.symm⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 12-12.2-7: conjugating a representation by a linear equivalence preserves
the representation law at `1`. -/
private theorem conjRepresentation_map_one_local
    {V : Type*} {W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Exercise 12-12.2-7: conjugating a representation by a linear equivalence preserves
multiplication. -/
private theorem conjRepresentation_map_mul_local
    {V : Type*} {W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-7: every finite-dimensional representation can be transported onto
the canonical finite free module of the same dimension. -/
private def finBasisRepresentation_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) : Representation K G (Fin (Module.finrank K V) → K) :=
  let e := (Module.finBasis K V).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conjRepresentation_map_one_local (K := K) (G := G) e ρ
    map_mul' := conjRepresentation_map_mul_local (K := K) (G := G) e ρ }

/-- Helper for Exercise 12-12.2-7: transporting through a chosen finite basis gives an equivalent
representation. -/
private def finBasisRepresentationEquiv_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ρ.Equiv (finBasisRepresentation_local (K := K) (G := G) ρ) :=
  Representation.Equiv.mk (Module.finBasis K V).equivFun fun g => by
    ext x i
    simp [finBasisRepresentation_local, LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-7: transporting a representation through a finite basis does not
change its character. -/
private theorem character_finBasisRepresentation_eq_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    (finBasisRepresentation_local (K := K) (G := G) ρ).character g = ρ.character g := by
  -- Conjugation preserves trace, so the character is unchanged after moving to coordinates.
  simpa [finBasisRepresentation_local, Representation.character] using
    (LinearMap.trace_conj' (ρ g) ((Module.finBasis K V).equivFun))

omit [CharZero K] in
/-- Helper for Exercise 12-12.2-7: the normalized pairing distributes over finite integer linear
combinations in the left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left_local
    {ι : Type*}
    (s : Finset ι)
    (a : ι → ℤ)
    (χ : ι → G → K)
    (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      have hzsmul : (a i • χ i : G → K) = (((a i : ℤ) : K) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      -- Rewrite the inserted summand into the scalar form expected by the pairing API.
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.2-7: pairing a character-ring element with an irreducible basis
character isolates the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G))
    (i : ι) :
    ⟪(x : G → K), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : G → K) := by
    -- Expand the basis expression of `x` inside the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x)
  have horth :
      Pairwise fun j k ↦
        ⟪(π j).character, (π k).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  calc
    ⟪(x : G → K), (π i).character⟫
        = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
            -- Replace `x` by its irreducible-basis expansion.
            simpa [hx] using
              congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character)
                hx.symm
    _ = ∑ j, ((c j : ℤ) : K) * ⟪(π j).character, (π i).character⟫ := by
          -- The pairing is linear across the basis expansion.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left_local (K := K) (s := Finset.univ)
              (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            simp [horth hji]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- Helper for Exercise 12-12.2-7: the self-pairing of an irreducible character is nonzero. -/
private theorem self_pairing_character_ne_zero_local
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let n : ℕ := Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ)
  have hn_pos : 0 < n := by
    have hV_nontriv : Nontrivial V := by
      by_contra hV_sub
      letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
      have hzero : (𝟙 V : V ⟶ V) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero V hzero
    letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
      refine ⟨0, 1, ?_⟩
      intro hone
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hx0 := congrArg (fun f : Representation.IntertwiningMap V.ρ V.ρ ↦ f x) hone
      exact hx (by simpa using hx0.symm)
    simpa [n] using
      (Module.finrank_pos_iff.mpr
        (inferInstance : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ)))
  have hpair :
      ⟪V.character, V.character⟫ = (n : K) := by
    -- The self-pairing is the dimension of the endomorphism space.
    simpa [n] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        K V.ρ V.ρ)
  intro hzero
  have hn_zero : (n : K) = 0 := by
    simpa [hpair] using hzero
  exact Nat.cast_ne_zero.mpr hn_pos.ne' hn_zero

/-- Helper for Exercise 12-12.2-7: quasisplitness over `L` turns an admissible algebraic-closure
witness into the extension-relative witness needed for the trace argument over `L/K`. -/
private theorem scaled_character_mem_overlineCharacterRingInExtension_of_isQuasisplit
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G))
    (hL : IsQuasisplitGroupAlgebra L G) :
    (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ overlineCharacterRingInExtension K L := by
  let χ : G → K := (((m : ℕ) : K)⁻¹) • ρ.ρ.character
  let ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift (R := K)
  let ιZ : AlgebraicClosure K →ₐ[ℤ] AlgebraicClosure L := ι.restrictScalars ℤ
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := ι.toRingHom.toAlgebra
  have hχ_closure :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ ∈
        R[AlgebraicClosure K](G) := by
    -- Unpack the source-facing `\overline{R}_K(G)` hypothesis.
    simpa [χ] using
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).1 hscaled
  have hχ_lifted :
      (ιZ.compLeft G)
          (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) ∈
        R[AlgebraicClosure L](G) :=
    map_mem_characterRingOverField_local
      (F := AlgebraicClosure K) (E := AlgebraicClosure L) (f := ιZ)
      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) hχ_closure
  have hχL_overline :
      ((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ ∈ R̄[L](G) := by
    -- The `L`-valued image of `χ` becomes an honest algebraic-closure character after lifting.
    rw [mem_overlineCharacterRingInExtension_iff L (AlgebraicClosure L)
      (((IsScalarTower.toAlgHom ℤ K L).compLeft G) χ)]
    convert hχ_lifted using 1
    ext g
    simp [ιZ, IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) (χ g)]
  have hEqL : R[L](G) = R̄[L](G) :=
    (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra
      (K := L) (G := G)).2 hL
  -- Replace `\overline{R}_L(G)` by `R_L(G)` and repackage the result over the base field `K`.
  exact (mem_overlineCharacterRingInExtension_iff K L χ).2 <| by
    simpa [hEqL, χ] using hχL_overline

/-- Helper for Exercise 12-12.2-7: once a multiple of the scaled irreducible character lands in
`R_K(G)`, coefficient comparison forces the denominator to divide that multiple. -/
private theorem denominator_dvd_of_zsmul_scaled_character_mem_characterRing
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (d : ℕ)
    (hmem : ((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K) ∈ R[K](G)) :
    (m : ℕ) ∣ d := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  letI : FiniteDimensional K ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  let ρfin : Representation K G (Fin (Module.finrank K ρ) → K) :=
    finBasisRepresentation_local (K := K) (G := G) ρ.ρ
  have hρfin_irr : ρfin.IsIrreducible := by
    exact isIrreducible_of_nonempty_equiv
      ⟨finBasisRepresentationEquiv_local (K := K) (G := G) ρ.ρ⟩
  have hρfin_char : ρfin.character = ρ.ρ.character := by
    ext g
    simpa [ρfin] using
      character_finBasisRepresentation_eq_local (K := K) (G := G) ρ.ρ g
  obtain ⟨i, hi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete ρfin hρfin_irr
  rcases hi with ⟨e⟩
  let x : R[K](G) := ⟨((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K), hmem⟩
  let c : ℤ :=
    (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i
  have hzsmul :
      ((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K) =
        ((((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) • ρ.ρ.character) := by
    ext g
    simp [zsmul_eq_mul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hpair_scaled :
      ⟪(x : G → K), (π i).character⟫ =
        (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
          ⟪(π i).character, (π i).character⟫ := by
    -- The chosen basis vector is isomorphic to `ρ`, so the pairing only sees the scalar factor.
    calc
      ⟪(x : G → K), (π i).character⟫
          = ⟪((((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) • ρ.ρ.character),
              (π i).character⟫ := by
                simpa [x, hzsmul]
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) * ⟪ρ.ρ.character, (π i).character⟫ := by
            rw [groupFunctionPairing_smul_left]
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := by
              congr 1
              calc
                ⟪ρ.ρ.character, (π i).character⟫ = ⟪ρfin.character, (π i).character⟫ := by
                  simpa using
                    congrArg
                      (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character)
                      hρfin_char.symm
                _ = ⟪(π i).character, (π i).character⟫ := by
                  simpa [ρfin] using
                    congrArg
                      (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character)
                      (FDRep.char_iso e)
  have hpair_basis :
      ⟪(x : G → K), (π i).character⟫ =
        ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
    -- The irreducible basis expansion identifies the same pairing with the `i`th coefficient.
    simpa [c] using
      basis_coefficient_pairing_eq_local
        (K := K) (π := π) hπ_pairwise hπ_complete x i
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact self_pairing_character_ne_zero_local (K := K) (V := π i)
  have hcoeff :
      ((c : ℤ) : K) = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
    apply mul_right_cancel₀ hself_ne
    calc
      ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫
          = ⟪(x : G → K), (π i).character⟫ := by
              simpa using hpair_basis.symm
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := hpair_scaled
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmulK :
      ((m : ℕ) : K) * ((c : ℤ) : K) = ((d : ℤ) : K) := by
    -- Multiply by the denominator to remove the inverse.
    calc
      ((m : ℕ) : K) * ((c : ℤ) : K)
          = ((m : ℕ) : K) * (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
              rw [hcoeff]
      _ = ((d : ℤ) : K) := by
            field_simp [hmK_ne]
  have hmulZ : ((m : ℤ) * c : ℤ) = d := by
    exact_mod_cast hmulK
  have hdivZ : ((m : ℤ) : ℤ) ∣ (d : ℤ) := ⟨c, hmulZ.symm⟩
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

-- Source/core/bridge triage: this theorem is `bridge/view`. Its primitive data are a single
-- irreducible `K`-representation `ρ`, a positive integer `m` whose source-facing scaled
-- character `((m : K)⁻¹) • χ_ρ` lies in `R̄[K](G)`, and the quasisplitness hypothesis on `L[G]`.
-- The source-facing family statement below is derived from this owner-level bridge by applying it
-- to the `i`th member of a complete irreducible family.
-- Proof sketch: by Corollary `12-12.2-2`, quasisplitness of `L[G]` identifies the image of
-- `R_L(G)` with `\overline{R}_L(G)`. Apply the finite-extension trace argument from Section
-- `12.1` to the extension `L/K`, then express the resulting index comparison in the basis of
-- scaled irreducible characters given by Proposition `12-12.2-1`; for an irreducible
-- representation, the coefficient comparison shows that `m` divides `[L : K]`.
/-- Auxiliary bridge for Exercise 12-12.2-7: if the scaled character
`((m : ℕ) : K)⁻¹ • χ_ρ` of an irreducible `K`-representation lies in `\overline{R}_K(G)` and
`L[G]` is quasisplit, then `m` divides `[L : K]`. -/
theorem scaled_character_denominator_dvd_extensionDegree_of_isQuasisplitGroupAlgebra
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G))
    (hL : IsQuasisplitGroupAlgebra L G) :
    (m : ℕ) ∣ Module.finrank K L := by
  let χKL : overlineCharacterRingInExtension K L :=
    ⟨(((m : ℕ) : K)⁻¹) • ρ.ρ.character,
      scaled_character_mem_overlineCharacterRingInExtension_of_isQuasisplit
        (ρ := ρ) (m := m) hscaled hL⟩
  have htrace :
      ((Module.finrank K L : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K) ∈ R[K](G) := by
    -- Quasisplitness over `L` makes the scaled character eligible for the finite-extension trace
    -- argument.
    simpa [χKL] using
      extensionDegree_smul_mem_characterRingOverField
        (K := K) (L := L) (G := G) χKL
  -- The irreducible coefficient comparison now forces the denominator to divide `[L : K]`.
  exact
    denominator_dvd_of_zsmul_scaled_character_mem_characterRing
      (ρ := ρ) (m := m) (d := Module.finrank K L) htrace

-- Source/core/bridge triage: this theorem is `bridge/view`. Its primitive data are a complete
-- irreducible family `π` in the canonical owner `FDRep K G`, the corresponding denominator data
-- `m`, and the quasisplitness hypothesis on `L[G]`. Since the hypotheses remain at the
-- source-facing scaled-character layer rather than the Chapter 12 owner `HasSchurIndex`, the
-- theorem stays a family-level bridge statement instead of becoming the source-facing Schur-index
-- API. The actual divisibility step is the single-representation bridge theorem above; the
-- complete-family owner is used only to derive irreducibility of the chosen member `π i`.
/-- Exercise 12-12.2-7, family bridge form: for a complete irreducible family in `FDRep K G`
whose scaled characters satisfy the denominator hypothesis of Proposition `12-12.2-1`, if the
group algebra `L[G]` is quasisplit for a finite extension `L/K`, then each denominator `mᵢ`
divides the extension degree `[L : K]`. -/
theorem
    scaled_character_denominator_dvd_extensionDegree_of_complete_irreducible_family
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (m : ι → ℕ+)
    (hscaled : ∀ i, FDRep.schurScaledCharacter (π i) (m i) ∈ R̄[K](G))
    (hL : IsQuasisplitGroupAlgebra L G)
    (i : ι) :
    (m i : ℕ) ∣ Module.finrank K L := by
  letI := hπ_complete.isSimple i
  letI : (Rep.of (π i).ρ).ρ.IsIrreducible := by
    simpa using (FDRep.isIrreducible_of_simple (π i))
  exact
    scaled_character_denominator_dvd_extensionDegree_of_isQuasisplitGroupAlgebra
      (Rep.of (π i).ρ) (m i) (by simpa [FDRep.schurScaledCharacter] using hscaled i) hL

end

end Representation
