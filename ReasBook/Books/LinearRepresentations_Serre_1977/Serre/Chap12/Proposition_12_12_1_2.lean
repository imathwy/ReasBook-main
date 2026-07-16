import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Corollary_2_2_3_4
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u x

namespace Representation

open CategoryTheory
open scoped Representation BigOperators

section

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 12-12.1-2: the order of a finite group stays nonzero in every
characteristic-zero coefficient field. -/
private theorem nat_card_ne_zero_of_charZero : (Nat.card G : K) ≠ 0 := by
  -- Finite groups have positive cardinality, so its cast cannot vanish in characteristic zero.
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- Helper for Proposition 12-12.1-2: the order of a finite group is invertible in every
characteristic-zero coefficient field. -/
private abbrev nat_card_invertible_of_charZero : Invertible (Nat.card G : K) :=
  invertibleOfNonzero (nat_card_ne_zero_of_charZero (K := K) (G := G))

end

section

variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 12-12.1-2: the order of a finite group is nonzero in `ℂ`. -/
private theorem nat_card_ne_zero_complex : (Nat.card G : ℂ) ≠ 0 := by
  -- The complex numbers also see the positive group cardinality as a nonzero scalar.
  exact_mod_cast Nat.card_pos.ne'

/-- Helper for Proposition 12-12.1-2: the order of a finite group is invertible in `ℂ`. -/
private abbrev nat_card_invertible_complex : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (nat_card_ne_zero_complex (G := G))

end

section

variable {K : Type u} [Field K] [Algebra K ℂ]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Helper for Proposition 12-12.1-2: scalar extension sends a `K`-character to its
coefficientwise image in `ℂ`. -/
private theorem scalarExtension_character_eq_map
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap K ℂ (τ.character g) := by
  -- The scalar-extension trace formula is exactly the coefficientwise transport of characters.
  ext g
  exact LinearMap.trace_baseChange (τ g) ℂ

/-- Helper for Proposition 12-12.1-2: extending coefficients commutes with the normalized
character pairing. -/
private theorem groupFunctionPairingOverField_map_eq
    (φ ψ : G → K) :
    ⟪(fun g ↦ algebraMap K ℂ (φ g)), fun g ↦ algebraMap K ℂ (ψ g)⟫ =
      algebraMap K ℂ ⟪φ, ψ⟫ := by
  -- Expand both pairings and move the algebra map through the finite sum and the averaging scalar.
  letI : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
  have hcardK : (Nat.card G : K) ≠ 0 := nat_card_ne_zero_of_charZero (K := K) (G := G)
  have hcardC : (Nat.card G : ℂ) ≠ 0 := nat_card_ne_zero_complex (G := G)
  simp [Representation.groupFunctionPairingOverField, map_mul, map_sum]

/-- Helper for Proposition 12-12.1-2: every `FDRep` object is canonically isomorphic to the
object rebuilt from its underlying unbundled representation. -/
private noncomputable def fdRepIsoOfRho (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Proposition 12-12.1-2: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V₁} {σ : Representation K G V₂}
    (e : ρ.Equiv σ) (τ : Representation K G W) :
    σ.IntertwiningMap τ ≃ₗ[K] ρ.IntertwiningMap τ :=
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

/-- Helper for Proposition 12-12.1-2: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
private noncomputable def directSumIntertwiningMapEquivPi
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    (Representation.directSum π).IntertwiningMap τ ≃ₗ[K] ∀ i, (π i).IntertwiningMap τ :=
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

/-- Helper for Proposition 12-12.1-2: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. -/
private theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : ρ1.IntertwiningMap ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- A nonzero intertwiner between irreducibles would be bijective, hence a representation
  -- equivalence, contradicting the nonisomorphism hypothesis.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_left
      (fun hf ↦ hρ ⟨f.ofBijective hf⟩)

/-- Helper for Proposition 12-12.1-2: a nonzero intertwiner between two explicit irreducible
representations upgrades to a representation equivalence. -/
private theorem nonempty_equiv_of_intertwiningMap_ne_zero_explicit
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : ρ1.IntertwiningMap ρ2) (hf : f ≠ 0) :
    Nonempty (ρ1.Equiv ρ2) := by
  -- Schur's lemma turns every nonzero intertwiner between irreducibles into an isomorphism.
  refine ⟨f.ofBijective ?_⟩
  exact
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_right hf

/-- Helper for Proposition 12-12.1-2: finite groups over a field admitting an embedding into `ℂ`
admit a complete pairwise nonisomorphic family of irreducible finite-dimensional
representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
  have hcard_ne : (Nat.card G : K) ≠ 0 := nat_card_ne_zero_of_charZero (K := K) (G := G)
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
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep K G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
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
    let f : (leftRegular K G).IntertwiningMap τ.ρ :=
      (Representation.leftRegularMapEquiv τ.ρ).symm v
    have hf_nonzero : f ≠ 0 := by
      intro hf
      apply hv
      have hf' := congrArg (Representation.leftRegularMapEquiv τ.ρ) hf
      simpa [f] using hf'
    let F : (Representation.directSum fun i ↦ (σ i).toRepresentation).IntertwiningMap τ.ρ :=
      intertwiningMapCongrLeft e τ.ρ f
    have hF_nonzero : F ≠ 0 := by
      intro hF
      exact hf_nonzero ((intertwiningMapCongrLeft e τ.ρ).injective hF)
    have hcomponent :
        ∃ i, (directSumIntertwiningMapEquivPi
          (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) ≠ 0 := by
      by_contra hnone
      have hnone' := not_exists.mp hnone
      apply hF_nonzero
      apply (directSumIntertwiningMapEquivPi
        (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ)).injective
      ext i x
      have hi0 :
          (directSumIntertwiningMapEquivPi
            (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) = 0 := by
        by_contra hi0
        exact hnone' i hi0
      simp [hi0]
    rcases hcomponent with ⟨i, hi⟩
    have hi_iso : Nonempty (((σ i).toRepresentation).Equiv τ.ρ) := by
      -- Route correction: use the nonzero coordinate intertwiner directly, instead of first
      -- proving a separate vanishing statement and deriving a contradiction.
      let fi : ((σ i).toRepresentation).IntertwiningMap τ.ρ := directSumIntertwiningMapEquivPi
        (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i
      letI : Representation.IsIrreducible ((σ i).toRepresentation) := by
        exact hσ_irr i
      -- A nonzero coordinate map between irreducibles is already an equivalence by Schur's lemma.
      exact
        @nonempty_equiv_of_intertwiningMap_ne_zero_explicit
          K inferInstance inferInstance G inferInstance inferInstance
          ↥(σ i).toSubmodule inferInstance inferInstance ↥τ inferInstance inferInstance
          ((σ i).toRepresentation) inferInstance τ.ρ inferInstance fi hi
    rcases hi_iso with ⟨eτ⟩
    -- A nonzero coordinate map between irreducibles is an equivalence, hence an `FDRep` isomorphism.
    refine ⟨i, ?_⟩
    exact ⟨(fdRepIsoOfRho (K := K) (G := G) τ).trans eτ.symm.toFDRepIso⟩
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

/-- Helper for Proposition 12-12.1-2: the normalized pairing is additive over finite integer
linear combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Convert the inserted integer multiple into the scalar form used by the pairing API.
      have hzsmul : (a i • χ i : G → K) = (((a i : ℤ) : K) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Proposition 12-12.1-2: pairing a representation-ring element with an irreducible
basis character isolates the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Fintype ι] [CharZero K]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G)) (i : ι) :
    ⟪(x : G → K), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  letI : Invertible (Nat.card G : K) := nat_card_invertible_of_charZero (K := K) (G := G)
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : G → K) := by
    -- Rewrite the basis expansion from `R[K](G)` into the ambient function space.
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
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left (K := K) (s := Finset.univ)
              (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          have hsum :
              ∑ j, ((c j : ℤ) : K) * ⟪(π j).character, (π i).character⟫ =
                ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
            refine Finset.sum_eq_single i ?_ ?_
            · intro j _ hji
              simp [horth hji]
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
          exact hsum

/-- Helper for Proposition 12-12.1-2: the self-intertwining space of a scalar-extended
finite-dimensional representation has positive complex dimension. -/
private theorem finrank_self_intertwiningMap_scalarExtension_pos
    (τ : FDRep K G) [Simple τ] :
    0 <
      Module.finrank ℂ
        ((Representation.scalarExtension (k := ℂ) τ.ρ).IntertwiningMap
          (Representation.scalarExtension (k := ℂ) τ.ρ)) := by
  have hτ_nontriv : Nontrivial τ := by
    by_contra hτ_sub
    letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
    have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero τ hzero
  have hspace_pos : 0 < Module.finrank ℂ (TensorProduct K ℂ τ) := by
    rw [Module.finrank_baseChange (S := K) (R := ℂ) (M' := τ)]
    exact Module.finrank_pos_iff.mpr hτ_nontriv
  have hspace_nontriv : Nontrivial (TensorProduct K ℂ τ) := Module.finrank_pos_iff.mp hspace_pos
  let σC := Representation.scalarExtension (k := ℂ) τ.ρ
  letI : Nontrivial (σC.IntertwiningMap σC) := by
    refine ⟨0, 1, ?_⟩
    intro hone
    obtain ⟨x, hx⟩ := exists_ne (0 : TensorProduct K ℂ τ)
    apply hx
    have hx0 := congrArg (fun f : σC.IntertwiningMap σC ↦ f x) hone
    simpa using hx0.symm
  exact Module.finrank_pos_iff.mpr inferInstance

/-- Helper for Proposition 12-12.1-2: if a complex character comes from `R[K](G)`, then its
coordinates in an irreducible `K`-character basis are all nonnegative. -/
private theorem basis_coefficients_nonnegative
    {ι : Type*} [Fintype ι] [CharZero K]
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G))
    (hχx : ρ.character = fun g ↦ algebraMap K ℂ (x g)) :
    ∀ i,
      0 ≤
        (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i := by
  intro i
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  let σC := Representation.scalarExtension (k := ℂ) (π i).ρ
  let m : ℕ := Module.finrank ℂ (ρ.IntertwiningMap σC)
  let d : ℕ := Module.finrank ℂ (σC.IntertwiningMap σC)
  have hleft :
      algebraMap K ℂ ⟪(x : G → K), (π i).character⟫ = (m : ℂ) := by
    letI : Invertible (Nat.card G : ℂ) := nat_card_invertible_complex (G := G)
    -- Rewrite the mapped pairing as the character pairing over `ℂ`, then use the intertwining
    -- dimension formula for the honest complex representation `ρ`.
    calc
      algebraMap K ℂ ⟪(x : G → K), (π i).character⟫
          = ⟪(fun g ↦ algebraMap K ℂ (x g)), fun g ↦ algebraMap K ℂ ((π i).character g)⟫ := by
              symm
              exact groupFunctionPairingOverField_map_eq (K := K) (φ := (x : G → K))
                (ψ := (π i).character)
      _ = ⟪ρ.character, σC.character⟫ := by
            change
              groupFunctionPairingOverField ℂ (fun g ↦ algebraMap K ℂ (x g))
                (fun g ↦ algebraMap K ℂ (Representation.character (π i).ρ g)) =
                  groupFunctionPairingOverField ℂ ρ.character σC.character
            simp [hχx, σC, scalarExtension_character_eq_map]
      _ = (m : ℂ) := by
            simp [m, σC,
              Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap]
  have hdiag :
      ⟪σC.character, σC.character⟫ = (d : ℂ) := by
    letI : Invertible (Nat.card G : ℂ) := nat_card_invertible_complex (G := G)
    -- The diagonal pairing is the dimension of the scalar-extended endomorphism space.
    simp [σC, d,
      Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap]
  have hcoeff_pair :
      algebraMap K ℂ ⟪(x : G → K), (π i).character⟫ =
        ((c i : ℤ) : ℂ) * ⟪σC.character, σC.character⟫ := by
    -- First isolate the basis coefficient over `K`, then transport the identity to `ℂ`.
    calc
      algebraMap K ℂ ⟪(x : G → K), (π i).character⟫
          = algebraMap K ℂ ((((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫)) := by
              rw [basis_coefficient_pairing_eq (K := K) (π := π) hπ_pairwise hπ_complete x i]
      _ = ((c i : ℤ) : ℂ) * algebraMap K ℂ ⟪(π i).character, (π i).character⟫ := by
            simp [map_mul]
      _ = ((c i : ℤ) : ℂ) * ⟪σC.character, σC.character⟫ := by
            congr 1
            calc
              algebraMap K ℂ ⟪(π i).character, (π i).character⟫
                  = ⟪(fun g ↦ algebraMap K ℂ ((π i).character g)),
                      fun g ↦ algebraMap K ℂ ((π i).character g)⟫ := by
                        symm
                        exact groupFunctionPairingOverField_map_eq (K := K)
                          (φ := (π i).character) (ψ := (π i).character)
              _ = ⟪σC.character, σC.character⟫ := by
                    change
                      groupFunctionPairingOverField ℂ
                        (fun g ↦ algebraMap K ℂ (Representation.character (π i).ρ g))
                        (fun g ↦ algebraMap K ℂ (Representation.character (π i).ρ g)) =
                          groupFunctionPairingOverField ℂ σC.character σC.character
                    simp [σC, scalarExtension_character_eq_map]
  have hmain : (m : ℂ) = ((c i : ℤ) : ℂ) * (d : ℂ) := by
    -- Compare the mapped left pairing with the diagonal pairing identity.
    calc
      (m : ℂ) = algebraMap K ℂ ⟪(x : G → K), (π i).character⟫ := by
        simpa using hleft.symm
      _ = ((c i : ℤ) : ℂ) * ⟪σC.character, σC.character⟫ := hcoeff_pair
      _ = ((c i : ℤ) : ℂ) * (d : ℂ) := by rw [hdiag]
  have hd_pos : 0 < d := by
    letI : Simple (π i) := hπ_complete.isSimple i
    simpa [d, σC] using
      finrank_self_intertwiningMap_scalarExtension_pos (K := K) (G := G) (π i)
  have hm_nonneg : (0 : ℝ) ≤ m := by
    exact_mod_cast Nat.zero_le m
  have hd_real_pos : (0 : ℝ) < d := by
    exact_mod_cast hd_pos
  have hreal : (m : ℝ) = (c i : ℝ) * d := by
    -- Taking real parts turns the complex equality into an ordered real equality.
    simpa using congrArg Complex.re hmain
  have hc_real_nonneg : (0 : ℝ) ≤ c i := by
    by_contra hcneg
    have hcneg' : (c i : ℝ) < 0 := lt_of_not_ge hcneg
    nlinarith
  exact_mod_cast hc_real_nonneg

/-- Helper for Proposition 12-12.1-2: every finite sum of honest `K`-characters is again the
character of a finite-dimensional `K`-representation. -/
private theorem exists_fdRep_with_character_eq_sum
    {ι : Type*} (s : Finset ι) (π : ι → FDRep K G) :
    ∃ τ : FDRep K G, τ.character = s.sum fun i ↦ (π i).character := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨FDRep.of (Representation.trivial K G (Fin 0 → K)), ?_⟩
      -- The trivial action on the zero-dimensional space has zero trace everywhere.
      ext g
      simp [FDRep.character, Representation.trivial]
  | insert i s hi ih =>
      rcases ih with ⟨τ, hτ⟩
      refine ⟨FDRep.of (Representation.prod (π i).ρ τ.ρ), ?_⟩
      -- Add one more summand and use the binary direct-sum character formula.
      calc
        (FDRep.of (Representation.prod (π i).ρ τ.ρ)).character =
            (Representation.prod (π i).ρ τ.ρ).character := rfl
        _ = Representation.character (π i).ρ + Representation.character τ.ρ := by
            exact Representation.char_prod (π i).ρ τ.ρ
        _ = (π i).character + τ.character := rfl
        _ = (π i).character + s.sum (fun j ↦ (π j).character) := by
            rw [hτ]
        _ = (insert i s).sum (fun j ↦ (π j).character) := by
            rw [Finset.sum_insert hi]

/-- Helper for Proposition 12-12.1-2: a finite nonnegative integral combination of irreducible
`K`-characters is the character of an honest finite-dimensional `K`-representation. -/
private theorem exists_fdRep_with_character_eq_repr_sum
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep K G) (c : ι → ℤ) (hc : ∀ i, 0 ≤ c i) :
    ∃ τ : FDRep K G, τ.character = ∑ i, c i • (π i).character := by
  let n : ι → ℕ := fun i ↦ Int.toNat (c i)
  let π' : (Σ i, Fin (n i)) → FDRep K G := fun j ↦ π j.1
  obtain ⟨τ, hτ⟩ :=
    exists_fdRep_with_character_eq_sum (K := K) (G := G) (s := Finset.univ) π'
  refine ⟨τ, ?_⟩
  -- Replicate each irreducible summand `c i` times and collapse the sigma-indexed sum.
  calc
    τ.character = ∑ j : Σ i, Fin (n i), (π' j).character := hτ
    _ = ∑ i, ∑ _ : Fin (n i), (π i).character := by
          simpa [π'] using
            (Fintype.sum_sigma (fun j : Σ i, Fin (n i) ↦ (π' j).character))
    _ = ∑ i, n i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [n]
    _ = ∑ i, c i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [show c i = Int.ofNat (n i) by
            simpa [n] using (Int.toNat_of_nonneg (hc i)).symm]
          simp

/-- Helper for Proposition 12-12.1-2: if a complex character agrees with the scalar extension of
an honest finite-dimensional `K`-representation, then the complex representation is realizable
over `K`. -/
private theorem isRealizableOver_of_scalarExtension_character_eq
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (τ : Representation K G W)
    (hchar : (Representation.scalarExtension τ).character = ρ.character) :
    IsRealizableOver K ρ := by
  letI : Invertible (Nat.card G : ℂ) := nat_card_invertible_complex (G := G)
  -- Equal complex characters force an equivariant equivalence after scalar extension.
  have hτ_equiv : Nonempty ((Representation.scalarExtension τ).Equiv ρ) := by
    exact (character_eq_iff_nonempty_equiv (Representation.scalarExtension τ) ρ).mp hchar
  -- Package the `K`-model together with the scalar-extension equivalence witness.
  exact ⟨W, inferInstance, inferInstance, inferInstance, τ, hτ_equiv⟩

-- Proof sketch: the forward implication is immediate from the definition of
-- `R[K](G)`, because a `K`-realization contributes a generator of the mapped
-- character ring. For the converse, one should expand the complex character in an
-- irreducible `K`-character basis from Proposition `12-12.1-1`, prove the basis
-- coefficients are nonnegative via character pairings, realize that finite
-- nonnegative combination over `K`, and then compare complex characters.
/-- Proposition 12-12.1-2: a finite-dimensional complex representation of `G` is realizable over
`K` exactly when its character belongs to Serre's `R_K(G)`, viewed inside the complex-valued
class functions by the pointwise algebra map `K → ℂ`. -/
theorem isRealizableOver_iff_character_mem_characterRingOverFieldInExtension
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] :
    IsRealizableOver K ρ ↔
      ρ.character ∈ characterRingOverFieldInExtension K ℂ G := by
  constructor
  · intro hρ
    -- Extract a `K`-model whose coefficientwise image is the complex character of `ρ`.
    rcases exists_character_eq_of_isRealizableOver (k₀ := K) hρ with
      ⟨W, _hWAdd, _hWModule, _hWFinite, ρK, hchar⟩
    -- That source character already lies in `R[K](G)`, so its image lies in the extension ring.
    have hρK_mem : ρK.character ∈ R[K](G) := by
      simpa using
        (rep_character_mem_characterRingOverField (K := K) (G := G) (Rep.of ρK))
    refine Subalgebra.mem_map.mpr ?_
    refine ⟨ρK.character, hρK_mem, ?_⟩
    ext g
    simpa using (congrFun hchar g).symm
  · intro hχ
    rcases Subalgebra.mem_map.mp hχ with ⟨χK, hχK, hχK_map⟩
    have hχK_map' : ρ.character = fun g ↦ algebraMap K ℂ (χK g) := by
      simpa using hχK_map.symm
    letI : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
    obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
      exists_complete_pairwise_nonisomorphic_irreducible_family (K := K) (G := G)
    letI : Fintype ι := hι
    let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
    let x : R[K](G) := ⟨χK, hχK⟩
    let c := b.repr x
    have hc_nonneg : ∀ i, 0 ≤ c i := by
      -- Pairing against each irreducible basis character identifies the coefficient with a
      -- nonnegative intertwining-space multiplicity.
      simpa [b, c, x] using
        basis_coefficients_nonnegative (K := K) (ρ := ρ) (π := π)
          hπ_pairwise hπ_complete x hχK_map'
    obtain ⟨τ, hτ_char⟩ :=
      exists_fdRep_with_character_eq_repr_sum (K := K) (G := G) π c hc_nonneg
    have hx_expand :
        ∑ i, c i • (π i).character = (x : G → K) := by
      -- Rewrite the basis expansion of `x` as an equality of ordinary `K`-valued functions.
      simpa [b, c, x, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using
        congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x)
    have hτ_map :
        (Representation.scalarExtension τ.ρ).character = ρ.character := by
      -- The realized `K`-model has character `χK`, so its scalar extension has the same complex
      -- character as `ρ`.
      calc
        (Representation.scalarExtension τ.ρ).character =
            fun g ↦ algebraMap K ℂ (τ.character g) := scalarExtension_character_eq_map τ.ρ
        _ = fun g ↦ algebraMap K ℂ ((x : G → K) g) := by
              rw [hτ_char, hx_expand]
        _ = ρ.character := by
              simpa [x] using hχK_map'.symm
    -- The final bridge is now a reusable character-equality criterion for realizability.
    exact isRealizableOver_of_scalarExtension_character_eq (K := K) (G := G) (ρ := ρ) τ.ρ hτ_map

end

end Representation
