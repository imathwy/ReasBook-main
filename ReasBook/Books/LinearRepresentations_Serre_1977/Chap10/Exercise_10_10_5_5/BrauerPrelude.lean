import LinearRepresentations_Serre_1977.Chap10.Exercise_10_10_5_5.AutoSplit
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_2_1

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

/-- A chosen representative of a conjugacy class. -/
noncomputable def conjClassRepresentative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

/-- The chosen representative belongs to its conjugacy class. -/
theorem conjClassRepresentative_mk (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Helper for Exercise 10-10.5-5: the quotient of a finite group by a normal subgroup is finite. -/
theorem quotientFinite (H : Subgroup G) [H.Normal] : Finite (G ⧸ H) := by
  infer_instance

/-- Helper for Exercise 10-10.5-5: the quotient of a finite group by a normal subgroup has a
fintype structure. -/
noncomputable abbrev quotientFintype (H : Subgroup G) [H.Normal] : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

/-- Helper for Exercise 10-10.5-5: a finite commutative group has finitely many complex degree-`1`
characters. -/
theorem linearCharacterFinite
    {A : Type u} [CommGroup A] [Finite A] :
    Finite (A →* ℂˣ) := by
  let eDual : (A →* ℂˣ) ≃* A :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := A) (M := ℂ))
  exact Finite.of_equiv A eDual.symm.toEquiv

/-- Helper for Exercise 10-10.5-5: the degree-`1` complex characters of a finite commutative
group form a finite type. -/
noncomputable abbrev linearCharacterFintype
    {A : Type u} [CommGroup A] [Finite A] :
    Fintype (A →* ℂˣ) := Fintype.ofFinite (A →* ℂˣ)

attribute [local instance] quotientFintype linearCharacterFintype

/-- Helper for Exercise 10-10.5-5: on a finite commutative group, the sum of all degree-`1`
complex characters vanishes away from the identity. -/
theorem commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one
    {A : Type u} [CommGroup A] [Finite A] {a : A} (ha : a ≠ 1) :
    ∑ χ : A →* ℂˣ, (χ a : ℂ) = 0 := by
  classical
  obtain ⟨φ, hφa⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := A) (M := ℂ) ha
  let e : (A →* ℂˣ) ≃ (A →* ℂˣ) :=
    { toFun := fun χ ↦ φ * χ
      invFun := fun χ ↦ φ⁻¹ * χ
      left_inv := by
        intro χ
        simp
      right_inv := by
        intro χ
        simp }
  have hsum :
      ∑ χ : A →* ℂˣ, ((φ * χ) a : ℂ) =
        ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
    exact Fintype.sum_equiv e
      (fun χ : A →* ℂˣ ↦ ((φ * χ) a : ℂ))
      (fun χ : A →* ℂˣ ↦ (χ a : ℂ))
      (fun χ ↦ rfl)
  have hmul :
      ∑ χ : A →* ℂˣ, ((φ * χ) a : ℂ) =
        (φ a : ℂ) * ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
    -- Pull the fixed scalar `φ(a)` out of the finite sum.
    simp [Finset.mul_sum]
  have hfactor :
      (((φ a : ℂ) - 1) * ∑ χ : A →* ℂˣ, (χ a : ℂ)) = 0 := by
    -- Compare the permutation-invariant sum with the same sum after multiplication by `φ(a)`.
    calc
      (((φ a : ℂ) - 1) * ∑ χ : A →* ℂˣ, (χ a : ℂ)) =
          (φ a : ℂ) * ∑ χ : A →* ℂˣ, (χ a : ℂ) -
            ∑ χ : A →* ℂˣ, (χ a : ℂ) := by
              ring
      _ = 0 := by
        rw [← hmul, hsum, sub_self]
  have hne : ((φ a : ℂ) - 1) ≠ 0 := by
    intro hzero
    have hcast : (φ a : ℂ) = 1 := sub_eq_zero.mp hzero
    apply hφa
    ext
    simpa using hcast
  exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Exercise 10-10.5-5: the regular character of a finite commutative group is the
sum of all of its degree-`1` complex characters. -/
theorem commGroup_regularCharacter_eq_sum_linearCharacters
    {A : Type u} [CommGroup A] [Finite A] :
    (leftRegular ℂ A).character = ∑ χ : A →* ℂˣ, χ.toRepresentation.character := by
  let _ : Fintype A := Fintype.ofFinite A
  ext a
  by_cases ha : a = 1
  · subst ha
    -- At the identity, every linear character has value `1`, so the sum is the number of them.
    rw [Representation.leftRegular_character_one, Finset.sum_apply]
    have hcard : Fintype.card A = Fintype.card (A →* ℂˣ) := by
      simpa using
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := A) (M := ℂ)).symm
    simp [hcard]
  · -- Away from the identity, the character sum vanishes by the translation argument above.
    rw [Representation.leftRegular_character_eq_zero_of_ne_one ha, Finset.sum_apply]
    simpa using
      (commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one (A := A) ha).symm

namespace Subgroup

/-- Helper for Exercise 10-10.5-5: evaluating an induced class function at the identity multiplies
the subgroup value at `1` by the subgroup index. -/
theorem inducedClassFunction_one_eq_index_mul_value
    (H : Subgroup G) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  classical
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  have h1H : (1 : G) ∈ H := by
    simp
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
    exact_mod_cast H.card_mul_index.symm
  have hχ1 : χ ⟨1, h1H⟩ = χ 1 := rfl
  have hsum0 : ∑ s : G, χ 1 = (Nat.card G : ℂ) * χ 1 := by
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hsum :
      ∑ s : G,
        (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
          (Nat.card G : ℂ) * χ 1 := by
    -- Every summand at the identity is the same subgroup value `χ 1`.
    have hterm :
        ∀ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) = χ 1 := by
      intro s
      have hs : s⁻¹ * (1 : G) * s ∈ H := by
        simpa using h1H
      simp [hs, hχ1]
    calc
      ∑ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
          = ∑ s : G, χ 1 := by
              simpa using
                (Fintype.sum_congr
                  (f := fun s : G ↦
                    if hs : s⁻¹ * (1 : G) * s ∈ H then
                      χ ⟨s⁻¹ * (1 : G) * s, hs⟩
                    else 0)
                  (g := fun _ : G ↦ χ 1)
                  hterm)
      _ = (Nat.card G : ℂ) * χ 1 := hsum0
  -- Now simplify the normalized induction formula using `|G| = |H| * [G : H]`.
  calc
    Ind[H](χ) 1
        = ((Nat.card H : ℂ)⁻¹) *
            ∑ s : G,
              (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) := by
            simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card H : ℂ)⁻¹) * ((Nat.card G : ℂ) * χ 1) := by
      rw [hsum]
    _ = ((Nat.card H : ℂ)⁻¹) * (((Nat.card H : ℂ) * H.index) * χ 1) := by
      rw [hcard]
    _ = (H.index : ℂ) * χ 1 := by
      field_simp [hH]

end Subgroup

/-- Helper for Exercise 10-10.5-5: the character of a finite-dimensional complex representation,
bundled as an element of LinearRepresentations_Serre_1977's character ring `R(G)`. -/
abbrev fdRepCharacterRing (V : FDRep ℂ G) : R(G) :=
  ⟨V.character, by simpa using Representation.rep_character_mem_characterRing (Rep.of V.ρ)⟩

/-- Helper for Exercise 10-10.5-5: the trivial one-dimensional representation gives the unit of
`R(G)`. -/
theorem fdRepCharacterRing_trivial_eq_one :
    fdRepCharacterRing (FDRep.of (Representation.trivial ℂ G ℂ)) = (1 : R(G)) := by
  -- The trivial character is the constant function `1`, so its bundled class is the unit.
  apply Subtype.ext
  ext g
  have htriv : (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
    ext x
    simp [Representation.character, Representation.trivial]
  change (Representation.trivial ℂ G ℂ).character g = 1
  simpa using congrFun htriv g

/-- Helper for Exercise 10-10.5-5: tensor products multiply finite-dimensional characters inside
LinearRepresentations_Serre_1977's character ring. -/
theorem fdRepCharacterRing_tensor_eq_mul (V W : FDRep ℂ G) :
    fdRepCharacterRing (CategoryTheory.MonoidalCategoryStruct.tensorObj V W) =
      fdRepCharacterRing V * fdRepCharacterRing W := by
  -- Bundle the tensor-product character formula into `R(G)`.
  apply Subtype.ext
  ext g
  change (CategoryTheory.MonoidalCategoryStruct.tensorObj V W).character g =
    (V.character * W.character) g
  exact congrFun (FDRep.char_tensor V W) g

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's subgroups `R₀'(G)` and `R'(G)`.
-- * core/canonical: `Subgroup.characterRingInduction` together with the ambient submodule owners
--   `Submodule.span`, `Submodule.map`, and `Submodule.sup`.
-- * bridge/view: the subgroup-side virtual character `α.toCharacterRing - 1` coming from a
--   degree-`1` complex character `α : E →* ℂˣ`.
--
-- Sampled owner declarations in this domain:
-- * `MonoidHom.toCharacterRing`
-- * `Subgroup.characterRingInduction`
-- * `Representation.artinInducedCharacterSubmodule`
-- * `Representation.pElementaryInducedCharacterSpan`
-- * `Representation.monomialCharacterSpan`
--
-- Primitive data: an elementary subgroup `E ≤ G` and a degree-`1` complex character
-- `α : E →* ℂˣ`.
-- Derived API: the virtual character `α.toCharacterRing - 1 ∈ R(E)` and its induced image in
-- `R(G)`.

/-- LinearRepresentations_Serre_1977's subgroup `R₀'(G)`, generated by the induced differences `Ind_E^G(α - 1)` where `E`
is elementary and `α : E →* ℂˣ` is a degree-one complex character. -/
def elementaryLinearCharacterAugmentationSpan (G : Type) [Group G] [Finite G] :
    Submodule ℤ (R(G)) :=
  Submodule.span ℤ
    { ψ : R(G) |
      ∃ E : Subgroup G, IsElementary E ∧ ∃ α : E →* ℂˣ,
        ψ = Subgroup.characterRingInduction E (α.toCharacterRing - 1) }

scoped[Representation] notation:max "R₀'(" G ")" =>
  Representation.elementaryLinearCharacterAugmentationSpan G

/-- LinearRepresentations_Serre_1977's subgroup `R'(G) = ℤ + R₀'(G)`, realized as the sum of the span of the trivial
character and `R₀'(G)`. -/
def elementaryLinearCharacterSpan (G : Type) [Group G] [Finite G] :
    Submodule ℤ (R(G)) :=
  Submodule.span ℤ ({1} : Set (R(G))) ⊔ R₀'(G)

scoped[Representation] notation:max "R'(" G ")" =>
  Representation.elementaryLinearCharacterSpan G

/-- Helper for Exercise 10-10.5-5: every finite group admits a finite complete pairwise
nonisomorphic family of irreducible complex representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family_local :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot have isomorphic representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : CategoryTheory.Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    -- Distinct quotient classes cannot label isomorphic regular summands.
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
    -- Multiplicity of one irreducible class in the regular representation equals its degree.
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
          Module.finrank ℂ (π q) := by
      letI : Representation.IsIrreducible (π q).ρ := by
        exact FDRep.isIrreducible_of_simple (π q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank ℂ (π q) ^ 2 := by
    -- Every regular summand inside one isomorphism class has the same degree.
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank ℂ (π q) := by
            simp
      _ = Module.finrank ℂ (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover : Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    -- Every irreducible regular summand lies in the quotient class determined by its own label.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    -- Summing the dimensions of the internal decomposition recovers the regular dimension.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing ℂ (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) = Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
            exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                simpa [dimσ] using
                  (Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule))
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    -- The quotient classes partition the regular summands, so the square-degree sum is `|G|`.
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    -- The square-degree sum criterion upgrades the quotient family to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 10-10.5-5: multiplying an induced class function by an ambient character
is the same as inducing the pointwise product with the restricted character. -/
private theorem restrict_mem_characterRing_preBrauer (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  -- Restriction is an algebra map, so it suffices to check it on irreducible generators.
  let res : (G → ℂ) →ₐ[ℤ] (H → ℂ) :=
    { toFun := fun φ : G → ℂ ↦ fun h : H ↦ φ h
      map_zero' := rfl
      map_one' := rfl
      map_add' := by
        intro φ ψ
        ext h
        rfl
      map_mul' := by
        intro φ ψ
        ext h
        rfl
      commutes' := by
        intro n
        ext h
        rfl }
  change res χ ∈ R(H)
  have hmap_le : R(G).map res ≤ R(H) := by
    refine (Subalgebra.gc_map_comap res).l_le ?_
    rw [Representation.characterRingOverField]
    refine (Algebra.adjoin_le_iff).2 ?_
    intro ψ hψ
    rcases hψ with ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    -- Restriction of representations restricts ordinary characters pointwise.
    change res (ρ.ρ.character) ∈ R(H)
    simpa [res] using
      (Representation.rep_character_mem_characterRingOverField (K := ℂ)
        (ρ := Rep.res H.subtype ρ))
  exact hmap_le ⟨χ, χ.property, rfl⟩

/-- Helper for Exercise 10-10.5-5: multiplying an induced class function by an ambient character
is the same as inducing the pointwise product with the restricted character. -/
private theorem induced_mul_eq_induced_mul_restriction_preBrauer
    (H : Subgroup G) (ψ : H → ℂ) (χ : R(G)) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  -- Compare the induction formula term-by-term after restricting the ambient character.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ :
        (χ : G → ℂ) (s⁻¹ * x * s) = (χ : G → ℂ) x := by
      exact (Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        (χ : G → ℂ) χ.property).eq_of_isConj <| isConj_iff.2 ⟨s, by group⟩
    have hχ' : (χ : G → ℂ) (s⁻¹ * (x * s)) = (χ : G → ℂ) x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for Exercise 10-10.5-5: Brauer's subgroup `V_p` is stable under multiplication by an
arbitrary virtual character of `G`. -/
theorem mul_mem_pElementaryInducedCharacterSpan_local (p : ℕ) {χ ψ : R(G)}
    (hψ : ψ ∈ (Representation.pElementaryInducedCharacterSpan p G)) :
    χ * ψ ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary p H) := Classical.decPred _
  -- Check the stability first on subgroup-induced generators, then extend by `iSup` induction.
  rw [Representation.pElementaryInducedCharacterSpan] at hψ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hψ
  refine Submodule.iSup_induction
      (p := fun H :
        {H : Subgroup G // H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary p H) Finset.univ} ↦
          LinearMap.range (Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦ χ * ξ ∈ (Representation.pElementaryInducedCharacterSpan p G))
      hψ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hprod : (fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h)) ∈ R(H) := by
      exact (R(H)).mul_mem η.property (restrict_mem_characterRing_preBrauer H χ)
    let ζ : R(H) := ⟨fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h), hprod⟩
    have hζ :
        χ * Subgroup.characterRingInduction H η =
          Subgroup.characterRingInduction H ζ := by
      -- Rewrite the product on characters, then repack it into the induced character owner.
      apply Subtype.ext
      ext g
      have hind :=
        congrFun (induced_mul_eq_induced_mul_restriction_preBrauer H (η : H → ℂ) χ) g
      simpa [ζ, Subgroup.characterRingInduction_apply, mul_comm] using hind
    exact hζ ▸
      Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem ζ
  · simpa using Submodule.zero_mem ((Representation.pElementaryInducedCharacterSpan p G))
  · intro ξ η hξ hη
    simpa [mul_add] using Submodule.add_mem ((Representation.pElementaryInducedCharacterSpan p G)) hξ hη

/-- Helper for Exercise 10-10.5-5: once a scalar multiple of the trivial character lies in `V_p`,
the same scalar multiple of every virtual character also lies in `V_p`. -/
private theorem smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem_local
    (p : ℕ) (l : ℕ) (hscalar : l • (1 : R(G)) ∈ (Representation.pElementaryInducedCharacterSpan p G)) (χ : R(G)) :
    l • χ ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
  -- Multiply the scalar witness by `χ` inside the character ring.
  have hmul :=
    mul_mem_pElementaryInducedCharacterSpan_local (G := G) (p := p)
      (χ := χ) (ψ := l • (1 : R(G))) hscalar
  simpa [mul_comm] using hmul

/-- Helper for Exercise 10-10.5-5: once a prime-to-`p` scalar multiple of the trivial character
lies in `V_p`, the additive quotient `R(G) / V_p` is finite and has order prime to `p`. -/
theorem finiteIndex_and_coprime_of_scalar_mem_pElementaryInducedCharacterSpan_local
    (p : Nat.Primes) (l : ℕ) (hl : Nat.Coprime p l)
    (hscalar : l • (1 : R(G)) ∈ (Representation.pElementaryInducedCharacterSpan p G)) :
    ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup.FiniteIndex ∧ Nat.Coprime p ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup.index := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  -- Build a basis of `R(G)` from a complete irreducible family so the `nsmul`-range index formula
  -- becomes available.
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family_local (G := G)
  let b :=
    Representation.irreducible_characters_basis_of_complete_family
      ℂ π hπ_pairwise hπ_complete
  letI : Module.Free ℤ (R(G)) := Module.Free.of_basis b
  letI : Module.Finite ℤ (R(G)) := Module.Finite.of_basis b
  have hl_ne_zero : l ≠ 0 := by
    intro hl0
    have hp_one : (p : ℕ) = 1 := by
      simpa [hl0] using hl
    exact p.2.ne_one hp_one
  have hlmul : ∀ χ : R(G), l • χ ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
    intro χ
    -- The scalar witness propagates from `1` to all of `R(G)` by multiplicative stability.
    exact smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem_local
      (G := G) (p := (p : ℕ)) l hscalar χ
  let L : AddSubgroup (R(G)) := (nsmulAddMonoidHom (α := R(G)) l).range
  have hL_le : L ≤ ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup := by
    intro χ hχ
    rcases hχ with ⟨x, rfl⟩
    exact hlmul x
  have hL_index : L.index = l ^ Module.finrank ℤ (R(G)) := by
    simpa [L] using AddSubgroup.index_range_nsmul (M := R(G)) l
  have hL_finite : L.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, hL_index]
    exact pow_ne_zero _ hl_ne_zero
  have hfinite : ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_le hL_le
  constructor
  · exact hfinite
  · have hdiv : ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup.index ∣ l ^ Module.finrank ℤ (R(G)) := by
      letI : L.FiniteIndex := hL_finite
      exact (AddSubgroup.index_dvd_of_le hL_le).trans (dvd_of_eq hL_index)
    exact Nat.Coprime.of_dvd_right hdiv (hl.pow_right _)

/-- Helper for Exercise 10-10.5-5: the remaining Brauer input is a prime-to-`p` scalar multiple
of the trivial character inside `V_p`. -/
private theorem quotient_card_smul_mem_pElementaryInducedCharacterSpan_of_finiteIndex_local
    (p : Nat.Primes)
    [hfinite : ((Representation.pElementaryInducedCharacterSpan p G)).toAddSubgroup.FiniteIndex] (χ : R(G)) :
    Nat.card (R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G)) • χ ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
  classical
  letI : Fintype (R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G)) := AddSubgroup.fintypeQuotientOfFiniteIndex
  let m : ℕ := Nat.card (R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G))
  let m' : ℕ := Fintype.card (R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G))
  have hm : m = m' := by
    simp [m, m', Nat.card_eq_fintype_card]
  have hzero :
      m' • (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ : R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G)) = 0 := by
    -- Finite additive groups are annihilated by their cardinality.
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [m'] using
        (card_nsmul_eq_zero
          (x := (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ : R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G))))
  have hmk_zero : Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) (m' • χ) = 0 := by
    -- Push the scalar action through the quotient map before reading membership upstairs.
    rw [map_nsmul]
    exact hzero
  have hmem' : m' • χ ∈ (Representation.pElementaryInducedCharacterSpan p G) :=
    (Submodule.Quotient.mk_eq_zero ((Representation.pElementaryInducedCharacterSpan p G))).1 hmk_zero
  simpa [m, m'] using hmem'


/-- Helper for Exercise 10-10.5-5: when `|G| = p^n l` with `(p, l) = 1`, the `p`-regular
elements are exactly the `l`-torsion elements. -/
theorem isPRegular_iff_pow_primeToPart_eq_one_local
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) {s : G} :
    IsPRegular (p : ℕ) s ↔ s ^ l = 1 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  constructor
  · -- The order of a `p`-regular element divides the prime-to-`p` factor `l`.
    intro hs
    have hs_not_dvd : ¬ (p : ℕ) ∣ orderOf s := by
      exact (isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) s).1 hs
    have hs_coprime_p : Nat.Coprime (p : ℕ) (orderOf s) := by
      exact (Nat.Prime.coprime_iff_not_dvd p.2).2 hs_not_dvd
    have hs_coprime_pow : Nat.Coprime (orderOf s) ((p : ℕ) ^ n) := by
      exact hs_coprime_p.symm.pow_right n
    have hs_dvd_l : orderOf s ∣ l := by
      apply Nat.Coprime.dvd_of_dvd_mul_right hs_coprime_pow
      rw [mul_comm, ← hcard]
      exact orderOf_dvd_natCard s
    calc
      s ^ l = s ^ (l % orderOf s) := by
        symm
        exact pow_mod_orderOf s l
      _ = 1 := by
        simp [Nat.mod_eq_zero_of_dvd hs_dvd_l]
  · -- Conversely, an `l`-torsion element has order dividing `l`, hence is prime to `p`.
    intro hs
    rw [isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) s]
    intro hp
    have hs_dvd_l : orderOf s ∣ l := orderOf_dvd_of_pow_eq_one hs
    have hpdivl : (p : ℕ) ∣ l := dvd_trans hp hs_dvd_l
    exact ((Nat.Prime.coprime_iff_not_dvd p.2).1 hl) hpdivl

/-- Helper for Exercise 10-10.5-5: the indicator of the `p`-regular locus is an integral virtual
character once `|G| = p^n l` with `(p, l) = 1`. -/
theorem pregular_indicator_mem_characterRing_local
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) :
    (fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0) ∈ R(G) := by
  let lpos : 0 < l := by
    -- The complementary factor `l` is positive because it is coprime to the prime `p`.
    apply Nat.pos_of_ne_zero
    intro hl0
    have hp_one : (p : ℕ) = 1 := by
      simpa [hl0] using hl
    exact p.2.ne_one hp_one
  have hscalar :
      (fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0) ∈
        Representation.characterRingScalarExtension ℤ G := by
    -- Important correction: do not apply Frobenius's Theorem 23 with `(A := ℤ)` here.
    -- In LinearRepresentations_Serre_1977 11.2, `A` is the subring of `ℂ` generated by the `|G|`-th roots of unity, so the
    -- theorem first gives the weighted Adams transform over that cyclotomic coefficient ring.
    -- The missing bridge is the separate integrality/descent step from that root-of-unity ring
    -- back to the integral character ring. The previous proof incorrectly skipped this descent.
    sorry
  have hspan : Representation.characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
    -- Over `ℤ`, scalar extension is just the original integral character ring.
    rw [Representation.characterRingScalarExtension]
    exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
  simpa [hspan] using hscalar

/-- Helper for Exercise 10-10.5-5: an integral value of the form `m / d` forces `d ∣ m`. -/
theorem nat_dvd_of_isIntegral_natCast_div_local
    {m d : ℕ} (hd : d ≠ 0) (h : IsIntegral ℤ ((m : ℂ) / d)) :
    d ∣ m := by
  let q : ℚ := m / d
  have hq : IsIntegral ℤ q := by
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m d hd).mp <| by
    simpa [q] using hden


end

end Representation
