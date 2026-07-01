import Mathlib
import Mathlib.Data.ZMod.QuotientRing
import Serre.Chap06.Exercise_6_6_5_10
import Serre.Chap07.Proposition_7_7_2_1
import Serre.Chap10.Lemma_10_10_3_3
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap10.Definition_10_10_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Representation SubgroupInduction TensorProduct

namespace Representation

open CategoryTheory

section

variable {G : Type u} [Group G] [Finite G]

/-- A finite group is equipped with its canonical `Fintype` structure when building finite
subgroup families. -/
local instance : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

namespace Subgroup

/-- Inducing a virtual character on `H` gives an element of the integral character ring `R(G)`. -/
theorem inducedClassFunction_mem_characterRing (H : Subgroup G) (χ : R(H)) :
    Ind[H]((χ : H → ℂ)) ∈ R(G) := by
  -- This is exactly the complex specialization of the subgroup-induction character theorem.
  simpa using _root_.Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H χ

/-- The canonical `ℤ`-linear induction map `R(H) → R(G)` on Serre's integral character rings. -/
def characterRingInduction (H : Subgroup G) :
    R(H) →ₗ[ℤ] R(G) where
  toFun χ := ⟨Ind[H]((χ : H → ℂ)), inducedClassFunction_mem_characterRing H χ⟩
  map_add' χ ψ := by
    let ind :=
      (((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).restrictScalars ℤ)
    have h_add :=
      ind.map_add (χ : H → ℂ) (ψ : H → ℂ)
    ext g
    exact congrFun h_add g
  map_smul' n χ := by
    let ind :=
      (((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).restrictScalars ℤ)
    have h_smul :=
      ind.map_smul n (χ : H → ℂ)
    ext g
    exact congrFun h_smul g

/-- Evaluating the subgroup induction map recovers the induced complex-valued class function. -/
@[simp] theorem characterRingInduction_apply (H : Subgroup G) (χ : R(H)) :
    ((Representation.Subgroup.characterRingInduction H χ : R(G)) : G → ℂ) =
      Ind[H]((χ : H → ℂ)) :=
  rfl

end Subgroup

/-- Brauer's subgroup `V_p ≤ R(G)`, realized canonically as the Chapter 9 Artin-induction owner
specialized to the `p`-elementary subgroups of `G`. -/
abbrev pElementaryInducedCharacterSpan (p : ℕ) (G : Type) [Group G] [Finite G] :
    Submodule ℤ (R(G)) :=
  let _ : DecidablePred fun H : Subgroup G ↦ IsPElementary p H := Classical.decPred _
  artinInducedCharacterSubmodule
    (Finset.univ.filter fun H : Subgroup G ↦ IsPElementary p H)

end

scoped[Representation] notation:max "V[" p "](" G ")" =>
  Representation.pElementaryInducedCharacterSpan p G

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H
local instance : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)

/-- Helper for Theorem 10-10.2-1: a finite group admits a complete pairwise nonisomorphic family
of irreducible complex finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
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
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
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
                have hfinrank :=
                  (Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule))
                simpa only [dimσ] using hfinrank
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
    -- The Chapter 2 square-degree criterion upgrades the quotient family to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 10-10.2-1: choose a concrete representative of a conjugacy class of `G`.
-/
private noncomputable def conjClassRepresentative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

omit [Finite G] in
/-- Helper for Theorem 10-10.2-1: the chosen representative realizes its conjugacy class. -/
private theorem conjClassRepresentative_mk (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

-- Proof sketch: the induced character lands in the range of the canonical induction map from the
-- corresponding `p`-elementary subgroup, hence in the supremum defining `V_p`.
/-- A character of `R(G)` induced from a representation of a `p`-elementary subgroup belongs to
Brauer's subgroup `V_p`. -/
theorem mem_pElementaryInducedCharacterSpan_of_eq_induced_character (p : ℕ)
    {χ : R(G)} (H : Subgroup G) (hH : IsPElementary p H) (W : FDRep ℂ H)
    (hχ : (χ : G → ℂ) = Ind[H](W.character)) :
    χ ∈ V[p](G) := by
  let η : R(H) := ⟨W.character, Representation.rep_character_mem_characterRing (Rep.of W.ρ)⟩
  have hη : Representation.Subgroup.characterRingInduction H η = χ := by
    -- Identify the source-facing induced class function with the owner-level induction element.
    apply Subtype.ext
    ext g
    exact congrFun hχ.symm g
  -- Rewrite `V_p` as the Artin owner and insert the single subgroup-induction generator.
  rw [Representation.pElementaryInducedCharacterSpan]
  let _ : DecidablePred (fun K : Subgroup G ↦ IsPElementary p K) := Classical.decPred _
  have hHmem : H ∈ Finset.univ.filter (fun K : Subgroup G ↦ IsPElementary p K) := by
    simp [hH]
  simpa [← hη] using
    Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem η

/-- Helper for Theorem 10-10.2-1: restrict a complex-valued class function on `G` to a subgroup
`H`. -/
private def functionRestriction (H : Subgroup G) : (G → ℂ) →ₐ[ℤ] (H → ℂ) where
  toFun χ := fun h ↦ χ h
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext h
    rfl
  map_mul' χ ψ := by
    ext h
    rfl
  commutes' n := by
    ext h
    rfl

omit [Finite G] in
/-- Helper for Theorem 10-10.2-1: restricting an ordinary virtual character to a subgroup stays
inside the subgroup character ring. -/
private theorem restrict_mem_characterRing (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  -- Restriction is an algebra map, so it suffices to check it on irreducible generators.
  change functionRestriction H χ ∈ R(H)
  have hmap_le : R(G).map (functionRestriction H) ≤ R(H) := by
    refine (Subalgebra.gc_map_comap (functionRestriction H)).l_le ?_
    rw [Representation.characterRingOverField]
    refine (Algebra.adjoin_le_iff).2 ?_
    intro ψ hψ
    rcases hψ with ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    -- Restriction of representations restricts ordinary characters pointwise.
    change functionRestriction H (ρ.ρ.character) ∈ R(H)
    simpa [functionRestriction] using
      (Representation.rep_character_mem_characterRingOverField (K := ℂ)
        (ρ := Rep.res H.subtype ρ))
  exact hmap_le ⟨χ, χ.property, rfl⟩

/-- Helper for Theorem 10-10.2-1: multiplying an induced class function by an ambient character is
the same as inducing the pointwise product with the restricted character. -/
private theorem induced_mul_eq_induced_mul_restriction
    (H : Subgroup G) (ψ : H → ℂ) (χ : R(G)) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  -- Compare the source and target formulas summand-by-summand in the induction expansion.
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

/-- Helper for Theorem 10-10.2-1: Brauer's subgroup `V_p` is stable under multiplication by an
arbitrary virtual character of `G`. -/
theorem mul_mem_pElementaryInducedCharacterSpan (p : ℕ) {χ ψ : R(G)}
    (hψ : ψ ∈ V[p](G)) :
    χ * ψ ∈ V[p](G) := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary p H) := Classical.decPred _
  -- Rewrite `V_p` as the supremum of subgroup-induction ranges and prove stability on generators.
  rw [Representation.pElementaryInducedCharacterSpan] at hψ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hψ
  refine Submodule.iSup_induction
      (p := fun H :
        {H : Subgroup G // H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary p H) Finset.univ} ↦
          LinearMap.range (Representation.Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦ χ * ξ ∈ V[p](G))
      hψ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hprod : (fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h)) ∈ R(H) := by
      exact (R(H)).mul_mem η.property (restrict_mem_characterRing H χ)
    let ζ : R(H) := ⟨fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h), hprod⟩
    have hζ :
        χ * Representation.Subgroup.characterRingInduction H η =
          Representation.Subgroup.characterRingInduction H ζ := by
      -- Compare the owner-level characters pointwise through the induction product formula.
      apply Subtype.ext
      ext g
      have hind :=
        congrFun (induced_mul_eq_induced_mul_restriction H (η : H → ℂ) χ) g
      simpa [ζ, Representation.Subgroup.characterRingInduction_apply, mul_comm] using hind
    exact hζ ▸
      Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem ζ
  · simp
  · intro ξ η hξ hη
    simpa [mul_add] using Submodule.add_mem (V[p](G)) hξ hη

/-- Helper for Theorem 10-10.2-1: once a scalar multiple of the trivial character lies in `V_p`,
the same scalar multiple of every virtual character also lies in `V_p`. -/
private theorem smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem
    (p : ℕ) (l : ℕ) (hscalar : l • (1 : R(G)) ∈ V[p](G)) (χ : R(G)) :
    l • χ ∈ V[p](G) := by
  -- Multiply the source scalar witness by `χ` inside the character ring.
  have hmul :=
    mul_mem_pElementaryInducedCharacterSpan (G := G) (p := p)
      (χ := χ) (ψ := l • (1 : R(G))) hscalar
  simpa [mul_comm] using hmul

/-- Helper for Theorem 10-10.2-1: the source-faithful scalar extension owner uses the algebraic
integers inside `ℂ`. -/
private abbrev pElementaryScalarExtensionRing : Type :=
  ↥(integralClosure ℤ ℂ)

/-- Helper for Theorem 10-10.2-1: the tensor owner `A ⊗ V_p` carries its canonical
`pElementaryScalarExtensionRing`-module structure. -/
local instance pElementaryScalarExtensionTensorModule (p : ℕ) :
    Module pElementaryScalarExtensionRing
      (TensorProduct ℤ pElementaryScalarExtensionRing ↥(V[p](G))) :=
  TensorProduct.leftModule

/-- Helper for Theorem 10-10.2-1: Serre's local owner is the scalar span of the ambient image of
Brauer's subgroup `V_p` inside `G → ℂ`. -/
private abbrev pElementaryScalarExtensionOwner (p : ℕ) :
    Submodule pElementaryScalarExtensionRing (G → ℂ) :=
  Submodule.span pElementaryScalarExtensionRing
    { φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) }

/-- Helper for Theorem 10-10.2-1: a character already in Brauer's subgroup contributes a
generator to the theorem-local scalar extension owner. -/
private theorem mem_pElementaryScalarExtensionOwner_of_mem
    (p : ℕ) {χ : R(G)} (hχ : χ ∈ V[p](G)) :
    (χ : G → ℂ) ∈ pElementaryScalarExtensionOwner (G := G) p := by
  -- The local owner is defined as the span of the image of `V_p`, so generators enter directly.
  exact Submodule.subset_span ⟨⟨χ, hχ⟩, rfl⟩

/-- Helper for Theorem 10-10.2-1: inducing an integral character from a `p`-elementary subgroup
lands in Brauer's subgroup `V_p`. -/
private theorem characterRingInduction_mem_pElementaryInducedCharacterSpan_local
    (p : ℕ) (H : Subgroup G) (hH : IsPElementary p H) (χ : R(H)) :
    Representation.Subgroup.characterRingInduction H χ ∈ V[p](G) := by
  classical
  -- Rewrite `V_p` as the filtered induction span and insert the subgroup generator directly.
  rw [Representation.pElementaryInducedCharacterSpan]
  let _ : DecidablePred (fun K : Subgroup G ↦ IsPElementary p K) := Classical.decPred _
  have hHmem :
      H ∈ Finset.univ.filter (fun K : Subgroup G ↦ IsPElementary p K) := by
    simp [hH]
  exact Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem χ

/-- Helper for Theorem 10-10.2-1: tensor induction from a `p`-elementary subgroup lands in the
source-faithful scalar extension owner `A ⊗ V_p`. -/
private theorem induced_tensor_character_mem_pElementary_scalarExtension
    (p : ℕ) (H : Subgroup G) (hH : IsPElementary p H)
    (ψ : pElementaryScalarExtensionRing ⊗R(H)) :
    Ind[H]((ψ : H → ℂ)) ∈ pElementaryScalarExtensionOwner (G := G) p := by
  classical
  -- Route correction: keep the Brauer witness in the scalar-extension owner and prove membership
  -- there by tensor induction instead of trying to descend prematurely to `R(G)`.
  induction ψ using TensorProduct.induction_on with
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      -- The local owner is a submodule, so it contains the zero character.
      change Ind[H]((0 : H → ℂ)) ∈ pElementaryScalarExtensionOwner (G := G) p
      rw [hzero]
      exact Submodule.zero_mem (pElementaryScalarExtensionOwner (G := G) p)
  | tmul a χ =>
      have hbase :
          Ind[H]((χ : H → ℂ)) ∈ pElementaryScalarExtensionOwner (G := G) p := by
        -- The honest induced character already belongs to `V_p`, hence to its scalar span.
        exact
          mem_pElementaryScalarExtensionOwner_of_mem (G := G) p
            (characterRingInduction_mem_pElementaryInducedCharacterSpan_local
              (G := G) p H hH χ)
      have hsmul :
          Ind[H](a • (χ : H → ℂ)) = a • Ind[H]((χ : H → ℂ)) := by
        -- Induction is linear in the induced class function.
        ext g
        simp [Subgroup.inducedClassFunction, Finset.mul_sum, Algebra.smul_def,
          mul_assoc, mul_left_comm]
      -- On pure tensors, induction commutes with scalar multiplication by algebraic integers.
      simpa [Representation.Subgroup.characterRingInduction_apply, hsmul] using
        (pElementaryScalarExtensionOwner (G := G) p).smul_mem a hbase
  | add ψ₁ ψ₂ hψ₁ hψ₂ =>
      have hadd :
          Ind[H](((ψ₁ : H → ℂ) + (ψ₂ : H → ℂ))) =
            (Ind[H]((ψ₁ : H → ℂ)) : G → ℂ) + Ind[H]((ψ₂ : H → ℂ)) := by
        -- Induction is additive in the induced class function.
        ext g
        exact congrFun
          ((((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).map_add
              (ψ₁ : H → ℂ) (ψ₂ : H → ℂ))) g
      -- The scalar-extension owner is closed under addition after rewriting the induced sum.
      rw [map_add, hadd]
      exact (pElementaryScalarExtensionOwner (G := G) p).add_mem hψ₁ hψ₂

/-- Helper for Theorem 10-10.2-1: every `p`-regular conjugacy class admits the source-faithful
Brauer witness in the scalar extension owner `A ⊗ V_p`, supported on that class among
`p`-regular elements. -/
private theorem exists_auxiliary_tensor_character_on_pregular_class
    (p : Nat.Primes) {x : G} (hx : IsPRegular (p : ℕ) x) :
    ∃ β : pElementaryScalarExtensionOwner (G := G) (p : ℕ),
      (∃ n : ℤ, (β : G → ℂ) x = (n : ℂ) ∧ ¬ (p : ℤ) ∣ n) ∧
        ∀ s : G, IsPRegular (p : ℕ) s → ¬ IsConj s x → (β : G → ℂ) s = 0 := by
  classical
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  let P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)) :=
    Classical.choice (Sylow.nonempty (p := (p : ℕ)) (G := Subgroup.centralizer ({x} : Set G)))
  let H := associatedPElementarySubgroup (p : ℕ) x P
  have hH : IsPElementary (p : ℕ) H := by
    simpa [H] using associatedPElementarySubgroup_isPElementary (p := (p : ℕ)) x hx P
  obtain ⟨ψ, _hψint, ⟨n, hnx, hndiv⟩, hψzero⟩ :=
    exists_associated_auxiliary_character_with_brauer_induction_support
      (p := (p : ℕ)) (x := x) P hx
  have hβmem :
      Ind[H]((ψ : H → ℂ)) ∈ pElementaryScalarExtensionOwner (G := G) (p : ℕ) := by
    -- The associated subgroup is `p`-elementary, so its induced tensor witness already lives in
    -- the source-faithful owner `A ⊗ V_p`.
    simpa [H] using
      induced_tensor_character_mem_pElementary_scalarExtension
        (G := G) (p := (p : ℕ)) H hH ψ
  refine ⟨⟨Ind[H]((ψ : H → ℂ)), hβmem⟩, ?_, ?_⟩
  · -- The explicit Brauer support theorem already provides the nonzero integer value at `x`.
    exact ⟨n, hnx, hndiv⟩
  · -- The same theorem also supplies the vanishing away from the chosen `p`-regular class.
    intro s hs hsx
    exact hψzero s hs hsx

/-- Helper for Theorem 10-10.2-1: every element of the theorem-local scalar-extension owner
`A ⊗ V_p` is a class function on `G`. -/
private theorem isClassFunction_of_mem_pElementaryScalarExtensionOwner
    (p : ℕ) {φ : G → ℂ} (hφ : φ ∈ pElementaryScalarExtensionOwner (G := G) p) :
    _root_.IsClassFunction φ := by
  -- The local owner is generated by genuine integral characters, and class-function invariance is
  -- preserved by the span operations.
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
      rcases hψ with ⟨β, rfl⟩
      exact Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        ((β : R(G)) : G → ℂ) (β : R(G)).property
  | zero =>
      simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : ℂ)))
  | add φ ψ _ _ hφ hψ =>
      letI : _root_.IsClassFunction φ := hφ
      letI : _root_.IsClassFunction ψ := hψ
      simpa using (inferInstance : _root_.IsClassFunction (φ + ψ))
  | smul a φ _ hφ =>
      letI : _root_.IsClassFunction φ := hφ
      simpa using (inferInstance : _root_.IsClassFunction (a • φ))

/-- Helper for Theorem 10-10.2-1: summing the class-supported auxiliary Brauer witnesses over the
finite set of `p`-regular conjugacy classes produces one tensor character in `A ⊗ V_p` whose
value on every `p`-regular element is a common positive integer prime to `p`. -/
private theorem exists_constant_pregular_value_tensor_character_in_pElementaryScalarExtension
    (p : Nat.Primes) :
    ∃ N : ℕ, Nat.Coprime p N ∧
      ∃ θ : pElementaryScalarExtensionOwner (G := G) (p : ℕ),
        ∀ s : G, IsPRegular (p : ℕ) s → (θ : G → ℂ) s = (N : ℂ) := by
  classical
  let C : Type := { c : ConjClasses G // IsPRegular (p : ℕ) (conjClassRepresentative c) }
  letI : Fintype C := Fintype.ofFinite C
  have haux :
      ∀ c : C,
        ∃ β : pElementaryScalarExtensionOwner (G := G) (p : ℕ),
          ∃ n : ℤ,
            (β : G → ℂ) (conjClassRepresentative c.1) = (n : ℂ) ∧
              ¬ (p : ℤ) ∣ n ∧
                ∀ s : G,
                  IsPRegular (p : ℕ) s →
                    ¬ IsConj s (conjClassRepresentative c.1) → (β : G → ℂ) s = 0 := by
    intro c
    -- Use the already-constructed class-supported witness on the chosen representative of the
    -- `p`-regular class `c`.
    rcases exists_auxiliary_tensor_character_on_pregular_class (G := G) p c.2 with
      ⟨β, ⟨n, hnval, hndiv⟩, hβzero⟩
    exact ⟨β, n, hnval, hndiv, hβzero⟩
  choose β n hnval hndiv hβzero using haux
  let N : ℕ := ∏ c : C, (n c).natAbs
  let coeff : C → ℤ := fun c ↦
    ((Finset.prod ((Finset.univ : Finset C).erase c) fun d : C ↦ (n d).natAbs : ℕ) : ℤ) *
      Int.sign (n c)
  let θ : pElementaryScalarExtensionOwner (G := G) (p : ℕ) := ∑ c : C, coeff c • β c
  have hNcoprime : Nat.Coprime p N := by
    -- Each class-wise value is nonzero modulo `p`, so their absolute-value product is prime to `p`.
    change Nat.Coprime p (∏ c : C, (n c).natAbs)
    refine (Nat.coprime_prod_right_iff).2 ?_
    intro c hc
    refine (p.2.coprime_iff_not_dvd).2 ?_
    intro hpdiv
    exact hndiv c (Int.natCast_dvd.2 hpdiv)
  refine ⟨N, hNcoprime, θ, ?_⟩
  intro s hs
  have hsrep : IsPRegular (p : ℕ) (conjClassRepresentative (ConjClasses.mk s)) := by
    -- The chosen representative of the class of a `p`-regular element is `p`-regular by conjugacy.
    have hconj :
        IsConj s (conjClassRepresentative (ConjClasses.mk s)) := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mp
      simpa using (conjClassRepresentative_mk (G := G) (ConjClasses.mk s)).symm
    rcases isConj_iff.1 hconj with ⟨t, ht⟩
    simpa [ht, mul_assoc] using isPRegular_conj (p := (p : ℕ)) s t hs
  let c₀ : C := ⟨ConjClasses.mk s, hsrep⟩
  have hβsame : (β c₀ : G → ℂ) s = (n c₀ : ℂ) := by
    -- On the supporting class, class-function invariance identifies the value at `s` with the
    -- value at the chosen representative of the same class.
    have hβclass :
        _root_.IsClassFunction (β c₀ : G → ℂ) :=
      isClassFunction_of_mem_pElementaryScalarExtensionOwner
        (G := G) (p := (p : ℕ)) (β c₀).2
    have hconj :
        IsConj s (conjClassRepresentative c₀.1) := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mp
      simpa [c₀] using (conjClassRepresentative_mk (G := G) (ConjClasses.mk s)).symm
    calc
      (β c₀ : G → ℂ) s = (β c₀ : G → ℂ) (conjClassRepresentative c₀.1) :=
        _root_.IsClassFunction.eq_of_isConj hβclass hconj
      _ = (n c₀ : ℂ) := hnval c₀
  have hcoeffprod : coeff c₀ * n c₀ = N := by
    -- The chosen coefficient is the product of the other absolute values, times the sign needed
    -- to turn the class value `n c₀` into its absolute value.
    unfold coeff N
    rw [mul_assoc, Int.sign_mul_self_eq_natAbs, ← Int.natCast_mul]
    exact congrArg (fun m : ℕ ↦ (m : ℤ))
      (Finset.prod_erase_mul (s := Finset.univ) (f := fun c : C ↦ (n c).natAbs) (by simp))
  have hcoeffprodC : ((coeff c₀ : ℤ) : ℂ) * (n c₀ : ℂ) = (N : ℂ) := by
    exact_mod_cast hcoeffprod
  -- All other class-supported witnesses vanish at `s`, so only the summand indexed by `c₀`
  -- survives and its value is exactly the common product `N`.
  calc
    (θ : G → ℂ) s = ∑ c : C, (((coeff c : ℤ) : ℂ) * (β c : G → ℂ) s) := by
      simp [θ, coeff, mul_assoc]
    _ = (((coeff c₀ : ℤ) : ℂ) * (β c₀ : G → ℂ) s) := by
      refine Finset.sum_eq_single c₀ ?_ ?_
      · intro c hc hne
        have hs_not_conj : ¬ IsConj s (conjClassRepresentative c.1) := by
          intro hsconj
          apply hne
          apply Subtype.ext
          simpa [c₀, conjClassRepresentative_mk (G := G) c.1] using
            (ConjClasses.mk_eq_mk_iff_isConj.2 hsconj).symm
        simp [hβzero c s hs hs_not_conj]
      · intro hc₀
        exact False.elim (hc₀ (by simp))
    _ = (((coeff c₀ : ℤ) : ℂ) * (n c₀ : ℂ)) := by rw [hβsame]
    _ = (N : ℂ) := hcoeffprodC

omit [Finite G] in
/-- Helper for Theorem 10-10.2-1: the order of a `p`-regular element divides the prime-to-`p`
part of `|G|`. -/
private theorem orderOf_dvd_ordCompl_card_of_isPRegular
    (p : Nat.Primes) {s : G} (hs : IsPRegular (p : ℕ) s) :
    orderOf s ∣ ordCompl[(p : ℕ)] (Nat.card G) := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  -- A `p`-regular element has order prime to `p`, so its order survives entirely inside the
  -- prime-to-`p` factor `ordCompl[p](|G|)`.
  have hs_not_dvd : ¬ (p : ℕ) ∣ orderOf s := by
    exact (isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) s).1 hs
  exact Nat.dvd_ordCompl_of_dvd_not_dvd (orderOf_dvd_natCard s) hs_not_dvd

omit [Finite G] in
/-- Helper for Theorem 10-10.2-1: when `|G| = p^n l` with `(p, l) = 1`, the `p`-regular
elements are exactly the `l`-torsion elements. This is the canonical Chapter 10 owner used by
later Brauer-induction support files. -/
theorem isPRegular_iff_pow_primeToPart_eq_one
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) {s : G} :
    IsPRegular (p : ℕ) s ↔ s ^ l = 1 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  constructor
  · -- Split `|G|` as `p^n l` and discard the `p`-power factor from the order of a `p`-regular
    -- element.
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
  · -- Conversely, an `l`-torsion element has order dividing the prime-to-`p` factor `l`.
    intro hs
    rw [isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) s]
    intro hp
    have hs_dvd_l : orderOf s ∣ l := orderOf_dvd_of_pow_eq_one hs
    have hpdivl : (p : ℕ) ∣ l := dvd_trans hp hs_dvd_l
    exact ((Nat.Prime.coprime_iff_not_dvd p.2).1 hl) hpdivl

/-- Helper for Theorem 10-10.2-1: the indicator of the `p`-regular locus is itself an integral
virtual character once `|G| = p^n l` with `(p, l) = 1`. This is the canonical Chapter 10 owner
consumed by later Brauer-induction support files. -/
theorem pregular_indicator_mem_characterRing
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) :
    (fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0) ∈ R(G) := by
  sorry

-- Proof sketch: Brauer's induction theorem shows that the additive quotient `R(G) / V_p` is
-- finite and that its cardinal, equivalently the index of `V_p` in `R(G)`, is prime to `p`.
/-- Helper for Theorem 10-10.2-1: once a prime-to-`p` scalar multiple of the trivial character
lies in `V_p`, the quotient `R(G) / V_p` is finite and has cardinal prime to `p`. -/
private theorem finiteIndex_and_coprime_of_scalar_mem_pElementaryInducedCharacterSpan
    (p : Nat.Primes) (l : ℕ) (hl : Nat.Coprime p l)
    (hscalar : l • (1 : R(G)) ∈ V[p](G)) :
    (V[p](G)).toAddSubgroup.FiniteIndex ∧ Nat.Coprime p (V[p](G)).toAddSubgroup.index := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  -- Route correction: the ambient finite-generation input should come from the earlier packaged
  -- complete irreducible family theorem, not from the unavailable raw existence name.
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
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
  have hlmul : ∀ χ : R(G), l • χ ∈ V[p](G) := by
    intro χ
    -- The scalar witness propagates to every character by multiplicative stability of `V_p`.
    exact smul_mem_pElementaryInducedCharacterSpan_of_scalar_mem
      (G := G) (p := (p : ℕ)) l hscalar χ
  let L : AddSubgroup (R(G)) := (nsmulAddMonoidHom (α := R(G)) l).range
  have hL_le : L ≤ (V[p](G)).toAddSubgroup := by
    intro χ hχ
    rcases hχ with ⟨x, rfl⟩
    exact hlmul x
  have hL_index : L.index = l ^ Module.finrank ℤ (R(G)) := by
    simpa [L] using AddSubgroup.index_range_nsmul (M := R(G)) l
  have hL_finite : L.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, hL_index]
    exact pow_ne_zero _ hl_ne_zero
  have hfinite : (V[p](G)).toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_le hL_le
  constructor
  · exact hfinite
  · have hdiv : (V[p](G)).toAddSubgroup.index ∣ l ^ Module.finrank ℤ (R(G)) := by
      letI : L.FiniteIndex := hL_finite
      exact (AddSubgroup.index_dvd_of_le hL_le).trans (dvd_of_eq hL_index)
    exact Nat.Coprime.of_dvd_right hdiv (hl.pow_right _)

set_option synthInstance.maxHeartbeats 100000 in
-- `card_nsmul_eq_zero` needs deeper instance search on the finite quotient.
/-- Helper for Theorem 10-10.2-1: once `V_p` has finite index, the cardinal of the quotient
annihilates the class of every virtual character modulo `V_p`. -/
private theorem quotient_card_smul_mem_pElementaryInducedCharacterSpan_of_finiteIndex
    (p : Nat.Primes)
    [hfinite : (V[p](G)).toAddSubgroup.FiniteIndex] (χ : R(G)) :
    Nat.card (R(G) ⧸ V[p](G)) • χ ∈ V[p](G) := by
  classical
  letI : Fintype (R(G) ⧸ V[p](G)) := AddSubgroup.fintypeQuotientOfFiniteIndex
  let m : ℕ := Nat.card (R(G) ⧸ V[p](G))
  let m' : ℕ := Fintype.card (R(G) ⧸ V[p](G))
  have hm : m = m' := by
    simp [m, m', Nat.card_eq_fintype_card]
  have hzero :
      m' • (Submodule.mkQ (V[p](G)) χ : R(G) ⧸ V[p](G)) = 0 := by
    -- Finite additive groups are annihilated by their cardinality.
    have hcard :=
      card_nsmul_eq_zero
        (x := (Submodule.mkQ (V[p](G)) χ : R(G) ⧸ V[p](G)))
    simpa only [m'] using hcard
  have hmk_zero : Submodule.mkQ (V[p](G)) (m' • χ) = 0 := by
    -- Push the scalar action through the quotient map before reading membership back upstairs.
    rw [map_nsmul]
    exact hzero
  have hmem' : m' • χ ∈ V[p](G) :=
    (Submodule.Quotient.mk_eq_zero (V[p](G))).1 hmk_zero
  simpa [m, m'] using hmem'

/-- Helper for Theorem 10-10.2-1: the normalized pairing of two honest characters is the
dimension of the intertwining space. -/
private theorem groupFunctionPairing_character_eq_finrank_intertwiningMap_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    ⟪σ.character, ρ.character⟫ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- This is the standard normalized character-pairing identity rewritten in the local notation.
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ))

/-- Helper for Theorem 10-10.2-1: pairing any integral virtual character with an honest
representation character gives an algebraic integer. -/
private theorem characterRing_pairing_isIntegral_with_rep_character_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (η : R(G)) (ρ : Representation ℂ G V) :
    IsIntegral ℤ ⟪(η : G → ℂ), ρ.character⟫ := by
  let S : Set (G → ℂ) :=
    { ψ |
        ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
          (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : G → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : G → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
            (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
            ψ = σ.character at hψ
          rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              change ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (τ : Representation ℂ G X),
                ξ = τ.character at hξ
              rcases hξ with ⟨X, _instXAdd, _instXMod, _instXfd, τ, rfl⟩
              let π : Representation ℂ G (TensorProduct ℂ W X) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ W X, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : G → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact (Submodule.zero_mem (Submodule.span ℤ S))
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using
                Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : G → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact (Submodule.zero_mem (Submodule.span ℤ S))
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : G → ℂ) ∈ Submodule.span ℤ S := by
    -- The integral character ring is generated by honest characters, and that span is stable
    -- under multiplication by tensor-product closure.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span ⟨σ, inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      rw [show algebraMap ℤ (G → ℂ) n =
          n • (Representation.trivial ℂ G ℂ).character by
        ext x
        simp [htriv]]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ G ℂ, rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Evaluate the pairing on the honest-character spanning set.
  refine
    Submodule.span_induction
      (p := fun ψ _ ↦ IsIntegral ℤ ⟪ψ, ρ.character⟫)
      ?_ ?_ ?_ ?_ hηspan
  · intro ψ hψ
    change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
      ψ = σ.character at hψ
    rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
    -- For a genuine character, the pairing is the finite dimension of the intertwining space.
    rw [groupFunctionPairing_character_eq_finrank_intertwiningMap_local (G := G) σ ρ]
    exact isIntegral_algebraMap
  · -- The pairing with the zero class function is zero.
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · intro ψ ξ _ _ hψ hξ
    simpa [Representation.groupFunctionPairing_add_left] using hψ.add hξ
  · intro n ψ _ hψ
    rw [show ⟪n • ψ, ρ.character⟫ = (n : ℂ) * ⟪ψ, ρ.character⟫ by
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (n : ℂ)) (φ := ψ) (ψ := ρ.character))]
    exact (isIntegral_algebraMap : IsIntegral ℤ (n : ℂ)).mul hψ

/-- Helper for Theorem 10-10.2-1: once the `p`-regular indicator is realized in `R(G)`, the
Chapter `10.3` congruence forces it to be the trivial character. -/
private theorem nat_dvd_of_isIntegral_natCast_div
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

/-- Helper for Theorem 10-10.2-1: once the `p`-regular indicator is realized in `R(G)`, pairing
it with the trivial character forces that indicator to be identically `1`. -/
private theorem pregular_indicator_eq_one
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) :
    let δ : R(G) :=
      ⟨fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0,
        pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
    δ = (1 : R(G)) := by
  classical
  let δ : R(G) :=
    ⟨fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0,
      pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
  let m : ℕ := Fintype.card { s : G // IsPRegular (p : ℕ) s }
  have hpair_integral :
      IsIntegral ℤ ⟪(δ : G → ℂ), (Representation.trivial ℂ G ℂ).character⟫ := by
    -- Pairing an integral virtual character with the trivial character is integral.
    simpa using
      characterRing_pairing_isIntegral_with_rep_character_local
        (G := G) (V := ℂ) δ (Representation.trivial ℂ G ℂ)
  have hpair_eq : ⟪(δ : G → ℂ), (Representation.trivial ℂ G ℂ).character⟫ =
      ((m : ℂ) / Nat.card G) := by
    rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
    calc
      (Nat.card G : ℂ)⁻¹ *
          ∑ x : G, (δ x) * (Representation.trivial ℂ G ℂ).character x⁻¹
          =
            (Nat.card G : ℂ)⁻¹ * ∑ x : G, if IsPRegular (p : ℕ) x then (1 : ℂ) else 0 := by
              congr 2
              ext x
              by_cases hx : IsPRegular (p : ℕ) x <;>
                simp [Representation.character, Representation.trivial, δ, hx]
      _ = (Nat.card G : ℂ)⁻¹ * ({ x : G | IsPRegular (p : ℕ) x }.toFinset.card : ℂ) := by
            simp
      _ = (Nat.card G : ℂ)⁻¹ * (m : ℂ) := by
            congr 1
            have hm_nat :
                { x : G | IsPRegular (p : ℕ) x }.toFinset.card = m := by
              simpa [m] using (Set.toFinset_card { x : G | IsPRegular (p : ℕ) x })
            exact_mod_cast hm_nat
      _ = ((m : ℂ) / Nat.card G) := by
            rw [div_eq_mul_inv, mul_comm]
  have hcard_dvd_m : Nat.card G ∣ m :=
    nat_dvd_of_isIntegral_natCast_div (d := Nat.card G) Nat.card_pos.ne' <| by
      simpa [hpair_eq] using hpair_integral
  have hm_pos : 0 < m := by
    refine Fintype.card_pos_iff.mpr ?_
    exact ⟨⟨1, isPRegular_one (p := (p : ℕ))⟩⟩
  have hm_eq : m = Nat.card G := by
    apply Nat.le_antisymm
    · simpa [m, Nat.card_eq_fintype_card] using
        (Fintype.card_subtype_le (fun s : G ↦ IsPRegular (p : ℕ) s))
    · exact Nat.le_of_dvd hm_pos hcard_dvd_m
  have hall : ∀ s : G, IsPRegular (p : ℕ) s := by
    intro s
    by_contra hs
    have hlt :
        m < Nat.card G := by
      simpa [m] using
        (Fintype.card_subtype_lt (p := fun x : G ↦ IsPRegular (p : ℕ) x) hs)
    exact Nat.lt_irrefl _ (hm_eq ▸ hlt)
  -- Route correction: instead of forcing the stronger scalar `l • 1 ∈ V_p`, first collapse the
  -- realized `p`-regular indicator to the trivial character by its integral pairing with `1`.
  apply Subtype.ext
  ext s
  simp [hall s]

/-- Helper for Theorem 10-10.2-1: the canonical inclusion of Brauer's subgroup `V_p` into the
ambient space of complex-valued class functions on `G`. -/
private abbrev pElementaryInducedCharacterToFunction
    (p : ℕ) :
    V[p](G) →ₗ[ℤ] G → ℂ :=
  ((R(G)).toSubmodule.subtype).comp (V[p](G)).subtype

/-- Helper for Theorem 10-10.2-1: the theorem-local generators of the scalar-extension owner are
exactly the range of the canonical inclusion `V[p](G) → G → ℂ`. -/
private theorem mem_range_pElementaryInducedCharacterToFunction_iff
    (p : ℕ) {φ : G → ℂ} :
    φ ∈ (LinearMap.range (pElementaryInducedCharacterToFunction (G := G) p) :
        Set (G → ℂ)) ↔
      ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) := by
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨β, rfl⟩
  · rintro ⟨β, rfl⟩
    exact ⟨β, rfl⟩

/-- Helper for Theorem 10-10.2-1: the source-faithful tensor realization of `A ⊗ V_p` attached
to the local inclusion `V[p](G) → G → ℂ`. -/
private abbrev tensorPElementaryInducedCharacterToFunction_local
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    TensorProduct ℤ pElementaryScalarExtensionRing ↥(V[p](G)) →ₗ[pElementaryScalarExtensionRing]
      G → ℂ :=
  (pElementaryInducedCharacterToFunction (G := G) p).liftBaseChange pElementaryScalarExtensionRing

/-- Helper for Theorem 10-10.2-1: elements of the theorem-local tensor owner `A ⊗ V_p` act as
complex-valued class functions through the canonical realization map. -/
local instance pElementaryScalarExtensionTensorCoeFun (p : ℕ) :
    CoeFun (TensorProduct ℤ pElementaryScalarExtensionRing ↥(V[p](G))) (fun _ ↦ G → ℂ) where
  coe := tensorPElementaryInducedCharacterToFunction_local (G := G) (p := p)

/-- Helper for Theorem 10-10.2-1: realizing a tensor in `A ⊗ V_p` agrees with first viewing it
inside `A ⊗ R(G)` and then using the ambient realization there. -/
private theorem tensorPElementaryInducedCharacterToFunction_eq_tensorCharacterRing_lTensor_local
    (p : ℕ) (ξ : TensorProduct ℤ pElementaryScalarExtensionRing ↥(V[p](G))) :
    (ξ : G → ℂ) =
      ((show pElementaryScalarExtensionRing ⊗R(G) from
          LinearMap.lTensor pElementaryScalarExtensionRing (V[p](G)).subtype ξ) : G → ℂ) := by
  induction ξ using TensorProduct.induction_on with
  | zero =>
      rfl
  | tmul a β =>
      ext g
      simp
  | add ξ η hξ hη =>
      simp [map_add, hξ, hη]

/-- Helper for Theorem 10-10.2-1: the theorem-local scalar-extension owner is exactly the range
of the canonical realization map `A ⊗ V_p → G → ℂ`. -/
private theorem pElementaryScalarExtensionOwner_eq_range_local
    (p : ℕ) :
    pElementaryScalarExtensionOwner (G := G) p =
      LinearMap.range (tensorPElementaryInducedCharacterToFunction_local (G := G) (p := p)) := by
  have hset :
      ({ φ : G → ℂ | ∃ β : V[p](G), φ = ((β : R(G)) : G → ℂ) } : Set (G → ℂ)) =
        (LinearMap.range (pElementaryInducedCharacterToFunction (G := G) p) : Set (G → ℂ)) := by
    ext φ
    constructor
    · intro hφ
      exact (mem_range_pElementaryInducedCharacterToFunction_iff (G := G) (p := p)).2 hφ
    · intro hφ
      exact (mem_range_pElementaryInducedCharacterToFunction_iff (G := G) (p := p)).1 hφ
  rw [pElementaryScalarExtensionOwner, hset]
  symm
  change
    LinearMap.range
        ((pElementaryInducedCharacterToFunction (G := G) p).liftBaseChange
          pElementaryScalarExtensionRing) =
      Submodule.span pElementaryScalarExtensionRing
        ((LinearMap.range (pElementaryInducedCharacterToFunction (G := G) p)) :
          Set (G → ℂ))
  exact LinearMap.range_liftBaseChange (A := pElementaryScalarExtensionRing)
    (pElementaryInducedCharacterToFunction (G := G) p)

/-- Helper for Theorem 10-10.2-1: the algebraic integers in `ℂ` are faithfully flat over `ℤ`. -/
private theorem integral_closure_faithfullyFlat_over_int_local :
    Module.FaithfullyFlat ℤ pElementaryScalarExtensionRing := by
  let A := pElementaryScalarExtensionRing
  let f := algebraMap A ℂ
  have hAC : Function.Injective f := IsIntegralClosure.algebraMap_injective A ℤ ℂ
  letI : IsDomain A := Function.Injective.isDomain f hAC
  have hZA : Function.Injective (algebraMap ℤ A) := by
    -- Compose `ℤ → A` with `A → ℂ` to reflect injectivity from the characteristic-zero field.
    intro m n hmn
    have hmn' := congrArg f hmn
    rw [← IsScalarTower.algebraMap_apply ℤ A ℂ m, ← IsScalarTower.algebraMap_apply ℤ A ℂ n] at hmn'
    exact Int.cast_injective hmn'
  letI : Module.IsTorsionFree ℤ A :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hZA
  haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ ℂ
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap ℤ A)) := by
    -- Integral extensions are surjective on prime spectra, so torsion-free flatness upgrades to
    -- faithful flatness.
    exact Algebra.IsIntegral.comap_surjective ℤ A
  exact Module.FaithfullyFlat.of_comap_surjective hsurj

/-- Helper for Theorem 10-10.2-1: the normalized character pairing expands over finite
algebraic-integer linear combinations in its left argument. -/
private theorem groupFunctionPairing_sum_algebra_smul_left_local
    {ι : Type*} (s : Finset ι) (a : ι → pElementaryScalarExtensionRing)
    (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ =
      ∑ j ∈ s, algebraMap pElementaryScalarExtensionRing ℂ (a j) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Replace the algebraic-integer scalar by its complex image, then expand across the sum.
      have hsmul :
          (a i • χ i : G → ℂ) = algebraMap pElementaryScalarExtensionRing ℂ (a i) • χ i := by
        ext g
        simp [Algebra.smul_def, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Theorem 10-10.2-1: a finite algebraic-integer linear combination of pairwise
nonisomorphic irreducible characters can vanish only when every coefficient is zero. -/
private theorem irreducible_character_coefficients_eq_zero_local
    {ι : Type*}
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : ι →₀ pElementaryScalarExtensionRing)
    (hc : c.sum (fun i a ↦ a • (π i).character) = 0) :
    c = 0 := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have horth :
      Pairwise fun i j ↦
        ⟪(π i).character, (π j).character⟫ = (0 : ℂ) :=
    Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  ext i
  -- Pair the vanishing relation with the `i`-th irreducible character to isolate one coefficient.
  have hpair0 :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ = (0 : ℂ) := by
    simpa [Representation.groupFunctionPairingOverField] using
      congrArg
        (fun φ : G → ℂ ↦ Representation.groupFunctionPairingOverField ℂ φ (π i).character) hc
  have hpair_expand :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ =
        c.sum
          (fun j a ↦ algebraMap pElementaryScalarExtensionRing ℂ a *
            ⟪(π j).character, (π i).character⟫) := by
    simpa [Finsupp.sum] using
      (groupFunctionPairing_sum_algebra_smul_left_local (G := G)
        (s := c.support) (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character))
  rw [hpair_expand] at hpair0
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : ℂ) := by
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    let X : Rep ℂ G := (CategoryTheory.forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (π i)
    let e₁ : ((π i) ⟶ (π i)) ≃ₗ[ℂ] (X ⟶ X) :=
      (FDRep.forget₂HomLinearEquiv (π i) (π i)).symm
    let e₂ : (X ⟶ X) ≃ₗ[ℂ] (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
    let e : ((π i) ⟶ (π i)) ≃ₗ[ℂ] (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      e₁.trans e₂
    letI : FiniteDimensional ℂ (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
    have hnontriv : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      refine ⟨0, e (𝟙 (π i)), ?_⟩
      intro h
      apply CategoryTheory.id_nonzero (π i)
      exact e.injective h.symm
    letI : Nontrivial (Representation.IntertwiningMap (π i).ρ (π i).ρ) := hnontriv
    have hpair :
        ⟪(π i).character, (π i).character⟫ =
          Module.finrank ℂ (Representation.IntertwiningMap (π i).ρ (π i).ρ) :=
      Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        ℂ (π i).ρ (π i).ρ
    rw [hpair]
    exact_mod_cast Module.finrank_pos.ne'
  have hpair_single :
      c.sum
          (fun j a ↦ algebraMap pElementaryScalarExtensionRing ℂ a *
            ⟪(π j).character, (π i).character⟫) =
        algebraMap pElementaryScalarExtensionRing ℂ (c i) *
          ⟪(π i).character, (π i).character⟫ := by
    rw [Finsupp.sum]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hi
      by_cases hci : c i = 0
      · simp [hci]
      · exact (hi (Finsupp.mem_support_iff.2 hci)).elim
  rw [hpair_single] at hpair0
  have hcoeffC : algebraMap pElementaryScalarExtensionRing ℂ (c i) = 0 :=
    (mul_eq_zero.mp hpair0).resolve_right hself_ne
  have hcoeffA : c i = 0 := by
    exact (IsIntegralClosure.algebraMap_injective pElementaryScalarExtensionRing ℤ ℂ) <| by
      simpa using hcoeffC
  simpa using hcoeffA

/-- Helper for Theorem 10-10.2-1: realizing a basis expansion in `A ⊗ R(G)` evaluates the
coefficients against the corresponding irreducible characters. -/
private theorem tensorCharacterRingToFunction_finsupp_sum_local
    {ι : Type*} (b : Module.Basis ι ℤ (R(G))) (c : ι →₀ pElementaryScalarExtensionRing) :
    ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : pElementaryScalarExtensionRing ⊗R(G)) : G → ℂ) =
      c.sum fun i a ↦ a • (((b i : R(G)) : G → ℂ)) := by
  classical
  -- Evaluate the ambient realization map termwise on the chosen basis expansion.
  simp [Finsupp.sum, map_sum]

/-- Helper for Theorem 10-10.2-1: the ambient realization of `A ⊗ R(G)` as complex-valued
functions is injective. -/
private theorem tensorCharacterRingToFunction_injective_local :
    Function.Injective
      (fun ξ : pElementaryScalarExtensionRing ⊗R(G) ↦ ((ξ : G → ℂ))) := by
  classical
  intro ξ η hξη
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  letI : Fintype ι := hι
  let b := Representation.irreducible_characters_basis_of_complete_family
    ℂ π hπ_pairwise hπ_complete
  have hdiff : ((ξ - η : pElementaryScalarExtensionRing ⊗R(G)) : G → ℂ) = 0 := by
    -- Compare the difference of the two tensors after realization.
    have hsub := congrArg
      (fun z : G → ℂ ↦ z - ((η : pElementaryScalarExtensionRing ⊗R(G)) : G → ℂ))
      hξη
    simpa [map_sub] using hsub
  obtain ⟨c, hc⟩ :=
    TensorProduct.eq_repr_basis_right (R := ℤ) (M := pElementaryScalarExtensionRing)
      (𝒞 := b) (x := ξ - η)
  have hrealized :
      c.sum (fun i a ↦ a • (π i).character) = 0 := by
    -- Rewrite the chosen tensor coordinates through the ambient realization map.
    have hsum := tensorCharacterRingToFunction_finsupp_sum_local (G := G) b c
    have hsum' :
        ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : pElementaryScalarExtensionRing ⊗R(G)) : G → ℂ) =
          c.sum (fun i a ↦ a • (π i).character) := by
      simpa [b, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using hsum
    rw [← hsum', hc, hdiff]
  have hc_zero : c = 0 :=
    irreducible_character_coefficients_eq_zero_local
      (G := G) π hπ_pairwise hπ_complete c hrealized
  have hξη' : ξ - η = 0 := by
    -- Once all basis coefficients vanish, the tensor difference vanishes as well.
    rw [← hc, hc_zero]
    simp
  exact sub_eq_zero.mp hξη'

/-- Helper for Theorem 10-10.2-1: an honest character whose underlying class function lies in the
local scalar-extension owner has trivial class in the quotient `R(G) / V_p`. -/
private theorem quotient_class_eq_zero_of_mem_pElementaryScalarExtensionOwner_local
    (p : ℕ) (χ : R(G))
    (hχ : (χ : G → ℂ) ∈ pElementaryScalarExtensionOwner (G := G) p) :
    Submodule.mkQ (V[p](G)) χ = 0 := by
  -- Route correction: identify the local owner directly with the realized range of `A ⊗ V_p`.
  rw [pElementaryScalarExtensionOwner_eq_range_local (G := G) (p := p)] at hχ
  rcases hχ with ⟨ξ, hξ⟩
  have hξ' : (ξ : G → ℂ) = χ := by
    simpa using hξ
  have htensor :
      ((1 : pElementaryScalarExtensionRing) ⊗ₜ[ℤ] χ : pElementaryScalarExtensionRing ⊗R(G)) =
        LinearMap.lTensor pElementaryScalarExtensionRing (V[p](G)).subtype ξ := by
    -- Compare both ambient tensors through their common realized function in `G → ℂ`.
    apply tensorCharacterRingToFunction_injective_local (G := G)
    calc
      (((1 : pElementaryScalarExtensionRing) ⊗ₜ[ℤ] χ :
          pElementaryScalarExtensionRing ⊗R(G)) : G → ℂ) = χ := by
        ext g
        simp
      _ = (ξ : G → ℂ) := by
        simpa using hξ'.symm
      _ = ((show pElementaryScalarExtensionRing ⊗R(G) from
              LinearMap.lTensor pElementaryScalarExtensionRing (V[p](G)).subtype ξ) :
            G → ℂ) := by
        simpa using
          tensorPElementaryInducedCharacterToFunction_eq_tensorCharacterRing_lTensor_local
            (G := G) (p := p) ξ
  have hquot_tmul :
      (1 : pElementaryScalarExtensionRing) ⊗ₜ[ℤ]
          (Submodule.mkQ (V[p](G)) χ) = 0 := by
    -- Quotienting kills the tensor image of `V_p`, so the previous ambient tensor equality
    -- descends to a vanishing pure tensor in the quotient.
    have hquot :=
      congrArg (LinearMap.lTensor pElementaryScalarExtensionRing (Submodule.mkQ (V[p](G))))
        htensor
    calc
      (1 : pElementaryScalarExtensionRing) ⊗ₜ[ℤ]
          (Submodule.mkQ (V[p](G)) χ) =
          LinearMap.lTensor pElementaryScalarExtensionRing (Submodule.mkQ (V[p](G)))
            (LinearMap.lTensor pElementaryScalarExtensionRing (V[p](G)).subtype ξ) := by
        simpa [LinearMap.lTensor_tmul] using hquot
      _ = 0 := by
        have hmkQ_subtype :
            (Submodule.mkQ (V[p](G))).comp (V[p](G)).subtype = 0 := by
          ext x
          exact (Submodule.Quotient.mk_eq_zero (V[p](G))).2 x.2
        have hcomp :
            (LinearMap.lTensor pElementaryScalarExtensionRing (Submodule.mkQ (V[p](G)))).comp
                (LinearMap.lTensor pElementaryScalarExtensionRing (V[p](G)).subtype) = 0 := by
          rw [← LinearMap.lTensor_comp, hmkQ_subtype, LinearMap.lTensor_zero]
        simpa using congrArg (fun f ↦ f ξ) hcomp
  letI : Module.FaithfullyFlat ℤ pElementaryScalarExtensionRing :=
    integral_closure_faithfullyFlat_over_int_local
  exact
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff
      (R := ℤ) (M := R(G) ⧸ V[p](G)) (A := pElementaryScalarExtensionRing)
      (Submodule.mkQ (V[p](G)) χ)).mp hquot_tmul

/-- Helper for Theorem 10-10.2-1: the intersection of the local scalar-extension owner
`A ⊗ V_p` with the integral character ring is exactly the image of `V_p`. -/
private theorem pElementaryScalarExtensionOwner_inter_characterRing_eq_image_local
    (p : ℕ) :
    ((pElementaryScalarExtensionOwner (G := G) p : Set (G → ℂ)) ∩
        (R(G) : Set (G → ℂ))) =
      ((LinearMap.range (pElementaryInducedCharacterToFunction (G := G) p)) :
        Set (G → ℂ)) := by
  ext φ
  constructor
  · rintro ⟨hφscalar, hφring⟩
    let φR : R(G) := ⟨φ, hφring⟩
    have hq :
        Submodule.mkQ (V[p](G)) φR = 0 :=
      quotient_class_eq_zero_of_mem_pElementaryScalarExtensionOwner_local
        (G := G) (p := p) φR hφscalar
    have hmem : φR ∈ V[p](G) := by
      exact (Submodule.Quotient.mk_eq_zero (V[p](G))).1 hq
    -- Vanishing in the quotient means the integral character already comes from `V_p`.
    exact ⟨⟨φR, hmem⟩, rfl⟩
  · rintro ⟨β, rfl⟩
    constructor
    · exact
        mem_pElementaryScalarExtensionOwner_of_mem
          (G := G) p β.property
    · exact (β : R(G)).property

/-- Helper for Theorem 10-10.2-1: the Chapter `10.3` constant-value witness yields some
prime-to-`p` scalar multiple of the trivial character inside Brauer's subgroup `V_p`. -/
private theorem exists_coprime_scalar_smul_one_mem_pElementaryInducedCharacterSpan
    (p : Nat.Primes) (n l : ℕ) (hcard : Nat.card G = (p : ℕ) ^ n * l)
    (hl : Nat.Coprime p l) :
    ∃ N : ℕ, Nat.Coprime p N ∧ N • (1 : R(G)) ∈ V[p](G) := by
  obtain ⟨N, hNcoprime, θ, hθconst⟩ :=
    exists_constant_pregular_value_tensor_character_in_pElementaryScalarExtension
      (G := G) p
  let δ : R(G) :=
    ⟨fun s : G ↦ if IsPRegular (p : ℕ) s then (1 : ℂ) else 0,
      pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
  have hδeq :
      δ = (1 : R(G)) :=
    pregular_indicator_eq_one (G := G) p n l hcard hl
  have hall : ∀ s : G, IsPRegular (p : ℕ) s := by
    -- Once the indicator equals `1`, every group element is `p`-regular.
    intro s
    have hsval :
        ((δ : G → ℂ) s) = 1 := by
      exact congrFun (congrArg (fun χ : R(G) ↦ (χ : G → ℂ)) hδeq) s
    by_cases hs : IsPRegular (p : ℕ) s
    · exact hs
    · exact False.elim (by simp [δ, hs] at hsval)
  have hθconst_all : ∀ s : G, (θ : G → ℂ) s = (N : ℂ) := by
    -- The tensor witness is constant on all of `G` because every element is `p`-regular.
    intro s
    exact hθconst s (hall s)
  have hθ_eq_scalar :
      (θ : G → ℂ) = ((N • (1 : R(G)) : R(G)) : G → ℂ) := by
    -- Compare both functions pointwise with the same constant value `N`.
    ext s
    simpa using hθconst_all s
  have hdesc : N • (1 : R(G)) ∈ V[p](G) := by
    -- Route correction: descend the final constant character through the local intersection
    -- theorem `(A ⊗ V_p) ∩ R(G) = V_p`, instead of trying to finish inside the tensor owner.
    have hscalar_mem :
        (((N • (1 : R(G)) : R(G)) : G → ℂ)) ∈
          pElementaryScalarExtensionOwner (G := G) (p : ℕ) := by
      rw [← hθ_eq_scalar]
      exact θ.2
    have hconst_mem_inter :
        (((N • (1 : R(G)) : R(G)) : G → ℂ)) ∈
          ((pElementaryScalarExtensionOwner (G := G) (p : ℕ) : Set (G → ℂ)) ∩
            (R(G) : Set (G → ℂ))) := by
      exact ⟨hscalar_mem, (N • (1 : R(G)) : R(G)).property⟩
    rw [pElementaryScalarExtensionOwner_inter_characterRing_eq_image_local
      (G := G) (p := (p : ℕ))] at hconst_mem_inter
    rcases hconst_mem_inter with ⟨β, hβ⟩
    have hβeq : (β : R(G)) = N • (1 : R(G)) := by
      apply Subtype.ext
      simpa [pElementaryInducedCharacterToFunction] using hβ
    simpa [hβeq] using β.property
  exact ⟨N, hNcoprime, hdesc⟩

/-- Theorem 10-10.2-1: if `V_p` is the subgroup of `R(G)` generated by characters induced from
representations of `p`-elementary subgroups of the finite group `G`, then `V_p` has finite index
in `R(G)` and that index is coprime to `p`. -/
theorem pElementaryInducedCharacterSpan_finiteIndex_and_index_coprime (p : Nat.Primes) :
    let Vp := V[p](G)
    Vp.toAddSubgroup.FiniteIndex ∧ Nat.Coprime p Vp.toAddSubgroup.index :=
  by
    let n := Nat.factorization (Nat.card G) p
    let l := ordCompl[(p : ℕ)] (Nat.card G)
    have hcard : Nat.card G = (p : ℕ) ^ n * l := by
      -- Split `|G|` into its `p`-part and prime-to-`p` part.
      simpa [n, l, mul_comm] using
        (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
    have hl : Nat.Coprime p l := by
      -- The complementary factor is prime to `p` by construction.
      simpa [l] using Nat.coprime_ordCompl (n := Nat.card G) p.2 (Nat.card_pos.ne')
    obtain ⟨N, hNcoprime, hNscalar⟩ :=
      exists_coprime_scalar_smul_one_mem_pElementaryInducedCharacterSpan
        (G := G) p n l hcard hl
    simpa [n, l] using
      finiteIndex_and_coprime_of_scalar_mem_pElementaryInducedCharacterSpan
        (G := G) p N hNcoprime hNscalar

end

end Representation
