import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_2_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.TensorCharacterBridge
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open scoped Representation SubgroupInduction TensorProduct

universe v

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]
variable {p : ℕ}

/-- A finite group is equipped with its canonical `Fintype` structure when building the tensor
realization of `V_p`. -/
private abbrev instFintypeLemma101023Group : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeLemma101023Group

/-- A subgroup of a finite group is finite. -/
private abbrev instFintypeLemma101023Subgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H
attribute [local instance] instFintypeLemma101023Subgroup

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's `A ⊗ V_p`.
-- * core/canonical: the tensor product owner
--   `TensorProduct ℤ A ((Representation.pElementaryInducedCharacterSpan p G))`.
-- * bridge/view: the canonical realization map
--   `tensorPElementaryInducedCharacterToFunction A p G` and its range-submodule
--   `pElementaryInducedCharacterScalarExtension A p G` in `G → ℂ`.
--
-- Primitive data: the tensor product owner and Brauer's subgroup
--   `(Representation.pElementaryInducedCharacterSpan p G)`.
-- Derived API: the range submodule, the coercion to functions, and the span/intersection lemmas.
scoped[Representation] notation:max A " ⊗V[" p "](" G ")" =>
  TensorProduct ℤ A ((Representation.pElementaryInducedCharacterSpan p G))

/-- The canonical inclusion of Brauer's subgroup `V_p` into the ambient space of complex-valued
functions on `G`. -/
abbrev pElementaryInducedCharacterToFunction
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    (Representation.pElementaryInducedCharacterSpan p G) →ₗ[ℤ] G → ℂ :=
  ((R(G)).toSubmodule.subtype).comp ((Representation.pElementaryInducedCharacterSpan p G)).subtype

/-- The canonical realization of LinearRepresentations_Serre_1977's tensor product `A ⊗ V_p` as complex-valued functions on
`G`. -/
abbrev tensorPElementaryInducedCharacterToFunction
    (A : Type v) [CommRing A] [Algebra A ℂ]
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    A ⊗V[p](G) →ₗ[A] G → ℂ :=
  (pElementaryInducedCharacterToFunction p G).liftBaseChange A

instance : CoeFun (A ⊗V[p](G)) (fun _ ↦ G → ℂ) where
  coe := tensorPElementaryInducedCharacterToFunction A p G

@[simp] theorem coe_tmul_pElementaryInducedCharacter
    (a : A) (χ : (Representation.pElementaryInducedCharacterSpan p G)) :
    ((a ⊗ₜ[ℤ] χ : A ⊗V[p](G)) : G → ℂ) = a • ((χ : R(G)) : G → ℂ) := by
  simp [tensorPElementaryInducedCharacterToFunction, pElementaryInducedCharacterToFunction]

/-- The ambient complex-function realization of LinearRepresentations_Serre_1977's tensor product `A ⊗V[p](G)`. This is a
bridge/view of the owner `A ⊗V[p](G)`. -/
def pElementaryInducedCharacterScalarExtension (A : Type v) [CommRing A] [Algebra A ℂ]
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    Submodule A (G → ℂ) :=
  LinearMap.range (tensorPElementaryInducedCharacterToFunction A p G)

/-- The realization bridge `pElementaryInducedCharacterScalarExtension A p G` is the `A`-span of
the canonical image of `V_p` in `G → ℂ`. -/
theorem pElementaryInducedCharacterScalarExtension_eq_span :
    pElementaryInducedCharacterScalarExtension A p G =
      Submodule.span A
        ((LinearMap.range (pElementaryInducedCharacterToFunction p G)) : Set (G → ℂ)) :=
  by
    rw [pElementaryInducedCharacterScalarExtension, LinearMap.range_liftBaseChange]

/-- Every realized tensor character in `A ⊗V[p](G)` belongs to its ambient bridge/view
`pElementaryInducedCharacterScalarExtension A p G`. -/
theorem tensorPElementaryInducedCharacter_mem_pElementaryInducedCharacterScalarExtension
    (χ : A ⊗V[p](G)) :
    (χ : G → ℂ) ∈ pElementaryInducedCharacterScalarExtension A p G :=
  ⟨χ, rfl⟩

-- Proof sketch: `V_p` maps into the generating image whose `A`-span realizes `A ⊗V[p](G)`.
/-- Coercing an element of Brauer's subgroup `V_p` to a class function lands in the realization of
`A ⊗V[p](G)`. -/
theorem mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementaryInducedCharacterSpan
    (χ : R(G)) (hχ : χ ∈ (Representation.pElementaryInducedCharacterSpan p G)) :
    (χ : G → ℂ) ∈ pElementaryInducedCharacterScalarExtension A p G := by
  let ψ : A ⊗V[p](G) :=
    (1 : A) ⊗ₜ[ℤ] (⟨χ, hχ⟩ : (Representation.pElementaryInducedCharacterSpan p G))
  have hψ : (ψ : G → ℂ) = χ := by
    ext g
    simp [ψ]
  rw [← hψ]
  exact tensorPElementaryInducedCharacter_mem_pElementaryInducedCharacterScalarExtension ψ

/-- Helper for Lemma 10-10.2-3: the `A`-scalar multiple of a Brauer generator already lies in the
ambient scalar extension `A ⊗ R(G)`. -/
private lemma smul_mem_characterRingScalarExtension_of_pElementary_generator
    (a : A) (χ : Representation.pElementaryInducedCharacterSpan p G) :
    a • (((χ : R(G)) : G → ℂ)) ∈ characterRingScalarExtension A G := by
  -- A Brauer generator is an honest virtual character of `G`, so any `A`-scalar multiple of its
  -- realization belongs to the ambient scalar-extended character ring.
  exact
    (characterRingScalarExtension A G).smul_mem a
      (mem_characterRingScalarExtension_of_mem_characterRing
        (((χ : R(G)) : G → ℂ)) (χ : R(G)).property)

-- Proof sketch: the generators of `V_p` already lie in the integral character ring `R(G)`, so
-- the `A`-span defining `A ⊗ V_p` is contained in the `A`-span defining `A ⊗ R(G)`.
/-- LinearRepresentations_Serre_1977's scalar extension `A ⊗ V_p` is contained in the scalar-extended character ring
`A ⊗ R(G)`. -/
theorem pElementaryInducedCharacterScalarExtension_le_characterRingScalarExtension :
    pElementaryInducedCharacterScalarExtension A p G ≤ characterRingScalarExtension A G := by
  rintro _ ⟨χ, rfl⟩
  induction χ using TensorProduct.induction_on with
  | zero =>
      exact zero_mem _
  | tmul a χ =>
      -- Route correction: isolate the bridge step for a single Brauer generator before returning
      -- to tensor-product induction.
      simpa [coe_tmul_pElementaryInducedCharacter] using
        smul_mem_characterRingScalarExtension_of_pElementary_generator
          (A := A) (p := p) a χ
  | add χ ψ hχ hψ =>
      simpa [map_add] using (characterRingScalarExtension A G).add_mem hχ hψ

/-- Helper for Lemma 10-10.2-3: every element of Brauer's subgroup `V_p` already lies in the
`A`-span of honest induced characters from `p`-elementary subgroups. -/
lemma mem_span_pElementary_induced_characters_of_mem_pElementaryInducedCharacterSpan
    {χ : R(G)} (hχ : χ ∈ (Representation.pElementaryInducedCharacterSpan p G)) :
    (χ : G → ℂ) ∈
      Submodule.span A
        { ξ : G → ℂ |
          ∃ H : Subgroup G, IsPElementary p H ∧ ∃ W : FDRep ℂ H,
            ξ = Ind[H](W.character) } := by
  classical
  let X : Finset (Subgroup G) := Finset.univ.filter fun H : Subgroup G ↦ IsPElementary p H
  let S : Set (G → ℂ) :=
    { ξ : G → ℂ |
        ∃ H : Subgroup G, IsPElementary p H ∧ ∃ W : FDRep ℂ H,
          ξ = Ind[H](W.character) }
  -- Route correction: expand `V_p` through the canonical Artin-induction presentation, then
  -- replace each subgroup virtual character by a difference of honest subgroup characters.
  rw [Representation.pElementaryInducedCharacterSpan] at hχ
  obtain ⟨ξ, hξ⟩ :=
    Representation.exists_family_characterRingInduction_eq_of_mem_artinInducedCharacterSubmodule
      (X := X) hχ
  choose Vpos Vneg hdiff using
    fun H : X ↦ Representation.virtual_character_eq_character_difference H.1 (ξ H)
  have hterm :
      ∀ H : X, Ind[H.1]((ξ H : H.1 → ℂ)) ∈ Submodule.span A S := by
    intro H
    have hH : IsPElementary p H.1 := (Finset.mem_filter.mp H.2).2
    have hpos : Ind[H.1]((Vpos H).character) ∈ Submodule.span A S := by
      exact Submodule.subset_span ⟨H.1, hH, Vpos H, rfl⟩
    have hneg : Ind[H.1]((Vneg H).character) ∈ Submodule.span A S := by
      exact Submodule.subset_span ⟨H.1, hH, Vneg H, rfl⟩
    -- Rewrite one induced virtual character as a difference of honest induced characters.
    have hrewrite :
        Ind[H.1]((ξ H : H.1 → ℂ)) =
          Ind[H.1]((Vpos H).character) - Ind[H.1]((Vneg H).character) := by
      calc
        Ind[H.1]((ξ H : H.1 → ℂ)) =
            Ind[H.1]((Vpos H).character - (Vneg H).character) := by
              rw [hdiff H]
        _ = Ind[H.1]((Vpos H).character) + Ind[H.1](-(Vneg H).character) := by
              simpa [sub_eq_add_neg] using
                Subgroup.inducedClassFunction_map_add H.1 (Vpos H).character
                  (-(Vneg H).character)
        _ = Ind[H.1]((Vpos H).character) - Ind[H.1]((Vneg H).character) := by
              have hmap_neg :
                  Ind[H.1](-(Vneg H).character) = -Ind[H.1]((Vneg H).character) := by
                simpa using
                  (Subgroup.inducedClassFunction_map_smul (H := H.1) (-1 : ℂ)
                    (Vneg H).character)
              simp [sub_eq_add_neg, hmap_neg]
    rw [hrewrite]
    exact Submodule.sub_mem (Submodule.span A S) hpos hneg
  have hsum :
      (∑ H : X, Ind[H.1]((ξ H : H.1 → ℂ))) ∈ Submodule.span A S := by
    simpa using
      (Submodule.sum_mem (Submodule.span A S) fun H _ ↦ hterm H)
  have hχ_fun : (χ : G → ℂ) = ∑ H : X, Ind[H.1]((ξ H : H.1 → ℂ)) := by
    -- Coerce the owner-level family decomposition to the ambient function space on `G`.
    simpa [Subgroup.characterRingInduction_apply] using
      congrArg (fun ζ : R(G) ↦ (ζ : G → ℂ)) hξ
  change (χ : G → ℂ) ∈ Submodule.span A S
  rw [hχ_fun]
  exact hsum

-- Proof sketch: the generators of `V_p` are exactly the characters induced from
-- finite-dimensional complex representations of `p`-elementary subgroups. Taking the `A`-span of
-- those generators gives the image of the scalar-extended induction map, while taking the
-- `A`-span of the whole subgroup `V_p` gives `pElementaryInducedCharacterScalarExtension A p G`;
-- the two spans coincide because `V_p` is generated by those induced characters.
/-- Lemma 10-10.2-3 (1): the image of `A ⊗ Ind` is `A ⊗ V_p`; in Lean, the image is the
`A`-span of the characters induced from `p`-elementary subgroups, and `A ⊗ V_p` is
`pElementaryInducedCharacterScalarExtension A p G`. -/
theorem span_pElementary_induced_characters_eq_pElementaryInducedCharacterScalarExtension :
    Submodule.span A
      { χ : G → ℂ |
        ∃ H : Subgroup G, IsPElementary p H ∧ ∃ W : FDRep ℂ H,
          χ = Ind[H](W.character) } =
      pElementaryInducedCharacterScalarExtension A p G := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    intro χ hχ
    rcases hχ with ⟨H, hH, W, rfl⟩
    let η : R(G) := ⟨Ind[H](W.character), by
      let ξ : R(H) := ⟨W.character, rep_character_mem_characterRing (Rep.of W.ρ)⟩
      simpa [ξ] using Subgroup.inducedClassFunction_mem_characterRing H ξ⟩
    have hη : η ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
      exact mem_pElementaryInducedCharacterSpan_of_eq_induced_character p H hH W rfl
    -- Honest induced generators already belong to `V_p`, hence to its scalar extension.
    simpa [η] using
      mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementaryInducedCharacterSpan
        (A := A) η hη
  · rw [pElementaryInducedCharacterScalarExtension_eq_span]
    refine Submodule.span_le.2 ?_
    intro χ hχ
    rcases hχ with ⟨ξ, rfl⟩
    -- Every generator coming from `V_p` is an integral combination of honest induced characters.
    exact mem_span_pElementary_induced_characters_of_mem_pElementaryInducedCharacterSpan
      (A := A) (p := p) ξ.property

end

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]
variable {p : ℕ} [Fact p.Prime]

open CategoryTheory

/-- A finite group is equipped with its canonical `Fintype` structure when comparing `A ⊗ V_p`
with `R(G)`. -/
private abbrev instFintypeLemma101023GroupCompare : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeLemma101023GroupCompare

/-- Helper for Lemma 10-10.2-3: if `A` is the integral closure of `ℤ` in `ℂ`, then `A` is
faithfully flat over `ℤ`. -/
lemma integral_closure_faithfullyFlat_over_int :
    Module.FaithfullyFlat ℤ A := by
  let f := algebraMap A ℂ
  have hAC : Function.Injective f := IsIntegralClosure.algebraMap_injective A ℤ ℂ
  letI : IsDomain A := Function.Injective.isDomain f hAC
  -- Compose `ℤ → A` with `A → ℂ` to reflect injectivity from the characteristic-zero field `ℂ`.
  have hZA : Function.Injective (algebraMap ℤ A) := by
    intro m n hmn
    have hmn' := congrArg f hmn
    rw [← IsScalarTower.algebraMap_apply ℤ A ℂ m, ← IsScalarTower.algebraMap_apply ℤ A ℂ n] at hmn'
    exact Int.cast_injective hmn'
  letI : Module.IsTorsionFree ℤ A :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hZA
  haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ ℂ
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap ℤ A)) := by
    exact Algebra.IsIntegral.comap_surjective ℤ A
  exact Module.FaithfullyFlat.of_comap_surjective hsurj

/-- Helper for Lemma 10-10.2-3: view `R(G)` as its underlying `ℤ`-submodule of complex-valued
functions on `G`. -/
abbrev characterRing_toSubmodule :
    R(G) →ₗ[ℤ] (R(G)).toSubmodule :=
  show R(G) →ₗ[ℤ] (R(G)).toSubmodule from
    (show R(G) ≃ₗ[ℤ] (R(G)).toSubmodule from LinearEquiv.refl ℤ R(G)).toLinearMap

/-- Helper for Lemma 10-10.2-3: the ambient inclusion `R(G) ↪ G → ℂ`. -/
abbrev characterRing_toFunction :
    R(G) →ₗ[ℤ] G → ℂ :=
  ((R(G)).toSubmodule.subtype).comp (characterRing_toSubmodule (G := G))

omit [Fact p.Prime] in
/-- Helper for Lemma 10-10.2-3: the realization of `V_p` factors through the ambient inclusion of
`R(G)` into complex-valued functions. -/
lemma pElementaryInducedCharacterToFunction_eq_characterRing_toFunction_comp_subtype :
    pElementaryInducedCharacterToFunction p G =
      (characterRing_toFunction (G := G)).comp
        ((Representation.pElementaryInducedCharacterSpan p G)).subtype := by
  ext χ g
  rfl

/-- Helper for Lemma 10-10.2-3: every finite group admits a finite complete pairwise
nonisomorphic family of irreducible complex representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family_local :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (Representation.leftRegular ℂ G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ i).toSubmodule)
              ((σ i).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := Representation.leftRegular ℂ G)
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
    -- Each representative comes from an irreducible regular summand.
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact Representation.FDRep.simple_of_isIrreducible (π q)
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := hπ_simple
        exists_iso := ?_ }
    intro τ _
    let τρ := τ.ρ
    have hτ_irreducible : Representation.IsIrreducible τρ := by
      exact Representation.FDRep.isIrreducible_of_simple τ
    letI : Representation.IsIrreducible τρ := hτ_irreducible
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero τ hzero
    letI : Nontrivial τ := hτ_nontriv
    have hτ_pos : 0 < Module.finrank ℂ τ := Module.finrank_pos
    have hτ_mult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank ℂ τ := by
      simpa [τρ] using
        Representation.leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr τρ
          inferInstance
    have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
      rw [hτ_mult]
      exact hτ_pos
    obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
    let q : ι := ⟦j⟧
    rcases hjτ with ⟨eτ⟩
    rcases Quotient.exact (Quotient.out_eq q) with ⟨eqj⟩
    -- Pick one regular summand isomorphic to `τ`, then pass to its quotient class.
    refine ⟨q, ?_⟩
    exact ⟨(eτ.symm.trans eqj.symm).toFDRepIso⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

omit [Fact p.Prime] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Lemma 10-10.2-3: the normalized character pairing expands over finite `A`-linear
combinations in its left argument after transporting coefficients along `A → ℂ`. -/
private theorem groupFunctionPairing_sum_algebra_smul_left
    {ι : Type*} (s : Finset ι) (a : ι → A) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, algebraMap A ℂ (a j) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Replace the `A`-scalar by the corresponding complex scalar, then expand across the sum.
      have hsmul : (a i • χ i : G → ℂ) = algebraMap A ℂ (a i) • χ i := by
        ext g
        simp [Algebra.smul_def, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Lemma 10-10.2-3: a finite `A`-linear combination of the characters of a complete
pairwise nonisomorphic irreducible family can vanish only if every coefficient is zero. -/
private lemma irreducible_character_coefficients_eq_zero
    {ι : Type*}
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c : ι →₀ A)
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
      congrArg (fun φ : G → ℂ ↦ Representation.groupFunctionPairingOverField ℂ φ (π i).character) hc
  have hpair_expand :
      ⟪c.sum (fun j a ↦ a • (π j).character), (π i).character⟫ =
        c.sum (fun j a ↦ algebraMap A ℂ a * ⟪(π j).character, (π i).character⟫) := by
    simpa [Finsupp.sum] using
      (groupFunctionPairing_sum_algebra_smul_left (A := A) (G := G)
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
      c.sum (fun j a ↦ algebraMap A ℂ a * ⟪(π j).character, (π i).character⟫) =
        algebraMap A ℂ (c i) * ⟪(π i).character, (π i).character⟫ := by
    rw [Finsupp.sum]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hi
      by_cases hci : c i = 0
      · simp [hci]
      · exact (hi (Finsupp.mem_support_iff.2 hci)).elim
  rw [hpair_single] at hpair0
  have hcoeffC : algebraMap A ℂ (c i) = 0 :=
    (mul_eq_zero.mp hpair0).resolve_right hself_ne
  have hcoeffA : c i = 0 := by
    exact (IsIntegralClosure.algebraMap_injective A ℤ ℂ) <| by
      simpa using hcoeffC
  simpa using hcoeffA

omit [Fact p.Prime] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Lemma 10-10.2-3: realizing a basis expansion in `A ⊗ R(G)` evaluates
coefficientwise on the corresponding virtual characters. -/
private lemma tensorCharacterRingToFunction_finsupp_sum
    {ι : Type*} (b : Module.Basis ι ℤ (R(G))) (c : ι →₀ A) :
    ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : A ⊗R(G)) : G → ℂ) =
      c.sum fun i a ↦ a • (((b i : R(G)) : G → ℂ)) := by
  classical
  -- Evaluate the ambient realization map termwise on the finitely supported basis expansion.
  simp [Finsupp.sum, map_sum]

/-- Helper for Lemma 10-10.2-3: the ambient realization of `A ⊗ R(G)` as complex-valued
functions is injective. -/
lemma tensorCharacterRingToFunction_injective :
    Function.Injective (fun χ : A ⊗R(G) ↦ ((χ : G → ℂ))) := by
  classical
  intro ξ η hξη
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family_local (G := G)
  letI : Fintype ι := hι
  let b := Representation.irreducible_characters_basis_of_complete_family
    ℂ π hπ_pairwise hπ_complete
  have hdiff : ((ξ - η : A ⊗R(G)) : G → ℂ) = 0 := by
    -- Route correction: expand the tensor difference in an irreducible-character basis and kill
    -- its coordinates by orthogonality, rather than using the false tensor-collapse identity.
    have hsub := congrArg (fun z : G → ℂ ↦ z - ((η : A ⊗R(G)) : G → ℂ)) hξη
    simpa [map_sub] using hsub
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (R := ℤ) (M := A) (𝒞 := b) (x := ξ - η)
  have hrealized :
      c.sum (fun i a ↦ a • (π i).character) = 0 := by
    -- Rewrite the chosen tensor coordinates through the ambient realization map.
    have hsum := tensorCharacterRingToFunction_finsupp_sum (A := A) (G := G) b c
    have hsum' :
        ((c.sum fun i a ↦ a ⊗ₜ[ℤ] b i : A ⊗R(G)) : G → ℂ) =
          c.sum (fun i a ↦ a • (π i).character) := by
      simpa [b, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using hsum
    rw [← hsum', hc, hdiff]
  have hc_zero : c = 0 :=
    irreducible_character_coefficients_eq_zero
      (A := A) (G := G) π hπ_pairwise hπ_complete c hrealized
  have hξη' : ξ - η = 0 := by
    -- Once the basis coefficients vanish, the tensor itself vanishes.
    rw [← hc, hc_zero]
    simp
  exact sub_eq_zero.mp hξη'

/-- Helper for Lemma 10-10.2-3: tensoring the ambient inclusion `R(G) ↪ G → ℂ` with `A`
preserves injectivity. -/
lemma lTensor_characterRing_toFunction_injective :
    Function.Injective (LinearMap.baseChange A (characterRing_toFunction (G := G))) := by
  letI : Module.Flat ℤ A := (integral_closure_faithfullyFlat_over_int (A := A)).toFlat
  have hchar : Function.Injective (characterRing_toFunction (G := G)) := by
    intro χ ψ hχψ
    exact Subtype.ext hχψ
  exact
    Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (characterRing_toFunction (G := G)) hchar

omit [Fact p.Prime] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Lemma 10-10.2-3: realizing a tensor in `A ⊗ V_p` agrees pointwise with first
viewing it inside the ambient tensor owner `A ⊗ R(G)` and then realizing there. -/
lemma tensorPElementaryInducedCharacterToFunction_eq_tensorCharacterRing_lTensor
    (ξ : A ⊗V[p](G)) :
    (ξ : G → ℂ) =
      ((show A ⊗R(G) from
          LinearMap.lTensor A
            ((Representation.pElementaryInducedCharacterSpan p G)).subtype ξ) : G → ℂ) := by
  -- Compare the two realization maps directly by tensor induction.
  induction ξ using TensorProduct.induction_on with
  | zero =>
      rfl
  | tmul a χ =>
      -- On pure tensors both realizations are the same scalar multiple of the underlying
      -- integral character.
      ext g
      simp
  | add ξ η hξ hη =>
      -- Additivity keeps the comparison stable under finite sums.
      simp [map_add, hξ, hη]

omit [Fact p.Prime] in
/-- Helper for Lemma 10-10.2-3: an ordinary character realized in `A ⊗ V_p` has trivial class in
the quotient `R(G) / V_p`. -/
lemma quotient_class_eq_zero_of_mem_pElementaryInducedCharacterScalarExtension
    (χ : R(G))
    (hχ : (χ : G → ℂ) ∈ pElementaryInducedCharacterScalarExtension A p G) :
    Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ = 0 := by
  rcases hχ with ⟨ξ, hξ⟩
  have htensor :
      ((1 : A) ⊗ₜ[ℤ] χ : A ⊗R(G)) =
        LinearMap.lTensor A ((Representation.pElementaryInducedCharacterSpan p G)).subtype ξ := by
    -- Route correction: compare the witness inside the ambient tensor owner `A ⊗ R(G)` rather
    -- than forcing the false collapse identity `1 ⊗ (a • f) = a ⊗ f`.
    apply tensorCharacterRingToFunction_injective (A := A) (G := G)
    calc
      (((1 : A) ⊗ₜ[ℤ] χ : A ⊗R(G)) : G → ℂ) = χ := by
        simp
      _ = (ξ : G → ℂ) := by
        simp [hξ]
      _ = ((show A ⊗R(G) from
            LinearMap.lTensor A
              ((Representation.pElementaryInducedCharacterSpan p G)).subtype ξ) : G → ℂ) := by
        simpa using
          tensorPElementaryInducedCharacterToFunction_eq_tensorCharacterRing_lTensor
            (A := A) (G := G) (p := p) ξ
  have hquot_tmul :
      (1 : A) ⊗ₜ[ℤ]
          (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ) = 0 := by
    -- Quotienting kills the tensor image of `V_p`, so the previous tensor equality descends to
    -- a vanishing pure tensor in the quotient.
    have hquot :=
      congrArg
        (LinearMap.lTensor A
          (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G))))
        htensor
    calc
      (1 : A) ⊗ₜ[ℤ]
          (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ) =
          LinearMap.lTensor A (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)))
            (LinearMap.lTensor A
              ((Representation.pElementaryInducedCharacterSpan p G)).subtype ξ) := by
        simpa [LinearMap.lTensor_tmul] using hquot
      _ = 0 := by
        have hmkQ_subtype :
            (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G))).comp
              ((Representation.pElementaryInducedCharacterSpan p G)).subtype = 0 := by
          ext x
          exact (Submodule.Quotient.mk_eq_zero _).2 x.2
        have hcomp :
            (LinearMap.lTensor A
              (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)))).comp
                (LinearMap.lTensor A
                  ((Representation.pElementaryInducedCharacterSpan p G)).subtype) = 0 := by
          rw [← LinearMap.lTensor_comp, hmkQ_subtype, LinearMap.lTensor_zero]
        simpa using congrArg (fun f ↦ f ξ) hcomp
  letI : Module.FaithfullyFlat ℤ A := integral_closure_faithfullyFlat_over_int (A := A)
  exact
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff
      (R := ℤ) (M := R(G) ⧸ (Representation.pElementaryInducedCharacterSpan p G)) (A := A)
      (Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χ)).mp hquot_tmul

-- Proof sketch: the inclusion `V_p ⊆ (A ⊗ V_p) ∩ R(G)` is immediate from the scalar-extension
-- construction. For the reverse inclusion, compare a class function in the intersection with its
-- class in the finite quotient `R(G) / V_p` from Theorem `10-10.2-1`; integrality over `ℤ`
-- forces the class to vanish, so the function already lies in `V_p`.
omit [Fact p.Prime] in
/-- Lemma 10-10.2-3 (2): the intersection of `A ⊗ V_p` with the integral character ring `R(G)` is
exactly `V_p`, viewed inside the ambient space of complex-valued functions on `G`. -/
theorem pElementaryInducedCharacterScalarExtension_inter_characterRing_eq_image
    :
    ((pElementaryInducedCharacterScalarExtension A p G : Set (G → ℂ)) ∩
        (R(G) : Set (G → ℂ))) =
      ((LinearMap.range (pElementaryInducedCharacterToFunction p G)) : Set (G → ℂ)) := by
  ext χ
  constructor
  · rintro ⟨hχscalar, hχring⟩
    let χR : R(G) := ⟨χ, hχring⟩
    have hq :
        Submodule.mkQ ((Representation.pElementaryInducedCharacterSpan p G)) χR = 0 :=
      quotient_class_eq_zero_of_mem_pElementaryInducedCharacterScalarExtension
        (A := A) (G := G) (p := p) χR hχscalar
    have hmem : χR ∈ (Representation.pElementaryInducedCharacterSpan p G) := by
      exact
        (Submodule.Quotient.mk_eq_zero
          ((Representation.pElementaryInducedCharacterSpan p G))).1 hq
    -- Vanishing in the quotient means the original character already comes from `V_p`.
    exact ⟨⟨χR, hmem⟩, rfl⟩
  · rintro ⟨χ, rfl⟩
    constructor
    · exact
        mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementaryInducedCharacterSpan
          (A := A) (p := p) (G := G) (χ : R(G)) χ.property
    · exact (χ : R(G)).property

end

end Representation
