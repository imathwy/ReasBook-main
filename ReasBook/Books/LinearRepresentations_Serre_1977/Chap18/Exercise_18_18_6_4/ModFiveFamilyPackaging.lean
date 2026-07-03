import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitGeneratorsAndRegularClasses

noncomputable section

open CategoryTheory
open Representation

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: choose one representative of each isomorphism class of simple
characteristic-`5` `A₅`-modules. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] :
    ∃ (ι : Type _) (π : ι → FDRep k A5),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type _ := { τ : FDRep k A5 // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type _ := Quotient r
  let π : ι → FDRep k A5 := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 18-18.6-4: a complete pairwise nonisomorphic simple family of
characteristic-`5` `A₅`-modules has a finite index type because its Brauer characters form a
basis of the finite-dimensional function space on `5`-regular conjugacy classes. -/
private theorem finite_index_of_complete_family_from_brauer_basis_local
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] {ι : Type*}
    (π : ι → FDRep k A5)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Finite ι := by
  letI : Fintype (_root_.PRegularConjClass A5 5) :=
    Fintype.ofFinite (_root_.PRegularConjClass A5 5)
  let b :=
    Representation.irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (primeToPRoots 5 k).subtype (Subgroup.subtype_injective (primeToPRoots 5 k))
      π hπ_pairwise hπ_complete
  letI : Module.Finite k (_root_.PRegularConjClass A5 5 → k) :=
    Module.Finite.of_basis (Pi.basisFun k (_root_.PRegularConjClass A5 5))
  -- Any basis of this finite-dimensional class-function space has a finite index type.
  exact Module.Finite.finite_basis b

/-- Helper for Exercise 18-18.6-4: a complete pairwise nonisomorphic simple family of
characteristic-`5` `A₅`-modules has as many indices as there are `5`-regular conjugacy classes. -/
theorem alternatingGroup_fin5_card_eq_card_pRegularConjugacyClasses
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] {ι : Type*}
    (π : ι → FDRep k A5)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card ι = Nat.card (_root_.PRegularConjClass A5 5) := by
  letI : Finite ι :=
    finite_index_of_complete_family_from_brauer_basis_local
      (k := k) π hπ_pairwise hπ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (_root_.PRegularConjClass A5 5) :=
    Fintype.ofFinite (_root_.PRegularConjClass A5 5)
  let b :=
    Representation.irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (primeToPRoots 5 k).subtype (Subgroup.subtype_injective (primeToPRoots 5 k))
      π hπ_pairwise hπ_complete
  calc
    Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ = Module.finrank k (_root_.PRegularConjClass A5 5 → k) := by
      simpa using (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (_root_.PRegularConjClass A5 5) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (_root_.PRegularConjClass A5 5) := Nat.card_eq_fintype_card.symm

/-- Helper for Exercise 18-18.6-4: after applying Corollary `18-18.2-5`, a complete irreducible
mod-`5` family of `A₅` may be reindexed by `Fin 3`. -/
theorem alternatingGroup_fin5_exists_complete_family_modFive
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] :
    ∃ π : Fin 3 → FDRep k A5,
      CategoryTheory.PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π := by
  obtain ⟨ι, σ, hσ_pairwise, hσ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (k := k)
  letI : Finite ι :=
    finite_index_of_complete_family_from_brauer_basis_local
      (k := k) σ hσ_pairwise hσ_complete
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (_root_.PRegularConjClass A5 5) :=
    Fintype.ofFinite (_root_.PRegularConjClass A5 5)
  have hcard : Fintype.card ι = 3 := by
    have hnat : Nat.card ι = 3 := by
      calc
        Nat.card ι = Nat.card (_root_.PRegularConjClass A5 5) := by
          exact alternatingGroup_fin5_card_eq_card_pRegularConjugacyClasses
            (k := k) σ hσ_pairwise hσ_complete
        _ = 3 := alternatingGroup_fin5_pRegularConjClass_modFive_card_eq_three
    simpa [Nat.card_eq_fintype_card] using hnat
  let e : ι ≃ Fin 3 := Fintype.equivOfCardEq hcard
  refine ⟨fun i ↦ σ (e.symm i), ?_, ?_⟩
  · intro i j hij
    have hij' : e.symm i ≠ e.symm j := by
      intro h
      apply hij
      exact e.symm.injective h
    exact hσ_pairwise hij'
  · refine ⟨?_, ?_⟩
    · intro i
      simpa using hσ_complete.isSimple (e.symm i)
    · intro τ hτ
      rcases hσ_complete.exists_iso τ hτ with ⟨i, hi⟩
      exact ⟨e i, by simpa using hi⟩

/-- Helper for Exercise 18-18.6-4: the degree-`1` LinearRepresentations_Serre_1977 slot is the trivial `A₅`-module. -/
abbrev alternatingGroup_fin5_trivial_fdRep
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] : FDRep k A5 :=
  FDRep.of (Representation.trivial k A5 k)

/-- Helper for Exercise 18-18.6-4: a one-dimensional representation over any field is
irreducible. -/
theorem isIrreducible_of_finrank_eq_one_local
    {k : Type} [Field k] {G : Type} [Monoid G]
    {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (hV : Module.finrank k V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule k V) :=
    (isSimpleModule_iff k V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Exercise 18-18.6-4: the trivial `A₅`-module is simple. -/
theorem alternatingGroup_fin5_trivial_fdRep_simple
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] :
    Simple (alternatingGroup_fin5_trivial_fdRep (k := k)) := by
  letI : Representation.IsIrreducible ((alternatingGroup_fin5_trivial_fdRep (k := k)).ρ) := by
    exact isIrreducible_of_finrank_eq_one_local
      (ρ := Representation.trivial k A5 k) (by simp)
  exact FDRep.simple_of_isIrreducible (alternatingGroup_fin5_trivial_fdRep (k := k))

/-- Helper for Exercise 18-18.6-4: the trivial `A₅`-module has degree `1`. -/
theorem alternatingGroup_fin5_trivial_fdRep_finrank_one
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5] :
    Module.finrank k (alternatingGroup_fin5_trivial_fdRep (k := k)).V = 1 := by
  simp [alternatingGroup_fin5_trivial_fdRep]

/-- Helper for Exercise 18-18.6-4: two bundled `A₅`-modules with different finranks cannot be
isomorphic. -/
theorem fdRep_not_iso_of_finrank_ne
    {k : Type} [Field k] {E F : FDRep k A5}
    (hfinrank : Module.finrank k E.V ≠ Module.finrank k F.V) :
    ¬ Nonempty (E ≅ F) := by
  rintro ⟨e⟩
  exact hfinrank (FDRep.isoToLinearEquiv e).finrank_eq

/-- Helper for Exercise 18-18.6-4: once source-faithful simple degree-`3` and degree-`5`
`A₅`-modules are available, the final complete family is a pure packaging step. -/
theorem a5_modFive_named_family_complete
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 5]
    (E3 E5 : FDRep k A5)
    (hE3_simple : Simple E3) (hE5_simple : Simple E5)
    (hE3_finrank : Module.finrank k E3.V = 3)
    (hE5_finrank : Module.finrank k E5.V = 5) :
    ∃ π : Fin 3 → FDRep k A5,
      IsCompleteIrreducibleFamily π ∧
        Module.finrank k (π 0).V = 1 ∧
        Module.finrank k (π 1).V = 3 ∧
        Module.finrank k (π 2).V = 5 := by
  let E1 : FDRep k A5 := alternatingGroup_fin5_trivial_fdRep (k := k)
  have hE1_simple : Simple E1 := alternatingGroup_fin5_trivial_fdRep_simple (k := k)
  have hE1_finrank : Module.finrank k E1.V = 1 :=
    alternatingGroup_fin5_trivial_fdRep_finrank_one (k := k)
  let π : Fin 3 → FDRep k A5
    | 0 => E1
    | 1 => E3
    | 2 => E5
  have hnot13 : ¬ Nonempty (E1 ≅ E3) := by
    exact
      fdRep_not_iso_of_finrank_ne (k := k) (by
        rw [hE1_finrank, hE3_finrank]
        decide)
  have hnot15 : ¬ Nonempty (E1 ≅ E5) := by
    exact
      fdRep_not_iso_of_finrank_ne (k := k) (by
        rw [hE1_finrank, hE5_finrank]
        decide)
  have hnot35 : ¬ Nonempty (E3 ≅ E5) := by
    exact
      fdRep_not_iso_of_finrank_ne (k := k) (by
        rw [hE3_finrank, hE5_finrank]
        decide)
  obtain ⟨σ, hσ_pairwise, hσ_complete⟩ :=
    alternatingGroup_fin5_exists_complete_family_modFive (k := k)
  rcases hσ_complete.exists_iso E1 hE1_simple with ⟨i1, hi1⟩
  rcases hσ_complete.exists_iso E3 hE3_simple with ⟨i3, hi3⟩
  rcases hσ_complete.exists_iso E5 hE5_simple with ⟨i5, hi5⟩
  have hi13 : i1 ≠ i3 := by
    intro h
    apply hnot13
    rcases hi1 with ⟨e1⟩
    rcases hi3 with ⟨e3⟩
    exact ⟨e1.trans (by simpa [h] using e3.symm)⟩
  have hi15 : i1 ≠ i5 := by
    intro h
    apply hnot15
    rcases hi1 with ⟨e1⟩
    rcases hi5 with ⟨e5⟩
    exact ⟨e1.trans (by simpa [h] using e5.symm)⟩
  have hi35 : i3 ≠ i5 := by
    intro h
    apply hnot35
    rcases hi3 with ⟨e3⟩
    rcases hi5 with ⟨e5⟩
    exact ⟨e3.trans (by simpa [h] using e5.symm)⟩
  let f : Fin 3 → Fin 3
    | 0 => i1
    | 1 => i3
    | 2 => i5
  have hf_injective : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
    · exact (hi13 hab).elim
    · exact (hi15 hab).elim
    · exact (hi13 hab.symm).elim
    · exact (hi35 hab).elim
    · exact (hi15 hab.symm).elim
    · exact (hi35 hab.symm).elim
  have hf_surjective : Function.Surjective f := by
    exact ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf_injective, rfl⟩).2
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simpa [π] using hE1_simple
      · simpa [π] using hE3_simple
      · simpa [π] using hE5_simple
    · intro τ hτ
      rcases hσ_complete.exists_iso τ hτ with ⟨j, hj⟩
      rcases hf_surjective j with ⟨n, rfl⟩
      fin_cases n
      · rcases hi1 with ⟨e1⟩
        exact ⟨0, ⟨(Classical.choice hj).trans e1.symm⟩⟩
      · rcases hi3 with ⟨e3⟩
        exact ⟨1, by simpa [π, f] using ⟨(Classical.choice hj).trans e3.symm⟩⟩
      · rcases hi5 with ⟨e5⟩
        exact ⟨2, by simpa [π, f] using ⟨(Classical.choice hj).trans e5.symm⟩⟩
  exact ⟨π, hπ_complete, hE1_finrank, hE3_finrank, hE5_finrank⟩
