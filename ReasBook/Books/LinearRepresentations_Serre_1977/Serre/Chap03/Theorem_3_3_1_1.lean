import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_2
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_4_4
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Representation

section

open CategoryTheory

private def uliftRepresentation
    {G k V : Type} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Representation k G (ULift.{v} V) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

private def uliftRepresentationEquiv
    {G k V : Type} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    ρ.Equiv (uliftRepresentation ρ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun g ↦ by
    ext x
    rfl

private theorem isIrreducible_uliftRepresentation
    {G k V : Type} [Monoid G] [Finite G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    (uliftRepresentation ρ).IsIrreducible := by
  exact isIrreducible_of_nonempty_equiv ⟨uliftRepresentationEquiv ρ⟩

variable {G : Type} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: Serre's criterion that a finite group is abelian exactly when all irreducible
--   complex representations have degree `1`, using the Chapter 1 owner
--   `Representation.IsIrreducible`.
-- * core/canonical: the complete-family arguments run through the bundled owner `FDRep ℂ G`,
--   where irreducibility is expressed by `Simple`, together with the Chapter 2 owner theorem
--   `isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card`.
-- * bridge/view: `FDRep.of` packages a finite-dimensional representation into the canonical
--   `FDRep` owner; the owner theorem `FDRep.isIrreducible_of_simple` moves back from a simple
--   bundled object to the source-facing irreducibility predicate.
--
-- Primitive data are only the finite group `G` and an irreducible representation
-- `ρ : Representation k G V`. The finite-dimensionality bridge is derived internally, at the
-- owner layer `Representation.IsIrreducible`, from the finite orbit of a nonzero vector; the
-- `FDRep`/`Simple` layer is used only internally when a complete irreducible family is chosen for
-- the reverse implication, and `Representation.Equiv.toFDRepIso` is the only bridge needed
-- between the source-facing and bundled owner layers.
-- Proof sketch: for the forward implication, apply
-- `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative` after inserting the derived
-- finite-dimensionality instance for `ρ`. For the reverse implication, choose a complete family
-- of irreducible complex representations in `FDRep ℂ G`, transport their simplicity to
-- `Representation.IsIrreducible`, use Chapter 2's owner theorem
-- `isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card` to recover completeness from the
-- square-degree sum, then combine Chapter 2's formulas
-- `sum_sq_degree_eq_card_of_complete_irreducible_family` and
-- `card_eq_card_conjClasses_of_complete_irreducible_family`, rewrite the latter equality as
-- `commProb G = 1` via `commProb_def'`, and conclude with `commProb_eq_one_iff`.

/-- Theorem 3-3.1-1: a finite group `G` is abelian if and only if every irreducible complex
representation of `G` has degree `1`. -/
theorem isMulCommutative_iff_forall_irreducible_finrank_eq_one :
    IsMulCommutative G ↔
      ∀ {V : Type v} [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) [ρ.IsIrreducible], Module.finrank ℂ V = 1 := by
  constructor
  · intro hG V _ _ ρ _
    letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
    letI : IsMulCommutative G := hG
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  · intro h
    classical
    let _ : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
        ∃ (ι : Type) (_ : Fintype ι) (σ : ι → Subrepresentation (leftRegular ℂ G)),
          iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
            (⨆ i, (σ i).toSubmodule) = ⊤ ∧
            ∀ i, (σ i).toRepresentation.IsIrreducible :=
      exists_isInternal_irreducible_subrepresentations (leftRegular ℂ G)
    let _ : Finite ι := inferInstance
    let _ : Fintype ι := Fintype.ofFinite ι
    let π : ι → FDRep ℂ G := fun i ↦ FDRep.of (σ i).toRepresentation
    let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
    have hπ_finrank (i : ι) : Module.finrank ℂ (π i) = 1 := by
      letI : (uliftRepresentation (σ i).toRepresentation).IsIrreducible :=
        isIrreducible_uliftRepresentation (σ i).toRepresentation
      simpa [π, finrank_ulift] using h (uliftRepresentation (σ i).toRepresentation)
    have hσ_finrank (i : ι) : Module.finrank ℂ (σ i).toSubmodule = 1 := by
      simpa [π] using hπ_finrank i
    have hπ_pairwise : PairwiseNonisomorphic π := by
      intro i j hij hijIso
      have hmult :
          Nat.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } = 1 := by
        letI : (σ i).toRepresentation.IsIrreducible := hσ_irr i
        calc
          Nat.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } =
              Module.finrank ℂ (σ i).toSubmodule := by
                simpa using
                  leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr
                    (σ i).toRepresentation inferInstance
          _ = 1 := hσ_finrank i
      have hcard :
          Fintype.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } =
            1 := by
        simpa [Nat.card_eq_fintype_card] using hmult
      rcases Fintype.card_eq_one_iff.mp hcard with ⟨a, ha⟩
      have hi :
          (⟨i, ⟨Representation.Equiv.refl (σ i).toRepresentation⟩⟩ :
            { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) }) = a := ha _
      have hjRep : Nonempty ((σ j).toRepresentation.Equiv (σ i).toRepresentation) := by
        rcases hijIso with ⟨e⟩
        exact ⟨(Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)).symm⟩
      have hj :
          (⟨j, hjRep⟩ :
            { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) }) = a := ha _
      exact hij <| by simpa using hi.trans hj.symm
    have hπ_simple (i : ι) : CategoryTheory.Simple (π i) := by
      letI : Representation.IsIrreducible (π i).ρ := by
        simpa [π] using hσ_irr i
      exact FDRep.simple_of_isIrreducible (π i)
    have hπ_sum :
        ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = Nat.card G := by
      have hsum_dims : ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule = Nat.card G := by
        letI := DirectSum.IsInternal.chooseDecomposition (fun i ↦ (σ i).toSubmodule) hinternal
        let e := (DirectSum.decomposeLinearEquiv (fun i ↦ (σ i).toSubmodule)).symm
        calc
          ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule = Module.finrank ℂ (G →₀ ℂ) := by
            symm
            calc
              Module.finrank ℂ (G →₀ ℂ) =
                  Module.finrank ℂ (DirectSum ι fun i ↦ (σ i).toSubmodule) := by
                    exact e.finrank_eq.symm
              _ = ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule := by
                    simp [Module.finrank_directSum]
          _ = Nat.card G := by
            let _ : Fintype G := Fintype.ofFinite G
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
      calc
        ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = ∑ i : ι, 1 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hπ_finrank i]
          simp
        _ = ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact (hσ_finrank i).symm
        _ = Nat.card G := hsum_dims
    have hπ_complete : IsCompleteIrreducibleFamily π := by
      exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
    have hcard_ι : Nat.card ι = Nat.card G := by
      calc
        Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
        _ = ∑ i : ι, 1 := by simp
        _ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
              symm
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [hπ_finrank i]
              simp
        _ = Nat.card G := hπ_sum
    have hconj : Nat.card (ConjClasses G) = Nat.card G := by
      calc
        Nat.card (ConjClasses G) = Nat.card ι := by
          symm
          exact
            card_eq_card_conjClasses_of_complete_irreducible_family
              π (fun i ↦ hπ_complete.isSimple i) hπ_pairwise
              (fun τ hτ ↦ hπ_complete.exists_iso τ hτ)
        _ = Nat.card G := hcard_ι
    have hcommProb : commProb G = 1 := by
      rw [commProb_def', hconj, div_self]
      exact_mod_cast Nat.card_pos.ne'
    exact (commProb_eq_one_iff).mp hcommProb

end

end Representation
