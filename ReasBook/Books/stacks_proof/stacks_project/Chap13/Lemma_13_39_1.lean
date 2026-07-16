import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Tactic.StacksAttribute
import stacks_proof.stacks_project.Chap13.Definition_13_33_1
import stacks_proof.stacks_project.Chap13.Lemma_13_33_6
import stacks_proof.stacks_project.Chap13.Remark_13_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/- Domain-style sampling for Lemma 13.39.1:
- source-facing owner: `IsBrownRepresentabilitySet` records the two explicit Stacks hypotheses on
  the set `S : Set D`;
- source-facing theorem: `brown_representability_of_detecting_factorization_set`;
- canonical companion: `brown_representability_of_detecting_factorization_set_isRepresentable`.

The source only fixes the triangulated category `D`; the additive target `Ab` should remain
universe-polymorphic, so the representing theorem is stated for `H : Dᵒᵖ ⥤ AddCommGrpCat.{w}`
instead of tying the codomain universe to the hom-universe of `D`. -/

/-- A set of objects satisfying the Stacks-project hypotheses used in Brown representability:
it detects nonzero objects and maps from its objects to countable direct sums factor through
countable direct sums of objects of the same set. -/
@[stacks 0GYG]
structure IsBrownRepresentabilitySet (S : Set D) : Prop where
  /-- Every nonzero object receives a nonzero morphism from some object of `S`. -/
  detects_nonzero_objects {X : D} (hX : ¬ IsZero X) :
    ∃ E : D, E ∈ S ∧ ∃ f : E ⟶ X, f ≠ 0
  /-- Every map from an object of `S` to a countable direct sum factors through a countable direct
  sum of objects of `S`, componentwise. -/
  factors_through_countable_coproducts (X : ℕ → D) {E : D} (hE : E ∈ S) (α : E ⟶ ∐ X) :
    ∃ (E' : ℕ → D), (∀ n : ℕ, E' n ∈ S) ∧
      ∃ (β : ∀ n : ℕ, E' n ⟶ X n) (γ : E ⟶ ∐ E'),
        γ ≫ Limits.Sigma.map β = α

/-- Helper for Lemma 13.39.1: enlarge `S` by all shifts and isomorphic copies so later Brown
constructions can work with a literally shift-stable detecting family. -/
private def brownShiftClosure (S : Set D) : Set D := fun X ↦
  ∃ E : D, E ∈ S ∧ ∃ n : ℤ, Nonempty (E⟦n⟧ ≅ X)

/-- Helper for Lemma 13.39.1: every original member of `S` belongs to the enlarged shift-closure
via the zero shift. -/
private lemma mem_brownShiftClosure_of_mem {S : Set D} {E : D} (hE : E ∈ S) :
    E ∈ brownShiftClosure (D := D) S := by
  -- Proof comment: the zero shift identifies `E⟦0⟧` with `E`, so no new source data is needed.
  refine ⟨E, hE, 0, ?_⟩
  exact ⟨(shiftFunctorZero D ℤ).app E⟩

/-- Helper for Lemma 13.39.1: the shift-closure is stable under ambient isomorphism. -/
private lemma mem_brownShiftClosure_of_iso {S : Set D} {X Y : D}
    (hX : X ∈ brownShiftClosure (D := D) S) (e : X ≅ Y) :
    Y ∈ brownShiftClosure (D := D) S := by
  -- Proof comment: just postcompose the stored shifted-source witness with the given isomorphism.
  rcases hX with ⟨E, hE, n, ⟨i⟩⟩
  exact ⟨E, hE, n, ⟨i.trans e⟩⟩

/-- Helper for Lemma 13.39.1: the enlarged Brown set is closed under further shifts. -/
private lemma mem_brownShiftClosure_shift {S : Set D} {X : D}
    (hX : X ∈ brownShiftClosure (D := D) S) (n : ℤ) :
    X⟦n⟧ ∈ brownShiftClosure (D := D) S := by
  -- Proof comment: reindex the stored shift witness from `m` to `m + n`.
  rcases hX with ⟨E, hE, m, ⟨i⟩⟩
  refine ⟨E, hE, m + n, ?_⟩
  refine ⟨(shiftAdd E m n).trans ((shiftFunctor D n).mapIso i)⟩

/-- Helper for Lemma 13.39.1: the Brown factorization hypothesis is invariant under replacing the
source by an isomorphic object. -/
private lemma IsBrownRepresentabilitySet.factors_through_countable_coproducts_of_iso_source
    {S : Set D} (hS : IsBrownRepresentabilitySet (D := D) S) (X : ℕ → D) {E E' : D}
    (hE : E ∈ S) (e : E' ≅ E) (α : E' ⟶ ∐ X) :
    ∃ (E'' : ℕ → D), (∀ n : ℕ, E'' n ∈ S) ∧
      ∃ (β : ∀ n : ℕ, E'' n ⟶ X n) (γ : E' ⟶ ∐ E''),
        γ ≫ Limits.Sigma.map β = α := by
  rcases hS.factors_through_countable_coproducts X hE (e.inv ≫ α) with
    ⟨E'', hE'', β, γ, hγ⟩
  refine ⟨E'', hE'', β, e.hom ≫ γ, ?_⟩
  -- Proof comment: precompose the original factorization by the source isomorphism.
  calc
    (e.hom ≫ γ) ≫ Limits.Sigma.map β = e.hom ≫ (γ ≫ Limits.Sigma.map β) := by
      simp [Category.assoc]
    _ = e.hom ≫ (e.inv ≫ α) := by rw [hγ]
    _ = α := by simp

/-- Helper for Lemma 13.39.1: the original nonzero-detection clause extends to the shift-closure. -/
private lemma detects_nonzero_objects_brownShiftClosure {S : Set D}
    (hS : IsBrownRepresentabilitySet (D := D) S) {X : D} (hX : ¬ IsZero X) :
    ∃ E : D, E ∈ brownShiftClosure (D := D) S ∧ ∃ f : E ⟶ X, f ≠ 0 := by
  -- Proof comment: the old detecting object already lies in the enlarged set.
  rcases hS.detects_nonzero_objects hX with ⟨E, hE, f, hf⟩
  exact ⟨E, mem_brownShiftClosure_of_mem (D := D) hE, f, hf⟩

/-- Helper for Lemma 13.39.1: if each component map is killed by the successor morphism, then the
induced coproduct map is fixed by the telescope endomorphism. -/
private lemma sigma_map_fixed_by_sequentialTelescopeMap_of_components_killed
    {X E' : ℕ → D} (ι : ∀ n : ℕ, X n ⟶ X (n + 1)) (β : ∀ n : ℕ, E' n ⟶ X n)
    (hβ : ∀ n : ℕ, β n ≫ ι n = 0) :
    Limits.Sigma.map β ≫ sequentialTelescopeMap (Functor.ofSequence ι) = Limits.Sigma.map β := by
  -- Proof comment: check the fixed-point identity on each coproduct summand of `∐ E'`.
  apply Limits.Sigma.hom_ext
  intro n
  conv_lhs =>
    rw [Sigma.ι_map_assoc]
  have hfixed :
      β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) = β n ≫ Sigma.ι X n := by
    -- Proof comment: the successor contribution vanishes because the `n`th component is killed.
    have hιbase :
        Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) =
          Sigma.ι X n - ι n ≫ Sigma.ι X (n + 1) := by
      simpa [Functor.ofSequence_map_homOfLE_succ] using
        (Sigma.ι_comp_sequentialTelescopeMap (K := Functor.ofSequence ι) n)
    have hι' :
        β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) =
          β n ≫ (Sigma.ι X n - ι n ≫ Sigma.ι X (n + 1)) := by
      exact congrArg (fun f ↦ β n ≫ f) hιbase
    have hι :
        β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) =
          β n ≫ Sigma.ι X n - β n ≫ ι n ≫ Sigma.ι X (n + 1) := by
      have htmp :
          β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) =
            β n ≫ (Sigma.ι X n - ι n ≫ Sigma.ι X (n + 1)) := hι'
      rw [Preadditive.comp_sub] at htmp
      simpa [Category.assoc] using htmp
    have hkill : β n ≫ ι n ≫ Sigma.ι X (n + 1) = 0 := by
      simpa [Category.assoc] using
        congrArg (fun g ↦ g ≫ Sigma.ι X (n + 1)) (hβ n)
    calc
      β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) =
          β n ≫ Sigma.ι X n - β n ≫ ι n ≫ Sigma.ι X (n + 1) := hι
      _ = β n ≫ Sigma.ι X n - 0 := by rw [hkill]
      _ = β n ≫ Sigma.ι X n := by simp
  have hmap :
      Sigma.ι E' n ≫ Limits.Sigma.map β = β n ≫ Sigma.ι X n := by
    simpa using (Sigma.ι_map (p := β) n)
  exact hfixed.trans hmap.symm

/-- Helper for Lemma 13.39.1: shifting commutes with countable coproducts. -/
private def sigma_shift_iso (X : ℕ → D) (n : ℤ) :
    (∐ fun i ↦ X i⟦n⟧) ≅ (∐ X)⟦n⟧ :=
  (PreservesCoproduct.iso (shiftFunctor D n) X).symm

/-- Helper for Lemma 13.39.1: under `sigma_shift_iso`, each shifted summand inclusion matches the
shift of the original summand inclusion. -/
private lemma sigma_ι_comp_sigma_shift_iso_hom (X : ℕ → D) (n : ℤ) (i : ℕ) :
    Limits.Sigma.ι (fun j ↦ X j⟦n⟧) i ≫ (sigma_shift_iso (D := D) X n).hom =
      (shiftFunctor D n).map (Limits.Sigma.ι X i) := by
  have hhom :
      (PreservesCoproduct.iso (shiftFunctor D n) X).hom =
        inv (sigmaComparison (shiftFunctor D n) X) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso (shiftFunctor D n) X))
  have hι :
      (shiftFunctor D n).map (Limits.Sigma.ι X i) ≫
          (PreservesCoproduct.iso (shiftFunctor D n) X).hom =
        Limits.Sigma.ι (fun j ↦ X j⟦n⟧) i := by
    -- Proof comment: rewrite the coproduct comparison through `sigmaComparison`.
    rw [hhom]
    exact Limits.map_ι_comp_inv_sigmaComparison (shiftFunctor D n) X i
  change Limits.Sigma.ι (fun j ↦ X j⟦n⟧) i ≫
      (PreservesCoproduct.iso (shiftFunctor D n) X).inv =
      (shiftFunctor D n).map (Limits.Sigma.ι X i)
  apply (cancel_mono (PreservesCoproduct.iso (shiftFunctor D n) X).hom).1
  simpa [sigma_shift_iso, Category.assoc] using hι.symm

/-- Helper for Lemma 13.39.1: shifting the componentwise coproduct map and then reassembling the
target family produces the coproduct map built from the shifted component maps. -/
private lemma sigma_map_shift_reassembly
    (E0 X : ℕ → D) (n : ℤ) (β0 : ∀ i : ℕ, E0 i ⟶ X i⟦-n⟧) :
    (sigma_shift_iso (D := D) E0 n).hom ≫
        (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
        Limits.Sigma.map (fun i ↦
          ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom) =
      Limits.Sigma.map (fun i ↦
        (shiftFunctor D n).map (β0 i) ≫
          ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom) := by
  let tail :
      ∐ (fun i ↦ X i⟦-n⟧⟦n⟧) ⟶ ∐ X :=
    Limits.Sigma.map (fun i ↦
      ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom)
  -- Proof comment: compare both maps on each source coproduct summand.
  apply Limits.Sigma.hom_ext
  intro i
  have htarget :
      (shiftFunctor D n).map (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i) ≫
          (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv =
        Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i := by
    -- Proof comment: cancel the comparison isomorphism on the shifted target family.
    apply (cancel_mono (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).hom).1
    simpa [Category.assoc] using
      (sigma_ι_comp_sigma_shift_iso_hom (D := D) (X := fun j ↦ X j⟦-n⟧) n i).symm
  calc
    Limits.Sigma.ι (fun j ↦ E0 j⟦n⟧) i ≫
        (sigma_shift_iso (D := D) E0 n).hom ≫
        (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
        (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv ≫
        tail =
      (shiftFunctor D n).map (Limits.Sigma.ι E0 i) ≫
        (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
        (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv ≫
        tail := by
      simpa [tail, Category.assoc] using
        congrArg
          (fun k ↦
            k ≫ (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
              (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv ≫ tail)
          (sigma_ι_comp_sigma_shift_iso_hom (D := D) (X := E0) n i)
    _ =
      (shiftFunctor D n).map (β0 i) ≫
        (shiftFunctor D n).map (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i) ≫
        (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv ≫
        tail := by
      have hmap :
          (shiftFunctor D n).map (Limits.Sigma.ι E0 i) ≫
              (shiftFunctor D n).map (Limits.Sigma.map β0) =
            (shiftFunctor D n).map (β0 i) ≫
              (shiftFunctor D n).map (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i) := by
        rw [← Functor.map_comp]
        rw [Limits.Sigma.ι_map]
        rw [Functor.map_comp]
      simpa [tail, Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv ≫ tail)
          hmap
    _ =
      (shiftFunctor D n).map (β0 i) ≫
        Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i ≫
        tail := by
      simpa [tail, Category.assoc] using
        congrArg (fun k ↦ (shiftFunctor D n).map (β0 i) ≫ k ≫ tail) htarget
    _ =
      Limits.Sigma.ι (fun j ↦ E0 j⟦n⟧) i ≫
        Limits.Sigma.map (fun j ↦
          (shiftFunctor D n).map (β0 j) ≫
            ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X j)).hom) := by
      simp [tail, Limits.Sigma.ι_map, Category.assoc]

/-- Helper for Lemma 13.39.1: the total shift/coproduct transport on a countable family agrees
with the coproduct of the pointwise shift-cancellation maps. -/
private lemma sigma_shift_total_transport
    (X : ℕ → D) (n : ℤ) :
    (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).hom ≫
        (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom =
      Limits.Sigma.map (fun i ↦
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom) := by
  let τX : ∀ i : ℕ, X i⟦-n⟧⟦n⟧ ⟶ X i := fun i ↦
    ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom
  -- Proof comment: compare the transported total map on each coproduct summand.
  apply Limits.Sigma.hom_ext
  intro i
  have hsource :
      Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i ≫
          (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).hom ≫
          (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom =
        (shiftFunctor D n).map ((shiftFunctor D (-n)).map (Limits.Sigma.ι X i)) := by
    calc
      Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i ≫
          (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).hom ≫
          (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom =
        (shiftFunctor D n).map (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i) ≫
          (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom)
            (sigma_ι_comp_sigma_shift_iso_hom (D := D) (X := fun j ↦ X j⟦-n⟧) n i)
      _ =
        (shiftFunctor D n).map
          (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i ≫
            (sigma_shift_iso (D := D) X (-n)).hom) := by
        simp [Functor.map_comp]
      _ =
        (shiftFunctor D n).map ((shiftFunctor D (-n)).map (Limits.Sigma.ι X i)) := by
        simpa [Category.assoc] using
          congrArg ((shiftFunctor D n).map)
            (sigma_ι_comp_sigma_shift_iso_hom (D := D) (X := X) (-n) i)
  have hnat :
      (shiftFunctor D n).map ((shiftFunctor D (-n)).map (Limits.Sigma.ι X i)) ≫
          ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom =
        τX i ≫ Limits.Sigma.ι X i := by
    -- Proof comment: this is the naturality square of the shift-composition comparison.
    simpa [τX, Functor.comp_map] using
      ((shiftFunctorCompIsoId D (-n) n (by simp)).hom.naturality (Limits.Sigma.ι X i))
  calc
    Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i ≫
        ((sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).hom ≫
          (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫
          ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom) =
      (shiftFunctor D n).map ((shiftFunctor D (-n)).map (Limits.Sigma.ι X i)) ≫
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom := by
      simpa [Category.assoc] using congrArg
        (fun k ↦ k ≫ ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom)
        hsource
    _ = τX i ≫ Limits.Sigma.ι X i := hnat
    _ =
      Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i ≫
        Limits.Sigma.map (fun j ↦ τX j) := by
      simp [τX]

/-- Helper for Lemma 13.39.1: the double-shift source transport agrees with the canonical
shift-cancellation comparison. -/
private lemma shift_source_transport_hom (E : D) (n : ℤ) :
    ((shiftFunctorCompIsoId D (-n) n (by simp)).app (E⟦n⟧)).hom =
      (shiftFunctor D n).map (((shiftFunctorCompIsoId D n (-n) (by simp)).app E).hom) := by
  have hadd : n + (-n) = 0 := by simp
  have hneg : -n + n = 0 := by simp
  -- Proof comment: this is the standard coherence identifying the two cancelation spellings.
  simpa [hadd, hneg] using
    (shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app (C := D) n E).symm

/-- Helper for Lemma 13.39.1: transporting a Brown factorization through the shift comparison and
then shifting the factor objects back termwise recovers the original map. -/
private lemma shifted_factorization_recovers_original_map
    (X E0 : ℕ → D) {E : D} (n : ℤ) (α : E⟦n⟧ ⟶ ∐ X)
    (γ0 : E ⟶ ∐ E0) (β0 : ∀ i : ℕ, E0 i ⟶ X i⟦-n⟧)
    (hγ0 : γ0 ≫ Limits.Sigma.map β0 =
      ((shiftFunctorCompIsoId D n (-n) (by simp)).app E).inv ≫
        (shiftFunctor D (-n)).map α ≫
        (sigma_shift_iso (D := D) X (-n)).inv) :
    let β : ∀ i : ℕ, E0 i⟦n⟧ ⟶ X i := fun i ↦
      (shiftFunctor D n).map (β0 i) ≫
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom
    let γ : E⟦n⟧ ⟶ ∐ fun i ↦ E0 i⟦n⟧ :=
      (shiftFunctor D n).map γ0 ≫ (sigma_shift_iso (D := D) E0 n).inv
    γ ≫ Limits.Sigma.map β = α := by
  have hadd : n + (-n) = 0 := by simp
  have hneg : -n + n = 0 := by simp
  let τE : E⟦n⟧⟦-n⟧ ≅ E := (shiftFunctorCompIsoId D n (-n) hadd).app E
  let τsource : E⟦n⟧⟦-n⟧⟦n⟧ ≅ E⟦n⟧ := (shiftFunctorCompIsoId D (-n) n hneg).app (E⟦n⟧)
  let τX : ∀ i : ℕ, X i⟦-n⟧⟦n⟧ ⟶ X i := fun i ↦
    ((shiftFunctorCompIsoId D (-n) n hneg).app (X i)).hom
  let τSigma : (∐ X)⟦-n⟧⟦n⟧ ≅ ∐ X := (shiftFunctorCompIsoId D (-n) n hneg).app (∐ X)
  have hreassembly :
      (sigma_shift_iso (D := D) E0 n).inv ≫
          Limits.Sigma.map
            (fun i ↦
              (shiftFunctor D n).map (β0 i) ≫
                ((shiftFunctorCompIsoId D (-n) n hneg).app (X i)).hom) =
        (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX := by
    -- Proof comment: first rewrite the shifted coproduct map using the pointwise reassembly lemma.
    calc
      (sigma_shift_iso (D := D) E0 n).inv ≫
          Limits.Sigma.map
            (fun i ↦
              (shiftFunctor D n).map (β0 i) ≫
                ((shiftFunctorCompIsoId D (-n) n hneg).app (X i)).hom) =
        (sigma_shift_iso (D := D) E0 n).inv ≫
          ((sigma_shift_iso (D := D) E0 n).hom ≫
            (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
            (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
            Limits.Sigma.map τX) := by
        exact congrArg ((sigma_shift_iso (D := D) E0 n).inv ≫ ·)
          (sigma_map_shift_reassembly (D := D) (E0 := E0) (X := X) n β0).symm
      _ =
        (shiftFunctor D n).map (Limits.Sigma.map β0) ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX := by
        simp [Category.assoc]
  have htransportTail :
      (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX =
        τSigma.hom := by
    have hmid :
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫ Limits.Sigma.map τX =
          (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫ τSigma.hom := by
      -- Proof comment: the transported coproduct tail is the standard shift-composition map.
      calc
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫ Limits.Sigma.map τX =
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
            ((sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).hom ≫
              (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫
              τSigma.hom) := by
          exact congrArg ((sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫ ·)
            (sigma_shift_total_transport (D := D) (X := X) n).symm
        _ = (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫ τSigma.hom := by
          simp
    calc
      (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX =
        (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
          ((shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫ τSigma.hom) := by
        rw [hmid]
      _ = τSigma.hom := by
        simp [Category.assoc]
  have hsourceInv :
      (shiftFunctor D n).map τE.inv = τsource.inv := by
    -- Proof comment: this is the inverse form of the shift-cancellation coherence.
    simpa [τE, τsource, hadd, hneg] using
      (shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app (C := D) n E)
  have hnatural :
      τsource.inv ≫ (shiftFunctor D n).map ((shiftFunctor D (-n)).map α) = α ≫ τSigma.inv := by
    -- Proof comment: naturality moves the comparison from the source of `α` to its target.
    simpa [τsource, τSigma, hneg, Functor.comp_map, Category.assoc] using
      ((shiftFunctorCompIsoId D (-n) n hneg).inv.naturality α).symm
  calc
    ((shiftFunctor D n).map γ0 ≫ (sigma_shift_iso (D := D) E0 n).inv) ≫
        Limits.Sigma.map
          (fun i ↦
            (shiftFunctor D n).map (β0 i) ≫
              ((shiftFunctorCompIsoId D (-n) n hneg).app (X i)).hom) =
      (shiftFunctor D n).map γ0 ≫
        ((sigma_shift_iso (D := D) E0 n).inv ≫
          Limits.Sigma.map
            (fun i ↦
              (shiftFunctor D n).map (β0 i) ≫
                ((shiftFunctorCompIsoId D (-n) n hneg).app (X i)).hom)) := by
      simp [Category.assoc]
    _ =
      (shiftFunctor D n).map γ0 ≫
        ((shiftFunctor D n).map (Limits.Sigma.map β0) ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX) := by
      simpa [Category.assoc] using congrArg ((shiftFunctor D n).map γ0 ≫ ·) hreassembly
    _ =
      (shiftFunctor D n).map (γ0 ≫ Limits.Sigma.map β0) ≫
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
        Limits.Sigma.map τX := by
      simp [Functor.map_comp, Category.assoc]
    _ =
      (shiftFunctor D n).map
          (τE.inv ≫ (shiftFunctor D (-n)).map α ≫
            (sigma_shift_iso (D := D) X (-n)).inv) ≫
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
        Limits.Sigma.map τX := by
      exact congrArg
        (fun k ↦
          (shiftFunctor D n).map k ≫
            (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
            Limits.Sigma.map τX)
        (by simpa [τE] using hγ0)
    _ =
      (shiftFunctor D n).map τE.inv ≫
        (shiftFunctor D n).map ((shiftFunctor D (-n)).map α) ≫
        (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
        Limits.Sigma.map τX := by
      simp [Functor.map_comp, Category.assoc]
    _ =
      τsource.inv ≫
        (shiftFunctor D n).map ((shiftFunctor D (-n)).map α) ≫
        (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
        (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
        Limits.Sigma.map τX := by
      rw [hsourceInv]
    _ = α ≫ τSigma.inv ≫
        ((shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
          (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
          Limits.Sigma.map τX) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            k ≫
              ((shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).inv ≫
                (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).inv ≫
                Limits.Sigma.map τX))
          hnatural
    _ = α ≫ τSigma.inv ≫ τSigma.hom := by
      rw [htransportTail]
    _ = α := by
      -- Proof comment: the last comparison cancels because `τSigma` is an isomorphism.
      simpa using congrArg (fun k ↦ α ≫ k) τSigma.inv_hom_id

/-- Helper for Lemma 13.39.1: a shifted Brown object still satisfies the countable-coproduct
factorization property after transporting through the shift/coproduct comparison. -/
private lemma IsBrownRepresentabilitySet.factors_through_countable_coproducts_of_shift_member
    {S : Set D} (hS : IsBrownRepresentabilitySet (D := D) S) (X : ℕ → D) {E : D}
    (hE : E ∈ S) (n : ℤ) (α : E⟦n⟧ ⟶ ∐ X) :
    ∃ (E' : ℕ → D), (∀ i : ℕ, E' i ∈ brownShiftClosure (D := D) S) ∧
      ∃ (β : ∀ i : ℕ, E' i ⟶ X i) (γ : E⟦n⟧ ⟶ ∐ E'),
        γ ≫ Limits.Sigma.map β = α := by
  let Xneg : ℕ → D := fun i ↦ X i⟦-n⟧
  let αneg : E ⟶ ∐ Xneg :=
    ((shiftFunctorCompIsoId D n (-n) (by simp)).app E).inv ≫
      (shiftFunctor D (-n)).map α ≫
      (sigma_shift_iso (D := D) X (-n)).inv
  rcases hS.factors_through_countable_coproducts Xneg hE αneg with
    ⟨E0, hE0, β0, γ0, hγ0⟩
  let Eshift : ℕ → D := fun i ↦ E0 i⟦n⟧
  let β : ∀ i : ℕ, Eshift i ⟶ X i := fun i ↦
    (shiftFunctor D n).map (β0 i) ≫
      ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom
  let γ : E⟦n⟧ ⟶ ∐ Eshift :=
    (shiftFunctor D n).map γ0 ≫ (sigma_shift_iso (D := D) E0 n).inv
  refine ⟨Eshift, ?_, β, γ, ?_⟩
  · intro i
    -- Proof comment: each transported factor object still lies in the shift-closure of `S`.
    exact mem_brownShiftClosure_shift (D := D)
      (mem_brownShiftClosure_of_mem (D := D) (hE0 i)) n
  · -- Proof comment: the explicit transport lemmas turn the shifted factorization back into `α`.
    simpa [Eshift, β, γ, Xneg, αneg] using
      shifted_factorization_recovers_original_map
        (D := D) (X := X) (E0 := E0) (E := E) n α γ0 β0 hγ0

/-- Helper for Lemma 13.39.1: enlarging a Brown representability set by all shifts and isomorphic
copies preserves both source axioms. -/
private lemma isBrownRepresentabilitySet_shift_closure {S : Set D}
    (hS : IsBrownRepresentabilitySet (D := D) S) :
    IsBrownRepresentabilitySet (brownShiftClosure (D := D) S) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    -- Proof comment: the original detecting clause already lands in the shift-closure.
    exact detects_nonzero_objects_brownShiftClosure (D := D) hS hX
  · intro X A hA α
    rcases hA with ⟨E, hE, n, ⟨e⟩⟩
    rcases hS.factors_through_countable_coproducts_of_shift_member (X := X) hE n
        (e.hom ≫ α) with ⟨E', hE', β, γ, hγ⟩
    refine ⟨E', hE', β, e.inv ≫ γ, ?_⟩
    -- Proof comment: transport the shifted-source factorization back across the chosen isomorphism.
    calc
      (e.inv ≫ γ) ≫ Limits.Sigma.map β = e.inv ≫ (γ ≫ Limits.Sigma.map β) := by
        simp [Category.assoc]
      _ = e.inv ≫ (e.hom ≫ α) := by rw [hγ]
      _ = α := by simp

/-- Helper for Lemma 13.39.1: if every morphism from an object of the Brown-detecting set `S`
into `X` vanishes, then `X` must already be zero. This packages the source-level detection step
that will later globalize generatorwise bijectivity of the Brown comparison map. -/
private lemma isZero_of_maps_from_brownSet_zero
    (S : Set D) (hS : IsBrownRepresentabilitySet (D := D) S) {X : D}
    (hvanish : ∀ ⦃E : D⦄, E ∈ S → ∀ f : E ⟶ X, f = 0) :
    IsZero X := by
  -- Proof comment: a nonzero object would admit a nonzero map from some `E ∈ S`, contradicting
  -- the vanishing hypothesis.
  by_contra hX
  obtain ⟨E, hE, f, hf⟩ := hS.detects_nonzero_objects hX
  exact hf (hvanish hE f)

/-- Helper for Lemma 13.39.1: if `H` is additive, then the function
`f ↦ H.map f.op a` sends the zero morphism to zero. This is the componentwise linearity datum
needed to build the Brown comparison natural transformation attached to `a ∈ H(X)`. -/
private lemma detectingBrownNatTransOfElementComponent_map_zero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ) :
    (fun f : Y.unop ⟶ X ↦ (H.map f.op).hom a) 0 = 0 := by
  -- Proof comment: additivity identifies the image of the zero morphism with the zero morphism
  -- in the target abelian group.
  simpa using congrArg (fun k ↦ k.hom a) (Functor.map_zero (F := H) (X := Y) (Y := op X))

/-- Helper for Lemma 13.39.1: if `H` is additive, then the function
`f ↦ H.map f.op a` preserves addition. This packages the additive structure of the Brown
comparison map attached to `a ∈ H(X)`. -/
private lemma detectingBrownNatTransOfElementComponent_map_add
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ)
    (f g : Y.unop ⟶ X) :
    (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) (f + g) =
      (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) f +
        (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) g := by
  -- Proof comment: the additivity of `H` turns sums of morphisms into sums of the induced group
  -- maps on values.
  simpa using congrArg (fun k ↦ k.hom a) (Functor.map_add (F := H) (f := f.op) (g := g.op))

/-- Helper for Lemma 13.39.1: the `Y`-component of the Brown comparison map attached to
`a ∈ H(X)` is the additive homomorphism `f ↦ H.map f.op a`. -/
private noncomputable def detectingBrownNatTransOfElementComponent
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ) :
    (preadditiveYoneda.obj X).obj Y ⟶ H.obj Y :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ (H.map f.op).hom a
      map_zero' := detectingBrownNatTransOfElementComponent_map_zero (a := a) Y
      map_add' := detectingBrownNatTransOfElementComponent_map_add (a := a) Y }

/-- Helper for Lemma 13.39.1: the component maps `f ↦ H.map f.op a` are natural in the source
object, so they assemble into the Brown comparison natural transformation attached to
`a ∈ H(X)`. -/
private lemma detectingBrownNatTransOfElementComponent_naturality
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X))
    {Y Y' : Dᵒᵖ} (f : Y ⟶ Y') :
    (preadditiveYoneda.obj X).map f ≫ detectingBrownNatTransOfElementComponent (H := H) a Y' =
      detectingBrownNatTransOfElementComponent (H := H) a Y ≫ H.map f := by
  -- Proof comment: this is the contravariant identity
  -- `H.map (g.op ≫ f) = H.map g.op ≫ H.map f` checked on each element.
  apply AddCommGrpCat.ext
  intro g
  change (H.map (g.op ≫ f)).hom a = (H.map f).hom ((H.map g.op).hom a)
  rw [Functor.map_comp]
  rfl

/-- Helper for Lemma 13.39.1: an element `a ∈ H(X)` defines the Brown comparison natural
transformation `preadditiveYoneda.obj X ⟶ H` by the usual Yoneda formula `f ↦ H.map f.op a`. -/
private noncomputable def detectingBrownNatTransOfElement
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) :
    preadditiveYoneda.obj X ⟶ H where
  app Y := detectingBrownNatTransOfElementComponent (H := H) a Y
  naturality {_ _} f := detectingBrownNatTransOfElementComponent_naturality (H := H) a f

/-- Helper for Lemma 13.39.1: evaluating the Brown comparison attached to `a ∈ H(X)` on
`f : Y ⟶ X` yields the element `H.map f.op a`. -/
@[simp] private lemma detectingBrownNatTransOfElement_app_apply
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X))
    {Y : Dᵒᵖ} (f : Y.unop ⟶ X) :
    ((detectingBrownNatTransOfElement (H := H) (a := a)).app Y).hom f = (H.map f.op).hom a := by
  -- Proof comment: unfold the component construction and read off the defining formula.
  change ((detectingBrownNatTransOfElementComponent (H := H) a Y).hom f) = (H.map f.op).hom a
  rfl

/-- Helper for Lemma 13.39.1: the Brown comparison attached to `a ∈ H(X)` sends the identity of
`X` to `a`. -/
@[simp] private lemma detectingBrownNatTransOfElement_app_id
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) :
    ((detectingBrownNatTransOfElement (H := H) (a := a)).app (op X)).hom (𝟙 X) = a := by
  -- Proof comment: this is the identity-instance of the defining Yoneda formula.
  simpa using detectingBrownNatTransOfElement_app_apply (H := H) a (f := 𝟙 X)

/-- Helper for Lemma 13.39.1: if `u : X ⟶ X'` carries `a' ∈ H(X')` to `a ∈ H(X)`, then the Brown
comparison map for `a'` restricts along `u` to the Brown comparison map for `a`. -/
@[simp] private lemma preadditiveYoneda_map_comp_detectingBrownNatTransOfElement
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X X' : D}
    (u : X ⟶ X') (a : H.obj (op X)) (a' : H.obj (op X'))
    (ha : (H.map u.op).hom a' = a) :
    preadditiveYoneda.map u ≫ detectingBrownNatTransOfElement (H := H) (a := a') =
      detectingBrownNatTransOfElement (H := H) (a := a) := by
  -- Proof comment: compare the two natural transformations componentwise and simplify using the
  -- compatibility assumption on the chosen elements.
  ext Y g
  change (H.map (u.op ≫ g.op)).hom a' = (H.map g.op).hom a
  rw [Functor.map_comp]
  change (H.map g.op).hom ((H.map u.op).hom a') = (H.map g.op).hom a
  rw [ha]

/-- Helper for Lemma 13.39.1: the universal coproduct of all generatorwise kernel morphisms into a
stage `X` packages the Brown successor-step source data before the cohomological lifting step. -/
private lemma detectingBrownKernelTriangle
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {I : Type (max u v)} (E : I → D)
    {X : D} (aX : H.obj (op X)) :
    ∃ (K : D) (κ : K ⟶ X) (X' : D) (u : X ⟶ X') (δ : X' ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk κ u δ ∈ distTriang D ∧
        ∀ (i : I) (φ : E i ⟶ X),
          ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 →
            ∃ ψ : E i ⟶ K, ψ ≫ κ = φ := by
  classical
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ i : I,
        { φ : E i ⟶ X //
          ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
  let K : D := ∐ fun j : J ↦ E j.down.1
  let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
  obtain ⟨X', u, δ, hT⟩ := distinguished_cocone_triangle κ
  refine ⟨K, κ, X', u, δ, hT, ?_⟩
  intro i φ hφ
  -- Proof comment: every kernel morphism appears as one chosen summand of the coproduct by
  -- construction of the index type `J`.
  refine ⟨Limits.Sigma.ι (fun j : J ↦ E j.down.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩, ?_⟩
  simpa [κ] using
    (Limits.Sigma.ι_desc (fun j : J ↦ j.down.2.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩)

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.39.1: after transporting a coproduct through the opposite
coproduct/product comparison and the preserved-product comparison for `H`, the `j`th product
projection is exactly `H.map` of the `j`th coproduct inclusion. -/
private lemma detectingBrownKernelCoproductProductIso_hom_comp_π
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}} {J : Type (max u v)} (K : J → D)
    [HasProduct (fun j ↦ Opposite.op (K j))]
    [HasProduct (fun j ↦ H.obj (Opposite.op (K j)))]
    [PreservesLimitsOfShape (Discrete J) H] (j : J) :
    ((H.mapIso (Limits.opCoproductIsoProduct K) ≪≫
        PreservesProduct.iso H (fun j ↦ Opposite.op (K j))).hom) ≫
      Pi.π (fun j ↦ H.obj (Opposite.op (K j))) j =
        H.map ((Limits.Sigma.ι K j).op) := by
  -- Proof comment: expand the transported coproduct/product comparison and read off the chosen
  -- product projection.
  rw [Iso.trans_hom, Category.assoc]
  calc
    (H.mapIso (Limits.opCoproductIsoProduct K)).hom ≫
        (PreservesProduct.iso H (fun j ↦ Opposite.op (K j))).hom ≫
          Pi.π (fun j ↦ H.obj (Opposite.op (K j))) j =
      (H.mapIso (Limits.opCoproductIsoProduct K)).hom ≫
        H.map (Pi.π (fun j ↦ Opposite.op (K j)) j) := by
          simpa [PreservesProduct.iso_hom, Category.assoc] using
            (piComparison_comp_π H (fun j ↦ Opposite.op (K j)) j)
    _ = H.map ((Limits.opCoproductIsoProduct K).hom ≫
          Pi.π (fun j ↦ Opposite.op (K j)) j) := by
          simpa using
            (Functor.map_comp H (Limits.opCoproductIsoProduct K).hom
              (Pi.π (fun j ↦ Opposite.op (K j)) j)).symm
    _ = H.map ((Limits.Sigma.ι K j).op) := by
          rw [Limits.opCoproductIsoProduct_hom_comp_π]

/-- Helper for Lemma 13.39.1: isomorphisms in `AddCommGrpCat` are injective on elements after
coercing their forward maps to functions. This isolates the algebraic cancellation used when the
kernel element is transported to a product object. -/
private lemma detectingBrownAddCommGrpIso_hom_injective {A B : AddCommGrpCat.{w}} (e : A ≅ B) :
    Function.Injective e.hom := by
  -- Proof comment: cancel the forward map by applying the inverse map on both sides.
  intro x y hxy
  have := congrArg e.inv hxy
  simpa using this

/-- Helper for Lemma 13.39.1: the explicit kernel coproduct used in the Brown successor step
really annihilates the current stage element after applying `H`. This is the product-comparison
bridge needed before the cohomological lifting step can run. -/
private lemma detectingBrownKernelCoproductMapZero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {I : Type (max u v)} (E : I → D)
    {X : D} (aX : H.obj (op X))
    (hprod :
      PreservesLimitsOfShape
        (Discrete
          (ULift.{max u v, max u v}
            (Σ i : I,
              { φ : E i ⟶ X //
                ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })))
        H) :
    let J : Type (max u v) :=
      ULift.{max u v, max u v}
        (Σ i : I,
          { φ : E i ⟶ X //
            ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
    let K : D := ∐ fun j : J ↦ E j.down.1
    let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
    (H.map κ.op).hom aX = 0 := by
  classical
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ i : I,
        { φ : E i ⟶ X //
          ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
  let K : D := ∐ fun j : J ↦ E j.down.1
  let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
  letI : PreservesLimitsOfShape (Discrete J) H := hprod
  let Hlift : Dᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    H ⋙ AddCommGrpCat.uliftFunctor.{max u v, v}
  letI : PreservesLimitsOfShape (Discrete J) Hlift := by
    infer_instance
  let e :
      Hlift.obj (op K) ≅ ∏ᶜ fun j : J ↦ Hlift.obj (op (E j.down.1)) :=
    Hlift.mapIso (Limits.opCoproductIsoProduct (fun j : J ↦ E j.down.1)) ≪≫
      PreservesProduct.iso Hlift (fun j : J ↦ Opposite.op (E j.down.1))
  have hzeroLift : ((Hlift.map κ.op).hom (ULift.up aX)) = 0 := by
    -- Proof comment: after transporting to the explicit product, each coordinate vanishes by the
    -- kernel witness stored in the indexing type.
    apply detectingBrownAddCommGrpIso_hom_injective e
    apply CategoryTheory.Limits.Concrete.limit_ext
    intro j
    rw [show limit.π (Discrete.functor (fun j : J ↦ Hlift.obj (op (E j.down.1)))) j =
        Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as by rfl]
    have hικ :
        Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as ≫ κ = j.as.down.2.1 := by
      simpa [κ] using (Limits.Sigma.ι_desc (fun j' : J ↦ j'.down.2.1) j.as)
    suffices hcoord :
        ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) = 0 by
      have hzero :
          ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom 0) = 0 := by
        simp
      exact hcoord.trans hzero.symm
    have hπ :
        e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as =
          Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op) :=
      detectingBrownKernelCoproductProductIso_hom_comp_π
        (H := Hlift) (K := fun j : J ↦ E j.down.1) j.as
    have hmap :
        ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) =
          ULift.up ((H.map (j.as.down.2.1).op).hom aX) := by
      calc
        ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
            ((Hlift.map κ.op).hom (ULift.up aX))) =
            ((Hlift.map
              (κ.op ≫ (Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
              (ULift.up aX)) := by
              exact congrArg (fun k ↦ k.hom (ULift.up aX))
                (Functor.map_comp Hlift κ.op
                  ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).symm
        _ = ((Hlift.map
              ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as ≫ κ).op)).hom
              (ULift.up aX)) := by
              exact congrArg (fun f ↦ (Hlift.map f).hom (ULift.up aX)) rfl
        _ = ((Hlift.map (j.as.down.2.1).op).hom (ULift.up aX)) := by
              exact congrArg
                (fun f : E j.as.down.1 ⟶ X ↦ (Hlift.map f.op).hom (ULift.up aX)) hικ
        _ = ULift.up ((H.map (j.as.down.2.1).op).hom aX) := by
              rfl
    have hj :
        (H.map (j.as.down.2.1).op).hom aX = 0 := by
      simpa [detectingBrownNatTransOfElement_app_apply] using j.as.down.2.2
    calc
      ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) =
          ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
            ((Hlift.map κ.op).hom (ULift.up aX))) := by
              exact congrArg (fun k ↦ k.hom ((Hlift.map κ.op).hom (ULift.up aX))) hπ
      _ = ULift.up ((H.map (j.as.down.2.1).op).hom aX) := hmap
      _ = 0 := congrArg ULift.up hj
  have hzeroBase : (H.map κ.op).hom aX = 0 := by
    -- Proof comment: `ulift` only changed universes, so the vanishing descends back to `H`.
    change ULift.up ((H.map κ.op).hom aX) = 0 at hzeroLift
    simpa using congrArg ULift.down hzeroLift
  exact hzeroBase

/-- Helper for Lemma 13.39.1: for a distinguished triangle `K ⟶ X ⟶ X' ⟶ K⟦1⟧`, any element of
`H.obj (op X)` annihilated by `H.map κ.op` lifts along `H.map u.op`. This isolates the exactness
input needed in each Brown successor step after the kernel coproduct has been constructed. -/
private lemma existsDetectingBrownLiftOfMapZero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} {K X X' : D} (κ : K ⟶ X) (u : X ⟶ X')
    (δ : X' ⟶ K⟦(1 : ℤ)⟧) (hT : Triangle.mk κ u δ ∈ distTriang D)
    (hH : H.rightOp.IsHomological) (aX : H.obj (op X))
    (hzero : (H.map κ.op).hom aX = 0) :
    ∃ aX' : H.obj (op X'), (H.map u.op).hom aX' = aX := by
  letI : H.rightOp.IsHomological := hH
  let SOp := (shortComplexOfDistTriangle (Triangle.mk κ u δ) hT).map H.rightOp
  have hExactOp : SOp.Exact := by
    -- Proof comment: the homological functor turns the distinguished triangle into an exact
    -- short complex in `AddCommGrpCatᵒᵖ`.
    simpa [SOp] using H.rightOp.map_distinguished_exact (Triangle.mk κ u δ) hT
  have hExact : SOp.unop.Exact := CategoryTheory.ShortComplex.Exact.unop hExactOp
  rw [CategoryTheory.ShortComplex.ab_exact_iff] at hExact
  have hz : SOp.unop.g aX = 0 := by
    -- Proof comment: after `unop`, the second map of the short complex is exactly `H.map κ.op`.
    simpa [SOp] using hzero
  obtain ⟨aX', haX'⟩ := hExact aX hz
  refine ⟨aX', ?_⟩
  -- Proof comment: exactness returns the desired preimage along `H.map u.op`.
  simpa [SOp] using haX'

/-- Helper for Lemma 13.39.1: every element of a sequential colimit in `AddCommGrpCat` is
already represented at one finite stage. This isolates the stage-representative input needed for
the missing Brown hocolim comparison. -/
private lemma detectingBrownExistsStageRepresentativeOfSequentialAddCommGrpColimit
    (G : ℕ ⥤ AddCommGrpCat.{v}) (z : (colimit G : AddCommGrpCat.{v})) :
    ∃ n : ℕ, ∃ x : G.obj n, colimit.ι G n x = z := by
  -- Proof comment: concrete filtered colimits in `AddCommGrpCat` are jointly covered by the
  -- stage inclusions.
  letI : IsFiltered ℕ := inferInstance
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit G (forget AddCommGrpCat) := by
    infer_instance
  exact Concrete.colimit_exists_rep G z

/-- Helper for Lemma 13.39.1: compatibility with the successor maps of a sequential diagram
assembles stagewise morphisms `A n ⟶ B` into a cocone over `Functor.ofSequence u`. -/
private lemma detectingBrownSequentialAddCommGrpConstCoconeNaturality
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) (n : ℕ) :
    (Functor.ofSequence u).map (homOfLE (Nat.le_succ n)) ≫ φ (n + 1) =
      φ n ≫ ((Functor.const ℕ).obj B).map (homOfLE (Nat.le_succ n)) := by
  -- Proof comment: the constant target functor contributes the identity transition, so this is
  -- exactly the successor compatibility relation.
  simpa [Functor.ofSequence_map_homOfLE_succ] using hcompat n

/-- Helper for Lemma 13.39.1: compatible maps from a sequential system of abelian groups to a
fixed target descend to the sequential colimit. -/
private noncomputable def detectingBrownSequentialAddCommGrpColimitDesc
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) :
    (colimit (Functor.ofSequence u) : AddCommGrpCat.{v}) ⟶ B :=
  colimit.desc (Functor.ofSequence u)
    (Cocone.mk B
      (NatTrans.ofSequence φ
        (detectingBrownSequentialAddCommGrpConstCoconeNaturality (u := u) φ hcompat)))

/-- Helper for Lemma 13.39.1: if every stagewise kernel element is killed by the next transition,
then any colimit element mapping to zero in the target is already zero. This is the injective-half
input for the future Brown `Hom`-colimit comparison. -/
private lemma detectingBrownSequentialAddCommGrpColimitDescEqZeroOfKernelKilled
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (hkill : ∀ (n : ℕ) (x : A n), (φ n).hom x = 0 → (u n).hom x = 0)
    {z : (colimit (Functor.ofSequence u) : AddCommGrpCat.{v})}
    (hz : (detectingBrownSequentialAddCommGrpColimitDesc u φ hcompat).hom z = 0) :
    z = 0 := by
  let G : ℕ ⥤ AddCommGrpCat.{v} := Functor.ofSequence u
  obtain ⟨n, x, rfl⟩ :=
    detectingBrownExistsStageRepresentativeOfSequentialAddCommGrpColimit G z
  have hxφ : (φ n).hom x = 0 := by
    -- Proof comment: vanishing in the colimit descends to vanishing of the chosen stage
    -- representative.
    change (((colimit.ι G n) ≫ detectingBrownSequentialAddCommGrpColimitDesc u φ hcompat).hom x) =
      0 at hz
    rw [detectingBrownSequentialAddCommGrpColimitDesc, colimit.ι_desc] at hz
    simpa [G, detectingBrownSequentialAddCommGrpColimitDesc] using hz
  have hxu : (u n).hom x = 0 := hkill n x hxφ
  have hzeroStage : colimit.ι G (n + 1) ((u n).hom x) = 0 := by
    -- Proof comment: the killed element maps to zero in the next stage of the colimit.
    rw [hxu]
    change (colimit.ι G (n + 1)).hom 0 = 0
    simp
  have htransport :
      colimit.ι G n x = colimit.ι G (n + 1) ((u n).hom x) := by
    -- Proof comment: the sequential colimit identifies a stage element with its image in the
    -- next stage.
    have hw := congrArg (fun k ↦ k.hom x) (colimit.w G (homOfLE (Nat.le_succ n)))
    simpa [G, Functor.ofSequence_map_homOfLE_succ] using hw.symm
  calc
    colimit.ι G n x = colimit.ι G (n + 1) ((u n).hom x) := htransport
    _ = 0 := hzeroStage

/-- Helper for Lemma 13.39.1: for a sequential system of abelian groups, stage-0 surjectivity and
one-step kernel killing imply that the descended colimit map is bijective. This is the algebraic
core of the planned Brown comparison on shifted generators. -/
private lemma
    detectingBrownSequentialAddCommGrpColimitBijectiveOfStage0SurjectiveAndKernelKilled
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (hsurj : Function.Surjective (φ 0).hom)
    (hkill : ∀ (n : ℕ) (x : A n), (φ n).hom x = 0 → (u n).hom x = 0) :
    Function.Bijective (detectingBrownSequentialAddCommGrpColimitDesc u φ hcompat).hom := by
  constructor
  · intro z₁ z₂ hEq
    -- Proof comment: injectivity reduces to the zero-kernel statement by subtracting the two
    -- colimit representatives.
    apply sub_eq_zero.mp
    apply detectingBrownSequentialAddCommGrpColimitDescEqZeroOfKernelKilled u φ hcompat hkill
    simpa [map_sub, hEq]
  · intro b
    -- Proof comment: surjectivity already holds at stage `0`, so every target element comes from
    -- the colimit.
    obtain ⟨x, rfl⟩ := hsurj b
    refine ⟨(colimit.ι (Functor.ofSequence u) 0).hom x, ?_⟩
    change
      (((colimit.ι (Functor.ofSequence u) 0) ≫
          detectingBrownSequentialAddCommGrpColimitDesc u φ hcompat).hom x) =
        (φ 0).hom x
    rw [detectingBrownSequentialAddCommGrpColimitDesc, colimit.ι_desc]
    rfl

/-- Helper for Lemma 13.39.1: a family of coordinates in `H(K j)` determines an element of
`H(∐ K)` whose images along the coproduct summand inclusions recover those coordinates. -/
private lemma detectingBrownInitialStageElementTransport
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {J : Type (max u v)} (K : J → D)
    (hprod : PreservesLimitsOfShape (Discrete J) H)
    (x : ∀ j : J, H.obj (op (K j))) :
    ∃ a : H.obj (op (∐ K)), ∀ j : J, (H.map ((Limits.Sigma.ι K j).op)).hom a = x j := by
  letI : PreservesLimitsOfShape (Discrete J) H := hprod
  let Hlift : Dᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    H ⋙ AddCommGrpCat.uliftFunctor.{max u v, v}
  letI : PreservesLimitsOfShape (Discrete J) Hlift := by
    infer_instance
  let Z : AddCommGrpCat.{max u v} := AddCommGrpCat.of (ULift.{max u v, 0} ℤ)
  let e :
      Hlift.obj (op (∐ K)) ≅ ∏ᶜ fun j : J ↦ Hlift.obj (op (K j)) :=
    Hlift.mapIso (Limits.opCoproductIsoProduct K) ≪≫
      PreservesProduct.iso Hlift (fun j ↦ Opposite.op (K j))
  let yComponent : ∀ j : J, Z ⟶ Hlift.obj (op (K j)) := fun j ↦
    AddCommGrpCat.ofHom
        { toFun := fun n ↦ ULift.up (n.down • x j)
          map_zero' := by
            ext
            simp
          map_add' := by
            intro m n
            ext
            simpa using add_zsmul (x j) m.down n.down }
  let yHom : Z ⟶ ∏ᶜ fun j : J ↦ Hlift.obj (op (K j)) :=
    Pi.lift yComponent
  refine ⟨ULift.down (e.inv.hom (yHom.hom (ULift.up (1 : ℤ)))), ?_⟩
  intro j
  have hy :
      ((Pi.π (fun j : J ↦ Hlift.obj (op (K j))) j).hom
          (yHom.hom (ULift.up (1 : ℤ)))) = ULift.up (x j) := by
    -- Proof comment: the product element was chosen so that its `j`th coordinate is exactly `x j`.
    change (((yHom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (K j))) j).hom)
      (ULift.up (1 : ℤ))) = ULift.up (x j)
    rw [Pi.lift_π]
    change ULift.up (((ULift.up (1 : ℤ) : ULift.{max u v, 0} ℤ).down) • x j) = ULift.up (x j)
    simp
  have hπ :
      e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (K j))) j =
        Hlift.map ((Limits.Sigma.ι K j).op) :=
    detectingBrownKernelCoproductProductIso_hom_comp_π (H := Hlift) (K := K) j
  -- Proof comment: rewrite the chosen element through the coproduct/product comparison and read
  -- off the prescribed coordinate.
  change ULift.down ((Hlift.map ((Limits.Sigma.ι K j).op)).hom
      (e.inv.hom (yHom.hom (ULift.up (1 : ℤ))))) = x j
  rw [← hπ]
  change ULift.down (((e.inv ≫ e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (K j))) j).hom)
      (yHom.hom (ULift.up (1 : ℤ)))) = x j
  simpa [hy]

/-- Helper for Lemma 13.39.1: the Brown initial stage is the coproduct of all pairs
`(E, a)` with `E ∈ brownShiftClosure S` and `a ∈ H(E)`. The chosen element of `H` on this
coproduct makes the stage-`0` Brown comparison surjective on every shifted generator. -/
private lemma detectingBrownInitialStage
    {S : Set D} {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive]
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ (X0 : D) (a0 : H.obj (op X0)),
      ∀ ⦃E : D⦄, E ∈ brownShiftClosure (D := D) S →
        Function.Surjective (((detectingBrownNatTransOfElement (H := H) (a := a0)).app
          (op E)).hom) := by
  classical
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ E : { E : D // E ∈ brownShiftClosure (D := D) S }, H.obj (op E.1))
  let X0 : D := ∐ fun j : J ↦ j.down.1.1
  obtain ⟨a0, ha0⟩ :=
    detectingBrownInitialStageElementTransport
      (H := H) (K := fun j : J ↦ j.down.1.1) (hprod J) (fun j ↦ j.down.2)
  refine ⟨X0, a0, ?_⟩
  intro E hE
  intro x
  let j : J := ⟨⟨⟨E, hE⟩, x⟩⟩
  refine ⟨Limits.Sigma.ι (fun j' : J ↦ j'.down.1.1) j, ?_⟩
  -- Proof comment: the summand indexed by `(E, x)` maps to `x` by the defining coordinate
  -- property of the transported universal element.
  simpa [X0, j, detectingBrownNatTransOfElement_app_apply] using ha0 j

/-- Helper for Lemma 13.39.1: one Brown successor step records the distinguished triangle, the
lifted next-stage element of `H`, and the fact that every generatorwise kernel element is killed
by the transition map. -/
private structure DetectingBrownSuccessorStep
    (S : Set D) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] (X : D)
    (aX : H.obj (op X)) where
  K : D
  kernelMap : K ⟶ X
  nextX : D
  map : X ⟶ nextX
  connecting : nextX ⟶ K⟦(1 : ℤ)⟧
  nextElement : H.obj (op nextX)
  distinguished : Triangle.mk kernelMap map connecting ∈ distTriang D
  compatible : (H.map map.op).hom nextElement = aX
  kernelKilled :
    ∀ ⦃E : D⦄, E ∈ brownShiftClosure (D := D) S → ∀ φ : E ⟶ X,
      ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op E)).hom φ = 0 →
        φ ≫ map = 0

/-- Helper for Lemma 13.39.1: the kernel-coproduct construction and the cohomological lifting step
produce a Brown successor step from any stage element `aX ∈ H(X)`. -/
private theorem existsDetectingBrownSuccessorStep
    {S : Set D} {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive]
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H)
    {X : D} (aX : H.obj (op X)) :
    Nonempty (DetectingBrownSuccessorStep (D := D) S H X aX) := by
  classical
  let I : Type (max u v) :=
    ULift.{max u v, u} { E : D // E ∈ brownShiftClosure (D := D) S }
  let E : I → D := fun i ↦ i.down.1
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ i : I,
        { φ : E i ⟶ X //
          ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
  let K : D := ∐ fun j : J ↦ E j.down.1
  let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
  obtain ⟨X', u, δ, hT⟩ := distinguished_cocone_triangle κ
  have hkernel :
      ∀ (i : I) (φ : E i ⟶ X),
        ((detectingBrownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 →
          ∃ ψ : E i ⟶ K, ψ ≫ κ = φ := by
    intro i φ hφ
    -- Proof comment: every kernel morphism appears as one chosen summand of the coproduct `K`.
    refine ⟨Limits.Sigma.ι (fun j : J ↦ E j.down.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩, ?_⟩
    simpa [κ] using
      (Limits.Sigma.ι_desc (fun j : J ↦ j.down.2.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩)
  have hzero :
      (H.map κ.op).hom aX = 0 := by
    simpa [I, E, J, K, κ] using
      (detectingBrownKernelCoproductMapZero
        (H := H) (I := I) (E := E) aX (hprod _))
  obtain ⟨aX', haX'⟩ := existsDetectingBrownLiftOfMapZero κ u δ hT hH aX hzero
  refine ⟨⟨K, κ, X', u, δ, aX', hT, haX', ?_⟩⟩
  intro E hE φ hφ
  obtain ⟨ψ, hψ⟩ := hkernel ⟨⟨E, hE⟩⟩ φ hφ
  have hκu : κ ≫ u = 0 := by
    -- Proof comment: the first two morphisms in every distinguished triangle compose to zero.
    simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hT
  -- Proof comment: any kernel morphism factors through `κ`, so the distinguished-triangle
  -- relation forces it to die after postcomposing with the successor map `u`.
  calc
    φ ≫ u = ψ ≫ (κ ≫ u) := by simpa [Category.assoc] using congrArg (fun f ↦ f ≫ u) hψ.symm
    _ = 0 := by simp [hκu]

/-- Helper for Lemma 13.39.1: package the recursive Brown tower over `brownShiftClosure S`,
together with stage compatibility, stage-`0` surjectivity, and one-step kernel killing. -/
private structure DetectingBrownTower (S : Set D) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] where
  X : ℕ → D
  map : ∀ n : ℕ, X n ⟶ X (n + 1)
  a : ∀ n : ℕ, H.obj (op (X n))
  compatible : ∀ n : ℕ, (H.map (map n).op).hom (a (n + 1)) = a n
  stageZeroSurjective :
    ∀ ⦃E : D⦄, E ∈ brownShiftClosure (D := D) S →
      Function.Surjective (((detectingBrownNatTransOfElement (H := H) (a := a 0)).app
        (op E)).hom)
  kernelKilled :
    ∀ ⦃E : D⦄, E ∈ brownShiftClosure (D := D) S → ∀ n : ℕ, ∀ φ : E ⟶ X n,
      ((detectingBrownNatTransOfElement (H := H) (a := a n)).app (op E)).hom φ = 0 →
        φ ≫ map n = 0

/-- Helper for Lemma 13.39.1: recursively assemble the Brown tower from the universal initial
stage and the successor-step package. This isolates the source-faithful tower construction from
the later hocolim and globalization arguments. -/
private theorem existsDetectingBrownTower
    {S : Set D} {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive]
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    Nonempty (DetectingBrownTower (D := D) S H) := by
  classical
  obtain ⟨X0, a0, hsurj0⟩ := detectingBrownInitialStage (D := D) (S := S) (H := H) hprod
  let stage : ℕ → Σ X : D, H.obj (op X) :=
    Nat.rec
      ⟨X0, a0⟩
      (fun _ prev ↦
        let s : DetectingBrownSuccessorStep (D := D) S H prev.1 prev.2 :=
          Classical.choice (existsDetectingBrownSuccessorStep (D := D) (S := S) (H := H)
            hH hprod prev.2)
        ⟨s.nextX, s.nextElement⟩)
  let X : ℕ → D := fun n ↦ (stage n).1
  let a : ∀ n : ℕ, H.obj (op (X n)) := fun n ↦ (stage n).2
  let step : ∀ n : ℕ, DetectingBrownSuccessorStep (D := D) S H (X n) (a n) := fun n ↦
    Classical.choice (existsDetectingBrownSuccessorStep (D := D) (S := S) (H := H)
      hH hprod (a n))
  let map : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ (step n).map
  have hcompat : ∀ n : ℕ, (H.map (map n).op).hom (a (n + 1)) = a n := by
    -- Proof comment: each recursive stage stores the compatibility of the lifted element with the
    -- previous stage.
    intro n
    exact (step n).compatible
  have hkernel :
      ∀ ⦃E : D⦄, E ∈ brownShiftClosure (D := D) S → ∀ n : ℕ, ∀ φ : E ⟶ X n,
        ((detectingBrownNatTransOfElement (H := H) (a := a n)).app (op E)).hom φ = 0 →
          φ ≫ map n = 0 := by
    -- Proof comment: one-step kernel killing is packaged directly in every recursive successor
    -- step.
    intro E hE n φ hφ
    exact (step n).kernelKilled hE φ hφ
  refine ⟨⟨X, map, a, hcompat, ?_, hkernel⟩⟩
  -- Proof comment: stage `0` is the universal coproduct over all shifted-generator elements.
  intro E hE
  simpa [X, a, stage] using hsurj0 hE

/-- Helper for Lemma 13.39.1: a compatible family of stage maps from a sequential diagram to a
fixed target descends along a chosen telescope presentation of its hocolim. This packages the
comparison-map construction used later for represented functors. -/
private lemma existsDetectingBrownComparisonMapFromHocolim
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {A : D}
    (toA : ∀ n : ℕ, X n ⟶ A) (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) :
    ∃ (Xinf : D) (ι : ∀ n : ℕ, X n ⟶ Xinf) (δ : Xinf ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧) (q : Xinf ⟶ A),
      (∀ n : ℕ, map n ≫ ι (n + 1) = ι n) ∧
        Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
          (δ ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D ∧
          (∀ n : ℕ, ι n ≫ q = toA n) := by
  obtain ⟨Xinf, g, δbase, hTbase⟩ :=
    distinguished_cocone_triangle (sequentialTelescopeMap (Functor.ofSequence map))
  let ι : ∀ n : ℕ, X n ⟶ Xinf := fun n ↦ Limits.Sigma.ι X n ≫ g
  let δ : Xinf ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧ :=
    δbase ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).hom
  have hdesc : Limits.Sigma.desc ι = g := by
    apply Limits.Sigma.hom_ext
    intro n
    simp [ι, Category.assoc]
  have hdelta :
      δ ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv = δbase := by
    simp [δ, Category.assoc]
  have htriangle :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
          (δ ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D := by
    -- Proof comment: rewrite the chosen cone of the telescope map in the standard presentation
    -- language expected by `telescopePresentation_compat`.
    rw [hdesc, hdelta]
    simpa using hTbase
  have hιcompat : ∀ n : ℕ, map n ≫ ι (n + 1) = ι n := by
    intro n
    -- Proof comment: the telescope presentation records exactly the successor compatibility of
    -- the hocolim legs.
    simpa [Functor.ofSequence_map_homOfLE_succ, ι, δ] using
      telescopePresentation_compat (S := Functor.ofSequence map) ι δ htriangle n
  have hzero :
      sequentialTelescopeMap (Functor.ofSequence map) ≫ Limits.Sigma.desc toA = 0 := by
    -- Proof comment: compatibility of the stage maps kills the telescope relation.
    exact sequentialTelescopeMap_comp_sigmaDesc
      (Functor.ofSequence map) toA (fun n ↦ by
        simpa [Functor.ofSequence_map_homOfLE_succ] using hcompat n)
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂
    (T := Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
      (δ ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv))
    htriangle (Limits.Sigma.desc toA) hzero
  refine ⟨Xinf, ι, δ, q, hιcompat, htriangle, ?_⟩
  intro n
  have hq' := congrArg (fun f ↦ Limits.Sigma.ι X n ≫ f) hq
  calc
    ι n ≫ q = (Limits.Sigma.ι X n ≫ Limits.Sigma.desc ι) ≫ q := by
      simpa [ι, Category.assoc] using
        congrArg (fun t ↦ t ≫ q) (Limits.Sigma.ι_desc ι n).symm
    _ = Limits.Sigma.ι X n ≫ Limits.Sigma.desc toA := by
      simpa [Category.assoc] using hq'.symm
    _ = toA n := by simp [Limits.Sigma.ι_desc]

/-- Helper for Lemma 13.39.1: once the Brown tower over the shift-closure of `S` is fixed, the
remaining work is to build its hocolim comparison and globalize generatorwise bijectivity to all
objects. -/
private lemma existsDetectingBrownRepresentationOfShiftClosure
    {S : Set D} (hS : IsBrownRepresentabilitySet (D := D) S)
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive]
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H)
    (tower : DetectingBrownTower (D := D) (brownShiftClosure (D := D) S) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  -- TODO: the remaining gap is now purely the source-style hocolim comparison and globalization:
  -- first build the compatible element on the telescope object of `tower.map`, then prove the
  -- resulting comparison map is bijective on `brownShiftClosure S`, and finally reuse
  -- `existsDetectingBrownComparisonMapFromHocolim` for represented functors to kill the cone of
  -- the comparison map by `isZero_of_maps_from_brownSet_zero`.
  sorry

/-- Lemma 13.39.1: if a triangulated category with direct sums admits a set `S` of objects that
detects nonzero objects and through which maps to countable direct sums factor componentwise, then
every contravariant cohomological functor `H : Dᵒᵖ ⥤ AddCommGrpCat` sending direct sums to
products is representable. -/
@[stacks 0GYG]
theorem brown_representability_of_detecting_factorization_set
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) :=
  -- Proof skeleton: the Brown comparison map, the kernel-coproduct successor datum, and the
  -- exactness-based lifting step are now restored locally as
  -- `detectingBrownNatTransOfElement`, `detectingBrownKernelTriangle`,
  -- `detectingBrownKernelCoproductMapZero`, and `existsDetectingBrownLiftOfMapZero`.
  -- Route correction: the source-faithful shift-closure normalization is now restored locally via
  -- `brownShiftClosure` and `isBrownRepresentabilitySet_shift_closure`, so the remaining gap is
  -- exactly the Brown tower / hocolim comparison / globalization package over that normalized set.
  by
    letI : H.rightOp.IsHomological := hH
    letI : H.rightOp.Additive := inferInstance
    letI : H.Additive := by
      simpa using (inferInstance : H.rightOp.leftOp.Additive)
    let S' : Set D := brownShiftClosure (D := D) S
    have hS' : IsBrownRepresentabilitySet (D := D) S' :=
      isBrownRepresentabilitySet_shift_closure (D := D) hS
    obtain ⟨tower⟩ := existsDetectingBrownTower (D := D) (S := S') (H := H) hH hprod
    -- Proof comment: the recursive tower is now packaged, so the remaining step is the hocolim
    -- comparison and globalization over the normalized Brown set.
    simpa [S'] using
      existsDetectingBrownRepresentationOfShiftClosure
        (D := D) (S := S) hS (H := H) hH hprod tower

/-- Canonical companion: Brown representability for a detecting factorization set implies
representability of the underlying `Type`-valued presheaf after the standard `ulift`, which is
the owner abstraction used by adjoint-functor criteria. -/
theorem brown_representability_of_detecting_factorization_set_isRepresentable
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ((H ⋙ forget AddCommGrpCat) ⋙ uliftFunctor.{v}).IsRepresentable := by
  -- Route correction: this companion can be proved immediately from the additive Yoneda
  -- representability statement once the codomain universe matches `preadditiveYoneda`.
  rcases brown_representability_of_detecting_factorization_set (D := D) S hS H hH hprod with
    ⟨X, ⟨e⟩⟩
  -- Forgetting additivity turns the additive Yoneda isomorphism into an ordinary Yoneda one.
  have hrep : (H ⋙ forget AddCommGrpCat).IsRepresentable := by
    exact Functor.IsRepresentable.mk' <| by
      simpa [whiskering_preadditiveYoneda] using
        (Functor.isoWhiskerRight e (forget AddCommGrpCat) :
          preadditiveYoneda.obj X ⋙ forget AddCommGrpCat ≅ H ⋙ forget AddCommGrpCat)
  -- The ordinary type-level universe lift preserves representability.
  letI : (H ⋙ forget AddCommGrpCat).IsRepresentable := hrep
  infer_instance

end

end CategoryTheory
