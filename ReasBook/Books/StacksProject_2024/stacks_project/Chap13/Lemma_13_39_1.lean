import Mathlib
import StacksProject_2024.Chap13.Definition_13_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/-
Domain-style sampling for Lemma 13.39.1:
- primary domain: Brown representability in triangulated categories, with the canonical
  representability layer owned by Yoneda/preadditive-Yoneda API;
- sampled owner declarations:
  `Functor.IsRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `whiskering_preadditiveYoneda`;
- best owner abstraction for the representability conclusion:
  `Functor.IsRepresentable (H ⋙ forget AddCommGrpCat)`;
- primitive data: the subset `S : Set D` together with the source-specific Brown hypotheses
  packaged by `IsBrownRepresentabilitySet S`, the functor `H`, its homologicality, and the
  product-preservation hypothesis `hprod`;
- derived API: the source-facing additive representability statement
  `∃ X, Nonempty (preadditiveYoneda.obj X ≅ H)` and the canonical representability companion for
  the underlying `Type`-valued functor;
- source/core/bridge triage:
  `source-facing`: `brown_representability_of_detecting_factorization_set`;
  `core/canonical`: `(H ⋙ forget AddCommGrpCat).IsRepresentable`;
  `bridge/view`: whiskering the additive Yoneda isomorphism along `forget AddCommGrpCat` and
  rewriting with `whiskering_preadditiveYoneda`.

The Brown-set hypothesis itself stays source-facing primitive data: there is no upstream owner in
the chapter or mathlib for the countable factorization clause, and the nonzero-detection clause is
not merely a duplicate of the stronger separating-owner API. -/

/-- A set of objects satisfying the Stacks-project hypotheses used in Brown representability:
it detects nonzero objects and maps from its objects to countable direct sums factor through
countable direct sums of objects of the same set. -/
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

/-- Helper for Lemma 13.39.1: the shift-closure of a Brown representability set, enlarged further
by isomorphism so that later arguments can work with literal shifted objects instead of constantly
transporting membership proofs. -/
def brownShiftClosure (S : Set D) : Set D := fun X ↦
  ∃ E : D, E ∈ S ∧ ∃ n : ℤ, Nonempty (E⟦n⟧ ≅ X)

/-- Helper for Lemma 13.39.1: every original member of `S` belongs to its shift-closure via the
trivial shift. -/
lemma mem_brownShiftClosure_of_mem {S : Set D} {E : D} (hE : E ∈ S) :
    E ∈ brownShiftClosure (D := D) S := by
  -- The zero shift identifies `E⟦0⟧` with `E`, so every original Brown object is already in the
  -- enlarged source-faithful set.
  refine ⟨E, hE, 0, ?_⟩
  exact ⟨(shiftFunctorZero D ℤ).app E⟩

/-- Helper for Lemma 13.39.1: the shift-closure is closed under isomorphism of the ambient
triangulated category. -/
lemma mem_brownShiftClosure_of_iso {S : Set D} {X Y : D}
    (hX : X ∈ brownShiftClosure (D := D) S) (e : X ≅ Y) :
    Y ∈ brownShiftClosure (D := D) S := by
  rcases hX with ⟨E, hE, n, ⟨i⟩⟩
  -- Compose the stored shift-isomorphism with the new ambient isomorphism.
  exact ⟨E, hE, n, ⟨i.trans e⟩⟩

/-- Helper for Lemma 13.39.1: the enlarged Brown set is closed under further shifts. This lets
the source proof work with a literally shift-stable detecting set after the initial enlargement
step. -/
lemma mem_brownShiftClosure_shift {S : Set D} {X : D} (hX : X ∈ brownShiftClosure (D := D) S)
    (n : ℤ) :
    X⟦n⟧ ∈ brownShiftClosure (D := D) S := by
  rcases hX with ⟨E, hE, m, ⟨i⟩⟩
  -- Reindex the stored witness from `m` to `m + n` and transport along the canonical
  -- shift-associativity isomorphism.
  refine ⟨E, hE, m + n, ?_⟩
  refine ⟨(shiftAdd E m n).trans ((shiftFunctor D n).mapIso i)⟩

/-- Helper for Lemma 13.39.1: the Brown factorization clause transports across an isomorphism of
the source object. This isolates the later tower construction from bookkeeping about replacing a
test object by an isomorphic one. -/
lemma IsBrownRepresentabilitySet.factors_through_countable_coproducts_of_iso_source
    {S : Set D} (hS : IsBrownRepresentabilitySet (D := D) S) (X : ℕ → D) {E E' : D}
    (hE : E ∈ S) (e : E' ≅ E) (α : E' ⟶ ∐ X) :
    ∃ (E'' : ℕ → D), (∀ n : ℕ, E'' n ∈ S) ∧
      ∃ (β : ∀ n : ℕ, E'' n ⟶ X n) (γ : E' ⟶ ∐ E''),
        γ ≫ Limits.Sigma.map β = α := by
  rcases hS.factors_through_countable_coproducts X hE (e.inv ≫ α) with
    ⟨E'', hE'', β, γ, hγ⟩
  refine ⟨E'', hE'', β, e.hom ≫ γ, ?_⟩
  -- Precompose the original factorization by the source isomorphism to return to the given map
  -- `α`.
  calc
    (e.hom ≫ γ) ≫ Limits.Sigma.map β = e.hom ≫ (γ ≫ Limits.Sigma.map β) := by
      simp [Category.assoc]
    _ = e.hom ≫ (e.inv ≫ α) := by rw [hγ]
    _ = α := by simp

/-- Helper for Lemma 13.39.1: the nonzero-detection clause already extends from `S` to its
shift-closure because the original detecting object lies in the enlarged set. -/
lemma detects_nonzero_objects_brownShiftClosure {S : Set D}
    (hS : IsBrownRepresentabilitySet (D := D) S) {X : D} (hX : ¬ IsZero X) :
    ∃ E : D, E ∈ brownShiftClosure (D := D) S ∧ ∃ f : E ⟶ X, f ≠ 0 := by
  rcases hS.detects_nonzero_objects hX with ⟨E, hE, f, hf⟩
  -- The original detecting object is in the shift-closure, so the same nonzero map still works.
  exact ⟨E, mem_brownShiftClosure_of_mem (D := D) hE, f, hf⟩

/-- Helper for Lemma 13.39.1: if each component map to a sequential system is killed by the
successor morphism, then the induced coproduct map is fixed by the telescope endomorphism. This is
the source calculation used later to deduce injectivity on `Hom(E, ∐ Xₙ)`. -/
lemma sigma_map_fixed_by_sequentialTelescopeMap_of_components_killed
    {X E' : ℕ → D} (ι : ∀ n : ℕ, X n ⟶ X (n + 1)) (β : ∀ n : ℕ, E' n ⟶ X n)
    (hβ : ∀ n : ℕ, β n ≫ ι n = 0) :
    Limits.Sigma.map β ≫ sequentialTelescopeMap (Functor.ofSequence ι) = Limits.Sigma.map β := by
  -- Check the claimed fixed-point identity on each coproduct summand of `∐ E'`.
  apply Limits.Sigma.hom_ext
  intro n
  conv_lhs =>
    rw [Sigma.ι_map_assoc]
  -- The successor component vanishes by hypothesis, so the telescope acts as the identity on the
  -- `n`th summand map.
  have hfixed :
      β n ≫ Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence ι) = β n ≫ Sigma.ι X n := by
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

/-- Helper for Lemma 13.39.1: shifting commutes with countable coproducts, so the coproduct of
the shifted family `X i⟦n⟧` canonically identifies with the shift of the coproduct `∐ X`. -/
def sigma_shift_iso (X : ℕ → D) (n : ℤ) :
    (∐ fun i ↦ X i⟦n⟧) ≅ (∐ X)⟦n⟧ :=
  (PreservesCoproduct.iso (shiftFunctor D n) X).symm

/-- Helper for Lemma 13.39.1: under `sigma_shift_iso`, the `i`th inclusion into the shifted
coproduct becomes the shifted inclusion of the original `i`th summand. -/
lemma sigma_ι_comp_sigma_shift_iso_hom (X : ℕ → D) (n : ℤ) (i : ℕ) :
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
    -- Rewrite the coproduct comparison through `sigmaComparison` and then apply the standard
    -- summand formula for preserved coproducts.
    rw [hhom]
    exact Limits.map_ι_comp_inv_sigmaComparison (shiftFunctor D n) X i
  -- Cancel the comparison isomorphism to read the identity in the source-facing orientation.
  change Limits.Sigma.ι (fun j ↦ X j⟦n⟧) i ≫
      (PreservesCoproduct.iso (shiftFunctor D n) X).inv =
      (shiftFunctor D n).map (Limits.Sigma.ι X i)
  apply (cancel_mono (PreservesCoproduct.iso (shiftFunctor D n) X).hom).1
  simpa [sigma_shift_iso, Category.assoc] using hι.symm

/-- Helper for Lemma 13.39.1: shifting the componentwise coproduct map `Sigma.map β₀` and then
reassembling the shifted target family yields the coproduct map built from the shifted component
maps. -/
lemma sigma_map_shift_reassembly
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
  -- Check the reassembled coproduct map on each summand of `∐ i, E0 i⟦n⟧`.
  apply Limits.Sigma.hom_ext
  intro i
  have htarget :
      (shiftFunctor D n).map (Limits.Sigma.ι (fun j ↦ X j⟦-n⟧) i) ≫
          (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).inv =
        Limits.Sigma.ι (fun j ↦ X j⟦-n⟧⟦n⟧) i := by
    -- Cancel the coproduct comparison isomorphism to rewrite the shifted target summand.
    apply (cancel_mono (sigma_shift_iso (D := D) (fun j ↦ X j⟦-n⟧) n).hom).1
    simpa [Category.assoc] using
      (sigma_ι_comp_sigma_shift_iso_hom (D := D) (X := fun j ↦ X j⟦-n⟧) n i).symm
  -- After the two coproduct-comparison rewrites, the summand calculation is exactly the pointwise
  -- definition of the shifted component map.
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

/-- Helper for Lemma 13.39.1: transporting a Brown factorization through the shift comparison and
then shifting the factor objects back termwise recovers the original map `α`. -/
lemma sigma_shift_total_transport
    (X : ℕ → D) (n : ℤ) :
    (sigma_shift_iso (D := D) (fun i ↦ X i⟦-n⟧) n).hom ≫
        (shiftFunctor D n).map (sigma_shift_iso (D := D) X (-n)).hom ≫
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (∐ X)).hom =
      Limits.Sigma.map (fun i ↦
        ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom) := by
  let τX : ∀ i : ℕ, X i⟦-n⟧⟦n⟧ ⟶ X i := fun i ↦
    ((shiftFunctorCompIsoId D (-n) n (by simp)).app (X i)).hom
  -- Compare both maps on each summand of the doubly shifted coproduct.
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
    -- This is exactly the naturality square of the shift-composition comparison on the `i`th
    -- coproduct inclusion.
    simpa [τX, Functor.comp_map] using
      ((shiftFunctorCompIsoId D (-n) n (by simp)).hom.naturality (Limits.Sigma.ι X i))
  -- Once the two comparison isomorphisms have been exposed, the target map is just the coproduct
  -- of the pointwise shift-composition comparisons.
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

/-- Helper for Lemma 13.39.1: transporting a Brown factorization through the shift comparison and
then shifting the factor objects back termwise recovers the original map `α`. -/
lemma shift_source_transport_hom (E : D) (n : ℤ) :
    ((shiftFunctorCompIsoId D (-n) n (by simp)).app (E⟦n⟧)).hom =
      (shiftFunctor D n).map (((shiftFunctorCompIsoId D n (-n) (by simp)).app E).hom) := by
  sorry

/-- Helper for Lemma 13.39.1: transporting a Brown factorization through the shift comparison and
then shifting the factor objects back termwise recovers the original map `α`. -/
lemma shifted_factorization_recovers_original_map
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
  sorry

/-- Helper for Lemma 13.39.1: a literal shifted member `E⟦n⟧` of the enlarged Brown set should
inherit the countable-coproduct factorization property from `E ∈ S` after transporting the map
through the coproduct/shift comparison. -/
lemma IsBrownRepresentabilitySet.factors_through_countable_coproducts_of_shift_member
    {S : Set D} (hS : IsBrownRepresentabilitySet (D := D) S) (X : ℕ → D) {E : D}
    (hE : E ∈ S) (n : ℤ) (α : E⟦n⟧ ⟶ ∐ X) :
    ∃ (E' : ℕ → D), (∀ i : ℕ, E' i ∈ brownShiftClosure (D := D) S) ∧
      ∃ (β : ∀ i : ℕ, E' i ⟶ X i) (γ : E⟦n⟧ ⟶ ∐ E'),
        γ ≫ Limits.Sigma.map β = α :=
by
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
    -- Each shifted-back witness still lies in the enlarged Brown set because the original
    -- witness lay in `S` and the shift-closure was built to absorb all shifts.
    exact mem_brownShiftClosure_shift (D := D)
      (mem_brownShiftClosure_of_mem (D := D) (hE0 i)) n
  · -- The explicit transport-back helper converts the Brown factorization of `αneg` back into a
    -- factorization of the original map `α`.
    simpa [Eshift, β, γ, Xneg, αneg] using
      shifted_factorization_recovers_original_map
        (D := D) (X := X) (E0 := E0) (E := E) n α γ0 β0 hγ0

/-- Helper for Lemma 13.39.1: enlarging a Brown representability set by all shifts and isomorphic
copies preserves the Brown factorization and nonzero-detection clauses. -/
lemma isBrownRepresentabilitySet_shift_closure {S : Set D}
    (hS : IsBrownRepresentabilitySet (D := D) S) :
    IsBrownRepresentabilitySet (brownShiftClosure (D := D) S) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    -- The original detecting clause already passes to the shift-closed enlargement.
    exact detects_nonzero_objects_brownShiftClosure (D := D) hS hX
  · intro X A hA α
    rcases hA with ⟨E, hE, n, ⟨e⟩⟩
    rcases hS.factors_through_countable_coproducts_of_shift_member (X := X) hE n
        (e.hom ≫ α) with ⟨E', hE', β, γ, hγ⟩
    refine ⟨E', hE', β, e.inv ≫ γ, ?_⟩
    -- Transport the shifted-source factorization back across the chosen isomorphism `e`.
    calc
      (e.inv ≫ γ) ≫ Limits.Sigma.map β = e.inv ≫ (γ ≫ Limits.Sigma.map β) := by
        simp [Category.assoc]
      _ = e.inv ≫ (e.hom ≫ α) := by rw [hγ]
      _ = α := by simp

-- Proof sketch: enlarge `S` by all shifts and run the standard Brown approximation argument.
-- Build the tower `X₁ ⟶ X₂ ⟶ ⋯` from all elements of `H(E)` and of the successive kernels, take
-- its homotopy colimit, and use the factorization hypothesis to show the induced comparison
-- `preadditiveYoneda.obj X ⟶ H` is bijective on `S`. The full subcategory on which this
-- comparison is an isomorphism is triangulated and closed under direct sums, so the detecting
-- hypothesis forces it to be all of `D`.
/-- Lemma 13.39.1: if a triangulated category with direct sums admits a set `S` of objects that
detects nonzero objects and through which maps to countable direct sums factor componentwise, then
every contravariant cohomological functor `H : Dᵒᵖ ⥤ AddCommGrpCat` sending direct sums to
products is representable. -/
theorem brown_representability_of_detecting_factorization_set
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  classical
  let Sshift : Set D := brownShiftClosure (D := D) S
  have hSshift : IsBrownRepresentabilitySet Sshift := by
    -- The shift-closure package is now isolated from the Brown tower itself.
    simpa [Sshift] using isBrownRepresentabilitySet_shift_closure (D := D) hS
  -- Route correction: the source proof first enlarges `S` by shifts and then runs the Brown
  -- approximation tower only on that shift-stable detecting set, and the shift-stability is now
  -- recorded by the packaged Brown-set structure `hSshift`.
  -- The pure telescope rewrite from the source proof is now available as
  -- `sigma_map_fixed_by_sequentialTelescopeMap_of_components_killed`.
  -- TODO: first prove that `Sshift` again satisfies the Brown factorization clause by transporting
  -- `hS.factors_through_countable_coproducts` across shifts; with that shift-source bridge in
  -- place, the Brown tower, telescope injectivity argument, and final globalization can follow
  -- the source proof verbatim.
  sorry

/-- Canonical companion: Brown representability for a detecting factorization set implies
representability of the universe-lifted underlying `Type`-valued presheaf, which is the owner
abstraction used by adjoint-functor criteria when the target Hom-universe is larger than the source
Hom-universe of `D`. -/
theorem brown_representability_of_detecting_factorization_set_isRepresentable
    (S : Set D) (hS : IsBrownRepresentabilitySet S) (H : Dᵒᵖ ⥤ AddCommGrpCat.{w})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ((H ⋙ forget AddCommGrpCat) ⋙ uliftFunctor.{v}).IsRepresentable := by
  -- TODO: once the main Brown representability theorem is upgraded to the universe-lifted
  -- additive target `AddCommGrpCat.{w}`, whisker its representing isomorphism along `forget` and
  -- `uliftFunctor` exactly as in Lemma 13.38.1.
  sorry

end

end CategoryTheory
