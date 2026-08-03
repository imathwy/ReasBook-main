module

public import Topology_Munkres_2000.Book.Definition_6_0_1.LocallyFinite
public import Mathlib.Topology.Bases

public section

open Set

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- Helper for Definition 6.0.2: a family is sigma-locally finite if its index type is
covered by countably many pieces whose restricted families are locally finite. -/
def SigmaLocallyFinite (f : ι → Set X) : Prop :=
  ∃ pieces : ℕ → Set ι,
    ⋃ n, pieces n = Set.univ ∧
      ∀ n, LocallyFinite (fun i : pieces n ↦ f i)

/-- Helper for Definition 6.0.2: an injectively indexed restricted family is
locally finite exactly when its image collection is locally finite. -/
private lemma locallyFiniteRestrict_iff_image {f : ι → Set X} {s : Set ι}
    (hinj : Set.InjOn f s) :
    LocallyFinite (fun i : s ↦ f i) ↔ (f '' s).LocallyFinite := by
  constructor
  · intro h
    -- Reindex the restricted family by its surjective image factorization.
    apply LocallyFinite.of_comp_surjective Set.imageFactorization_surjective
    rw [Set.imageFactorization_eq]
    simpa only [Function.comp_def] using h
  · intro h
    -- Injectivity of the factorization identifies the image family with the restriction.
    have himage := h.comp_injective hinj.imageFactorization_injective
    rw [Set.imageFactorization_eq] at himage
    simpa only [Function.comp_def] using himage

/-- Helper for Definition 6.0.2: a subcollection is sigma-locally finite exactly when it
is a countable union of locally finite subcollections. -/
theorem sigmaLocallyFinite_subtype_iff {𝓑 : Set (Set X)} :
    SigmaLocallyFinite (Subtype.val : 𝓑 → Set X) ↔
      ∃ pieces : ℕ → Set (Set X),
        𝓑 = ⋃ n, pieces n ∧
          ∀ n, (pieces n).LocallyFinite := by
  constructor
  · rintro ⟨pieces, hcover, hfinite⟩
    -- Send every subtype-indexed piece to its underlying subcollection.
    refine ⟨fun n ↦ Subtype.val '' pieces n, ?_, fun n ↦ ?_⟩
    · calc
        𝓑 = Subtype.val '' (Set.univ : Set 𝓑) := (Subtype.coe_image_univ 𝓑).symm
        _ = Subtype.val '' ⋃ n, pieces n := congrArg (Set.image Subtype.val) hcover.symm
        _ = ⋃ n, Subtype.val '' pieces n := Set.image_iUnion
    · exact (locallyFiniteRestrict_iff_image Subtype.val_injective.injOn).mp (hfinite n)
  · rintro ⟨pieces, hcover, hfinite⟩
    -- Pull every proposed subcollection back to the basis subtype.
    refine ⟨fun n ↦ Subtype.val ⁻¹' pieces n, ?_, fun n ↦ ?_⟩
    · calc
        ⋃ n, Subtype.val ⁻¹' pieces n = Subtype.val ⁻¹' ⋃ n, pieces n :=
          Set.preimage_iUnion.symm
        _ = Subtype.val ⁻¹' 𝓑 := congrArg (Set.preimage Subtype.val) hcover.symm
        _ = Set.univ := Subtype.coe_preimage_self 𝓑
    · have hsubset : pieces n ⊆ 𝓑 := by
        -- Membership in the nth summand gives membership in the full basis collection.
        intro A hA
        rw [hcover]
        exact Set.mem_iUnion_of_mem n hA
      apply (locallyFiniteRestrict_iff_image Subtype.val_injective.injOn).mpr
      simpa only [Subtype.image_preimage_val, inter_eq_right.mpr hsubset] using hfinite n
