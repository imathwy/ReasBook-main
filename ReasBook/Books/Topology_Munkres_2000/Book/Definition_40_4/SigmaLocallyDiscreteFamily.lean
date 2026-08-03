module

public import Topology_Munkres_2000.Book.Definition_40_3.LocallyDiscreteFamily
public import Mathlib.Topology.Bases

public section

open Set

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- A family is sigma-locally discrete if its index type is covered by countably many pieces
whose restricted families are locally discrete. -/
def SigmaLocallyDiscreteFamily (f : ι → Set X) : Prop :=
  ∃ pieces : ℕ → Set ι,
    ⋃ n, pieces n = Set.univ ∧
      ∀ n, LocallyDiscreteFamily (fun i : pieces n ↦ f i)

/-- Helper for Definition 40.4: local discreteness is unchanged when a subtype-indexed
family is reindexed by the ambient image of its indices. -/
private lemma locallyDiscreteFamily_subtypeVal_image_iff {𝓑 : Set (Set X)}
    (s : Set 𝓑) :
    LocallyDiscreteFamily (fun B : s ↦ (B.1 : Set X)) ↔
      LocallyDiscreteFamily (Subtype.val : (Subtype.val '' s) → Set X) := by
  classical
  let e : s ≃ Subtype.val '' s := Equiv.Set.image Subtype.val s Subtype.val_injective
  constructor
  · intro hs
    -- Reindex the restricted family along the inverse image equivalence.
    have hreindexed := hs.comp_injective e.symm.injective
    have hfun : (fun B : s ↦ (B.1 : Set X)) ∘ e.symm =
        (Subtype.val : (Subtype.val '' s) → Set X) := by
      funext B
      exact congrArg Subtype.val (e.apply_symm_apply B)
    rwa [hfun] at hreindexed
  · intro hs
    -- Reindex the ambient image family along the forward image equivalence.
    have hreindexed := hs.comp_injective e.injective
    have hfun : (Subtype.val : (Subtype.val '' s) → Set X) ∘ e =
        (fun B : s ↦ (B.1 : Set X)) := by
      funext B
      rfl
    rwa [hfun] at hreindexed

/-- A collection is sigma-locally discrete exactly when it is a countable union of locally
discrete subcollections. -/
theorem sigmaLocallyDiscreteFamily_subtype_iff {𝓑 : Set (Set X)} :
    SigmaLocallyDiscreteFamily (Subtype.val : 𝓑 → Set X) ↔
      ∃ pieces : ℕ → Set (Set X),
        𝓑 = ⋃ n, pieces n ∧
          ∀ n, LocallyDiscreteFamily (Subtype.val : pieces n → Set X) := by
  constructor
  · rintro ⟨pieces, hcover, hlocal⟩
    refine ⟨fun n ↦ Subtype.val '' pieces n, ?_, ?_⟩
    · -- Passing each index piece to its ambient image preserves the countable union.
      ext A
      constructor
      · intro hA
        let B : 𝓑 := ⟨A, hA⟩
        have hB : B ∈ ⋃ n, pieces n := by
          rw [hcover]
          exact Set.mem_univ B
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hB
        exact Set.mem_iUnion.mpr ⟨n, B, hn, rfl⟩
      · intro hA
        obtain ⟨n, B, hB, rfl⟩ := Set.mem_iUnion.mp hA
        exact B.property
    · intro n
      -- The adapter transfers local discreteness to the ambient image collection.
      exact (locallyDiscreteFamily_subtypeVal_image_iff (pieces n)).mp (hlocal n)
  · rintro ⟨pieces, hunion, hlocal⟩
    refine ⟨fun n ↦ Subtype.val ⁻¹' pieces n, ?_, ?_⟩
    · -- Pulling the ambient pieces back to `𝓑` covers every subtype index.
      ext B
      constructor
      · intro _
        exact Set.mem_univ B
      · intro _
        have hB : (B : Set X) ∈ ⋃ n, pieces n := by
          rw [← hunion]
          exact B.property
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hB
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · intro n
      have hsubset : pieces n ⊆ 𝓑 := by
        intro A hA
        rw [hunion]
        exact Set.mem_iUnion.mpr ⟨n, hA⟩
      have himage :
          Subtype.val '' (Subtype.val ⁻¹' pieces n : Set 𝓑) = pieces n := by
        ext A
        constructor
        · rintro ⟨B, hB, rfl⟩
          exact hB
        · intro hA
          exact ⟨⟨A, hsubset hA⟩, hA, rfl⟩
      -- The image of the pulled-back piece is the original ambient piece.
      have hlocaln := hlocal n
      rw [← himage] at hlocaln
      exact (locallyDiscreteFamily_subtypeVal_image_iff
        (Subtype.val ⁻¹' pieces n : Set 𝓑)).mpr hlocaln

/-- A space has a sigma-locally discrete basis if some topological basis is a
sigma-locally discrete family. -/
def HasSigmaLocallyDiscreteBasis (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝓑 : Set (Set X),
    TopologicalSpace.IsTopologicalBasis 𝓑 ∧
      SigmaLocallyDiscreteFamily (Subtype.val : 𝓑 → Set X)

/-- A space has a sigma-locally discrete basis exactly when it has a basis that is a
countable union of locally discrete subcollections. -/
theorem hasSigmaLocallyDiscreteBasis_iff (X : Type u) [TopologicalSpace X] :
    HasSigmaLocallyDiscreteBasis X ↔
      ∃ 𝓑 : Set (Set X), ∃ pieces : ℕ → Set (Set X),
        TopologicalSpace.IsTopologicalBasis 𝓑 ∧
          𝓑 = ⋃ n, pieces n ∧
            ∀ n, LocallyDiscreteFamily (Subtype.val : pieces n → Set X) := by
  constructor
  · rintro ⟨𝓑, hbasis, hsigma⟩
    -- Expand sigma-local discreteness into ambient subcollections of the basis.
    obtain ⟨pieces, hunion, hlocal⟩ :=
      sigmaLocallyDiscreteFamily_subtype_iff.mp hsigma
    exact ⟨𝓑, pieces, hbasis, hunion, hlocal⟩
  · rintro ⟨𝓑, pieces, hbasis, hunion, hlocal⟩
    -- Repackage the ambient subcollections as a sigma-locally discrete basis family.
    refine ⟨𝓑, hbasis, ?_⟩
    exact sigmaLocallyDiscreteFamily_subtype_iff.mpr ⟨pieces, hunion, hlocal⟩
