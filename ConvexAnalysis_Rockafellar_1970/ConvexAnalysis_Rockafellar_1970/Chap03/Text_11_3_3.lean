import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_1_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_8

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open AffineSubspace
open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Text 11.3.3 says that when a subset of a finite-dimensional affine space is not
  full-dimensional, its affine hull can be enlarged to a codimension-one affine subspace
  containing the whole set.
- `core/canonical`: the owner abstractions are `affineSpan` (rendered on theorem surfaces as
  `aff[𝕜]`) for the intrinsic affine hull of `C` and `AffineSubspace.is_hyperplane` for
  codimension-one affine subspaces; the earlier project
  owner theorem `AffineSubspace.exists_eq_sInf_finset_hyperplanes` is the canonical containment
  source for proper affine subspaces in the model vector space.
- `bridge/view`: pass from an affine subspace `s : AffineSubspace 𝕜 P` to the vector-space owner
  `s.direction.toAffineSubspace`, choose one containing hyperplane there using
  `AffineSubspace.exists_eq_sInf_finset_hyperplanes`, and translate it back with
  `AffineSubspace.mk'`.
- Domain-style sampling used here: `affineSpan`, `aff[𝕜]`, `affineSpan_le`,
  `AffineSubspace.exists_eq_sInf_finset_hyperplanes`, and `AffineSubspace.mk'_eq`.
- Primitive data vs derived API: the primitive extension input is a proper affine subspace
  `s ≠ ⊤`; the source hypothesis `aff[𝕜] C ≠ ⊤` is its set-level specialization, while the
  set containment `C ⊆ H` is derived from the owner-level inclusion `aff[𝕜] C ≤ H`.
- Ambient minimization: the owner declarations already live over an arbitrary affine space over a
  division ring, and this item uses no coordinate or order structure, so finite-dimensional
  assumptions should be attached only where the chosen owner bridge actually uses them.
- Layer target: the affine-subspace extension theorem is the reusable `bridge/view` owner statement,
  and the set-level hyperplane-containment theorem is its `source-facing` specialization.
-/

namespace AffineSubspace

/-- A proper affine subspace with `s ≠ ⊥` is contained in some hyperplane. This owner-level form
keeps nontriviality proof-local: no global `[Nontrivial V]` assumption is needed in the statement.
-/
theorem exists_hyperplane_of_ne_bot_of_ne_top (s : AffineSubspace 𝕜 P) (hsbot : s ≠ ⊥)
    [FiniteDimensional 𝕜 (V ⧸ s.direction)]
    (hs : s ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, s ≤ H ∧ H.is_hyperplane := by
  have hs_nonempty : (s : Set P).Nonempty := by
    rwa [AffineSubspace.nonempty_iff_ne_bot]
  let e : (V ⧸ (s.direction.toAffineSubspace).direction) ≃ₗ[𝕜] (V ⧸ s.direction) :=
    Submodule.quotEquivOfEq _ _ (Submodule.toAffineSubspace_direction s.direction)
  letI : FiniteDimensional 𝕜 (V ⧸ (s.direction.toAffineSubspace).direction) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hsdir_ne_bot : s.direction.toAffineSubspace ≠ (⊥ : AffineSubspace 𝕜 V) := by
    rw [← AffineSubspace.nonempty_iff_ne_bot]
    exact ⟨0, by simp⟩
  obtain ⟨t, ht, hsdir⟩ :=
    AffineSubspace.exists_eq_sInf_finset_hyperplanes_of_ne_bot s.direction.toAffineSubspace
      hsdir_ne_bot
  have ht_nonempty : t.Nonempty := by
    by_contra ht_empty
    have htop : s.direction.toAffineSubspace = (⊤ : AffineSubspace 𝕜 V) := by
      rw [hsdir, Finset.not_nonempty_iff_eq_empty.mp ht_empty]
      simp
    have hdir_top : s.direction = ⊤ := by
      simpa using congrArg AffineSubspace.direction htop
    exact hs ((AffineSubspace.direction_eq_top_iff_of_nonempty hs_nonempty).mp hdir_top)
  rcases ht_nonempty with ⟨H₀, hH₀mem⟩
  have hsdirH₀ : s.direction.toAffineSubspace ≤ H₀ := by
    rw [hsdir]
    exact sInf_le hH₀mem
  have hdir_le : s.direction ≤ H₀.direction := by
    simpa using AffineSubspace.direction_le hsdirH₀
  have hH₀ : H₀.is_hyperplane := ht H₀ hH₀mem
  rcases hs_nonempty with ⟨p, hp⟩
  refine ⟨AffineSubspace.mk' p H₀.direction, ?_, ?_⟩
  · rw [← AffineSubspace.mk'_eq hp]
    intro q hq
    rw [AffineSubspace.mem_mk'] at hq ⊢
    exact hdir_le hq
  · refine ⟨?_, ?_⟩
    · intro hbot
      have hp' : p ∈ AffineSubspace.mk' p H₀.direction := AffineSubspace.self_mem_mk' _ _
      simpa [hbot] using hp'
    · rw [AffineSubspace.direction_mk']
      exact hH₀.2

/-- A nonempty proper affine subspace is contained in some hyperplane. This is the source-facing
nonempty-set corollary of the owner-level theorem
`exists_hyperplane_of_ne_bot_of_ne_top`. -/
theorem exists_hyperplane_of_nonempty_of_ne_top (s : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 (V ⧸ s.direction)]
    (hs_nonempty : (s : Set P).Nonempty) (hs : s ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, s ≤ H ∧ H.is_hyperplane := by
  refine exists_hyperplane_of_ne_bot_of_ne_top s ?_ hs
  exact (AffineSubspace.nonempty_iff_ne_bot s).1 hs_nonempty

/-- A proper affine subspace whose direction quotient is finite-dimensional and nontrivial is
contained in some hyperplane. -/
-- Proof sketch: the nonempty case is the primitive owner theorem
-- `exists_hyperplane_of_ne_bot_of_ne_top`. For `s = ⊥`, choose a hyperplane direction in the
-- model vector space from `exists_eq_sInf_finset_hyperplanes` and translate it through any point
-- of `⊤`.
theorem exists_hyperplane_of_ne_top (s : AffineSubspace 𝕜 P)
    [FiniteDimensional 𝕜 (V ⧸ s.direction)]
    [Nontrivial (V ⧸ s.direction)]
    (hs : s ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, s ≤ H ∧ H.is_hyperplane := by
  rcases s.eq_bot_or_nonempty with rfl | hs_nonempty
  · letI : Nontrivial (V ⧸ (⊥ : Submodule 𝕜 V)) := by
      simpa using (inferInstance : Nontrivial (V ⧸ (⊥ : AffineSubspace 𝕜 P).direction))
    letI : Nontrivial V :=
      Function.Surjective.nontrivial (Submodule.mkQ_surjective (⊥ : Submodule 𝕜 V))
    let e :
        (V ⧸ (⊥ : AffineSubspace 𝕜 V).direction) ≃ₗ[𝕜]
          (V ⧸ (⊥ : AffineSubspace 𝕜 P).direction) :=
      Submodule.quotEquivOfEq _ _ (by simp)
    letI : FiniteDimensional 𝕜 (V ⧸ (⊥ : AffineSubspace 𝕜 V).direction) :=
      FiniteDimensional.of_injective e.toLinearMap e.injective
    obtain ⟨t, ht, hbot_eq⟩ :=
      AffineSubspace.exists_eq_sInf_finset_hyperplanes (⊥ : AffineSubspace 𝕜 V)
    have ht_nonempty : t.Nonempty := by
      by_contra ht_empty
      have htop : (⊥ : AffineSubspace 𝕜 V) = ⊤ := by
        rw [hbot_eq, Finset.not_nonempty_iff_eq_empty.mp ht_empty]
        simp
      exact (show (⊥ : AffineSubspace 𝕜 V) ≠ ⊤ by simp) htop
    rcases ht_nonempty with ⟨H₀, hH₀mem⟩
    have hH₀ : H₀.is_hyperplane := ht H₀ hH₀mem
    have htop_nonempty : ((⊤ : AffineSubspace 𝕜 P) : Set P).Nonempty := by
      rw [AffineSubspace.nonempty_iff_ne_bot]
      exact hs.symm
    rcases htop_nonempty with ⟨p, -⟩
    refine ⟨AffineSubspace.mk' p H₀.direction, bot_le, ?_⟩
    refine ⟨?_, ?_⟩
    · intro hbot
      have hp : p ∈ AffineSubspace.mk' p H₀.direction := AffineSubspace.self_mem_mk' _ _
      simpa [hbot] using hp
    · rw [AffineSubspace.direction_mk']
      exact hH₀.2
  · have hsbot : s ≠ ⊥ := by
      exact (AffineSubspace.nonempty_iff_ne_bot s).1 hs_nonempty
    exact exists_hyperplane_of_ne_bot_of_ne_top s hsbot hs

end AffineSubspace

/-- Text 11.3.3, intrinsic affine-span owner form: if `aff[𝕜] C` is proper and nonempty,
then some hyperplane contains that affine hull. -/
theorem exists_hyperplane_of_affineSpan_ne_bot_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    (hCbot : (aff[𝕜] C) ≠ ⊥) (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, (aff[𝕜] C) ≤ H ∧ H.is_hyperplane := by
  simpa using
    (aff[𝕜] C).exists_hyperplane_of_ne_bot_of_ne_top hCbot hC

/-- Text 11.3.3, intrinsic affine-span owner form with nonempty-set input: if `C` is nonempty and
`aff[𝕜] C` is proper, then some hyperplane contains `aff[𝕜] C`. -/
theorem exists_hyperplane_of_nonempty_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    (hC_nonempty : C.Nonempty) (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, (aff[𝕜] C) ≤ H ∧ H.is_hyperplane := by
  have hCbot : (aff[𝕜] C) ≠ ⊥ := by
    rw [← AffineSubspace.nonempty_iff_ne_bot]
    exact hC_nonempty.affineSpan 𝕜
  exact exists_hyperplane_of_affineSpan_ne_bot_of_affineSpan_ne_top hCbot hC

/-- Text 11.3.3, intrinsic affine-span owner form: if `aff[𝕜] C` is proper and its quotient
is finite-dimensional and nontrivial, then some hyperplane contains `aff[𝕜] C`. -/
theorem exists_hyperplane_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    [Nontrivial (V ⧸ (aff[𝕜] C).direction)]
    (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, (aff[𝕜] C) ≤ H ∧ H.is_hyperplane := by
  simpa using (aff[𝕜] C).exists_hyperplane_of_ne_top hC

/-- Text 11.3.3, source-facing containment form: every subset with proper nonempty affine hull is
contained in a hyperplane. -/
theorem exists_hyperplane_containing_of_affineSpan_ne_bot_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    (hCbot : (aff[𝕜] C) ≠ ⊥) (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, C ⊆ H ∧ H.is_hyperplane := by
  rcases exists_hyperplane_of_affineSpan_ne_bot_of_affineSpan_ne_top
      (C := C) hCbot hC with ⟨H, hspanH, hH⟩
  exact ⟨H, (Set.aff_le_iff).1 hspanH, hH⟩

/-- Text 11.3.3, source-facing nonempty-set form: every nonempty subset whose affine hull is proper
is contained in a hyperplane. -/
theorem exists_hyperplane_containing_of_nonempty_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    (hC_nonempty : C.Nonempty) (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, C ⊆ H ∧ H.is_hyperplane := by
  rcases exists_hyperplane_of_nonempty_of_affineSpan_ne_top
      (C := C) hC_nonempty hC with ⟨H, hspanH, hH⟩
  exact ⟨H, (Set.aff_le_iff).1 hspanH, hH⟩

/-- Text 11.3.3, source-facing containment form: every subset whose affine hull has
finite-dimensional nontrivial quotient and is proper is contained in a hyperplane. -/
theorem exists_hyperplane_containing_of_affineSpan_ne_top {C : Set P}
    [FiniteDimensional 𝕜 (V ⧸ (aff[𝕜] C).direction)]
    [Nontrivial (V ⧸ (aff[𝕜] C).direction)]
    (hC : (aff[𝕜] C) ≠ ⊤) :
    ∃ H : AffineSubspace 𝕜 P, C ⊆ H ∧ H.is_hyperplane := by
  rcases exists_hyperplane_of_affineSpan_ne_top (C := C) hC with ⟨H, hspanH, hH⟩
  exact ⟨H, (Set.aff_le_iff).1 hspanH, hH⟩

end
