import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_11_3_1 (from Chap03) -/
namespace Set

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 11.3.1 defines what it means for a closed half-space to support a set.
- `core/canonical`: the owner abstractions already present in the project are the predicate
  `IsClosedHalfSpace` on subsets of `X` and the topological boundary operator `frontier`.
- `bridge/view`: the textbook phrase "supporting half-space" is the conjunction of those owner
  notions for a pair `(s, C)`; it does not introduce new primitive structure beyond the
  underlying half-space candidate `s`.
- Primitive data vs derived API: the primitive inputs are the candidate half-space `s` and the
  supported set `C`; the supporting condition itself is a derived `Prop` on the owner `s`,
  with primitive contact data encoded intrinsically as the set-level condition
  `(C ∩ frontier s).Nonempty`, while the pointwise witness form
  `∃ x ∈ C, x ∈ frontier s` is bridge API.
- Domain-style sampling used here: the project declaration `IsClosedHalfSpace`, the Chapter 11
  owner-predicate style in `AffineSubspace.IsSupportingHyperplane`, the refinement pattern in
  `AffineSubspace.IsNontrivialSupportingHyperplane`, and the standard boundary operator
  `frontier`. The notion depends only on these coordinate-free owners, so the declaration should
  live on the pairing-based half-space layer and specialize to concrete coordinate models only
  through downstream bridge instances.
- Layer target: `source-facing`, as a thin predicate on the owner set `s` with ambient supported
  set `C` and atomic companion lemmas, not as a typeclass wrapper.
-/

/-- Text 11.3.1, stated coordinate-free: a set `s` is a supporting half-space to `C` when `s` is
a closed half-space, contains `C`, and has a point of `C` on its boundary. -/
def IsSupportingHalfSpace {𝕜 : Type*} [LE 𝕜] [CommSemiring 𝕜]
    {X Y : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜] (s C : Set X) : Prop :=
  (closedHalfSpace[Y,𝕜] s) ∧ C ⊆ s ∧ (C ∩ frontier s).Nonempty

/-- Canonical notation for supporting half-spaces with pairing side `Y` over `𝕜`. -/
scoped[Rockafellar] notation:50 s " supports[" Y "," 𝕜 "] " C =>
  Set.IsSupportingHalfSpace (Y := Y) (𝕜 := 𝕜) s C

section

variable {X Y 𝕜 : Type*}
variable [LE 𝕜] [CommSemiring 𝕜]
variable [TopologicalSpace X]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
open scoped Rockafellar

variable {C s : Set X}

local notation:50 s " supports " C =>
  s supports[Y,𝕜] C

/-- A supporting half-space is a closed half-space. -/
theorem IsSupportingHalfSpace.isClosedHalfSpace (hs : s supports C) :
    IsClosedHalfSpace Y 𝕜 s :=
  hs.1

/-- The supported set lies in every supporting half-space to it. -/
theorem IsSupportingHalfSpace.subset (hs : s supports C) :
    C ⊆ s :=
  hs.2.1

/-- A supporting half-space has a point of the supported set on its boundary. -/
theorem IsSupportingHalfSpace.exists_mem_frontier (hs : s supports C) :
    ∃ x ∈ C, x ∈ frontier s := by
  rcases hs.2.2 with ⟨x, hxC, hxs⟩
  exact ⟨x, hxC, hxs⟩

/-- A supporting half-space meets the supported set on its boundary. -/
theorem IsSupportingHalfSpace.inter_frontier_nonempty
    (hs : s supports C) : (C ∩ frontier s).Nonempty :=
  hs.2.2

end

end Set

/-! ### Text_11_3_2 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]

/-
Source/core/bridge triage:
- `source-facing`: Text 11.3.2 defines what it means for a hyperplane to support a set `C`.
- `core/canonical`: the owner layer uses `AffineSubspace` and `AffineSubspace.affineHyperplane`
  for hyperplanes and the supporting-half-space owner `s supports C`.
- `bridge/view`: the textbook's first sentence is the source-facing owner definition; the concrete
  closed-half-space presentation is a theorem-level bridge in normed ordered scalar settings.
- Primitive data vs derived API: the primitive owner input is the affine subspace `H`; being a
  supporting hyperplane is a derived `Prop` on `H` and `C`, obtained from one supporting half-space.
- Topology-language choice: this owner keeps the ambient boundary operator `frontier` on purpose.
  The supported object is an ambient half-space `s : Set V`, so boundary contact is ambient by
  construction; intrinsic/relative restatements are theorem-level views downstream.
-/

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C : Set V}

/-- Text 11.3.2: an affine subspace `H` is a supporting hyperplane to `C` when its underlying set
is the boundary of some supporting half-space to `C`. -/
def IsSupportingHyperplane (Y : Type*) [AddCommMonoid Y] [Module 𝕜 Y]
    [HasLinearPairing V Y 𝕜] (H : AffineSubspace 𝕜 V) (C : Set V) : Prop :=
  ∃ s : Set V, (s supports[Y,𝕜] C) ∧ frontier s = H

/-- Textbook-facing notation for "supporting hyperplane". -/
scoped[Rockafellar] notation:50 H " supportsHyperplane[" Y "] " C =>
  AffineSubspace.IsSupportingHyperplane Y H C

end AffineSubspace

end

section

open scoped Rockafellar
open Set

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 E} {C : Set E}
local notation:50 s " supports " C =>
  s supports[Y,𝕜] C

private theorem frontier_closedHalfSpaceLE_eq_affineHyperplane
    {b : Y} {β : 𝕜}
    (hb : (HasLinearPairing.pairingLinear.flip b : E →ₗ[𝕜] 𝕜) ≠ 0) :
    frontier (closedHalfSpaceLE b β : Set E) =
      ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
  let f : E →ₗ[𝕜] 𝕜 := HasLinearPairing.pairingLinear.flip b
  let fCL : E →L[𝕜] 𝕜 := ⟨f, by
    simpa [f] using
      (HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) b)⟩
  have hcont : Continuous f := by
    simpa [f] using
      (HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) b)
  have hfCL : fCL ≠ 0 := by
    intro h0
    apply hb
    ext x
    exact congrArg (fun g : E →L[𝕜] 𝕜 => g x) h0
  have hopen : IsOpenMap f := by
    simpa [f, fCL] using (fCL.isOpenMap_of_ne_zero hfCL)
  have hpre : (closedHalfSpaceLE b β : Set E) = f ⁻¹' Set.Iic β := by
    ext x
    simp [f, closedHalfSpaceLE]
  calc
    frontier (closedHalfSpaceLE b β : Set E)
        = frontier (f ⁻¹' Set.Iic β) := by simp [hpre]
    _ = f ⁻¹' frontier (Set.Iic β : Set 𝕜) :=
      (hopen.preimage_frontier_eq_frontier_preimage hcont _).symm
    _ = f ⁻¹' ({β} : Set 𝕜) := by simp
    _ = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
      ext x
      simp [f, mem_affineHyperplane_iff]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasContinuousPairing E Y 𝕜] [OrderTopology 𝕜] in
private theorem closedHalfSpaceGE_eq_closedHalfSpaceLE_neg (b : Y) (β : 𝕜) :
    (closedHalfSpaceGE b β : Set E) = closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) := by
  ext x
  constructor
  · intro hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := mem_closedHalfSpaceGE_iff.mp hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : Y)⟫ₚ ≤ -β := by
      simpa using (neg_le_neg hx_ge)
    exact mem_closedHalfSpaceLE_iff.mpr hx_le
  · intro hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : Y)⟫ₚ ≤ -β :=
      mem_closedHalfSpaceLE_iff.mp hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := by
      exact neg_le_neg_iff.mp (by simpa using hx_le)
    exact mem_closedHalfSpaceGE_iff.mpr hx_ge

/-- A supporting hyperplane is exactly the affine hyperplane bounding some supporting closed
half-space for `C`, cut out by a nontrivial pairing functional. -/
theorem isSupportingHyperplane_iff :
    (H supportsHyperplane[Y] C) ↔
      ∃ b : Y, ∃ β : 𝕜, H = affineHyperplane b β ∧
        (HasLinearPairing.pairingLinear.flip b : E →ₗ[𝕜] 𝕜) ≠ 0 ∧
        (closedHalfSpaceLE b β supports C) := by
  constructor
  · rintro ⟨s, hs, hfrontier⟩
    rcases hs.isClosedHalfSpace with ⟨b, β, hb, hle | hge⟩
    · rcases hle with rfl
      have hset : (H : Set E) = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
        calc
          (H : Set E) = frontier (closedHalfSpaceLE b β : Set E) := by
            simpa using hfrontier.symm
          _ = ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) :=
            frontier_closedHalfSpaceLE_eq_affineHyperplane hb
      have hH : H = affineHyperplane b β := by
        ext x
        simpa using congrArg (fun t : Set E => x ∈ t) hset
      exact ⟨b, β, hH, hb, by simpa using hs⟩
    · rcases hge with rfl
      have hbneg : (HasLinearPairing.pairingLinear.flip (((-1 : 𝕜) • b) : Y) : E →ₗ[𝕜] 𝕜) ≠ 0 := by
        simpa using hb
      have hfrontier' :
          frontier (closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) : Set E) = (H : Set E) := by
        simpa [closedHalfSpaceGE_eq_closedHalfSpaceLE_neg] using hfrontier
      have hset :
          (H : Set E) =
            ((affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) : AffineSubspace 𝕜 E) : Set E) := by
        calc
          (H : Set E) = frontier (closedHalfSpaceLE (((-1 : 𝕜) • b) : Y) (-β) : Set E) := by
            simpa using hfrontier'.symm
          _ = ((affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) : AffineSubspace 𝕜 E) : Set E) :=
            frontier_closedHalfSpaceLE_eq_affineHyperplane hbneg
      have hH : H = affineHyperplane (((-1 : 𝕜) • b) : Y) (-β) := by
        ext x
        simpa using congrArg (fun t : Set E => x ∈ t) hset
      refine ⟨(((-1 : 𝕜) • b) : Y), -β, hH, hbneg, ?_⟩
      simpa [closedHalfSpaceGE_eq_closedHalfSpaceLE_neg] using hs
  · rintro ⟨b, β, hH, hb, hs⟩
    refine ⟨closedHalfSpaceLE b β, hs, ?_⟩
    have hfrontier : frontier (closedHalfSpaceLE b β : Set E) =
        ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) :=
      frontier_closedHalfSpaceLE_eq_affineHyperplane hb
    simpa [hH] using hfrontier

/-- A supporting hyperplane comes with a nontrivial pairing normal in the Chapter 1 sense. -/
theorem IsSupportingHyperplane.hasNormal (h : H supportsHyperplane[Y] C) :
    ∃ b : Y, H.HasNormal b := by
  rcases isSupportingHyperplane_iff.mp h with ⟨b, β, hH, hb, _hs⟩
  exact ⟨b, ⟨β, hb, hH⟩⟩

/-- A supporting hyperplane is a hyperplane. -/
theorem IsSupportingHyperplane.is_hyperplane [FiniteDimensional 𝕜 E]
    (h : H supportsHyperplane[Y] C) :
    H.is_hyperplane := by
  rcases h.hasNormal with ⟨b, hb⟩
  exact hb.is_hyperplane

end AffineSubspace

end

/-! ### Text_11_3_3 (from Chap03) -/
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

/-! ### Theorem_11_3 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [IsTopologicalAddGroup V]
  [Module 𝕜 V] [ContinuousSMul 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]
variable {C1 C2 : Set V}

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 11.3 characterizes when two nonempty convex sets admit a proper
  separating hyperplane.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, the chapter relation
  `AffineSubspace.SeparatesProperly`, and the relative interior operator `intrinsicInterior 𝕜`.
- `bridge/view`: Rockafellar's `ri C₁` and `ri C₂` are represented by `ri[𝕜](C1)` and
  `ri[𝕜](C2)` as a thin notation bridge over `intrinsicInterior 𝕜`, while proper separation is
  represented at raw owner level by `AffineSubspace.SeparatesProperly Y H C1 C2`.
- Best owner abstraction: there is no exact upstream theorem with the target interface, so the
  public owner layer here remains the Chapter 11 relation `AffineSubspace.SeparatesProperly`
  together with the canonical owner `intrinsicInterior 𝕜`; the `ri[𝕜](·)` surface is a
  source-facing bridge theorem, not the primitive owner statement.
- Primitive data vs derived API: the primitive inputs are the two sets together with convexity
  and nonemptiness. The proper-separation criterion and the relative-interior disjointness
  condition are theorem-level content.
- Domain-style sampling used here: the Chapter 11 owner predicate
  `AffineSubspace.SeparatesProperly` from `Text_11_0_2`, the separation theorem
  `exists_separating_hyperplane_containing_of_disjoint_relativelyOpen_convex` from
  `Theorem_11_2`, the owner-side Minkowski-sum relative-interior formula
  `Convex.intrinsicInterior_add` from `Corollary_6_6_2`, and the relative-interior inclusion
  theorem from `Corollary_6_5_2`.
- Layer target: `source-facing`, with the theorem stated directly in the existing Chapter 11
  owner relation and the canonical intrinsic-interior API, rather than through a new separation
  wrapper.
- Ambient refinement: although Rockafellar states the theorem in coordinate form, the owner
  abstractions for proper separation and relative interior already live on finite-dimensional
  topological pairing modules, so the public statement is kept at that canonical ambient level
  rather than a concrete coordinate model.
-/

/-- Theorem 11.3 at the primitive owner layer: for nonempty convex sets `C1` and `C2` in a
finite-dimensional topological pairing module over `𝕜`, there exists a hyperplane separating `C1`
and `C2` properly if and only if their intrinsic interiors are disjoint. -/
-- Proof sketch: apply Theorem 11.2 to the pointwise difference set `C1 - C2` and the affine set
-- `{0}`. Rewriting `C1 - C2` as `C1 + (-C2)` and using Corollary 6.6.2 identifies its relative
-- interior with `ri[𝕜](C1) + (-ri[𝕜](C2))`, so the origin lies outside that relative interior
-- exactly when `ri[𝕜](C1)` and `ri[𝕜](C2)` are disjoint. The resulting separating hyperplane for
-- `C1 - C2` is equivalent to a proper separating hyperplane for `C1` and `C2`, and the converse
-- uses Corollary 6.5.2 to push the relative interior of `C1 - C2` into the open half-space
-- determined by the separator.
theorem exists_separatesProperly_iff_disjoint_intrinsicInterior
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 V, AffineSubspace.SeparatesProperly Y H C1 C2) ↔
      Disjoint (intrinsicInterior 𝕜 C1) (intrinsicInterior 𝕜 C2) := sorry

/-- Source-facing `ri` bridge form of Theorem 11.3. -/
theorem exists_separatesProperly_iff_disjoint_ri
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 V, AffineSubspace.SeparatesProperly Y H C1 C2) ↔
      Disjoint (ri[𝕜](C1)) (ri[𝕜](C2)) := by
  simpa using exists_separatesProperly_iff_disjoint_intrinsicInterior
    (Y := Y) hC1_conv hC1_nonempty hC2_conv hC2_nonempty

end

/-! ### Text_11_3_4 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} {V : Type*}
variable [CommRing 𝕜] [LE 𝕜]
variable [TopologicalSpace V]
variable [AddCommGroup V] [Module 𝕜 V]
variable (Y : Type*)
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C : Set V}

/-- Text 11.3.4: a non-trivial supporting hyperplane to `C` is a supporting hyperplane to `C`
that does not contain `C` itself. -/
def IsNontrivialSupportingHyperplane (H : AffineSubspace 𝕜 V) (C : Set V) : Prop :=
  H.IsSupportingHyperplane Y C ∧ ¬ C ⊆ H

/-- A non-trivial supporting hyperplane is, in particular, a supporting hyperplane. -/
-- Proof sketch: this is the first conjunct in the definition of
-- `IsNontrivialSupportingHyperplane`.
theorem IsNontrivialSupportingHyperplane.isSupportingHyperplane
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    H.IsSupportingHyperplane Y C :=
  h.1

/-- A non-trivial supporting hyperplane does not contain the set it supports. -/
-- Proof sketch: this is the second conjunct in the definition of
-- `IsNontrivialSupportingHyperplane`.
theorem IsNontrivialSupportingHyperplane.not_subset
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    ¬ C ⊆ H :=
  h.2

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 E} {C : Set E}

/-- A non-trivial supporting hyperplane is a hyperplane. -/
theorem IsNontrivialSupportingHyperplane.is_hyperplane [FiniteDimensional 𝕜 E]
    (h : H.IsNontrivialSupportingHyperplane Y C) :
    H.is_hyperplane :=
  h.isSupportingHyperplane.is_hyperplane

/-- A non-trivial supporting hyperplane through `x` yields a nonzero pairing normal `b` such that
the pairing functional `z ↦ ⟪z, b⟫ₚ` attains its maximum over `C` at `x` and is not constant on
`C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonzero_pairing_maximizing
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hx : x ∈ H) :
    ∃ b : Y, b ≠ 0 ∧ IsMaxOn (fun z : E ↦ (⟪z, b⟫ₚ : 𝕜)) C x ∧
      ∃ y ∈ C, (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
  rcases isSupportingHyperplane_iff.mp h.isSupportingHyperplane with
      ⟨b, β, hH, hbflip, hs⟩
  have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero
    hbflip
  refine ⟨b, hb0, ?_⟩
  constructor
  · refine isMaxOn_iff.2 ?_
    intro y hy
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp <| hs.subset hy
    have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
      rw [hH] at hx
      exact mem_affineHyperplane_iff.mp hx
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_le
  · rcases Set.not_subset.mp h.not_subset with ⟨y, hyC, hy_notH⟩
    refine ⟨y, hyC, ?_⟩
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp <| hs.subset hyC
    have hy_not_aff : y ∉ ((affineHyperplane b β : AffineSubspace 𝕜 E) : Set E) := by
      simpa [hH] using hy_notH
    have hy_ne : (⟪y, b⟫ₚ : 𝕜) ≠ β := by
      intro hy_eq
      apply hy_not_aff
      exact mem_affineHyperplane_iff.mpr hy_eq
    have hy_lt_beta : (⟪y, b⟫ₚ : 𝕜) < β := lt_of_le_of_ne hy_le hy_ne
    have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
      rw [hH] at hx
      exact mem_affineHyperplane_iff.mp hx
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_lt_beta

/-- A non-trivial supporting hyperplane through `x` yields a linear functional that attains its
maximum over `C` at `x` and is not constant on `C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonconstant_linearMap_maximizing
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hx : x ∈ H) :
    ∃ f : E →ₗ[𝕜] 𝕜, IsMaxOn f C x ∧ ∃ y ∈ C, f y < f x := by
  rcases h.exists_nonzero_pairing_maximizing hx with ⟨b, _hb0, hmax, y, hyC, hy_lt⟩
  refine ⟨HasLinearPairing.pairingLinear.flip b, ?_⟩
  constructor
  · simpa [HasLinearPairing.pairing_eq_pairingLinear] using hmax
  · exact ⟨y, hyC, by simpa [HasLinearPairing.pairing_eq_pairingLinear] using hy_lt⟩

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 E} {C : Set E}

/-- A non-trivial supporting hyperplane through `x` yields a nonzero normal vector to `C` at `x`,
with strict inequality at some point of `C`. -/
theorem IsNontrivialSupportingHyperplane.exists_nonzero_normal_pairing_lt
    {x : E} (h : H.IsNontrivialSupportingHyperplane Y C) (hxC : x ∈ C) (hxH : x ∈ H) :
    ∃ b : Y, b ≠ 0 ∧ b ∈ N[𝕜](x | C) ∧
      ∃ y ∈ C, (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
  rcases isSupportingHyperplane_iff.mp h.isSupportingHyperplane with
      ⟨b, β, hH, hbflip, hs⟩
  have hb0 : b ≠ 0 := Set.ne_zero_of_pairingLinear_flip_ne_zero
    hbflip
  have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
    rw [hH] at hxH
    exact mem_affineHyperplane_iff.mp hxH
  have hnormal : b ∈ N[𝕜](x | C) := by
    rw [mem_normalCone_iff]
    refine ⟨hxC, ?_⟩
    intro y hy
    have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hs.subset hy)
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    have hyx : (⟪y, b⟫ₚ : 𝕜) ≤ ⟪x, b⟫ₚ := by
      simpa [hx_eq'] using hy_le
    have hsub_nonneg : (0 : 𝕜) ≤ (⟪x, b⟫ₚ : 𝕜) - ⟪y, b⟫ₚ := sub_nonneg.mpr hyx
    simpa [sub_eq_add_neg, map_add, map_neg, add_assoc, add_left_comm, add_comm] using
      hsub_nonneg
  rcases Set.not_subset.mp h.not_subset with ⟨y, hyC, hy_notH⟩
  have hy_le : (⟪y, b⟫ₚ : 𝕜) ≤ β := mem_closedHalfSpaceLE_iff.mp (hs.subset hyC)
  have hy_ne : (⟪y, b⟫ₚ : 𝕜) ≠ β := by
    intro hy_eq
    apply hy_notH
    simpa [hH] using mem_affineHyperplane_iff.mpr hy_eq
  have hy_lt : (⟪y, b⟫ₚ : 𝕜) < ⟪x, b⟫ₚ := by
    have hy_lt_beta : (⟪y, b⟫ₚ : 𝕜) < β := lt_of_le_of_ne hy_le hy_ne
    have hx_eq' : β = (⟪x, b⟫ₚ : 𝕜) := hx_eq.symm
    simpa [hx_eq'] using hy_lt_beta
  exact ⟨b, hb0, hnormal, y, hyC, hy_lt⟩
end AffineSubspace

end
