import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.RestrictionFamily
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryConjugation
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryDetection
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.IntegralRestrictionSplitting
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ElementaryCoherence
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.SubgroupLinearPairing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TopLocalPairing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CoatomDivisibility
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.KernelQuotientCharacters
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.CyclicQuotientPairings
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.QuotientPullbackPairings
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.QuotientPullbackDivisibility
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.StrictBranchResidual
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.MappedCoatomSlices
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.MappedCoatomReindexing
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.StrictKernelGrowth
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.ChosenCoatomFaithful
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.KernelQuotientRecursion
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.AmbientCoatomInduction

noncomputable section

universe v

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

/-- Helper for Remark 11-11.1-3: every subgroup of a finite group is finite. -/
local instance fintypeHelperLocalAmbientResidualFamily1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
theorem ambient_local_pairing_divisibility_package_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    (∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
      let KX : X := ⟨J.map H.1.subtype,
        (hXelem (J.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
      ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) ∧
      (∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        let XH : Finset (Subgroup H.1) := Finset.univ
        let ψH : (J : XH) → R(J.1) := fun J ↦
          Subgroup.characterRingTransport
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (x ⟨J.1.map H.1.subtype,
              (hXelem (J.1.map H.1.subtype)).2 <|
                isElementary_of_mulEquiv_local
                  (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
                  (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
      let K0 : XH := ⟨⊤, by simp [XH]⟩
      ∃ b : ℤ,
          ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H.1))) :
                (⊤ : Subgroup H.1) → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b)) := by
  classical
  -- The old theorem name is now just the interface wrapper used by later declarations.
  simpa using
    ambient_local_pairing_divisibility_package_strong_induction
      X hXelem s hs hn hx hdx H sH hsH

/-- Helper for Remark 11-11.1-3: project the top-local witness from the joint ambient package so
the coatom branch can consume it on a smaller ambient subgroup without rebuilding the induction.
-/
theorem top_local_pairing_divisible_of_defect_multiple_on_smaller_ambient
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (α : (⊤ : Subgroup H.1) →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let K0 : XH := ⟨⊤, by simp [XH]⟩
    ∃ b : ℤ,
      ⟪(α.toCharacterRing : (⊤ : Subgroup H.1) → ℂ),
          (((Representation.characterRingRestriction XH) (sH ψH) K0 : R((⊤ : Subgroup H.1))) :
            (⊤ : Subgroup H.1) → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  -- The joint package is the owner theorem; this is only the interface projection used later in
  -- the coatom branch.
  simpa using
    (ambient_local_pairing_divisibility_package_of_defect_multiple
      X hXelem s hs hn hx hdx H sH hsH).2 α

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
theorem proper_subgroup_pairing_int_divisible_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ) :
    let KX : X := ⟨J.map H.1.subtype,
      (hXelem (J.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
    ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c := by
  classical
  obtain ⟨sH, hsH⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions
      (G := H.1) (Finset.univ : Finset (Subgroup H.1))
      subgroup_restriction_detection_on_elementary_group
  -- Project the proper-subgroup component from the joint ambient package so the coatom recursion
  -- is owned in one place instead of being rebuilt here.
  simpa using
    (ambient_local_pairing_divisibility_package_of_defect_multiple
      X hXelem s hs hn hx hdx H sH hsH).1 J hJ α

/-- Helper for Remark 11-11.1-3: this is the proper-subgroup branch of the source proof. For a
proper subgroup `J < H`, the induced linear-character pairing against the top local image is an
`n`-multiple. -/
theorem proper_induced_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (K : XH) → R(K.1) := fun K ↦
      Subgroup.characterRingTransport
        (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨K.1.map H.1.subtype,
          (hXelem (K.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (K.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local K.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ,
        ⟪Ind[J](α.toRepresentation.character), (ξH : H.1 → ℂ)⟫ =
          algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: isolate the proper-subgroup branch as its own owner lemma before the
  -- coatom argument, exactly as in the source proof.
  dsimp
  obtain ⟨c, hc⟩ :=
    proper_subgroup_pairing_int_divisible_of_defect_multiple
      X hXelem s hs hn hx hdx H J hJ α
  -- Feed the isolated arithmetic premise into the already-proved transport-to-induced wrapper.
  exact
    proper_induced_pairing_divisible_of_transport_pairing_int_divisible
      X hXelem hdx H sH hsH J α ⟨c, hc⟩

/-- Helper for Remark 11-11.1-3: the coatom quotient step depends only on the already established
proper-subgroup arithmetic branch, so the later residual-family theorem can be a corollary rather
than a second owner of the quotient argument. -/
theorem coatom_quotient_pairing_divisible_package_of_proper_branch
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (hproper :
      ∀ (J : Subgroup H.1) (hJ : J < ⊤) (α : J →* ℂˣ),
        let KX : X := ⟨J.map H.1.subtype,
          (hXelem (J.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J ((hXelem H.1).1 H.2))⟩
        ∃ c : ℤ, linear_character_pairing_int H.1 J α (x KX) = n * c) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: the quotient argument belongs in one helper that consumes only the proper
  -- arithmetic branch. The ambient induction theorem and the residual-family theorem should both
  -- reuse this package instead of duplicating the prime-quotient analysis.
  simpa using
    coatom_quotient_pairing_divisible_package_core_of_proper_branch
      X hXelem s hs hn hx hdx H sH hsH hproper

/-- Helper for Remark 11-11.1-3: this packages the Chapter 10 coatom step for the top-subgroup
branch. It simultaneously controls the trivial line and the top generators
`Ind_⊤^H(α - 1)`. -/
theorem coatom_quotient_pairing_divisible_package_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    (∃ b₀ : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b₀)) ∧
      ∀ α : (⊤ : Subgroup H.1) →* ℂˣ,
        ∃ b : ℤ,
          ⟪((Subgroup.characterRingInduction (⊤ : Subgroup H.1)
                (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
              (ξH : H.1 → ℂ)⟫ =
            algebraMap ℤ ℂ (n * b) := by
  classical
  -- The residual-family theorem now only repackages the proper branch through the dedicated
  -- coatom helper; it no longer owns a second copy of the quotient argument.
  dsimp
  exact
    coatom_quotient_pairing_divisible_package_of_proper_branch
      X hXelem s hs hn hx hdx H sH hsH
      (fun J hJ α ↦
        (ambient_local_pairing_divisibility_package_of_defect_multiple
          X hXelem s hs hn hx hdx H sH hsH).1 J hJ α)

/-- Helper for Remark 11-11.1-3: isolate the trivial-character line before reassembling the full
elementary span `R'`. -/
theorem top_local_image_trivial_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: the old proof tried to consume the augmentation relation for
  -- `Ind[K](χ) - [H : K] · 1` directly. The source proof first isolates the trivial-character
  -- line via the Chapter 10 coatom quotient package before reassembling the whole span `R'`.
  dsimp
  exact
    (coatom_quotient_pairing_divisible_package_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH).1

/-- Helper for Remark 11-11.1-3: once the trivial-character line is controlled, every element of
that line pairs with the top local image by an `n`-multiple. -/
theorem pairing_divisible_of_mem_trivial_character_line_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1))
    (hη : η ∈ Submodule.span ℤ ({1} : Set (R(H.1)))) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  rcases Submodule.mem_span_singleton.mp hη with ⟨m, rfl⟩
  obtain ⟨b, hb⟩ :=
    top_local_image_trivial_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH
  refine ⟨m * b, ?_⟩
  -- Reduce the whole line to the previously isolated trivial-character case.
  calc
    ⟪(((m • (1 : R(H.1))) : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        (m : ℂ) * ⟪((1 : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ := by
          have hcoe : (((m • (1 : R(H.1))) : R(H.1)) : H.1 → ℂ) =
              (m : ℂ) • ((1 : R(H.1)) : H.1 → ℂ) := by
            ext h
            simp [zsmul_eq_mul]
          rw [hcoe]
          exact Representation.groupFunctionPairing_smul_left
            (a := (m : ℂ)) (φ := ((1 : R(H.1)) : H.1 → ℂ)) (ψ := (ξH : H.1 → ℂ))
    _ = (m : ℂ) * algebraMap ℤ ℂ (n * b) := by rw [hb]
    _ = algebraMap ℤ ℂ (n * (m * b)) := by
          simp [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Generator helper for
`pairing_divisible_of_mem_elementaryLinearCharacterAugmentationSpan_of_residual_family`: a single
induced augmentation generator pairs into an explicit `n`-multiple. -/
private theorem augmentation_generator_pairing_divisible_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (E : Subgroup H.1) (α : E →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    ∃ b : ℤ,
      ⟪((Subgroup.characterRingInduction E (α.toCharacterRing - 1) : R(H.1)) : H.1 → ℂ),
          ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  intro XH ψH
  by_cases hEtop : E = ⊤
  · subst hEtop
    -- The source top-subgroup generator branch is exactly the second output of the coatom
    -- package.
    exact
      (coatom_quotient_pairing_divisible_package_of_residual_family
        X hXelem s hs hn hx hdx H sH hsH).2 α
  · have hEproper : E < ⊤ := lt_of_le_of_ne le_top hEtop
    -- The source proper-subgroup generator branch is handled by combining the dedicated
    -- proper induced-pairing lemma at `α` and at the trivial character.
    obtain ⟨bα, hbα⟩ :=
      proper_induced_pairing_divisible_of_residual_family
        X hXelem s hs hn hx hdx H sH hsH E hEproper α
    obtain ⟨b1, hb1⟩ :=
      proper_induced_pairing_divisible_of_residual_family
        X hXelem s hs hn hx hdx H sH hsH E hEproper 1
    refine ⟨bα - b1, ?_⟩
    have hfunα :
        ((Subgroup.characterRingInduction E α.toCharacterRing : R(H.1)) : H.1 → ℂ) =
          Ind[E](α.toRepresentation.character) := by
      funext g
      rw [Subgroup.characterRingInduction_apply]
      all_goals congr 1
      all_goals funext e
      all_goals simp [MonoidHom.toCharacterRing_apply]
    have hfun1 :
        ((Subgroup.characterRingInduction E (1 : R(E)) : R(H.1)) : H.1 → ℂ) =
          Ind[E]((1 : E →* ℂˣ).toRepresentation.character) := by
      funext g
      rw [Subgroup.characterRingInduction_apply]
      all_goals congr 1
      all_goals funext e
      all_goals simp [MonoidHom.toCharacterRing_apply, Subgroup.toCharacterRing_one]
    let pairLeft : R(H.1) →ₗ[ℤ] ℂ :=
      { toFun := fun ζ ↦ ⟪(ζ : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫
        map_add' := by
          intro ζ θ
          simpa using
            Representation.groupFunctionPairing_add_left
              (ζ : H.1 → ℂ) (θ : H.1 → ℂ) (((sH ψH : R(H.1)) : H.1 → ℂ))
        map_smul' := by
          intro a ζ
          have hcoe : ((a • ζ : R(H.1)) : H.1 → ℂ) = (a : ℂ) • (ζ : H.1 → ℂ) := by
            ext h
            simp [zsmul_eq_mul]
          have h := Representation.groupFunctionPairing_smul_left
            (a := (a : ℂ)) (φ := (ζ : H.1 → ℂ))
            (ψ := (((sH ψH : R(H.1)) : H.1 → ℂ)))
          simp only [RingHom.id_apply]
          rw [hcoe, h, zsmul_eq_mul] }
    have h1 : pairLeft (Subgroup.characterRingInduction E α.toCharacterRing) =
        algebraMap ℤ ℂ (n * bα) := by
      show ⟪_, _⟫ = _
      rw [hfunα]
      exact hbα
    have h2 : pairLeft (Subgroup.characterRingInduction E (1 : R(E))) =
        algebraMap ℤ ℂ (n * b1) := by
      show ⟪_, _⟫ = _
      rw [hfun1]
      exact hb1
    have hgoal :
        pairLeft (Subgroup.characterRingInduction E (α.toCharacterRing - 1)) =
          algebraMap ℤ ℂ (n * (bα - b1)) := by
      rw [show Subgroup.characterRingInduction E (α.toCharacterRing - 1) =
          Subgroup.characterRingInduction E α.toCharacterRing -
            Subgroup.characterRingInduction E (1 : R(E)) from map_sub _ _ _]
      rw [map_sub, h1, h2, ← map_sub]
      congr 1
      ring
    exact hgoal

/-- Helper for Remark 11-11.1-3: the augmentation summand `R₀'` is the inner source-faithful
owner statement for the top local image divisibility argument. -/
theorem pairing_divisible_of_mem_elementaryLinearCharacterAugmentationSpan_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1)) (hη : η ∈ R₀'(H.1)) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  -- Route correction: this is the actual owner statement for the source proof. The outer theorem
  -- on `R'` should only reassemble `ℤ · 1` with `R₀'`, not rediscover the generator analysis.
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  rw [elementaryLinearCharacterAugmentationSpan] at hη
  induction hη using Submodule.span_induction with
  | mem ζ hζ =>
      rcases hζ with ⟨E, hEelem, α, rfl⟩
      -- Each generator is handled by the dedicated private branch lemma.
      exact
        augmentation_generator_pairing_divisible_local
          X hXelem s hs hn hx hdx H sH hsH E α
  | zero =>
      refine ⟨0, ?_⟩
      simp [Representation.groupFunctionPairingOverField]
  | add η₁ η₂ _ _ hη₁ hη₂ =>
      rcases hη₁ with ⟨b₁, hb₁⟩
      rcases hη₂ with ⟨b₂, hb₂⟩
      refine ⟨b₁ + b₂, ?_⟩
      -- Pairing is additive in the left variable, so the two divisibility witnesses add.
      calc
        ⟪((η₁ + η₂ : R(H.1)) : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            ⟪(η₁ : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ +
              ⟪(η₂ : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
                have hcoe : ((η₁ + η₂ : R(H.1)) : H.1 → ℂ) =
                    (η₁ : H.1 → ℂ) + (η₂ : H.1 → ℂ) := rfl
                rw [hcoe]
                exact
                  Representation.groupFunctionPairing_add_left
                    (η₁ : H.1 → ℂ) (η₂ : H.1 → ℂ)
                    (((sH ψH : R(H.1)) : H.1 → ℂ))
        _ = algebraMap ℤ ℂ (n * b₁) + algebraMap ℤ ℂ (n * b₂) := by
              rw [hb₁, hb₂]
              simp [eq_intCast]
        _ = algebraMap ℤ ℂ (n * (b₁ + b₂)) := by
              rw [← map_add (algebraMap ℤ ℂ) (n * b₁) (n * b₂)]
              congr 1
              ring
  | smul m η _ hη =>
      rcases hη with ⟨b, hb⟩
      refine ⟨m * b, ?_⟩
      -- Pairing is `ℤ`-linear in the left variable, so scalar multiples preserve divisibility.
      calc
        ⟪(((m • η : R(H.1)) : H.1 → ℂ)), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ =
            (m : ℂ) * ⟪(η : H.1 → ℂ), ((sH ψH : R(H.1)) : H.1 → ℂ)⟫ := by
              have hcoe : ((m • η : R(H.1)) : H.1 → ℂ) =
                  (m : ℂ) • (η : H.1 → ℂ) := by
                ext h
                simp [zsmul_eq_mul]
              rw [hcoe]
              exact Representation.groupFunctionPairing_smul_left
                (a := (m : ℂ)) (φ := (η : H.1 → ℂ))
                (ψ := (((sH ψH : R(H.1)) : H.1 → ℂ)))
        _ = (m : ℂ) * algebraMap ℤ ℂ (n * b) := by
              rw [hb]
              simp [eq_intCast]
        _ = algebraMap ℤ ℂ (n * (m * b)) := by
              simp [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Remark 11-11.1-3: the remaining source-faithful endgame is that the explicit local
image term coming from the chosen splitting has all of its linear pairings divisible by `n`. -/
theorem pairing_divisible_of_mem_elementaryLinearCharacterSpan_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (η : R(H.1)) (hη : η ∈ R'(H.1)) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let ξH : R(H.1) := sH ψH
    ∃ b : ℤ, ⟪(η : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ = algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  rw [elementaryLinearCharacterSpan] at hη
  rcases Submodule.mem_sup.mp hη with ⟨η₁, hη₁, η₀, hη₀, rfl⟩
  obtain ⟨b₁, hb₁⟩ :=
    pairing_divisible_of_mem_trivial_character_line_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH η₁ hη₁
  obtain ⟨b₀, hb₀⟩ :=
    pairing_divisible_of_mem_elementaryLinearCharacterAugmentationSpan_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH η₀ hη₀
  refine ⟨b₁ + b₀, ?_⟩
  -- Reassemble the outer decomposition `R' = ℤ · 1 ⊔ R₀'` additively at the pairing level.
  calc
    ⟪((η₁ + η₀ : R(H.1)) : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ =
        ⟪(η₁ : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ +
          ⟪(η₀ : H.1 → ℂ), (ξH : H.1 → ℂ)⟫ := by
            exact
              Representation.groupFunctionPairing_add_left
                (η₁ : H.1 → ℂ) (η₀ : H.1 → ℂ) (ξH : H.1 → ℂ)
    _ = algebraMap ℤ ℂ (n * b₁) + algebraMap ℤ ℂ (n * b₀) := by rw [hb₁, hb₀]
    _ = algebraMap ℤ ℂ (n * (b₁ + b₀)) := by
          rw [← map_add (algebraMap ℤ ℂ) (n * b₁) (n * b₀)]
          congr 1
          ring

/-- Helper for Remark 11-11.1-3: the remaining source-faithful endgame is that the explicit local
image term coming from the chosen splitting has all of its linear pairings divisible by `n`. -/
theorem top_local_image_pairing_divisible_of_residual_family
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let K0 : XH := ⟨K, by simp [XH]⟩
    ∃ b : ℤ,
      ⟪(χ.toCharacterRing : K → ℂ),
          (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ =
        algebraMap ℤ ℂ (n * b) := by
  classical
  dsimp
  let ψH : (J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  let ξH : R(H.1) := sH ψH
  have hpair_as_induced :
      ⟪(χ.toCharacterRing : K → ℂ),
          (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))) ξH
              ⟨K, by simp⟩ : R(K)) : K → ℂ)⟫ =
        ⟪Ind[K](χ.toRepresentation.character), (ξH : H.1 → ℂ)⟫ := by
    -- Package the restriction-to-induced conversion once so the remaining blocker is purely the
    -- source-proof divisibility step on the induced pairing.
    simpa [ξH] using
      (top_local_coordinate_pairing_eq_induced_pairing
        (sH := sH) (ψH := ψH) (K := K) (χ := χ))
  have hHelem : IsElementary H.1 := (hXelem H.1).1 H.2
  have hη :
      Subgroup.characterRingInduction K χ.toCharacterRing ∈ R'(H.1) :=
    induced_linearCharacter_mem_elementaryLinearCharacterSpan_of_subgroup_of_isElementary_local
      K χ hHelem
  obtain ⟨b, hb⟩ :=
    pairing_divisible_of_mem_elementaryLinearCharacterSpan_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH
      (Subgroup.characterRingInduction K χ.toCharacterRing) hη
  refine ⟨b, ?_⟩
  calc
    ⟪(χ.toCharacterRing : K → ℂ),
        (((Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))) ξH
            ⟨K, by simp⟩ : R(K)) : K → ℂ)⟫ =
      ⟪Ind[K](χ.toRepresentation.character), (ξH : H.1 → ℂ)⟫ := hpair_as_induced
    _ = ⟪(((Subgroup.characterRingInduction K χ.toCharacterRing : R(H.1)) : H.1 → ℂ)),
          (ξH : H.1 → ℂ)⟫ := by
          -- The bundled induced character-ring element evaluates to the same induced character.
          simp [Subgroup.characterRingInduction_apply]
    _ = algebraMap ℤ ℂ (n * b) := hb

/-- Algebra helper for `residual_subgroup_pairing_int_divisible_of_defect_multiple`: rearrange the
residual-projector identity into the image-minus-family form. -/
private theorem image_residual_of_residual_projector_local
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (fH : M →ₗ[ℤ] N) (sH : N →ₗ[ℤ] M) (ψ δ : N) {n : ℤ}
    (h : ((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) ψ =
      (-n) • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ)) :
    fH (sH ψ) - ψ = n • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ) := by
  have h' : ψ - fH (sH ψ) = (-n) • (((LinearMap.id : N →ₗ[ℤ] N) - fH.comp sH) δ) := by
    simpa [LinearMap.sub_apply, LinearMap.comp_apply] using h
  have hneg := congrArg Neg.neg h'
  simpa [neg_sub, neg_smul, neg_neg] using hneg

/-- Decomposition stage for `residual_subgroup_pairing_int_divisible_of_defect_multiple`: the
transported local family pairing decomposes into the local-image pairing plus an explicit
`n`-multiple. -/
private theorem residual_coordinate_pairing_decomposition_local
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X)
    (sH : ((J : (Finset.univ : Finset (Subgroup H.1))) → R(J.1)) →ₗ[ℤ] R(H.1))
    (hsH : Function.LeftInverse sH
      (Representation.characterRingRestriction (Finset.univ : Finset (Subgroup H.1))).toLinearMap)
    (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let XH : Finset (Subgroup H.1) := Finset.univ
    let ψH : (J : XH) → R(J.1) := fun J ↦
      Subgroup.characterRingTransport
        (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (x ⟨J.1.map H.1.subtype,
          (hXelem (J.1.map H.1.subtype)).2 <|
            isElementary_of_mulEquiv_local
              (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
              (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
    let K0 : XH := ⟨K, by simp [XH]⟩
    ∃ m : ℤ,
      ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
  classical
  intro XH ψH K0
  let δH : (J : XH) → R(J.1) := fun J ↦
    let JX : X := ⟨J.1.map H.1.subtype,
      (hXelem (J.1.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩
    let pJ : elementary_restriction_relation X := ⟨(H, JX), subgroup_chain_map_le_local H.1 J.1⟩
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (t.1 pJ)
  have htransported :
      ((Representation.characterRingRestriction XH).toLinearMap (x H)) - ψH = n • δH :=
    transported_subgroup_family_defect_eq_zsmul X hXelem hdx H
  let fH : R(H.1) →ₗ[ℤ] ((J : XH) → R(J.1)) :=
    (Representation.characterRingRestriction XH).toLinearMap
  let rH : ((J : XH) → R(J.1)) →ₗ[ℤ] ((J : XH) → R(J.1)) := LinearMap.id - fH.comp sH
  have hresidual : rH ψH = (-n) • rH δH :=
    local_residual_projector_eq_neg_zsmul XH sH hsH htransported
  have himage_residual : fH (sH ψH) - ψH = n • rH δH :=
    image_residual_of_residual_projector_local fH sH ψH δH hresidual
  exact
    local_residual_pairing_decomposition_of_defect_multiple XH sH hsH himage_residual K0 χ

/-- Helper for Remark 11-11.1-3: the remaining arithmetic step is to show that the residual
`K`-coordinate pairing extracted from the defect identity is divisible by `n` in `ℤ`. -/
theorem residual_subgroup_pairing_int_divisible_of_defect_multiple
    (X : Finset (Subgroup G))
    (hXelem : ∀ H : Subgroup G, H ∈ X ↔ IsElementary H)
    (s : ((H : X) → R(H.1)) →ₗ[ℤ] R(G))
    (hs : Function.LeftInverse s (Representation.characterRingRestriction X).toLinearMap)
    {x : (H : X) → R(H.1)} {t : elementary_coherence_target X hXelem} {n : ℤ}
    (hn : n ≠ 0) (hx : s x = 0)
    (hdx : elementary_coherence_defect X hXelem x = n • t)
    (H : X) (K : Subgroup H.1) (χ : K →* ℂˣ) :
    let KX : X := ⟨K.map H.1.subtype,
      (hXelem (K.map H.1.subtype)).2 <|
        isElementary_of_mulEquiv_local
          (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
          (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
    ∃ m : ℤ, linear_character_pairing_int H.1 K χ (x KX) = n * m := by
  classical
  let KX : X := ⟨K.map H.1.subtype,
    (hXelem (K.map H.1.subtype)).2 <|
      isElementary_of_mulEquiv_local
        (K.equivMapOfInjective H.1.subtype H.1.subtype_injective)
        (subgroup_isElementary_of_isElementary_local K ((hXelem H.1).1 H.2))⟩
  let XH : Finset (Subgroup H.1) := Finset.univ
  let ψH : (J : XH) → R(J.1) := fun J ↦
    Subgroup.characterRingTransport
      (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
      (x ⟨J.1.map H.1.subtype,
        (hXelem (J.1.map H.1.subtype)).2 <|
          isElementary_of_mulEquiv_local
            (J.1.equivMapOfInjective H.1.subtype H.1.subtype_injective)
            (subgroup_isElementary_of_isElementary_local J.1 ((hXelem H.1).1 H.2))⟩)
  obtain ⟨sH, hsH⟩ :=
    characterRingRestriction_has_leftInverse_of_detection_by_restrictions
      (G := H.1) XH subgroup_restriction_detection_on_elementary_group
  let K0 : XH := ⟨K, by simp [XH]⟩
  -- The transported-defect decomposition now lives in a dedicated private stage lemma.
  obtain ⟨m, hdecomp₀⟩ :=
    residual_coordinate_pairing_decomposition_local X hXelem hdx H sH hsH K χ
  -- Re-package the decomposition in terms of the local `let`-bound family.
  have hdecomp :
      ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := hdecomp₀
  have hpair_x :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ), (ψH K0 : K → ℂ)⟫ := by
    -- The transported `K`-coordinate of `ψH` is exactly the ambient `KX`-coordinate of `x`.
    simpa [KX, K0, ψH] using
      (subgroup_linear_character_pairing_int_transport_eq H.1 K χ (x KX)).symm
  have hpair_decomp :
      algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := by
    rw [hpair_x]
    exact hdecomp
  obtain ⟨b, hb⟩ :=
    top_local_image_pairing_divisible_of_residual_family
      X hXelem s hs hn hx hdx H sH hsH K χ
  refine ⟨b + m, ?_⟩
  apply Int.cast_injective (α := ℂ)
  -- Combine the explicit local-image divisibility with the residual decomposition.
  calc
    algebraMap ℤ ℂ (linear_character_pairing_int H.1 K χ (x KX)) =
        ⟪(χ.toCharacterRing : K → ℂ),
            (((Representation.characterRingRestriction XH) (sH ψH) K0 : R(K)) : K → ℂ)⟫ +
          algebraMap ℤ ℂ (n * m) := hpair_decomp
    _ = algebraMap ℤ ℂ (n * b) + algebraMap ℤ ℂ (n * m) := by rw [hb]
    _ = algebraMap ℤ ℂ ((n * b) + (n * m)) := by simp [Int.cast_add]
    _ = algebraMap ℤ ℂ (n * (b + m)) := by ring



end CharacterizationOfCharacters

end Representation
