import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for this item:
* `virtualModularCharacter` in Remark `18-18.1-3` is the source-facing Grothendieck-group owner
  for modular characters on the `p`-regular locus.
* `virtualModularCharacter_decomposition_eq_character_restriction` in Remark `18-18.1-3` is the
  canonical comparison between that owner and the ordinary virtual character upstairs.
* `virtualModularCharacterOnPRegularConjClass` and
  `bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass` in Theorem `18-18.2-2`
  provide the chapter's injectivity owner after passing to the canonical quotient
  `PRegularConjClass G p`.

Layer triage:
* source-facing: vanishing of the ordinary virtual character on the `p`-regular elements.
* core/canonical: vanishing of
  `virtualModularCharacterOnPRegularConjClass p lift ((decompositionHom A K G) x)` for an
  injective lift.
* bridge/view:
  `virtualModularCharacterOnPRegularConjClass_ofSubtype` and
  `virtualModularCharacter_decomposition_eq_character_restriction`.
-/

-- Proof sketch: pass from the subtype `{ g : G // IsPRegular p g }` to the canonical owner
-- `PRegularConjClass G p`, then apply the injectivity result from Theorem `18-18.2-2` to the
-- descended Brauer-character owner.
omit [CharZero K] [Fact p.Prime] in
/-- Corollary 18-18.2-4 (core/canonical form): an element of `R_K(G)` lies in the kernel of the
decomposition homomorphism exactly when the descended Brauer character of its reduction is zero on
`PRegularConjClass G p`, for an injective lift of the prime-to-`p` roots. -/
theorem mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) = 0 :=
by
  have hφinj :
      Function.Injective
        (virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift) :
          R₀[k](G) →+ (PRegularConjClass G p → K)) :=
    _root_.Representation.virtualModularCharacterOnPRegularConjClass_injective lift hlift
  rw [AddMonoidHom.mem_ker]
  change (decompositionHom A K G x = 0 ↔
    virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) =
      virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift) 0)
  simpa using (Function.Injective.eq_iff hφinj).symm

-- Proof sketch: choose an injective lift from the existence hypothesis, apply the canonical owner
-- statement at `PRegularConjClass.ofSubtype p s`, then rewrite through
-- `virtualModularCharacterOnPRegularConjClass_ofSubtype` and
-- `virtualModularCharacter_decomposition_eq_character_restriction`.
omit [CharZero K] [Fact p.Prime] in
/-- Corollary 18-18.2-4: the kernel of the decomposition homomorphism
`d : R_K(G) → R_k(G)` consists exactly of those elements whose ordinary virtual character
vanishes on the `p`-regular locus of `G`, provided there exists an injective lift of the
prime-to-`p` roots into `Kˣ`. -/
theorem mem_decompositionHom_ker_iff_character_eq_zero_on_pRegular
    (hexists : ∃ lift : PrimeToPRoot p k →* Kˣ, Function.Injective lift) (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      ∀ s : { g : G // IsPRegular p g },
        (finiteRepGrothendieckCharacter K G x : G → K) s.1 = 0 := by
  rcases hexists with ⟨lift, hlift⟩
  constructor
  · intro hx s
    have hzero :
        virtualModularCharacterOnPRegularConjClass p (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) x) = 0 :=
      (mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift x).1 hx
    simpa [virtualModularCharacterOnPRegularConjClass_ofSubtype,
      virtualModularCharacter_decomposition_eq_character_restriction] using
      congrFun hzero (PRegularConjClass.ofSubtype p s)
  · intro hx
    refine
      (mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift x).2 ?_
    ext c
    rcases c with ⟨c, hc⟩
    obtain ⟨s, rfl⟩ := ConjClasses.mk_surjective c
    have hs : IsPRegular p s := hc s <| by
      simp [ConjClasses.mem_carrier_iff_mk_eq]
    have hsubtype :
        PRegularConjClass.ofSubtype p ⟨s, hs⟩ =
          ⟨ConjClasses.mk s, hc⟩ := by
      apply Subtype.ext
      rfl
    simpa [virtualModularCharacterOnPRegularConjClass_ofSubtype,
      virtualModularCharacter_decomposition_eq_character_restriction, ← hsubtype] using
      hx ⟨s, hs⟩

end

end Representation
