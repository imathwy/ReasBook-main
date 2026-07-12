import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.DecompositionComparison

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
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
/-- Corollary 18-18.2-4 (core/canonical form): an element of `R_K(G)` lies in the kernel of the
decomposition homomorphism exactly when the descended Brauer character of its reduction is zero on
`PRegularConjClass G p`, for an injective lift of the prime-to-`p` roots. -/
theorem mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) = 0 :=
by
  have hφinj :
      Function.Injective
        (virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift) :
          R₀[k](G) →+ (PRegularConjClass G p → K)) :=
    _root_.Representation.virtualModularCharacterOnPRegularConjClass_injective lift hlift
  rw [AddMonoidHom.mem_ker]
  change (decompositionHom A K G x = 0 ↔
    virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) x) =
      virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift) 0)
  simpa using (Function.Injective.eq_iff hφinj).symm

-- Proof sketch: choose an injective, reduction-compatible lift from the existence hypothesis,
-- apply the canonical owner statement at `PRegularConjClass.ofSubtype p s`, then rewrite through
-- `virtualModularCharacterOnPRegularConjClass_ofSubtype` and the Chapter `18.3` decomposition
-- comparison `virtualModularCharacter_decomposition_eq_character_restriction`.
/-- Corollary 18-18.2-4: the kernel of the decomposition homomorphism
`d : R_K(G) → R_k(G)` consists exactly of those elements whose ordinary virtual character
vanishes on the `p`-regular locus of `G`, provided there exists an injective lift of the
prime-to-`p` roots into `Kˣ` that is compatible with reduction modulo `𝔪_A` (the canonical
Brauer lift).  We work in the standard Chapter `18` ordinary-character regime
`[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, used to produce the primitive roots of unity of
order `orderOf s` needed by the source comparison. -/
theorem mem_decompositionHom_ker_iff_character_eq_zero_on_pRegular
    [CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hexists : ∃ lift : PrimeToPRoot p k →* Kˣ, Function.Injective lift ∧
      ∀ x : PrimeToPRoot p k, ∃ a : A,
        algebraMap A K a = ((lift x : Kˣ) : K) ∧
          IsLocalRing.residue A a = ((x : kˣ) : k))
    (x : R₀[K](G)) :
    x ∈ (decompositionHom A K G).ker ↔
      ∀ s : { g : G // IsPRegular p g },
        (finiteRepGrothendieckCharacter K G x : G → K) s.1 = 0 := by
  rcases hexists with ⟨lift, hlift, hred⟩
  -- Primitive roots of order `orderOf s` exist in the standard ordinary-character regime.
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  -- The Chapter `18.3` decomposition comparison: reducing an ordinary virtual character and then
  -- evaluating the Brauer character on the `p`-regular locus restricts the original character.
  have hcomp :
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) x) =
        (finiteRepGrothendieckCharacter K G x : G → K) ∘ Subtype.val :=
    virtualModularCharacter_decomposition_eq_character_restriction
      (p := p) (B := A) (K := K) (G := G) lift hred hω x
  constructor
  · intro hx s
    have hzero :
        virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) x) = 0 :=
      (mem_decompositionHom_ker_iff_virtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift x).1 hx
    have hval :=
      (virtualModularCharacterOnPRegularConjClass_ofSubtype
        (p := p) (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) x) s).symm.trans
        (congrFun hzero (PRegularConjClass.ofSubtype p s))
    -- `hval : virtualModularCharacter (toFieldLift lift) (d x) s = 0`; rewrite to the ordinary
    -- character restriction via the comparison.
    have := hval
    rw [show virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) x) s
        = ((finiteRepGrothendieckCharacter K G x : G → K) ∘ Subtype.val) s from
        congrFun hcomp s] at this
    simpa using this
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
    have hval :=
      virtualModularCharacterOnPRegularConjClass_ofSubtype
        (p := p) (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) x) ⟨s, hs⟩
    rw [show virtualModularCharacter (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) x)
          ⟨s, hs⟩
        = ((finiteRepGrothendieckCharacter K G x : G → K) ∘ Subtype.val) ⟨s, hs⟩ from
        congrFun hcomp ⟨s, hs⟩] at hval
    simp only [Function.comp_apply] at hval
    rw [← hsubtype, hval]
    exact hx ⟨s, hs⟩

end

end Representation
