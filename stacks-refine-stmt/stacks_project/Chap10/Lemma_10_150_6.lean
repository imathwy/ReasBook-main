import stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S) (J : Ideal S)
variable (hf : f.FormallyEtale)
variable (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp f))

/-
Domain-style sampling:
- primary domain: formally étale maps and their effect on nilpotent thickenings and associated
  graded rings;
- sampled owner API:
  `RingHom.FormallyEtale`,
  `Ideal.quotientMap`,
  `idealAssociatedGradedRing`,
  `idealAssociatedGradedRingGrade`,
  `idealAssociatedGradedMap`;
- source-facing: the bijectivity of the induced maps on `R / (comap f J)^n` and on the associated
  graded ring of the `J`-adic filtration, expressed degreewise on the homogeneous pieces;
- core/canonical: formal étaleness is owned by `RingHom.FormallyEtale`, and the associated graded
  ring and its induced comparison maps are owned by `idealAssociatedGradedRing` and
  `idealAssociatedGradedMap`, with `idealAssociatedGradedRingGrade` exposing the owner grading;
- bridge/view: the canonical quotient-thickening maps `R / (comap f J)^n → S / J^n` and the
  induced owner-level degree maps
  `idealAssociatedGradedGradeMap (Ideal.comap f J) J f le_rfl n`.

Primitive data are the ring map `f`, the ideal `J`, and the canonical owner objects
`idealAssociatedGradedRing (Ideal.comap f J)` and `idealAssociatedGradedRing J`, together with the
owner-level comparison map `idealAssociatedGradedMap f le_rfl`.
The quotient-Rees presentation is implementation-level behind that owner abstraction. The
degree-`n` comparison on the associated graded ring is derived API obtained by restricting that
owner map to `idealAssociatedGradedRingGrade` via `idealAssociatedGradedGradeMap`.
-/

local notation "Icomap" => Ideal.comap f J

-- Proof sketch: first identify `R / comap f J ≃ S / J` from the surjectivity of `R → S / J`.
-- Then use the unique lifting property of formal étaleness inductively to produce inverse maps
-- between the higher nilpotent thickenings `R / (comap f J)^n` and `S / J^n`.
/-- Lemma 10.150.6 (1): if `R → S / J` is surjective and `f : R →+* S` is formally étale, then
the induced map `R / (comap f J)^n → S / J^n` is bijective for every `n`. -/
theorem formallyEtale_quotientMap_pow_bijective (n : ℕ) :
    Function.Bijective
      ((Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) :
        R ⧸ (Icomap ^ n) →+* S ⧸ (J ^ n)) := sorry

-- Proof sketch: apply quotient-thickening bijectivity to the successive quotients defining the
-- associated graded ring to obtain bijectivity of the owner map `idealAssociatedGradedMap f
-- le_rfl`. The degreewise homogeneous-piece statement is then the derived restriction of this
-- owner-level comparison along `idealAssociatedGradedRingGrade`.

/-- Lemma 10.150.6 (2): under the same hypotheses, the induced map on associated graded rings
`gr_(comap f J)(R) → gr_J(S)` is bijective. -/
theorem formallyEtale_associatedGradedMap_bijective :
    Function.Bijective
      ((idealAssociatedGradedMap f le_rfl) :
        idealAssociatedGradedRing Icomap →+* idealAssociatedGradedRing J) := sorry

/-- Companion: the bijective associated graded ring map restricts to a bijection on each
degree-`n` homogeneous piece. -/
theorem formallyEtale_associatedGradedGradeMap_bijective (n : ℕ) :
    Function.Bijective (idealAssociatedGradedGradeMap Icomap J f le_rfl n) := sorry

end RingHom
