import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.OpenImmersion

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall:
- `lean_leansearch` surfaced the canonical ring-level local-property framework
  `RingHom.PropertyIsLocal` together with `RingHom.Locally` and
  `RingHom.IsStandardOpenImmersion`;
- the open-immersion clause is therefore best stated on the canonical owner
  `RingHom.Locally RingHom.IsStandardOpenImmersion`, while the remaining clauses use thin
  source-faithful ring-hom predicates;
- these are the lightweight `Lemma 29.14.7` owners reused directly by `Lemma 29.14.8` and
  `Lemma 29.14.9`.
-/

universe u

namespace RingHom

variable {R A : Type u} [CommRing R] [CommRing A]

/-- A ring map induces an isomorphism on the local rings of the target at every prime. -/
def isIsoOnLocalRings (φ : R →+* A) : Prop :=
  ∀ (q : Ideal A) [q.IsPrime],
    Function.Bijective (Localization.localRingHom (q.comap φ) q φ rfl)

/-- A ring map has locally Noetherian target if its target ring is Noetherian. -/
def targetIsNoetherian (φ : R →+* A) : Prop :=
  IsNoetherianRing A

/-- Lemma 29.14.7 (1): the property that `R → A` induces an isomorphism
`R_{𝔭} → A_{𝔮}` for every prime `𝔮` of `A` is local. -/
theorem isIsoOnLocalRings_propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.isIsoOnLocalRings := sorry

/-- Lemma 29.14.7 (2): the open-immersion ring-map condition, expressed as being locally a
standard open immersion on the target, is local. -/
theorem openImmersion_propertyIsLocal :
    RingHom.PropertyIsLocal (RingHom.Locally RingHom.IsStandardOpenImmersion) := sorry

/-- Lemma 29.14.7 (5): the property that the target ring `A` is Noetherian is local. -/
theorem targetIsNoetherian_propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.targetIsNoetherian := sorry

end RingHom
