import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Domain-style sampling:
- primary domain: formally étale and étale commutative ring homomorphisms;
- sampled owner API:
  `RingHom.FormallyEtale`,
  `RingHom.Etale`,
  `Algebra.FormallyEtale`,
  `Algebra.Etale.of_formallyUnramified_of_flat`;
- source-facing: the finite-presentation criterion identifying formal étaleness with étaleness for
  a ring map;
- core/canonical: the owner predicates `RingHom.FormallyEtale` and `RingHom.Etale`, viewed through
  the canonical algebra owners `Algebra.FormallyEtale` and `Algebra.Etale`;
- bridge/view: the induced `R`-algebra structure `f.toAlgebra`.

Primitive data are only the ring map `f` and the finite-presentation hypothesis. Flatness,
formal smoothness, and formal unramifiedness are derived owner-level consequences, so this file
should prove the source-facing criterion directly from the canonical owners instead of introducing
parallel local wrappers.
-/

-- Proof sketch: for a ring map `f : R →+* S`, algebraize the statement. If `f` is formally étale
-- and finitely presented, then it is formally smooth and hence smooth by finite presentation, while
-- formal étaleness also gives formal unramifiedness; thus `f` is étale. Conversely, an étale map is
-- formally étale by the defining typeclass field of `Algebra.Etale`.
/-- Lemma 10.150.3: a finitely presented ring map is formally étale if and only if it is étale. -/
theorem formallyEtale_iff_etale (f : R →+* S) (hf : f.FinitePresentation) :
    f.FormallyEtale ↔ f.Etale := by
  letI := f.toAlgebra
  change Algebra.FormallyEtale R S ↔ Algebra.Etale R S
  change Algebra.FinitePresentation R S at hf
  constructor
  · intro h
    letI : Algebra.FormallyEtale R S := h
    letI : Algebra.FinitePresentation R S := hf
    letI : Algebra.Smooth R S := ⟨inferInstance, inferInstance⟩
    exact Algebra.Etale.of_formallyUnramified_of_flat
  · intro h
    letI : Algebra.Etale R S := h
    exact inferInstance

end RingHom
