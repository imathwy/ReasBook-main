import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S' : Type v} {S : Type w}
variable [CommRing R] [CommRing S'] [CommRing S]
variable [Algebra R S'] [Algebra S' S]
variable (q' : Ideal S') [q'.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver q']

/- Domain triage:
- primary domain: Kähler differentials, cotangent modules, and localizations at prime ideals;
- sampled owner API:
  `Localization.localRingHom`,
  the canonical `Localization.AtPrime` algebra instance for primes in a lying-over relation,
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.kerCotangentToTensor_toCotangent`;
- core/canonical owner: `KaehlerDifferential.kerCotangentToTensor` specialized to the localized map
  `S'_{𝔮'} → S_𝔮`;
- bridge/view: the textbook "localized conormal map" is this owner construction at the localized
  prime rings.

Primitive data are the existing localized `Algebra` structure and the owner conormal map. The
formula on classes in the kernel ideal is derived API, so no extra local wrapper is needed. -/

/- The canonical `S'_{𝔮'}`-algebra structure on `S_𝔮` is already the mathlib owner instance from
`Localization.AtPrime`. -/
#check (inferInstance : Algebra (Localization.AtPrime q') (Localization.AtPrime q))

/- 10.141.2.1: the localized conormal map
`I_{𝔮'}/I_{𝔮'}^2 → S_𝔮 ⊗[S'_{𝔮'}] Ω[S'_{𝔮'}⁄R]`, where
`I_{𝔮'} = ker(S'_{𝔮'} → S_𝔮)`, is the canonical owner
`KaehlerDifferential.kerCotangentToTensor` for the localized map `S'_{𝔮'} → S_𝔮`. -/
#check
  ((KaehlerDifferential.kerCotangentToTensor R (Localization.AtPrime q') (Localization.AtPrime q)) :
    (RingHom.ker (algebraMap (Localization.AtPrime q') (Localization.AtPrime q))).Cotangent →ₗ[
      Localization.AtPrime q']
      Localization.AtPrime q ⊗[Localization.AtPrime q'] Ω[Localization.AtPrime q'⁄R])

/- On the class of an element of the localized kernel ideal, the conormal map is exactly
`x ↦ 1 ⊗ d x`; this is the direct specialization of
`KaehlerDifferential.kerCotangentToTensor_toCotangent`. -/
#check
  ((KaehlerDifferential.kerCotangentToTensor_toCotangent
      R (Localization.AtPrime q') (Localization.AtPrime q)) :
    ∀ x : RingHom.ker (algebraMap (Localization.AtPrime q') (Localization.AtPrime q)),
      KaehlerDifferential.kerCotangentToTensor R (Localization.AtPrime q') (Localization.AtPrime q)
          (Ideal.toCotangent _ x) =
        1 ⊗ₜ[Localization.AtPrime q'] KaehlerDifferential.D R (Localization.AtPrime q') x.1
  )

end
