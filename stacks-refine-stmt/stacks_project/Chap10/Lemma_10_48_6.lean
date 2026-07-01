import Mathlib
import stacks_project.Chap10.Definition_10_48_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

universe u

namespace Algebra

local notation "Idempotents" R => {e : R // IsIdempotentElem e}

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

-- Proof sketch: reduce to the finite-type case using Lemma `10.48.5` and the finite-subalgebra
-- detection result for tensor-product idempotents from Lemma `10.43.4`. In the finite-type case
-- the spectra are Noetherian, so connected components are clopen; translate idempotents to clopen
-- decompositions via Lemmas `10.21.4`, `10.22.2`, and `10.24.3`, and then compare with the
-- connected-components statement.
/-- Lemma 10.48.6 (Tag 037W): if `k` is a field, `S` is geometrically connected over `k`, and `R`
is any `k`-algebra, then the canonical map `R → R ⊗[k] S` induces bijections both on idempotents
and on connected components of prime spectra. -/
@[stacks 037W]
theorem Lemma_10_48_6
    (hgeom : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))) :
    Function.Bijective
      (fun e : Idempotents R ↦
        (⟨includeLeft e.1, e.2.map (includeLeft : R →ₐ[k] R ⊗[k] S)⟩ :
          Idempotents (R ⊗[k] S))) ∧
      Function.Bijective
        ((PrimeSpectrum.continuous_comap (includeLeft : R →ₐ[k] R ⊗[k] S)).connectedComponentsMap :
          ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
            ConnectedComponents (PrimeSpectrum R)) :=
  sorry

end

end Algebra
