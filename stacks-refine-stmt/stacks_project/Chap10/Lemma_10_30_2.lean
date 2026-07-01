import Mathlib.RingTheory.Spectrum.Prime.Chevalley

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology PrimeSpectrum TopologicalSpace

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}
variable {E : Set (PrimeSpectrum S)} {ξ : PrimeSpectrum R}

local notation "Zξ" => closure (Set.singleton ξ : Set (PrimeSpectrum R))
local notation "traceOnClosure" =>
  ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (comap f '' E))

/- Layering for this item:
* source-facing: the existence of an open dense subset in the trace of `comap f '' E` on
  `closure {ξ}` for a finite type map;
* core/canonical owner: `PrimeSpectrum.comap`, `IsConstructible`, and the generic-point space
  `closure ({ξ} : Set (PrimeSpectrum R))`;
* bridge/view: the finite-presentation constructible-image theorem
  `PrimeSpectrum.isConstructible_comap_image`, the generic-point package `isGenericPoint_closure`,
  and the Chapter 5 dense-trace criteria
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`
  and `IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed`.
-/
-- Proof sketch: replace `Spec R` by the irreducible closed subset `closure {ξ}` and the source by
-- the closure of a point of `E` above `ξ`, so that `ξ` becomes a generic point. Lemma `10.30.1`
-- gives dense opens on which the finite type map is finitely presented, Chevalley's theorem makes
-- the corresponding image constructible, and the generic-point criterion for constructible subsets
-- then yields an open dense subset of `closure {ξ}` contained in the image.
/-- Lemma 10.30.2: for a finite type ring map `f : R →+* S` and a constructible subset
`E ⊆ Spec(S)`, if `ξ ∈ Spec(R)` lies in the image of `E` under `Spec(S) → Spec(R)`, then the
trace of that image on `closure {ξ}` contains an open dense subset of `closure {ξ}`. -/
lemma exists_open_dense_subset_closure_singleton_of_mem_comap_image_constructible
    (f : R →+* S) (hf : f.FiniteType) (hE : IsConstructible E) (hξ : ξ ∈ comap f '' E) :
    ∃ U : Opens Zξ, Dense (U : Set Zξ) ∧ (U : Set Zξ) ⊆ traceOnClosure := sorry

end
