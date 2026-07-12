import StacksProject_2024.Chap10.Lemma_10_35_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology PrimeSpectrum RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

section

variable [IsNoetherianRing R]
variable {E : Set (PrimeSpectrum S)}

local notation "R₀" => closedPoints (PrimeSpectrum R)
local notation "S₀" => closedPoints (PrimeSpectrum S)
local notation "ιR" => (Subtype.val : R₀ → PrimeSpectrum R)
local notation "ιS" => (Subtype.val : S₀ → PrimeSpectrum S)
local notation "E₀" => ιS ⁻¹' E

/- Layering for this item:
* source-facing: the finite-type/noetherian specialization of Chevalley together with the induced
  commutativity statement on traces to closed points;
* core/canonical owner: `PrimeSpectrum.isConstructible_comap_image`;
* bridge/view: `preimage_comap_image_eq_image_comapClosedPoints`.
-/

-- Proof sketch: Chevalley gives constructibility of `f(E)`, and Lemma `10.35.21` identifies the
-- closed points of `f(E)` with the images of the closed points of `E`. Rewriting that identity in
-- the closed-point subspaces gives exactly the square in Stacks `00GE`.
/-- Lemma 10.35.22 (`00GE`): if `R` is a Noetherian Jacobson ring and `f : R →+* S` is finite
type, then for every constructible subset `E ⊆ Spec(S)` the image `f(E)` is constructible in
`Spec(R)`, and tracing to closed points commutes with taking the image under `f`. Equivalently,
the square
`Constr(Spec(S)) → Constr(Spec(R))` and `Constr((Spec(S))₀) → Constr((Spec(R))₀)` commutes, with
horizontal arrows given by Lemma `5.18.8`. This is a thin source-facing conjunction of the
canonical constructible-image theorem and the owner-level closed-point trace bridge from Lemma
`10.35.21`. -/
theorem isConstructible_comap_image_and_preimage_closedPoints_eq
    (f : R →+* S) (hf : f.FiniteType) (hE : IsConstructible E) :
    IsConstructible (comap f '' E) ∧
      ιR ⁻¹' (comap f '' E) = comapClosedPoints f hf '' E₀ := by
  refine ⟨isConstructible_comap_image (FinitePresentation.of_finiteType.mp hf) hE, ?_⟩
  exact preimage_comap_image_eq_image_comapClosedPoints f hf hE

end

end
