import Mathlib
import stacks_project.Chap10.Proposition_10_35_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

local notation "R₀" => closedPoints (PrimeSpectrum R)
local notation "S₀" => closedPoints (PrimeSpectrum S)
local notation "ιR" => (Subtype.val : R₀ → PrimeSpectrum R)
local notation "ιS" => (Subtype.val : S₀ → PrimeSpectrum S)

/- Layering for this item:
* source-facing: the closed-point image statement for constructible subsets and the density
  criterion for membership in `comap f '' E`;
* core/canonical owner: `closedPoints`, `PrimeSpectrum.comap`, and the restricted map
  `PrimeSpectrum.comapClosedPoints`;
* bridge/view: `preimage_comap_image_eq_image_comapClosedPoints`, which rewrites the source-facing
  closed-point image statement in owner-level closed-point-subspace form.
-/

section

variable (f : R →+* S) (hf : f.FiniteType)
variable {E : Set (PrimeSpectrum S)}

local notation "E₀" => ιS ⁻¹' E
local notation "fE₀" => ιR '' (comapClosedPoints f hf '' E₀)

-- Proof sketch: start with a closed point of the constructible subspace `comap f '' E`;
-- finite type over the Jacobson ring `R` makes `S` Jacobson by Proposition `10.35.19 (1)`,
-- so Jacobsonity of the constructible subspace `E` produces a closed point of `E` above it, and
-- Proposition `10.35.19 (2)` packages the induced map on ambient closed points as
-- `PrimeSpectrum.comapClosedPoints`.
/-- Lemma 10.35.21 (1): for a finite type ring map `f : R →+* S` from a Jacobson ring and a
constructible subset `E ⊆ Spec(S)`, the closed points of `f(E)` are exactly the images, under the
canonical restricted map on closed points, of the closed points of `E`. -/
theorem closedPoints_comap_image_eq_image_closedPoints
    (hE : IsConstructible E) :
    Subtype.val '' closedPoints (comap f '' E) = fE₀ := sorry

-- Proof sketch: Chevalley makes `comap f '' E` constructible, so Lemma `5.18.8` identifies the
-- closed points of the constructible subspace `comap f '' E` with the trace of `comap f '' E` on
-- `R₀`. The first theorem identifies those closed points with the image of the closed points of
-- `E`, and Proposition `10.35.19` packages the ambient map on closed points as
-- `PrimeSpectrum.comapClosedPoints`.
/-- Lemma 10.35.21 (1), owner-level bridge: tracing the constructible image `f(E)` to the
closed-point subspace of `Spec(R)` agrees with applying the restricted spectrum map on closed
points to the trace of `E` on the closed-point subspace of `Spec(S)`. -/
theorem preimage_comap_image_eq_image_comapClosedPoints
    (hE : IsConstructible E) :
    ιR ⁻¹' (comap f '' E) = comapClosedPoints f hf '' E₀ := sorry

section

variable {ξ : PrimeSpectrum R}

local notation "Zξ" => closure (Set.singleton ξ : Set (PrimeSpectrum R))
local notation "ιξ" => (Subtype.val : Zξ → PrimeSpectrum R)

-- Proof sketch: if `ξ ∈ f(E)`, Lemma `10.30.2` gives an open dense subset of `closure {ξ}`
-- contained in `f(E)`, and the owner-level bridge above identifies the closed points of that
-- constructible trace with the image of the closed-point trace of `E` under
-- `PrimeSpectrum.comapClosedPoints`. Conversely, write the constructible set `E` as the image of a
-- finitely presented map using Lemma `10.29.4`, reduce to the case `E = Spec(S)`, and apply Lemma
-- `10.30.4` to the induced map over the residue domain at `ξ`.
/-- If `ξ : Spec(R)` lies in the image of a constructible subset `E ⊆ Spec(S)`, then the trace of
`f(E_0)` on `closure {ξ}` is dense there; conversely, density of that trace characterizes
membership of `ξ` in `f(E)`. -/
theorem mem_comap_image_iff_dense_preimage_closedPoints
    (hE : IsConstructible E) :
    ξ ∈ comap f '' E ↔ Dense (ιξ ⁻¹' fE₀) := sorry

end

end

end
