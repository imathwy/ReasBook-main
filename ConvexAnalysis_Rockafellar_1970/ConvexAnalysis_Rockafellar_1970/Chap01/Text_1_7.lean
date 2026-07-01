import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.7 introduces the textbook predicate that a vector is normal to a
  hyperplane.
- `core/canonical`: the primitive chapter owner abstraction is the linear-functional hyperplane
  family `linearHyperplane f β`, while `affineHyperplane b β` is now the pairing-level
  specialization used on the source-facing surface.
- `bridge/view`: `AffineSubspace.HasNormal` is only a thin source-facing predicate expressing that
  `H` lies in that owner family for a fixed nontrivial pairing normal `b`.
- Primitive data vs derived API: the primitive owner data already lives in
  `linearHyperplane`/`affineHyperplane`, so this file should not introduce any new wrapper
  structure; the normal predicate is derived API on top of the pairing bridge, while the textbook
  vector-normal form is a specialization recovered by choosing an appropriate pairing.
- Domain-style sampling used here: `linearHyperplane`, `affineHyperplane`,
  `AffineSubspace.is_hyperplane`, and
  `AffineSubspace.exists_eq_affineHyperplane_of_is_hyperplane_of_surjective_pairing` from
  `Theorem_1_3`.
-/
section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

/-- Text 1.7: a pairing normal `b` to `H` is a witness that `H` is cut out by one nontrivial
pairing equation `⟪x, b⟫ₚ = β`. -/
def HasNormal (H : AffineSubspace 𝕜 V) (b : Y) : Prop :=
  ∃ β : 𝕜, (HasLinearPairing.pairingLinear.flip b : V →ₗ[𝕜] 𝕜) ≠ 0 ∧
    H = affineHyperplane b β

end AffineSubspace

scoped[Rockafellar] notation:50 b " ⟂ₕ " H => AffineSubspace.HasNormal H b

end

section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {b : Y}

/-- Helper for Text 1.7: a pairing normal to `H` witnesses that `H` is a hyperplane. -/
theorem HasNormal.is_hyperplane (hb : b ⟂ₕ H) :
    H.is_hyperplane := by
  -- Unpack the normal equation and rewrite `H` as the corresponding affine hyperplane.
  rcases hb with ⟨β, hb, rfl⟩
  -- Theorem 1.3 already proves that the affine fiber of a nonzero linear functional is a hyperplane.
  simpa [affineHyperplane] using
    linearHyperplane_is_hyperplane (HasLinearPairing.pairingLinear.flip b) β hb

end AffineSubspace

end

section

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V}
variable [FiniteDimensional 𝕜 V]

/-- Helper for Text 1.7: in finite dimensions, if every scalar-valued linear functional is
represented by a pairing normal, then hyperplanes are exactly affine subspaces admitting a
nonzero normal equation in that pairing. -/
theorem is_hyperplane_iff_exists_hasNormal_of_surjective_pairing
    (hflip :
      Function.Surjective
        (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 V)) :
    H.is_hyperplane ↔ ∃ b : Y, b ⟂ₕ H := by
  constructor
  · intro hH
    -- Use the surjective-pairing form of Theorem 1.3 to recover one affine-hyperplane equation.
    rcases exists_eq_affineHyperplane_of_is_hyperplane_of_surjective_pairing hflip hH with
      ⟨b, hb, β, hH'⟩
    -- Repackage the nontriviality witness in the `HasNormal` language.
    exact ⟨b, β, (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).2 hb, hH'⟩
  · rintro ⟨b, hb⟩
    -- The forward bridge shows that any such normal equation cuts out a hyperplane.
    exact hb.is_hyperplane

/-- Helper for Text 1.7: in finite dimensions, a hyperplane is exactly an affine subspace
admitting a nonzero dual normal equation. This is the canonical dual-pairing specialization of
`is_hyperplane_iff_exists_hasNormal_of_surjective_pairing`. -/
theorem is_hyperplane_iff_exists_hasNormal :
    H.is_hyperplane ↔ ∃ b : Module.Dual 𝕜 V, b ⟂ₕ H := by
  -- Specialize the surjective-pairing criterion to the tautological dual pairing.
  refine is_hyperplane_iff_exists_hasNormal_of_surjective_pairing ?_
  intro f
  refine ⟨f, ?_⟩
  ext x
  rfl

end AffineSubspace

end
