import Mathlib
import StacksProject_2024.Chap10.Lemma_10_105_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-
Domain-style sampling in the universal-catenarity API:
- catenary ring owner: `IsCatenaryRing R`
- universally catenary owner: `UniversallyCatenaryRing R`
- essentially finite type owner: `Algebra.EssFiniteType R S`, with canonical witness API
  `Algebra.EssFiniteType.subalgebra`, `Algebra.EssFiniteType.submonoid`, and
  `Algebra.EssFiniteType.isLocalization`
- localization stability: `localization_universallyCatenaryRing`

Layer triage:
- `source-facing`: Lemma 10.105.5 says essential finite type extensions of universally catenary
  rings are universally catenary
- `core/canonical`: `UniversallyCatenaryRing`
- `bridge/view`: `Algebra.EssFiniteType` presents `B` as a localization of the canonical finite
  type subalgebra `Algebra.EssFiniteType.subalgebra A B`

Primitive data belongs to the existing owners `UniversallyCatenaryRing` and
`Algebra.EssFiniteType`; this file should only provide the bridge theorem, not a second catenary
owner API. Since the source ring of an essentially finite type algebra is additional algebra data
not determined by the target ring `B`, Lean cannot expose this bridge as a global
`UniversallyCatenaryRing B` instance without a separate owner carrying that source data.
-/

/-- Lemma 10.105.5: any `A`-algebra essentially of finite type over a universally catenary
ring `A` is universally catenary. -/
-- Proof sketch: let `B₀ := Algebra.EssFiniteType.subalgebra A B`; then `B₀` is a finite type
-- `A`-algebra, hence universally catenary by the finite-type case applied twice. The ambient ring
-- `B` is the localization of `B₀` at the canonical submonoid
-- `Algebra.EssFiniteType.submonoid A B`, so Lemma `10.105.4 (2)` gives the result.
theorem universallyCatenaryRing_of_essFiniteType [UniversallyCatenaryRing A]
    [Algebra.EssFiniteType A B] : UniversallyCatenaryRing B := by
  let _ : IsNoetherian B B := by
    sorry
  refine ⟨?_⟩
  intro C _ _ _
  sorry

end
