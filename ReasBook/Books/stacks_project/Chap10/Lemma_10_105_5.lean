import Mathlib
import stacks_project.Chap10.Lemma_10_105_4

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

/-- Helper for Lemma 10.105.5: a finite type algebra over a universally catenary ring is again
universally catenary. -/
theorem universallyCatenaryRing_of_finiteType {S : Type v} [CommRing S] [Algebra A S]
    [UniversallyCatenaryRing.{u, v} A] [Algebra.FiniteType A S] :
    UniversallyCatenaryRing.{v, v} S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  refine { catenary_of_finiteType := ?_ }
  intro C _ _ _
  letI : Algebra A C := RingHom.toAlgebra ((algebraMap S C).comp (algebraMap A S))
  letI : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Compose the two finite type algebra structures back to the original base ring `A`.
  have hfinite : Algebra.FiniteType A C :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A S) inferInstance
  letI : Algebra.FiniteType A C := hfinite
  -- Universal catenarity of `A` now applies directly to the composed finite type algebra.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} A).catenary_of_finiteType

/-- Helper for Lemma 10.105.5: universal catenarity transports across a ring equivalence. -/
theorem universallyCatenaryRing_of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) [UniversallyCatenaryRing.{u, v} R] :
    UniversallyCatenaryRing.{v, v} S := by
  letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  refine { catenary_of_finiteType := ?_ }
  intro T _ _ _
  letI : Algebra R S := RingHom.toAlgebra e.toRingHom
  letI : Algebra R T := RingHom.toAlgebra ((algebraMap S T).comp e.toRingHom)
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Regard `S` and then `T` as algebras over `R` through the equivalence `e`.
  have hRS : Algebra.FiniteType R S := by
    let eAlg : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun x ↦ rfl
    exact Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType R R) eAlg
  have hRT : Algebra.FiniteType R T :=
    Algebra.FiniteType.trans hRS inferInstance
  letI : Algebra.FiniteType R T := hRT
  -- The target `T` is finite type over `R`, so universal catenarity descends from `R`.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} R).catenary_of_finiteType

/-- Helper for Lemma 10.105.5: the canonical witness localization for an essentially finite type
`A`-algebra identifies with the algebra itself. -/
noncomputable def essFiniteType_witness_localization_ringEquiv [Algebra.EssFiniteType A B] :
    Localization (Algebra.EssFiniteType.submonoid A B) ≃+* B :=
  (IsLocalization.algEquiv (Algebra.EssFiniteType.submonoid A B)
    (Localization (Algebra.EssFiniteType.submonoid A B)) B).toRingEquiv

/-- Lemma 10.105.5: any `A`-algebra essentially of finite type over a universally catenary
ring `A` is universally catenary. -/
-- Proof sketch: let `B₀ := Algebra.EssFiniteType.subalgebra A B`; then `B₀` is a finite type
-- `A`-algebra, hence universally catenary by the finite-type case applied twice. The ambient ring
-- `B` is the localization of `B₀` at the canonical submonoid
-- `Algebra.EssFiniteType.submonoid A B`, so Lemma `10.105.4 (2)` gives the result.
theorem universallyCatenaryRing_of_essFiniteType [UniversallyCatenaryRing.{u, v} A]
    [Algebra.EssFiniteType A B] : UniversallyCatenaryRing.{v, v} B := by
  let B₀ := Algebra.EssFiniteType.subalgebra A B
  let M₀ := Algebra.EssFiniteType.submonoid A B
  -- First prove the finite type witness subalgebra is universally catenary.
  have hB₀ : UniversallyCatenaryRing.{v, v} B₀ := by
    exact universallyCatenaryRing_of_finiteType (A := A) (S := B₀)
  letI : UniversallyCatenaryRing.{v, v} B₀ := hB₀
  letI : UniversallyCatenaryRing.{v, v} (Localization M₀) := localization_universallyCatenaryRing M₀
  -- The source proof finishes by transporting the localization result along the canonical witness
  -- equivalence `Localization M₀ ≃+* B`.
  exact universallyCatenaryRing_of_ringEquiv
    (essFiniteType_witness_localization_ringEquiv (A := A) (B := B))

end
