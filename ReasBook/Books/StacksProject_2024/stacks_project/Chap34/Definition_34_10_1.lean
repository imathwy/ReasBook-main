import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

/-- An extension of a valuation ring `V` by another valuation ring `W`. -/
structure ValuationRingExtension (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] where
  /-- The target valuation ring. -/
  W : Type u
  /-- The commutative-ring structure on the target. -/
  instCommRing : CommRing W
  /-- The target is a domain. -/
  instIsDomain : IsDomain W
  /-- The target is a valuation ring. -/
  instValuationRing : ValuationRing W
  /-- The source acts on the target through the extension map. -/
  instAlgebra : Algebra V W
  /-- The structure map `V → W` is a local homomorphism. -/
  isLocalHom : IsLocalHom (algebraMap V W)
  /-- The structure map `V → W` is injective. -/
  algebraMap_injective : Function.Injective (algebraMap V W)

attribute [instance] ValuationRingExtension.instCommRing
attribute [instance] ValuationRingExtension.instIsDomain
attribute [instance] ValuationRingExtension.instValuationRing
attribute [instance] ValuationRingExtension.instAlgebra

/-- A finite family of affine schemes mapping to a fixed base scheme `T`. -/
structure AffineFamilyOver (T : Scheme.{u}) where
  /-- The number of members in the family. -/
  n : ℕ
  /-- The source schemes in the family. -/
  U : Fin n → Scheme.{u}
  /-- The structure morphisms to the common base `T`. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Every member of the family is affine. -/
  isAffine : ∀ j, IsAffine (U j)

/-- An affine family over `T` can be used as its underlying finite family of morphisms to `T`. -/
instance {T : Scheme.{u}} : CoeFun (AffineFamilyOver T) (fun 𝒰 ↦ (j : Fin 𝒰.n) → 𝒰.U j ⟶ T) where
  coe 𝒰 := 𝒰.map

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- A refinement of finite affine families over the same base scheme `T`. -/
structure Refinement (𝒱 𝒰 : AffineFamilyOver T) where
  /-- The target index in the coarser family for each member of the refining family. -/
  toIndex : Fin 𝒱.n → Fin 𝒰.n
  /-- The factorization morphisms exhibiting the refinement. -/
  lift : (k : Fin 𝒱.n) → 𝒱.U k ⟶ 𝒰.U (toIndex k)
  /-- Each refining morphism factors through the chosen member of the coarser family. -/
  fac : ∀ k, lift k ≫ 𝒰.map (toIndex k) = 𝒱.map k

/-- A refinement can be used as its underlying family of factorization morphisms. -/
instance {𝒱 𝒰 : AffineFamilyOver T} :
    CoeFun (Refinement 𝒱 𝒰) (fun r ↦ (k : Fin 𝒱.n) → 𝒱.U k ⟶ 𝒰.U (r.toIndex k)) where
  coe r := r.lift

/-- A witness that a finite affine family over `T` is isomorphic, as a family over `T`, to the
base change of a finite affine family over `S` along `p : T ⟶ S`. -/
structure IsBaseChangeOf {S T : Scheme.{u}} (p : T ⟶ S)
    (𝒰S : AffineFamilyOver S) (𝒰T : AffineFamilyOver T) where
  /-- The index bijection between the original family and the displayed base-changed family. -/
  indexEquiv : Fin 𝒰S.n ≃ Fin 𝒰T.n
  /-- The componentwise isomorphisms from the categorical pullbacks to the displayed members. -/
  componentIso : ∀ j : Fin 𝒰S.n, pullback p (𝒰S.map j) ≅ 𝒰T.U (indexEquiv j)
  /-- Each component isomorphism is compatible with the structure morphism to the new base. -/
  map_eq : ∀ j : Fin 𝒰S.n,
    (componentIso j).hom ≫ 𝒰T.map (indexEquiv j) = pullback.fst p (𝒰S.map j)

/- Definition 34.10.1: a finite affine family `𝒰` over an affine scheme `T` is a standard `V`
covering if every morphism `g : Spec(V) ⟶ T` from a valuation ring lifts, after passing to an
extension of valuation rings `V ⊆ W`, through one member of the family. -/
@[stacks 0ETB]
class IsStandardVCover (𝒰 : AffineFamilyOver T) : Prop where
  /-- For every valuation-ring point of `T`, the map lifts after an extension of valuation rings
  through one member of the family. -/
  valuativeLift :
    ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (CommRingCat.of V) ⟶ T),
        ∃ ext : ValuationRingExtension V,
          ∃ j : Fin 𝒰.n,
            ∃ lift : Spec (CommRingCat.of ext.W) ⟶ 𝒰.U j,
              Spec.map (CommRingCat.ofHom (algebraMap V ext.W)) ≫ g = lift ≫ 𝒰.map j

/-- Source-facing specification of `IsStandardVCover`: a finite affine family over an affine
scheme is a standard `V` covering exactly when every valuation-ring point of the base lifts after
passing to an extension of valuation rings. -/
theorem isStandardVCover_iff_valuativeLift (𝒰 : AffineFamilyOver T) :
    IsStandardVCover 𝒰 ↔
      ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
        (g : Spec (CommRingCat.of V) ⟶ T),
          ∃ ext : ValuationRingExtension V,
            ∃ j : Fin 𝒰.n,
              ∃ lift : Spec (CommRingCat.of ext.W) ⟶ 𝒰.U j,
                Spec.map (CommRingCat.ofHom (algebraMap V ext.W)) ≫ g = lift ≫ 𝒰.map j := by
  constructor
  · intro h𝒰
    exact h𝒰.valuativeLift
  · intro h𝒰
    exact ⟨h𝒰⟩

/-- A standard `V` covering supplies a valuative factorization after extending the valuation ring.
-/
theorem IsStandardVCover.exists_valuativeLift {T : Scheme.{u}} {𝒰 : AffineFamilyOver T}
    (h𝒰 : IsStandardVCover 𝒰) {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    (g : Spec (CommRingCat.of V) ⟶ T) :
    ∃ ext : ValuationRingExtension V,
      ∃ j : Fin 𝒰.n,
        ∃ lift : Spec (CommRingCat.of ext.W) ⟶ 𝒰.U j,
          Spec.map (CommRingCat.ofHom (algebraMap V ext.W)) ≫ g = lift ≫ 𝒰.map j :=
  h𝒰.valuativeLift g

end AffineFamilyOver

end

end AlgebraicGeometry
