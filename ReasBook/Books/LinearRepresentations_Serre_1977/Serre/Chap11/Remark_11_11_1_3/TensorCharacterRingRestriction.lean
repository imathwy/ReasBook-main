import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.TensorCharacterBridge

-- Stable subgroup tensor-character-ring restriction infrastructure extracted from Remark 11-11.1-3.

noncomputable section

universe v

namespace Subgroup

section TensorCharacterRing

open scoped Pointwise Representation SubgroupInduction TensorProduct

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A]

/-- A finite group carries a canonical `Fintype` instance for these tensor-character-ring
constructions. -/
local instance fintypeHelperLocalTensorCharacterRingRestriction1 : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance fintypeHelperLocalTensorCharacterRingRestriction2 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local notation:max s " •ᶜ " H => (MulAut.conj s • H : Subgroup G)

private def precompAlgHom {α β : Type*} (f : α → β) : (β → ℂ) →ₐ[ℤ] α → ℂ where
  toFun := LinearMap.funLeft ℤ ℂ f
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext x
    rfl
  map_mul' χ ψ := by
    ext x
    rfl
  commutes' n := by
    ext x
    rfl

private theorem finiteDimensional_res
    {H J : Type} [Monoid H] [Monoid J] (f : H →* J) (ρ : Rep ℂ J)
    [FiniteDimensional ℂ ρ] : FiniteDimensional ℂ (Rep.res f ρ) := by
  infer_instance

private theorem precomp_mem_characterRing
    {H J : Type} [Group H] [Finite H] [Group J] [Finite J]
    (f : H →* J) (χ : R(J)) :
    precompAlgHom f χ ∈ R(H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R(H)
    letI : FiniteDimensional ℂ ρ := hρfd
    letI : FiniteDimensional ℂ (Rep.res f ρ) := finiteDimensional_res f ρ
    exact Representation.rep_character_mem_characterRing (Rep.res f ρ)
  · intro n
    exact (R(H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R(H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R(H)).mul_mem hx hy

/-- The canonical transport on Serre's character ring along a group isomorphism. -/
def characterRingTransport
    {H J : Type} [Group H] [Finite H] [Group J] [Finite J] (e : H ≃* J) :
    R(J) →ₐ[ℤ] R(H) :=
  (((precompAlgHom e).comp (R(J)).val).codRestrict (R(H))
    (precomp_mem_characterRing e.toMonoidHom))

/-- Helper for Remark 11-11.1-3: restricting a global character-ring element to a subgroup stays
inside the subgroup character ring. -/
private theorem restrict_mem_characterRing
    (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  simpa using precomp_mem_characterRing H.subtype χ

/-- The canonical restriction map `R(G) → R(H)` attached to a subgroup `H ≤ G`. -/
def characterRingRestriction (H : Subgroup G) : R(G) →ₐ[ℤ] R(H) :=
  (((precompAlgHom H.subtype).comp (R(G)).val).codRestrict (R(H))
    (restrict_mem_characterRing H))

scoped[Representation] notation:max H " ↾R[ℂ]" =>
  Subgroup.characterRingRestriction H

/-- Helper for Remark 11-11.1-3: evaluating subgroup restriction just evaluates the original
global character on the same ambient group element. -/
@[simp] theorem characterRingRestriction_apply
    (H : Subgroup G) (χ : R(G)) (h : H) :
    (((H ↾R[ℂ]) χ : R(H)) : H → ℂ) h = (χ : G → ℂ) h := rfl

/-- Helper for Remark 11-11.1-3: restricting a local character-ring element along a subgroup
inclusion stays inside the smaller subgroup character ring. -/
private theorem restrict_mem_characterRingOfLe
    {H J : Subgroup G} (h : H ≤ J) (χ : R(J)) :
    (fun x : H ↦ (χ : J → ℂ) (Subgroup.inclusion h x)) ∈ R(H) := by
  simpa using precomp_mem_characterRing (Subgroup.inclusion h) χ

/-- The canonical restriction map `R(J) → R(H)` attached to an inclusion `H ≤ J`. -/
def characterRingRestrictionOfLe
    {H J : Subgroup G} (h : H ≤ J) : R(J) →ₐ[ℤ] R(H) :=
  (((precompAlgHom (Subgroup.inclusion h)).comp (R(J)).val).codRestrict (R(H))
    (restrict_mem_characterRingOfLe h))

scoped[Representation] notation:max h " ↾R[ℂ]" =>
  Subgroup.characterRingRestrictionOfLe h

/-- Helper for Remark 11-11.1-3: evaluating restriction along an inclusion `H ≤ J` only changes
the ambient owner of the same subgroup element. -/
@[simp] theorem characterRingRestrictionOfLe_apply
    {H J : Subgroup G} (h : H ≤ J) (χ : R(J)) (x : H) :
    (((characterRingRestrictionOfLe h χ : R(H)) : H → ℂ) x) =
      (χ : J → ℂ) (Subgroup.inclusion h x) :=
  rfl

/-- Helper for Remark 11-11.1-3: transport along a subgroup isomorphism evaluates by
precomposition with that isomorphism. -/
@[simp] theorem characterRingTransport_apply
    {H J : Type} [Group H] [Finite H] [Group J] [Finite J] (e : H ≃* J)
    (χ : R(J)) (h : H) :
    ((characterRingTransport e χ : R(H)) : H → ℂ) h = (χ : J → ℂ) (e h) := by
  rfl

/-- The canonical restriction map on Serre's tensor character ring attached to a subgroup `H ≤ G`.
-/
abbrev tensorCharacterRingRestriction (H : Subgroup G) :
    A ⊗R(G) →ₗ[A] A ⊗R(H) :=
  (H ↾R[ℂ]).toLinearMap.baseChange A

/-- The canonical transport on Serre's tensor character ring along a subgroup isomorphism. -/
abbrev tensorCharacterRingTransport {H J : Type} [Group H] [Finite H] [Group J] [Finite J]
    (e : H ≃* J) :
    A ⊗R(J) →ₗ[A] A ⊗R(H) :=
  (characterRingTransport e).toLinearMap.baseChange A

/-- The canonical restriction map on Serre's tensor character ring attached to an inclusion
`H ≤ J`. -/
abbrev tensorCharacterRingRestrictionOfLe {H J : Subgroup G} (h : H ≤ J) :
    A ⊗R(J) →ₗ[A] A ⊗R(H) :=
  (h ↾R[ℂ]).toLinearMap.baseChange A

/-- The canonical conjugation transport on Serre's tensor character ring. -/
abbrev conjugateTensorCharacterRingTransport (H : Subgroup G) (s : G) :
    A ⊗R(H) →ₗ[A] A ⊗R(s •ᶜ H) :=
  tensorCharacterRingTransport ((MulAut.conj s).subgroupMap H).symm

section Evaluation

open scoped Representation TensorProduct

variable [Algebra A ℂ]

/-- Helper for Remark 11-11.1-3: restricting a tensor character to a subgroup does not change its
value at a subgroup element. -/
@[simp] theorem tensorCharacterRingRestriction_apply
    (H : Subgroup G) (χ : A ⊗R(G)) (h : H) :
    ((H.tensorCharacterRingRestriction χ : A ⊗R(H)) : H → ℂ) h = χ h.1 := by
  induction χ using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a ψ =>
      simp [tensorCharacterRingRestriction, LinearMap.baseChange_tmul]
  | add χ ψ hχ hψ =>
      calc
        ((H.tensorCharacterRingRestriction (χ + ψ) : A ⊗R(H)) : H → ℂ) h =
            ((H.tensorCharacterRingRestriction χ : A ⊗R(H)) : H → ℂ) h +
              ((H.tensorCharacterRingRestriction ψ : A ⊗R(H)) : H → ℂ) h := by
                simp [map_add]
        _ = χ h.1 + ψ h.1 := by rw [hχ, hψ]
        _ = (χ + ψ) h.1 := by simp

end Evaluation

/-- Helper for Remark 11-11.1-3: the cyclic subgroup generated by any element of a finite group is
elementary. -/
theorem isElementary_zpowers (g : G) :
    IsElementary (Subgroup.zpowers g) := by
  let H : Subgroup G := Subgroup.zpowers g
  letI : Finite H := by infer_instance
  letI : IsCyclic H := Subgroup.isCyclic_zpowers g
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (Nat.card H + 1)
  refine ⟨p, ⊤, ⊥, ?_⟩
  refine ⟨hpprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.2 inferInstance
  · have hlt : Nat.card H < p := lt_of_lt_of_le (Nat.lt_succ_self _) hpge
    have hcard_top : Nat.card (⊤ : Subgroup H) = Nat.card H :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [Nat.Prime.coprime_iff_not_dvd hpprime]
    rw [hcard_top]
    exact Nat.not_dvd_of_pos_of_lt Nat.card_pos hlt
  · simpa using (IsPGroup.of_bot (p := p) : IsPGroup p (⊥ : Subgroup H))
  · intro c hc y hy
    have hy1 : y = 1 := by simpa using hy
    simpa [hy1]
  · simpa using (Subgroup.isComplement'_top_bot : Subgroup.IsComplement' (⊤ : Subgroup H) ⊥)

end TensorCharacterRing

end Subgroup
