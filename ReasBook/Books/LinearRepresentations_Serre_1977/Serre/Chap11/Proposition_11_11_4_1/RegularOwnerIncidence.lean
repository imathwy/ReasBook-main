import LinearRepresentations_Serre_1977.Serre.Chap11.Proposition_11_11_4_1.OwnersAndPrimeFibers

-- Stable regular-owner incidence helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

namespace Proposition_11_11_4_1

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance regularOwnerIncidenceFintypeGroup : Fintype G := Fintype.ofFinite G
local instance regularOwnerIncidenceFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "P0" => tensorCharacterRingZeroPrimeIdeal

section RegularPrime

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsIntegralClosure A ℤ ℂ]

local instance instFactPrime_roi (p : Nat.Primes) : Fact ((p : ℕ).Prime) := ⟨p.2⟩

/-- Helper for Proposition 11-11.4-1: the `p`-regular owner class represented by the `p'`-part of
an element. This is the source-side bridge from ordinary conjugacy classes to Serre's regular
class parameter. -/
def pregular_conj_class_of_element
    (p : Nat.Primes) (x : G) : PRegularConjClass G p :=
  PRegularConjClass.ofSubtype p ⟨pRegularComponent p x, isPRegular_pRegularComponent x⟩

/-- Helper for Proposition 11-11.4-1: conjugate elements define the same `p`-regular owner class
after passing to the `p'`-component. -/
theorem pregular_conj_class_of_element_eq_of_isConj
    (p : Nat.Primes) {x y : G} (hxy : IsConj x y) :
    pregular_conj_class_of_element (G := G) p x =
      pregular_conj_class_of_element (G := G) p y := by
  apply Subtype.ext
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rcases isConj_iff.mp hxy with ⟨t, rfl⟩
  exact isConj_iff.mpr ⟨t, by simp [pRegularComponent_conj]⟩

/-- Helper for Proposition 11-11.4-1: the canonical `p`-regular owner class attached to an
ordinary conjugacy class by taking the `p'`-component of any representative. -/
def pregular_conj_class_of_conj_class
    (p : Nat.Primes) : ConjClasses G → PRegularConjClass G p :=
  Quotient.lift
    (pregular_conj_class_of_element (G := G) p)
    (fun _ _ hxy ↦ pregular_conj_class_of_element_eq_of_isConj (G := G) p hxy)

/-- Helper for Proposition 11-11.4-1: if the input class is already `p`-regular, the canonical
owner construction returns it unchanged. -/
@[simp] theorem pregular_conj_class_of_conj_class_coe
    (p : Nat.Primes) (c : PRegularConjClass G p) :
    pregular_conj_class_of_conj_class (G := G) p (c : ConjClasses G) = c := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective (c : ConjClasses G)
  have hxreg : IsPRegular p x :=
    c.2 x (ConjClasses.mem_carrier_iff_mk_eq.mpr hx)
  rw [show (c : ConjClasses G) = ConjClasses.mk x by simp [hx]]
  change (pregular_conj_class_of_element (G := G) p x : ConjClasses G) = ConjClasses.mk x
  simp [pregular_conj_class_of_element, pRegularComponent_eq_self_of_isPRegular hxreg]

/-- Helper for Proposition 11-11.4-1: any element lying in the carrier of the canonical
`p`-regular owner of an ordinary conjugacy class determines that same owner class. -/
theorem pregular_conj_class_of_conj_class_eq_of_mem_carrier
    (p : Nat.Primes) {c : ConjClasses G} {x : G}
    (hx : x ∈ (pregular_conj_class_of_conj_class (G := G) p c : ConjClasses G).carrier) :
    pregular_conj_class_of_conj_class (G := G) p (ConjClasses.mk x) =
      pregular_conj_class_of_conj_class (G := G) p c := by
  calc
    pregular_conj_class_of_conj_class (G := G) p (ConjClasses.mk x) =
        pregular_conj_class_of_conj_class (G := G) p
          ((pregular_conj_class_of_conj_class (G := G) p c : PRegularConjClass G p) :
            ConjClasses G) := by
              rw [ConjClasses.mem_carrier_iff_mk_eq.mp hx]
    _ = pregular_conj_class_of_conj_class (G := G) p c := by
          simpa using
            pregular_conj_class_of_conj_class_coe (G := G) p
              (pregular_conj_class_of_conj_class (G := G) p c)

/-- Helper for Proposition 11-11.4-1: an associated `p`-elementary subgroup built from a
representative of the `p`-regular owner of `c` already meets the original conjugacy class `c`.
This is the source-faithful carrier bridge behind the incidence profile. -/
theorem associated_p_elementary_subgroup_nonempty_inter_carrier
    (p : Nat.Primes) {c : ConjClasses G} {x : G}
    (hx : x ∈ (pregular_conj_class_of_conj_class (G := G) p c : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) :
    ((associatedPElementarySubgroup (p : ℕ) x P : Set G) ∩ c.carrier).Nonempty := by
  classical
  obtain ⟨y, hyc⟩ := ConjClasses.mk_surjective c
  have hxmk : ConjClasses.mk x = ConjClasses.mk (pRegularComponent p y) := by
    calc
      ConjClasses.mk x =
          (pregular_conj_class_of_conj_class (G := G) p c : ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      _ =
          (pregular_conj_class_of_conj_class (G := G) p (ConjClasses.mk y) :
            ConjClasses G) := by
              rw [hyc]
      _ = (pregular_conj_class_of_element (G := G) p y : ConjClasses G) := rfl
      _ = ConjClasses.mk (pRegularComponent p y) := by
            simp [pregular_conj_class_of_element]
  obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxmk)
  let y' : G := g⁻¹ * y * g
  have hy'c : y' ∈ c.carrier := by
    refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
    calc
      ConjClasses.mk y' = ConjClasses.mk y := by
        refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
        exact isConj_iff.mpr ⟨g, by simp [y', mul_assoc]⟩
      _ = c := hyc
  have hy'reg : pRegularComponent p y' = x := by
    calc
      pRegularComponent p y' = g⁻¹ * pRegularComponent p y * g := by
        simpa [y'] using pRegularComponent_conj (p := (p : ℕ)) y g⁻¹
      _ = x := by
        rw [← hg]
        simp [mul_assoc]
  let u : G := pUnipotentComponent p y'
  have hu_mem_centralizer : u ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [u, hy'reg] using
      (p_component_decomposition_exists (p := (p : ℕ)) y'
        (isOfFinOrder_of_finite y')).commute.eq
  rcases
      (p_component_decomposition_exists (p := (p : ℕ)) y'
        (isOfFinOrder_of_finite y')).isPElement with ⟨k, hk⟩
  have hu_pgroup : IsPGroup (p : ℕ) (Subgroup.zpowers u) := by
    exact IsPGroup.of_card ((Nat.card_zpowers u).trans hk)
  have hu_zpowers_le_centralizer :
      Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set G) := by
    exact Subgroup.zpowers_le.mpr hu_mem_centralizer
  have hu_pgroup_centralizer :
      IsPGroup (p : ℕ)
        ((Subgroup.zpowers u).subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
    exact hu_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hu_zpowers_le_centralizer).symm
  obtain ⟨Q, hQ⟩ := hu_pgroup_centralizer.exists_le_sylow
  have hu_mem_Q :
      ⟨u, hu_mem_centralizer⟩ ∈
        (Q : Subgroup (Subgroup.centralizer ({x} : Set G))) := by
    apply hQ
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u)
  have hu_mem_assoc_Q :
      u ∈ Subgroup.map (Subgroup.centralizer ({x} : Set G)).subtype
        (Q : Subgroup (Subgroup.centralizer ({x} : Set G))) := by
    exact Subgroup.mem_map.mpr ⟨⟨u, hu_mem_centralizer⟩, hu_mem_Q, rfl⟩
  have hy'_eq : y' = x * u := by
    calc
      y' = u * pRegularComponent p y' := by
        simpa [u] using
          (p_component_decomposition_exists (p := (p : ℕ)) y'
            (isOfFinOrder_of_finite y')).eq_mul
      _ = x * u := by
        simpa [u, hy'reg] using
          (p_component_decomposition_exists (p := (p : ℕ)) y'
            (isOfFinOrder_of_finite y')).commute.eq
  have hy'_mem_assoc_Q : y' ∈ associatedPElementarySubgroup (p : ℕ) x Q := by
    rw [hy'_eq, associatedPElementarySubgroup]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) hu_mem_assoc_Q
  obtain ⟨z, hz⟩ :=
    associatedPElementarySubgroup_conjugate_in_centralizer (p := (p : ℕ)) x Q P
  have hz_mem :
      (z : G) * y' * (z : G)⁻¹ ∈ associatedPElementarySubgroup (p : ℕ) x P := by
    have hz_map :
        MulAut.conj (z : G) y' ∈
          Subgroup.map (MulAut.conj (z : G)).toMonoidHom
            (associatedPElementarySubgroup (p : ℕ) x Q) := by
      exact Subgroup.mem_map.mpr ⟨y', hy'_mem_assoc_Q, rfl⟩
    have hz_eq :
        Subgroup.map (MulAut.conj (z : G)).toMonoidHom
            (associatedPElementarySubgroup (p : ℕ) x Q) =
          associatedPElementarySubgroup (p : ℕ) x P := by
      simpa using hz
    have hz_mem' :
        MulAut.conj (z : G) y' ∈ associatedPElementarySubgroup (p : ℕ) x P := by
      exact hz_eq ▸ hz_map
    simpa [MulAut.conj_apply, mul_assoc] using hz_mem'
  have hz_carrier : (z : G) * y' * (z : G)⁻¹ ∈ c.carrier := by
    refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
    calc
      ConjClasses.mk ((z : G) * y' * (z : G)⁻¹) = ConjClasses.mk y' := by
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr
          (isConj_iff.mpr ⟨z⁻¹, by simp [mul_assoc]⟩)
      _ = c := ConjClasses.mem_carrier_iff_mk_eq.mp hy'c
  exact ⟨(z : G) * y' * (z : G)⁻¹, hz_mem, hz_carrier⟩

/-- Helper for Proposition 11-11.4-1: if a subgroup contains an associated `p`-elementary
subgroup from the regular owner `c`, then it already meets every ordinary conjugacy class whose
canonical `p`-regular component is `c`. -/
theorem nonempty_inter_carrier_of_hasAssociatedPElementarySubgroupInClass
    (p : Nat.Primes) {c : PRegularConjClass G p} {H : Subgroup G} {d : ConjClasses G}
    (hd : pregular_conj_class_of_conj_class (G := G) p d = c)
    (hAssoc : HasAssociatedPElementarySubgroupInClass c H) :
    ((H : Set G) ∩ d.carrier).Nonempty := by
  rcases hAssoc with ⟨x, hx, P, hP⟩
  have hx' : x ∈ (pregular_conj_class_of_conj_class (G := G) p d : ConjClasses G).carrier := by
    simpa [hd] using hx
  rcases associated_p_elementary_subgroup_nonempty_inter_carrier
      (G := G) p hx' P with ⟨y, hyAssoc, hyd⟩
  exact ⟨y, hP hyAssoc, hyd⟩

/-- Helper for Proposition 11-11.4-1: if a subgroup misses an ordinary conjugacy class `d`, then
it cannot contain any associated `p`-elementary subgroup coming from the canonical `p`-regular
owner of `d`. This is the carrier-side contrapositive of the source bridge from owner data back
to ordinary classes. -/
theorem not_hasAssociatedPElementarySubgroupInClass_of_disjoint_owner_carrier
    (p : Nat.Primes) (H : Subgroup G) (d : ConjClasses G)
    (hdisj : ((H : Set G) ∩ d.carrier) = ∅) :
    ¬ HasAssociatedPElementarySubgroupInClass
        (pregular_conj_class_of_conj_class (G := G) p d) H := by
  intro hAssoc
  rcases nonempty_inter_carrier_of_hasAssociatedPElementarySubgroupInClass
      (G := G) (p := p)
      (c := pregular_conj_class_of_conj_class (G := G) p d)
      (H := H) (d := d) rfl hAssoc with ⟨y, hy⟩
  exact by simpa [hdisj] using hy

/-- Helper for Proposition 11-11.4-1: ambient conjugation carries the centralizer of `x` onto the
centralizer of the conjugated element `g x g⁻¹`. This is the proposition-level owner needed
before defining the induced subgroup equivalence. -/
theorem centralizer_conj_map_eq
    (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({MulAut.conj g x} : Set G) := by
  -- Conjugation sends centralizing elements for `x` exactly to those centralizing `g x g⁻¹`.
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    simpa [MulAut.conj_apply, mul_assoc] using
      congrArg (fun t => g * t * g⁻¹) hz
  · intro hy
    refine Subgroup.mem_map.2 ?_
    refine ⟨MulAut.conj g⁻¹ y, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      simpa [MulAut.conj_apply, mul_assoc] using
        congrArg (fun t => g⁻¹ * t * g) hy
    · simp [MulAut.conj_apply, mul_assoc]

/-- Helper for Proposition 11-11.4-1: the stable centralizer equivalence induced by ambient
conjugation. This packages the subgroup transport in a reusable non-propositional owner. -/
noncomputable def centralizer_conj_equiv
    (g x : G) :
    Subgroup.centralizer ({x} : Set G) ≃*
      Subgroup.centralizer ({MulAut.conj g x} : Set G) :=
  ((MulAut.conj g).subgroupMap (Subgroup.centralizer ({x} : Set G))).trans
    (MulEquiv.subgroupCongr (centralizer_conj_map_eq (G := G) g x))

/-- Helper for Proposition 11-11.4-1: conjugating the associated `p`-elementary subgroup of `x`
transports it to the associated subgroup of the conjugated representative. This isolates the
centralizer-transport bookkeeping behind a stable owner-facing lemma. -/
theorem associatedPElementarySubgroup_conj_transport_stable
    (p : Nat.Primes) {x g : G}
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) :
    Subgroup.map (MulAut.conj g).toMonoidHom
        (associatedPElementarySubgroup (p : ℕ) x P) =
      associatedPElementarySubgroup (p : ℕ) (MulAut.conj g x)
        (P.mapSurjective
          (show Function.Surjective (centralizer_conj_equiv (G := G) g x).toMonoidHom from
            (centralizer_conj_equiv (G := G) g x).surjective)) := by
  classical
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let Cx' : Subgroup G := Subgroup.centralizer ({MulAut.conj g x} : Set G)
  let e : Cx ≃* Cx' := centralizer_conj_equiv (G := G) g x
  have hmap_zpowers :
      Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.zpowers x) =
        Subgroup.zpowers (MulAut.conj g x) := by
    -- Conjugation sends the cyclic factor `⟨x⟩` to the cyclic factor of the conjugate element.
    rw [MonoidHom.map_zpowers]
    rfl
  have hcomp :
      (MulAut.conj g).toMonoidHom.comp Cx.subtype =
        Cx'.subtype.comp e.toMonoidHom := by
    -- The transported centralizer equivalence is just the restriction of ambient conjugation.
    ext y
    change (MulAut.conj g y : G) =
      (Subgroup.centralizer ({MulAut.conj g x} : Set G)).subtype
        ((MulEquiv.subgroupCongr (centralizer_conj_map_eq (G := G) g x))
          (((MulAut.conj g).subgroupMap (Subgroup.centralizer ({x} : Set G))) y))
    rfl
  have he_subgroup :
      ((P.mapSurjective (show Function.Surjective e.toMonoidHom from e.surjective) :
          Sylow (p : ℕ) Cx') : Subgroup Cx') =
        Subgroup.map e.toMonoidHom (P : Subgroup Cx) := by
    simpa [Sylow.coe_mapSurjective]
  calc
    Subgroup.map (MulAut.conj g).toMonoidHom (associatedPElementarySubgroup (p : ℕ) x P)
        = Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.zpowers x) ⊔
            Subgroup.map (MulAut.conj g).toMonoidHom
              (Subgroup.map Cx.subtype (P : Subgroup Cx)) := by
      rw [associatedPElementarySubgroup, Subgroup.map_sup]
    _ = Subgroup.zpowers (MulAut.conj g x) ⊔
          Subgroup.map (MulAut.conj g).toMonoidHom
            (Subgroup.map Cx.subtype (P : Subgroup Cx)) := by
      rw [hmap_zpowers]
    _ = Subgroup.zpowers (MulAut.conj g x) ⊔
          Subgroup.map Cx'.subtype
            ((P.mapSurjective (show Function.Surjective e.toMonoidHom from e.surjective) :
                Sylow (p : ℕ) Cx') : Subgroup Cx') := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, he_subgroup]
    _ = associatedPElementarySubgroup (p : ℕ) (MulAut.conj g x)
          (P.mapSurjective (show Function.Surjective e.toMonoidHom from e.surjective)) := by
      rw [associatedPElementarySubgroup]

/-- Helper for Proposition 11-11.4-1: if the same ambient prime satisfies Serre's intrinsic
regular-owner predicate for two `p`-regular classes, then the two classes have the same
associated-`p`-elementary subgroup incidence profile. This isolates the already-verified formal
part of the regular-branch uniqueness argument, leaving only the source-side profile-separation
step open. -/
theorem hasAssociatedPElementarySubgroupInClass_iff_of_same_regular_prime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {P : PrimeSpectrum (A ⊗R(G))} {c₁ c₂ : PRegularConjClass G p}
    (h₁ : IsTensorCharacterRingRegularPrime A G p M c₁ P)
    (h₂ : IsTensorCharacterRingRegularPrime A G p M c₂ P)
    (H : Subgroup G) :
    HasAssociatedPElementarySubgroupInClass c₁ H ↔
      HasAssociatedPElementarySubgroupInClass c₂ H := by
  constructor
  · intro hAssoc
    by_contra hNotAssoc
    have hcontain₂ :
        tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ P.asIdeal := by
      exact (h₂.2 H).2 hNotAssoc
    have hcontain₁ :
        tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ P.asIdeal := by
      simpa using hcontain₂
    exact ((h₁.2 H).1 hcontain₁) hAssoc
  · intro hAssoc
    by_contra hNotAssoc
    have hcontain₁ :
        tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ P.asIdeal := by
      exact (h₁.2 H).2 hNotAssoc
    have hcontain₂ :
        tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ P.asIdeal := by
      simpa using hcontain₁
    exact ((h₂.2 H).1 hcontain₂) hAssoc

/-- Helper for Proposition 11-11.4-1: once the bottom fiber is parametrized by a surjective map
from conjugacy classes and that parametrization is known to transport back to the ambient zero
owners `P₀,c`, the zero-contraction branch is formally closed. This isolates the remaining
zero-side work to constructing the source-faithful lift/transport package. -/
theorem zero_fiber_prime_classification_over_bot_of_fiber_lift
    (lift : ConjClasses G → PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))))
    (hlift_surj : Function.Surjective lift)
    (htransport :
      ∀ c : ConjClasses G,
        ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
          (lift c)).1 = (P0 A c).asIdeal)
    {𝔭 : PrimeSpectrum (A ⊗R(G))}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥) :
    ∃ c : ConjClasses G, P0 A c = 𝔭 := by
  let q : PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
    prime_over_bot_to_fiber (A := A) (G := G) 𝔭 h𝔭
  obtain ⟨c, hc⟩ := hlift_surj q
  refine ⟨c, ?_⟩
  apply PrimeSpectrum.ext
  calc
    (P0 A c).asIdeal =
        ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
          (lift c)).1 := by
            symm
            exact htransport c
    _ =
        ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm q).1 := by
          simpa [q] using congrArg
            (fun t : PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) ↦
              ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm t).1)
            hc
    _ = 𝔭.asIdeal := prime_over_bot_to_fiber_symm (A := A) (G := G) 𝔭 h𝔭

end RegularPrime

end

end Proposition_11_11_4_1
