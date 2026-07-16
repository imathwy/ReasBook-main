import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_3
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3

noncomputable section

open CategoryTheory
open scoped Representation IsMulCommutative

universe u

namespace Representation

section PRegularComponentVirtualModularCharacters

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type u} [AddCommGroup A]
variable {G : Type u} [Group G] [Finite G]

/- Domain-style sampling for this item:
* primary domain: modular representation theory of finite groups at the interface between
  Brauer/virtual modular characters on the `p`-regular locus and ordinary virtual characters on
  all of `G`;
* `virtualModularCharacter` in Remark `18-18.1-3` is the core/canonical owner on the
  `p`-regular locus.
* `pRegularComponent` in Chapter `10` is the chapter's canonical source-facing passage from an
  arbitrary element of `G` to its chosen `p`-regular component.
* `R[K](G)` from Chapter `12` is the canonical owner for ordinary virtual characters on all of
  `G` over a characteristic-zero field `K`.
* `finiteRepGrothendieckCharacter` in Theorem `16-16.2-1` is the canonical bridge from
  `R₀[K](G)` back to `R[K](G)`.

Layer triage:
* source-facing: Serre's class function `x ↦ x'` on all of `G`.
* core/canonical owner reused here: `virtualModularCharacter lift`.
* bridge/view: `pRegularComponentVirtualModularCharacter p lift`, obtained by precomposition along
  `g ↦ ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩`.
* derived API: the canonical codomain restriction of
  `pRegularComponentVirtualModularCharacter p lift` to `R[K](G)`, used directly in part `(2)`.

Primitive data vs. derived API:
* primitive data: the additive map to all class functions on `G`.
* derived API: the codomain restriction `pRegularComponentVirtualCharacter` to `R[K](G)`,
  supplied by part `(1)` and used directly in part `(2)`.
-/

variable (p)

/-- The class function on `G` obtained by evaluating a virtual modular character on the chosen
`p`-regular component of each group element. This is Serre's `f ↦ f'` construction. -/
def pRegularComponentVirtualModularCharacter
    (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ G → A where
  toFun x g :=
    virtualModularCharacter lift x
      ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩
  map_zero' := by
    ext g
    simp
  map_add' x y := by
    ext g
    simp

/- Do `open scoped Representation` to write Serre's `f'` operation as `x′[p, lift]` for
`pRegularComponentVirtualModularCharacter p lift x`. The prime notation is source-facing, while
the explicit `[p, lift]` keeps the non-inferable prime and coefficient-field lift visible. -/
set_option quotPrecheck false in
scoped notation:max x "′[" p ", " lift "]" =>
  pRegularComponentVirtualModularCharacter p lift x

@[simp] theorem pRegularComponentVirtualModularCharacter_apply
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G)) (g : G) :
    x′[p, lift] g =
      virtualModularCharacter lift x
        ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩ :=
  rfl

end PRegularComponentVirtualModularCharacters

section CharacterRingLift

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 18-18.4-1: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq :
          Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 18-18.4-1: Serre's `x ↦ x'` construction is constant on conjugacy
classes, so it defines a bundled `K`-valued class function on `G`. -/
theorem pRegularComponentVirtualModularCharacter_isClassFunction
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G)) :
    x′[p, PrimeToPRoot.toFieldLift lift] ∈ classFunctionSubmodule K G := by
  refine (mem_classFunctionSubmodule_iff K _).2 ?_
  refine ⟨?_⟩
  intro s t hst
  rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
  have hconj : t = (a : G) * s * (a : G)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).2
    simpa [mul_assoc] using ha.eq.symm
  rw [hconj]
  simpa [pRegularComponentVirtualModularCharacter_apply, pRegularComponent_conj] using
    virtualModularCharacter_conj
      (lift := PrimeToPRoot.toFieldLift lift) (x := x)
      (s := pRegularComponent p s) (t := a)
      (isPRegular_pRegularComponent s) |>.symm

/-- Helper for Theorem 18-18.4-1: on a `p`-regular element, Serre's `x ↦ x'` construction simply
recovers the original virtual modular character. -/
@[simp] theorem pRegularComponentVirtualModularCharacter_apply_of_isPRegular
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G))
    (s : { g : G // IsPRegular p g }) :
    x′[p, PrimeToPRoot.toFieldLift lift] s.1 =
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) x s := by
  simp [pRegularComponentVirtualModularCharacter_apply,
    pRegularComponent_eq_self_of_isPRegular s.2]

/-- Helper for Theorem 18-18.4-1: computing the `p`-regular component inside a subgroup and then
including into `G` gives the same ambient element as computing it directly in `G`. -/
private theorem subgroup_coe_pRegularComponent_eq
    (H : Subgroup G) (h : H) :
    ((pRegularComponent p h : H) : G) = pRegularComponent p (h : G) := by
  simp [pRegularComponent, orderOf_submonoid]

/-- Helper for Theorem 18-18.4-1: pointwise, restricting the ambient transformed simple class to
`H` agrees with forming Serre's transform from the restricted representation. -/
theorem pRegularComponentVirtualModularCharacter_restrict_simple_class_apply
    (lift : PrimeToPRoot p k →* Kˣ) (H : Subgroup G) (S : FDRep k G) (h : H) :
    (H.classFunctionRestriction
      ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
        pRegularComponentVirtualModularCharacter_isClassFunction
          (p := p) (k := k) (K := K) (G := G) lift [S]₀⟩ : H → K) h =
      ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift lift] h := by
  rw [Subgroup.classFunctionRestriction_apply]
  simp only [pRegularComponentVirtualModularCharacter_apply, virtualModularCharacter_class,
    FGModuleCat.of_carrier, ModuleCat.of_coe, FDRep.of_ρ']
  let hHreg : { x : H // IsPRegular p x } :=
    ⟨pRegularComponent p h, isPRegular_pRegularComponent h⟩
  let hGreg₁ : { x : G // IsPRegular p x } :=
    ⟨(hHreg : H), by simpa [IsPRegular, orderOf_submonoid] using hHreg.2⟩
  let hGreg₂ : { x : G // IsPRegular p x } :=
    ⟨pRegularComponent p (h : G), isPRegular_pRegularComponent (h : G)⟩
  have hsub :
      modularCharacter (PrimeToPRoot.toFieldLift lift) (S.ρ.comp H.subtype) hHreg =
        modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ hGreg₁ := by
    subst hHreg hGreg₁
    change
      (Multiset.map
        (fun μ ↦
          ((lift
              (charpolyRoot_primeToPRoot (p := p) (k := k) (S.ρ.comp H.subtype)
                (isPRegular_pRegularComponent h) μ.2) : Kˣ) : K))
        ((S.ρ ((pRegularComponent p h : H) : G)).charpoly.roots.attach)).sum =
      (Multiset.map
        (fun μ ↦
          ((lift
              (charpolyRoot_primeToPRoot (p := p) (k := k) S.ρ
                (by simpa [IsPRegular, orderOf_submonoid] using
                  (isPRegular_pRegularComponent h : IsPRegular p (pRegularComponent p h))) μ.2) :
              Kˣ) : K))
        ((S.ρ ((pRegularComponent p h : H) : G)).charpoly.roots.attach)).sum
    apply congrArg Multiset.sum
    congr
    ext μ
    apply congrArg (fun ζ : PrimeToPRoot p k => ((lift ζ : Kˣ) : K))
    ext
    simp [charpolyRoot_primeToPRoot_coe]
  have hgreg : hGreg₁ = hGreg₂ := by
    apply Subtype.ext
    exact subgroup_coe_pRegularComponent_eq (p := p) H h
  calc
    modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ hGreg₂
        = modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ hGreg₁ := by
            simpa [hgreg] using
              (rfl :
                modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ hGreg₁ =
                  modularCharacter (PrimeToPRoot.toFieldLift lift) S.ρ hGreg₁)
    _ = modularCharacter (PrimeToPRoot.toFieldLift lift) (S.ρ.comp H.subtype) hHreg := hsub.symm

/-- Helper for Theorem 18-18.4-1: restricting Serre's simple-class transform to a subgroup agrees
pointwise with the same construction formed from the restricted representation. -/
theorem pRegularComponentVirtualModularCharacter_restrict_simple_class
    (lift : PrimeToPRoot p k →* Kˣ) (H : Subgroup G) (S : FDRep k G) :
    (H.classFunctionRestriction
      ⟨([S]₀)′[p, PrimeToPRoot.toFieldLift lift],
        pRegularComponentVirtualModularCharacter_isClassFunction
          (p := p) (k := k) (K := K) (G := G) lift [S]₀⟩ : H → K) =
      ([FDRep.of (S.ρ.comp H.subtype)]₀)′[p, PrimeToPRoot.toFieldLift lift] := by
  funext h
  exact pRegularComponentVirtualModularCharacter_restrict_simple_class_apply
    (p := p) (k := k) (K := K) (G := G) lift H S h

end CharacterRingLift

end Representation
