import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GaloisPowerAction
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3

noncomputable section

universe u x

open CategoryTheory

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Helper for Theorem 18-18.2-1: the conjugacy classes of `G` consisting entirely of
`p`-regular elements. -/
abbrev PRegularConjClass (G : Type u) [Group G] (p : ℕ) :=
  {c : ConjClasses G // ∀ x ∈ c.carrier, IsPRegular p x}

namespace PRegularConjClass

/-- Helper for Theorem 18-18.2-1: every element of the conjugacy class of a chosen `p`-regular
element is again `p`-regular. -/
theorem carrier_isPRegular_ofSubtype (p : ℕ) (s : { x : G // IsPRegular p x }) :
    ∀ x ∈ (ConjClasses.mk s.1).carrier, IsPRegular p x := by
  -- Transport `p`-regularity across conjugacy inside the ambient conjugacy class.
  intro x hx
  have hmk : ConjClasses.mk x = ConjClasses.mk s.1 :=
    ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hsx : IsConj s.1 x := (ConjClasses.mk_eq_mk_iff_isConj.mp hmk).symm
  rcases isConj_iff.1 hsx with ⟨t, rfl⟩
  simpa using isPRegular_conj p s.1 t s.2

/-- Helper for Theorem 18-18.2-1: package the conjugacy class of a chosen `p`-regular element as
an element of `PRegularConjClass G p`. -/
def ofSubtype (p : ℕ) (s : { x : G // IsPRegular p x }) : PRegularConjClass G p :=
  ⟨ConjClasses.mk s.1, carrier_isPRegular_ofSubtype (G := G) p s⟩

/-- Helper for Theorem 18-18.2-1: forgetting `PRegularConjClass.ofSubtype` recovers the ambient
conjugacy class. -/
@[simp] theorem coe_ofSubtype (s : { x : G // IsPRegular p x }) :
    (ofSubtype (G := G) p s : ConjClasses G) = ConjClasses.mk s.1 :=
  rfl

end PRegularConjClass

namespace IsClassFunction

variable {R : Type x}

/-- Helper for Theorem 18-18.2-1: a class function descends to `PRegularConjClass G p`. -/
def pRegularLift {f : G → R} (hf : _root_.IsClassFunction f) (p : ℕ) :
    PRegularConjClass G p → R :=
  fun c ↦ hf.lift c.1

/-- Helper for Theorem 18-18.2-1: evaluating `pRegularLift` on a chosen representative gives the
original class-function value. -/
@[simp] theorem pRegularLift_ofSubtype {f : G → R}
    (hf : _root_.IsClassFunction f)
    (s : { x : G // IsPRegular p x }) :
    pRegularLift (G := G) (p := p) hf (PRegularConjClass.ofSubtype (G := G) p s) = f s.1 := by
  -- The descended owner evaluates by the original class-function lift on the underlying
  -- conjugacy class of the representative.
  rw [pRegularLift, PRegularConjClass.coe_ofSubtype, _root_.IsClassFunction.lift_mk]

end IsClassFunction

/- Domain-style sampling for Theorem 18-18.2-1:
* source-facing Brauer-character owner in this domain:
  `FDRep.modularCharacterOnPRegularConjClass`;
* chapter/project coefficient-ring owner for Exercise `18.4`:
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring`;
* companion basis-owner pattern for field-valued Brauer characters:
  `irreducible_characters_basis_of_complete_family`;
* sampled linear-independence companion:
  `linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic_overSemiring`;
* sampled spanning companion:
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring`.

Best owner abstraction:
* the coefficient-ring basis owner on `PRegularConjClass G p`;
* this file is its field-valued specialization along `PrimeToPRoot.toFieldLift`.

Primitive data vs. derived API:
* primitive data: an injective multiplicative lift `PrimeToPRoot p k →* Kˣ` and a complete
  pairwise-nonisomorphic irreducible family `E`;
* derived API: the resulting `K`-basis of `PRegularConjClass G p → K`, obtained by specializing
  the semiring owner along `PrimeToPRoot.toFieldLift`.

Source/core/bridge triage:
* source-facing: Theorem `18-18.2-1`, the field-valued Brauer-character basis theorem, now
  exposed through its canonical field-valued specialization;
* core/canonical reused here:
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring`;
* bridge/view: `PrimeToPRoot.toFieldLift`.

This file should therefore keep Theorem `42` as the field-valued owner, while any stronger
coefficient-ring extension remains an Exercise `18.4` companion rather than part of the source
theorem itself.
-/

namespace FDRep

/-- Helper for Theorem 18-18.2-1: the Brauer character of `E` descended to LinearRepresentations_Serre_1977's owner
`PRegularConjClass G p` of `p`-regular conjugacy classes. -/
noncomputable def modularCharacterOnPRegularConjClass
    {A : Type x} [AddCommMonoid A]
    (E : FDRep k G) (lift : PrimeToPRoot p k → A) : PRegularConjClass G p → A :=
  let hclass : _root_.IsClassFunction (FDRep.modularCharacterZeroExtension (p := p) E lift) := by
    -- The zero-extended Brauer character is constant on conjugacy classes because the regular
    -- branch is Proposition `18-18.1-2 (2)` and the singular branch stays zero under conjugation.
    refine ⟨?_⟩
    intro s t hst
    rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
    have hconj : t = (a : G) * s * (a : G)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      simpa [mul_assoc] using ha.eq.symm
    rw [hconj]
    by_cases hs : IsPRegular p s
    · have hts : IsPRegular p ((a : G) * s * (a : G)⁻¹) :=
        isPRegular_conj p s (a : G) hs
      rw [FDRep.modularCharacterZeroExtension, FDRep.modularCharacterZeroExtension,
        dif_pos hs, dif_pos hts]
      exact (modularCharacter_conj (p := p) (lift := lift) E.ρ s (a : G) hs).symm
    · have hts : ¬ IsPRegular p ((a : G) * s * (a : G)⁻¹) := by
        intro hreg
        exact hs <| by
          simpa [mul_assoc] using
            (isPRegular_conj p ((a : G) * s * (a : G)⁻¹) ((a : G)⁻¹) hreg)
      rw [FDRep.modularCharacterZeroExtension, FDRep.modularCharacterZeroExtension,
        dif_neg hs, dif_neg hts]
  -- Descend the class function from `G` to the quotient owner of `p`-regular classes.
  IsClassFunction.pRegularLift hclass p

/-- Helper for Theorem 18-18.2-1: evaluating the descended Brauer character on a chosen
`p`-regular representative recovers the original modular character value. -/
@[simp] theorem modularCharacterOnPRegularConjClass_ofSubtype
    {A : Type x} [AddCommMonoid A]
    (E : FDRep k G) (lift : PrimeToPRoot p k → A) (s : { x : G // IsPRegular p x }) :
    modularCharacterOnPRegularConjClass (p := p) E lift (PRegularConjClass.ofSubtype p s) =
      φ[lift](E.ρ) s := by
  -- The descended owner is defined through `pRegularLift`, so evaluation on `ofSubtype` returns
  -- the original zero-extension value, whose regular branch is the Brauer character itself.
  have hclass : _root_.IsClassFunction (FDRep.modularCharacterZeroExtension (p := p) E lift) := by
    refine ⟨?_⟩
    intro s t hst
    rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
    have hconj : t = (a : G) * s * (a : G)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      simpa [mul_assoc] using ha.eq.symm
    rw [hconj]
    by_cases hs : IsPRegular p s
    · have hts : IsPRegular p ((a : G) * s * (a : G)⁻¹) :=
        isPRegular_conj p s (a : G) hs
      rw [FDRep.modularCharacterZeroExtension, FDRep.modularCharacterZeroExtension,
        dif_pos hs, dif_pos hts]
      exact (modularCharacter_conj (p := p) (lift := lift) E.ρ s (a : G) hs).symm
    · have hts : ¬ IsPRegular p ((a : G) * s * (a : G)⁻¹) := by
        intro hreg
        exact hs <| by
          simpa [mul_assoc] using
            (isPRegular_conj p ((a : G) * s * (a : G)⁻¹) ((a : G)⁻¹) hreg)
      rw [FDRep.modularCharacterZeroExtension, FDRep.modularCharacterZeroExtension,
        dif_neg hs, dif_neg hts]
  simpa [modularCharacterOnPRegularConjClass, FDRep.modularCharacterZeroExtension, s.2] using
    (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hclass s)

/-- Helper for Theorem 18-18.2-1: the ordinary character of `X`, restricted to the owner
`PRegularConjClass G p` of `p`-regular conjugacy classes. -/
noncomputable def ordinaryCharacterOnPRegularConjClass
    (p : ℕ) (X : FDRep K G) : PRegularConjClass G p → K :=
  let hclass : _root_.IsClassFunction X.character := by
    refine ⟨?_⟩
    intro s t hst
    rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
    have hconj : t = (a : G) * s * (a : G)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      simpa [mul_assoc] using ha.eq.symm
    rw [hconj]
    exact (X.char_conj s a).symm
  IsClassFunction.pRegularLift hclass p

/-- Helper for Theorem 18-18.2-1: evaluating the descended restricted ordinary character on a
chosen `p`-regular representative recovers the original ordinary character value. -/
@[simp] theorem ordinaryCharacterOnPRegularConjClass_ofSubtype
    (p : ℕ) (X : FDRep K G) (s : { x : G // IsPRegular p x }) :
    ordinaryCharacterOnPRegularConjClass (p := p) X (PRegularConjClass.ofSubtype p s) =
      X.character s := by
  -- Re-express the descended owner through `pRegularLift`, then evaluate on the chosen
  -- representative.
  have hclass : _root_.IsClassFunction X.character := by
    refine ⟨?_⟩
    intro s t hst
    rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
    have hconj : t = (a : G) * s * (a : G)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      simpa [mul_assoc] using ha.eq.symm
    rw [hconj]
    exact (X.char_conj s a).symm
  simpa [ordinaryCharacterOnPRegularConjClass] using
    (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hclass s)

end FDRep

section VirtualModularCharactersOnPRegularConjClass

variable {A : Type x} [AddCommGroup A]

/-- Helper for Theorem 18-18.2-1: choose a `p`-regular representative of a regular conjugacy
class. -/
noncomputable def PRegularConjClass.representative (c : PRegularConjClass G p) :
    { g : G // IsPRegular p g } := by
  classical
  let g : G := Classical.choose (Quotient.exists_rep c.1)
  have hg : ConjClasses.mk g = c.1 := Classical.choose_spec (Quotient.exists_rep c.1)
  refine ⟨g, c.2 g ?_⟩
  rw [← hg]
  exact ConjClasses.mem_carrier_mk

/-- Helper for Theorem 18-18.2-1: the chosen representative lies in the underlying conjugacy
class. -/
@[simp] theorem PRegularConjClass.mk_representative (c : PRegularConjClass G p) :
    ConjClasses.mk (PRegularConjClass.representative (G := G) (p := p) c).1 = c.1 := by
  classical
  simpa [PRegularConjClass.representative] using
    (Classical.choose_spec (Quotient.exists_rep c.1))

/-- Helper for Theorem 18-18.2-1: descend the virtual modular character from the `p`-regular locus
to LinearRepresentations_Serre_1977's owner `PRegularConjClass G p`. -/
noncomputable def virtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ (PRegularConjClass G p → A) :=
  { toFun := fun x ↦
      fun c ↦ virtualModularCharacter lift x (PRegularConjClass.representative (G := G) (p := p) c)
    map_zero' := by
      ext c
      -- Evaluate the additive Grothendieck character at the chosen representative and use its
      -- additive identity law.
      simpa using congrFun (map_zero (virtualModularCharacter lift))
        (PRegularConjClass.representative (G := G) (p := p) c)
    map_add' := by
      intro x y
      ext c
      -- Evaluate at the chosen representative, where additivity is the additive-map structure of
      -- `virtualModularCharacter lift`.
      simpa using congrFun (map_add (virtualModularCharacter lift) x y)
        (PRegularConjClass.representative (G := G) (p := p) c)
  }

/-- Helper for Theorem 18-18.2-1: evaluating the descended virtual modular character on a chosen
`p`-regular representative recovers the original virtual modular character value. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_ofSubtype
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G))
    (s : { g : G // IsPRegular p g }) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift x
        (PRegularConjClass.ofSubtype (G := G) p s) =
      virtualModularCharacter lift x s := by
  classical
  let r :=
    PRegularConjClass.representative (G := G) (p := p)
      (PRegularConjClass.ofSubtype (G := G) p s)
  change virtualModularCharacter lift x r = virtualModularCharacter lift x s
  have hr :
      ConjClasses.mk r.1 = ConjClasses.mk s.1 := by
    simpa [r] using
      (PRegularConjClass.mk_representative (G := G) (p := p)
        (PRegularConjClass.ofSubtype (G := G) p s))
  have hsr : IsConj s.1 r.1 := ConjClasses.mk_eq_mk_iff_isConj.mp hr.symm
  rcases isConj_iff.1 hsr with ⟨a, ha⟩
  -- The chosen representative is conjugate to the original one, so the virtual character takes
  -- the same value on both regular representatives.
  simpa [r, ha] using
    (virtualModularCharacter_conj (p := p) (lift := lift) x s.1 a s.2)

/-- Helper for Theorem 18-18.2-1: on an honest representation class, the descended virtual modular
character agrees with the descended Brauer character. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_class_ofSubtype
    (lift : PrimeToPRoot p k → A) (E : FDRep k G)
    (s : { g : G // IsPRegular p g }) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift [E]₀
        (PRegularConjClass.ofSubtype (G := G) p s) =
      modularCharacter lift E.ρ s := by
  -- Route correction: this is the Grothendieck-level owner needed for the source proof, so the
  -- evaluation identity is exposed before the density and decomposition steps.
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
  exact congrFun (virtualModularCharacter_class lift E) s

/-- Helper for Theorem 18-18.2-1: on the class of an honest representation, the descended virtual
modular character agrees as a function on `PRegularConjClass G p` with the descended Brauer
character. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift [E]₀ =
      FDRep.modularCharacterOnPRegularConjClass (p := p) E lift := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate both descended owners at the chosen representative of the regular conjugacy class.
  rw [← hs]
  rw [virtualModularCharacterOnPRegularConjClass_class_ofSubtype,
    FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  rfl

end VirtualModularCharactersOnPRegularConjClass

section PRegularLinearRelations

variable {A : Type x} [Semiring A]

/-- Helper for Theorem 18-18.2-1: evaluating a finite-support relation among descended Brauer
characters at a chosen `p`-regular representative recovers the corresponding scalar relation among
the ordinary modular-character values. -/
theorem pointwise_zero_of_sum_smul_modularCharacterOnPRegularConjClass_eq_zero
    {ι : Type x}
    (lift : PrimeToPRoot p k → A)
    (E : ι → FDRep k G)
    (a : ι →₀ A)
    (hzero :
      (Finset.sum a.support
          fun i ↦ a i • FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift) =
        (0 : PRegularConjClass G p → A))
    (s : { g : G // IsPRegular p g }) :
    (Finset.sum a.support fun i ↦ a i * (φ[lift]((E i).ρ) s)) = 0 := by
  -- Evaluate the functional relation at `PRegularConjClass.ofSubtype p s`, then rewrite every
  -- descended Brauer character back to the original modular character on the chosen representative.
  have hEval := congrFun hzero (PRegularConjClass.ofSubtype (G := G) p s)
  simpa [FDRep.modularCharacterOnPRegularConjClass_ofSubtype] using hEval

end PRegularLinearRelations

section DecompositionBridgeOnGenerators

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Theorem 18-18.2-1: on the class of a genuine `K[G]`-representation, the
decomposition map followed by the virtual modular character agrees on the `p`-regular subtype with
the ordinary character upstairs. -/
theorem virtualModularCharacter_decomposition_finiteRepClass_eq_character_restriction
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (E : FDRep K G)
    (L : StableLattice A E.ρ) :
    virtualModularCharacter (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) [E]₀) =
      E.character ∘ Subtype.val := by
  funext s
  -- Route correction: first compare the generator class obtained from stable-lattice reduction,
  -- then apply LinearRepresentations_Serre_1977's source clause `(6)` at the chosen regular element.
  rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) E L,
    virtualModularCharacter_class]
  simpa using
    (modularCharacter_stableLatticeReduction_eq_character_restriction
      (p := p) (A := A) (K := K) (G := G) lift E.ρ L s)

/-- Helper for Theorem 18-18.2-1: after descending to `PRegularConjClass G p`, the decomposition
map sends a genuine `K[G]`-representation class to its restricted ordinary character. -/
@[simp] theorem
    virtualModularCharacterOnPRegularConjClass_decomposition_finiteRepClass_eq
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (E : FDRep K G)
    (L : StableLattice A E.ρ) :
    virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
        ((decompositionHom A K G) [E]₀) =
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) E := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended bridge at the chosen representative and rewrite both owners there.
  rw [← hs]
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype,
    virtualModularCharacter_decomposition_finiteRepClass_eq_character_restriction
      (p := p) (A := A) (K := K) (G := G) lift E L,
    FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype]
  rfl

end DecompositionBridgeOnGenerators

section VirtualCharacterSpan

variable {K : Type u} [Field K]

/-- Helper for Theorem 18-18.2-1: the descended virtual modular character of any virtual class
lies in the span of the Brauer characters of a complete irreducible family. -/
private theorem virtualModularCharacterOnPRegularConjClass_mem_span_of_complete_family
    (lift : PrimeToPRoot p k → K)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (x : R₀[k](G)) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift x ∈
      Submodule.span K
        (Set.range fun i ↦ FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift) := by
  classical
  let b := simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete
  let coeffs : ι →₀ ℤ := b.repr x
  have hx :
      virtualModularCharacterOnPRegularConjClass (p := p) lift x =
        coeffs.support.sum fun i ↦ ((coeffs i : ℤ) : K) •
          virtualModularCharacterOnPRegularConjClass (p := p) lift (b i) := by
    -- Route correction: expand `x` through the finitely supported coefficient family `b.repr x`,
    -- so the proof uses only the support of this single vector and not a global finite index type.
    calc
      virtualModularCharacterOnPRegularConjClass (p := p) lift x
          = virtualModularCharacterOnPRegularConjClass (p := p) lift
              (Finsupp.linearCombination ℤ b coeffs) := by
                rw [b.linearCombination_repr]
      _ = coeffs.support.sum fun i ↦
            coeffs i • virtualModularCharacterOnPRegularConjClass (p := p) lift (b i) := by
            rw [Finsupp.linearCombination_apply, Finsupp.sum]
            simp [map_sum, map_zsmul]
      _ = coeffs.support.sum fun i ↦
            ((coeffs i : ℤ) : K) • virtualModularCharacterOnPRegularConjClass (p := p) lift (b i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← Int.cast_smul_eq_zsmul K]
  -- Expand the virtual class in the simple-class basis and map that expansion through the
  -- descended virtual modular character.
  rw [hx]
  refine Submodule.sum_mem _ ?_
  intro i hi
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ?_
  refine Set.mem_range.mpr ⟨i, ?_⟩
  -- Each simple-class basis vector maps to the corresponding descended Brauer character.
  rw [show b i = [E i]₀ by simp [b, simple_finiteRep_classes_basis_of_complete_family_apply]]
  simpa using
    (virtualModularCharacterOnPRegularConjClass_class (p := p) (lift := lift) (E := E i))

end VirtualCharacterSpan

section OrdinaryCharacterSpan

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Theorem 18-18.2-1: every restricted ordinary character coming from the fraction
field belongs to the span of the irreducible Brauer characters of a complete modular family. -/
private theorem ordinaryCharacterOnPRegularConjClass_mem_span_of_complete_family_local
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (X : FDRep K G) :
    FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X ∈
      Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) := by
  let L : StableLattice A X.ρ := Classical.choice (exists_stableLattice A X.ρ)
  have hmem :
      virtualModularCharacterOnPRegularConjClass (p := p) (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom A K G) [X]₀) ∈
        Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) :=
    virtualModularCharacterOnPRegularConjClass_mem_span_of_complete_family
      (p := p) (k := IsLocalRing.ResidueField A) (K := K)
      (lift := PrimeToPRoot.toFieldLift lift) E hE_pairwise hE_complete
      ((decompositionHom A K G) [X]₀)
  -- Rewrite the descended decomposition class of `[X]₀` by the generator-level comparison.
  rw [virtualModularCharacterOnPRegularConjClass_decomposition_finiteRepClass_eq
    (p := p) (A := A) (K := K) (G := G) lift X L] at hmem
  exact hmem

end OrdinaryCharacterSpan

section HonestCharacterRestrictionSpan

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Theorem 18-18.2-1: the descended lift of a class function is independent of the
chosen proof that the function is constant on conjugacy classes. -/
private theorem pRegularLift_eq_of_isClassFunction
    {f : G → K}
    (hf₁ hf₂ : _root_.IsClassFunction f) :
    IsClassFunction.pRegularLift (G := G) (p := p) hf₁ =
      IsClassFunction.pRegularLift (G := G) (p := p) hf₂ := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate both descended lifts at the same regular representative.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hf₁ c = f s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf₁ s)
    _ = IsClassFunction.pRegularLift (G := G) (p := p) hf₂ c := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf₂ s).symm

/-- Helper for Theorem 18-18.2-1: descending an ordinary character through `pRegularLift`
recovers the restricted ordinary character owner. -/
private theorem pRegularLift_character_eq_ordinaryCharacterOnPRegularConjClass
    (X : FDRep K G)
    (hclass : _root_.IsClassFunction X.character) :
    IsClassFunction.pRegularLift (G := G) (p := p) hclass =
      FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Both descended owners evaluate to the same ordinary character value on a regular
  -- representative.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hclass c = X.character s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hclass s)
    _ = FDRep.ordinaryCharacterOnPRegularConjClass (p := p) X c := by
      simpa [hs] using
        (FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype (p := p) X s).symm

/-- Helper for Theorem 18-18.2-1: descending the zero class function gives the zero function on
`PRegularConjClass G p`. -/
private theorem pRegularLift_zero
    (hzero : _root_.IsClassFunction (0 : G → K)) :
    IsClassFunction.pRegularLift (G := G) (p := p) hzero = 0 := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- The descended zero class function still evaluates to zero on every regular representative.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hzero c = (0 : G → K) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hzero s)
    _ = 0 := by
      simp

/-- Helper for Theorem 18-18.2-1: `pRegularLift` is additive on class functions. -/
private theorem pRegularLift_add
    {f g : G → K}
    (hf : _root_.IsClassFunction f)
    (hg : _root_.IsClassFunction g)
    (hfg : _root_.IsClassFunction (f + g)) :
    IsClassFunction.pRegularLift (G := G) (p := p) hfg =
      IsClassFunction.pRegularLift (G := G) (p := p) hf +
        IsClassFunction.pRegularLift (G := G) (p := p) hg := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended sum on one representative and reduce to pointwise addition upstairs.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hfg c = (f + g) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hfg s)
    _ = f s + g s := by
      rfl
    _ =
        (IsClassFunction.pRegularLift (G := G) (p := p) hf +
          IsClassFunction.pRegularLift (G := G) (p := p) hg) c := by
      simpa [Pi.add_apply, hs] using
        congrArg₂ (· + ·)
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf s).symm
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hg s).symm

/-- Helper for Theorem 18-18.2-1: `pRegularLift` commutes with scalar multiplication on class
functions. -/
private theorem pRegularLift_smul
    (a : K)
    {f : G → K}
    (hf : _root_.IsClassFunction f)
    (haf : _root_.IsClassFunction (a • f)) :
    IsClassFunction.pRegularLift (G := G) (p := p) haf =
      a • IsClassFunction.pRegularLift (G := G) (p := p) hf := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended scalar multiple on one representative and reduce to pointwise scalar
  -- multiplication upstairs.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) haf c = (a • f) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) haf s)
    _ = a * f s := by
      rfl
    _ = (a • IsClassFunction.pRegularLift (G := G) (p := p) hf) c := by
      simpa [Pi.smul_apply, hs] using
        congrArg (a • ·)
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf s).symm

/-- Helper for Theorem 18-18.2-1: once a class function on `G` is known to lie in the span of
honest ordinary characters, its restriction to `PRegularConjClass G p` lies in the Brauer-character
span of a complete irreducible modular family. -/
theorem pRegularLift_mem_span_of_complete_family_local
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    {f : G → K}
    (hfClass : _root_.IsClassFunction f)
    (hf :
      f ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }) :
    IsClassFunction.pRegularLift (G := G) (p := p) hfClass ∈
      Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) := by
  let S : Set (G → K) := { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }
  let T :=
    Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift))
  have hspan :
      ∀ {g : G → K} (hg : g ∈ Submodule.span K S),
          ∃ hgClass : _root_.IsClassFunction g,
            IsClassFunction.pRegularLift (G := G) (p := p) hgClass ∈ T := by
    intro g hg
    refine
      Submodule.span_induction
        (s := S)
        (p := fun g _ ↦
          ∃ hgClass : _root_.IsClassFunction g,
            IsClassFunction.pRegularLift (G := G) (p := p) hgClass ∈ T)
        ?_ ?_ ?_ ?_ hg
    · intro ψ hψ
      rcases hψ with ⟨X, rfl⟩
      have hclass : _root_.IsClassFunction X.character := by
        refine ⟨?_⟩
        intro s t hst
        rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
        have hconj : t = (a : G) * s * (a : G)⁻¹ := by
          apply (eq_mul_inv_iff_mul_eq).2
          simpa [mul_assoc] using ha.eq.symm
        rw [hconj]
        exact (X.char_conj s a).symm
      refine ⟨hclass, ?_⟩
      rw [pRegularLift_character_eq_ordinaryCharacterOnPRegularConjClass
        (G := G) (p := p) X hclass]
      exact ordinaryCharacterOnPRegularConjClass_mem_span_of_complete_family_local
        (p := p) (A := A) (K := K) (G := G) lift E hE_pairwise hE_complete X
    · have hzeroClass : _root_.IsClassFunction (0 : G → K) := ⟨by intro s t hst; rfl⟩
      refine ⟨hzeroClass, ?_⟩
      rw [pRegularLift_zero (G := G) (p := p) (K := K) hzeroClass]
      exact Submodule.zero_mem T
    · intro g h hg_mem hh_mem ihg ihh
      rcases ihg with ⟨hgClass, hg_span⟩
      rcases ihh with ⟨hhClass, hh_span⟩
      have hsumClass : _root_.IsClassFunction (g + h) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg₂ (· + ·) (hgClass.eq_of_mk_eq hst) (hhClass.eq_of_mk_eq hst)
      refine ⟨hsumClass, ?_⟩
      rw [pRegularLift_add (G := G) (p := p) (K := K) hgClass hhClass hsumClass]
      exact Submodule.add_mem T hg_span hh_span
    · intro a g hg_mem ihg
      rcases ihg with ⟨hgClass, hg_span⟩
      have hsmulClass : _root_.IsClassFunction (a • g) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg (a • ·) (hgClass.eq_of_mk_eq hst)
      refine ⟨hsmulClass, ?_⟩
      rw [pRegularLift_smul (G := G) (p := p) (K := K) a hgClass hsmulClass]
      exact Submodule.smul_mem T a hg_span
  rcases hspan hf with ⟨hfClass', hf_mem⟩
  -- The restriction owner depends only on the underlying class function, so either class-function
  -- witness yields the same descended regular function.
  rw [pRegularLift_eq_of_isClassFunction (G := G) (p := p) (K := K) hfClass hfClass']
  exact hf_mem

end HonestCharacterRestrictionSpan

section RegularClassFunctionExtension

variable {K : Type u} [Field K]

/-- Helper for Theorem 18-18.2-1: extend a function on `PRegularConjClass G p` to all of `G` by
LinearRepresentations_Serre_1977's source route, namely by keeping the given value on `p`-regular elements and sending the
non-regular locus to `0`. -/
def regularClassFunctionExtension
    (f : PRegularConjClass G p → K) : G → K :=
  fun g ↦
    if hg : IsPRegular p g then
      f (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
    else
      0

/-- Helper for Theorem 18-18.2-1: on a chosen `p`-regular representative, LinearRepresentations_Serre_1977's extension
recovers the original regular class function. -/
@[simp] theorem regularClassFunctionExtension_ofSubtype
    (f : PRegularConjClass G p → K)
    (s : { g : G // IsPRegular p g }) :
    regularClassFunctionExtension (G := G) (p := p) f s.1 =
      f (PRegularConjClass.ofSubtype (G := G) p s) := by
  -- The extension uses the original value on the regular branch.
  simp [regularClassFunctionExtension, s.2]

/-- Helper for Theorem 18-18.2-1: LinearRepresentations_Serre_1977's extension vanishes on the non-regular locus. -/
@[simp] theorem regularClassFunctionExtension_eq_zero_of_not_isPRegular
    (f : PRegularConjClass G p → K)
    {g : G} (hg : ¬ IsPRegular p g) :
    regularClassFunctionExtension (G := G) (p := p) f g = 0 := by
  -- The non-regular branch of the extension is definitionally zero.
  simp [regularClassFunctionExtension, hg]

/-- Helper for Theorem 18-18.2-1: LinearRepresentations_Serre_1977's zero-extension is still a class function on `G`. -/
theorem regularClassFunctionExtension_isClassFunction
    (f : PRegularConjClass G p → K) :
    _root_.IsClassFunction (regularClassFunctionExtension (G := G) (p := p) f) := by
  refine ⟨?_⟩
  intro s t hst
  rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
  have hconj : t = (a : G) * s * (a : G)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).2
    simpa [mul_assoc] using ha.eq.symm
  rw [hconj]
  by_cases hs : IsPRegular p s
  · have hts : IsPRegular p ((a : G) * s * (a : G)⁻¹) :=
      isPRegular_conj p s (a : G) hs
    have hclass :
        PRegularConjClass.ofSubtype (G := G) p ⟨(a : G) * s * (a : G)⁻¹, hts⟩ =
          PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩ := by
      -- Both representatives define the same regular conjugacy class.
      apply Subtype.ext
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
        isConj_iff.2 ⟨(a : G)⁻¹, by simp [mul_assoc]⟩
    -- On the regular branch, equality reduces to equality in the quotient owner.
    rw [regularClassFunctionExtension, regularClassFunctionExtension, dif_pos hs, dif_pos hts]
    exact congrArg f hclass.symm
  · have hts : ¬ IsPRegular p ((a : G) * s * (a : G)⁻¹) := by
      intro hreg
      exact hs <| by
        simpa [mul_assoc] using
          (isPRegular_conj p ((a : G) * s * (a : G)⁻¹) ((a : G)⁻¹) hreg)
    -- On the singular branch, both values are definitionally zero.
    simp [regularClassFunctionExtension, hs, hts]

/-- Helper for Theorem 18-18.2-1: raising a `p`-regular element to a power coming from any
subgroup of exponent units preserves `p`-regularity. This isolates the only arithmetic fact needed
to compare LinearRepresentations_Serre_1977's zero-extension along power orbits. -/
private theorem isPRegular_pow_gamma_local
    {Γ : Subgroup (ZMod (Monoid.exponent G))ˣ}
    (t : Γ) {g : G} (hg : IsPRegular p g) :
    IsPRegular p (g ^ t) := by
  have hcop :
      Nat.Coprime (orderOf g)
        (galoisPowerExponentUnit (G := G) (t : (ZMod (Monoid.exponent G))ˣ)) :=
    (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent g)
      (ZMod.val_coe_unit_coprime (t : (ZMod (Monoid.exponent G))ˣ))).symm
  -- The `Γ`-action uses a unit exponent modulo the group exponent, so it preserves the
  -- prime-to-`p` part of the order.
  rw [pow_subgroup_eq_pow_nat (G := G) (s := g) (t := t)]
  simpa [IsPRegular, hcop.orderOf_pow] using hg

/-- Helper for Theorem 18-18.2-1: if the zero-extension of `f` is constant on the `Γ`-power
classes of `G`, then `f` is already invariant under the induced `Γ`-power action on the
`p`-regular locus. This records the exact extra hypothesis hidden inside any quotient-basis route
through `GaloisPowerClass Γ`. -/
theorem pregular_pow_invariant_of_regularClassFunctionExtension_isConstantOnGaloisPowerClasses_local
    {Γ : Subgroup (ZMod (Monoid.exponent G))ˣ}
    (f : PRegularConjClass G p → K)
    (hconst :
      IsConstantOnGaloisPowerClasses Γ
        (regularClassFunctionExtension (G := G) (p := p) f)) :
    ∀ s : {g : G // IsPRegular p g}, ∀ t : Γ,
      f (PRegularConjClass.ofSubtype (G := G) p
          ⟨s.1 ^ t, isPRegular_pow_gamma_local (G := G) (p := p) (Γ := Γ) t s.2⟩) =
        f (PRegularConjClass.ofSubtype (G := G) p s) := by
  intro s t
  have hsPow : IsPRegular p (s.1 ^ t) :=
    isPRegular_pow_gamma_local (G := G) (p := p) (Γ := Γ) t s.2
  have hpow :=
    (isConstantOnGaloisPowerClasses_iff_forall_pow_eq
      (ΓK := Γ)
      (f := regularClassFunctionExtension (G := G) (p := p) f)
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)).1
      hconst s.1 t
  -- On the regular branch, `regularClassFunctionExtension` just re-evaluates `f`, so
  -- `Γ`-constancy upstairs becomes the explicit power-invariance statement downstairs.
  calc
    f (PRegularConjClass.ofSubtype (G := G) p ⟨s.1 ^ t, hsPow⟩) =
        regularClassFunctionExtension (G := G) (p := p) f (s.1 ^ t) := by
          simpa using
            (regularClassFunctionExtension_ofSubtype (G := G) (p := p) f ⟨s.1 ^ t, hsPow⟩).symm
    _ = regularClassFunctionExtension (G := G) (p := p) f s.1 := hpow.symm
    _ = f (PRegularConjClass.ofSubtype (G := G) p s) := by
          simpa using
            regularClassFunctionExtension_ofSubtype (G := G) (p := p) f s

/-- Helper for Theorem 18-18.2-1: conversely, LinearRepresentations_Serre_1977's zero-extension is constant on the
`Γ`-power classes of `G` whenever the original regular class function is invariant under the
induced `Γ`-power action on `p`-regular representatives. This turns an implicit quotient-basis
assumption into an explicit checkable condition. -/
theorem regularClassFunctionExtension_isConstantOnGaloisPowerClasses_of_pregular_pow_invariant_local
    {Γ : Subgroup (ZMod (Monoid.exponent G))ˣ}
    (f : PRegularConjClass G p → K)
    (hfpow :
      ∀ s : {g : G // IsPRegular p g}, ∀ t : Γ,
        f (PRegularConjClass.ofSubtype (G := G) p
            ⟨s.1 ^ t, isPRegular_pow_gamma_local (G := G) (p := p) (Γ := Γ) t s.2⟩) =
          f (PRegularConjClass.ofSubtype (G := G) p s)) :
    IsConstantOnGaloisPowerClasses Γ
      (regularClassFunctionExtension (G := G) (p := p) f) := by
  refine
    (isConstantOnGaloisPowerClasses_iff_forall_pow_eq
      (ΓK := Γ)
      (f := regularClassFunctionExtension (G := G) (p := p) f)
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)).2 ?_
  intro g t
  by_cases hg : IsPRegular p g
  · let s : {g : G // IsPRegular p g} := ⟨g, hg⟩
    have hgpow : IsPRegular p (g ^ t) :=
      isPRegular_pow_gamma_local (G := G) (p := p) (Γ := Γ) t hg
    -- On the regular branch, the assumed power-invariance of `f` gives the required equality
    -- upstairs for the zero-extension.
    calc
      regularClassFunctionExtension (G := G) (p := p) f g =
          f (PRegularConjClass.ofSubtype (G := G) p s) := by
            simpa [s] using regularClassFunctionExtension_ofSubtype (G := G) (p := p) f s
      _ =
          f (PRegularConjClass.ofSubtype (G := G) p
            ⟨g ^ t, hgpow⟩) := by
              simpa [s, pow_subgroup_eq_pow_nat (G := G) (s := g) (t := t)] using
                (hfpow s t).symm
      _ = regularClassFunctionExtension (G := G) (p := p) f (g ^ t) := by
            simpa using
              (regularClassFunctionExtension_ofSubtype (G := G) (p := p) f ⟨g ^ t, hgpow⟩).symm
  · have hgpow_not : ¬ IsPRegular p (g ^ t) := by
      intro hgpow
      have hcop :
          Nat.Coprime (orderOf g)
            (galoisPowerExponentUnit (G := G) (t : (ZMod (Monoid.exponent G))ˣ)) :=
        (Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent g)
          (ZMod.val_coe_unit_coprime (t : (ZMod (Monoid.exponent G))ˣ))).symm
      have hg' : IsPRegular p g := by
        -- Because the power exponent is a unit modulo the group exponent, `orderOf (g ^ t) =
        -- orderOf g`, so non-regularity is also preserved backwards.
        rw [pow_subgroup_eq_pow_nat (G := G) (s := g) (t := t)] at hgpow
        simpa [IsPRegular, hcop.orderOf_pow] using hgpow
      exact hg hg'
    -- On the singular branch, both values are definitionally zero.
    rw [regularClassFunctionExtension_eq_zero_of_not_isPRegular (G := G) (p := p) f hg,
      regularClassFunctionExtension_eq_zero_of_not_isPRegular (G := G) (p := p) f hgpow_not]

/-- Helper for Theorem 18-18.2-1: package LinearRepresentations_Serre_1977's zero-extension as a bundled class function on
`G`. -/
def regularClassFunctionExtensionClassFunction
    (f : PRegularConjClass G p → K) : classFunctionSubmodule K G :=
  ⟨regularClassFunctionExtension (G := G) (p := p) f,
    regularClassFunctionExtension_isClassFunction (G := G) (p := p) f⟩

/-- Helper for Theorem 18-18.2-1: coercing the bundled zero-extension back to a function recovers
LinearRepresentations_Serre_1977's original extension on `G`. -/
@[simp] theorem regularClassFunctionExtensionClassFunction_coe
    (f : PRegularConjClass G p → K) :
    ((regularClassFunctionExtensionClassFunction (G := G) (p := p) f :
        classFunctionSubmodule K G) : G → K) =
      regularClassFunctionExtension (G := G) (p := p) f :=
  rfl

/-- Helper for Theorem 18-18.2-1: descending LinearRepresentations_Serre_1977's extension back to
`PRegularConjClass G p` recovers the original function. -/
@[simp] theorem pRegularLift_regularClassFunctionExtension
    (f : PRegularConjClass G p → K) :
    IsClassFunction.pRegularLift
        (G := G) (p := p)
        (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) =
      f := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended extension on the chosen regular representative.
  rw [← hs]
  rw [IsClassFunction.pRegularLift_ofSubtype
    (G := G) (p := p)
    (f := regularClassFunctionExtension (G := G) (p := p) f)
    (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) s]
  simpa using regularClassFunctionExtension_ofSubtype (G := G) (p := p) f s

end RegularClassFunctionExtension

end

end Representation
