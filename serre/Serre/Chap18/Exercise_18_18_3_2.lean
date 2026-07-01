import Mathlib
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap14.Corollary_14_14_3_3
import Serre.Chap14.Corollary_14_14_4_4
import Serre.Chap15.Definition_15_15_1_1
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap16.Corollary_16_16_1_6
import Serre.Chap16.Corollary_16_16_1_8
import Serre.Chap16.Corollary_16_16_1_8.Index
import Serre.Chap16.Corollary_16_16_1_8_CartanGramSupport
import Serre.Chap16.Theorem_16_16_1_2
import Serre.Chap16.Theorem_16_16_2_1
import Serre.Chap18.Definition_18_18_1_1
import Serre.Chap18.Proposition_18_18_1_2
import Serre.Chap18.Remark_18_18_1_3
import Serre.Chap18.Corollary_18_18_2_5
import Serre.Chap18.Theorem_18_18_3_1
import Serre.Chap18.Exercise_18_18_3_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section LocalExercise1829Fallback

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Helper for Exercise 18-18.3-2: local fallback export of the Exercise `18-18.2-9`
coefficient-ring Brauer basis API through the already imported semiring owner from
Theorem `18-18.2-1`. -/
def exercise_18_18_2_9_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  -- Route correction: the source-faithful owner should be the earlier Exercise `18-18.2-9`
  -- coefficient-ring basis, but the compiled environment currently lacks the expected canonical
  -- semiring owner `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring`.
  -- TODO: restore that earlier API owner (or a compiled local equivalent) and replace this local
  -- wrapper by the canonical basis theorem exactly as in `Serre/Chap18/Exercise_18_18_2_9.lean`.
  sorry

/-- Helper for Exercise 18-18.3-2: evaluation rule for the local Exercise `18-18.2-9` Brauer
basis owner. -/
@[simp] theorem exercise_18_18_2_9_irreducible_modular_characters_basis_apply
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) (A := A) lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift := by
  -- TODO: once the missing Exercise `18-18.2-9` basis owner is restored, this becomes the
  -- corresponding `[simp]` evaluation theorem by unfolding that canonical wrapper.
  sorry

end LocalExercise1829Fallback

section LocalChapter18Comparisons

variable {p : ℕ}
variable {B : Type u} [CommRing B] [IsLocalRing B]
variable {K : Type u} [Field K] [Algebra B K] [IsFractionRing B K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain B] [IsDiscreteValuationRing B]
variable [IsAlgClosed (IsLocalRing.ResidueField B)] [CharP (IsLocalRing.ResidueField B) p]

local notation "k" => IsLocalRing.ResidueField B

/-- Helper for Exercise 18-18.3-2: temporary local decomposition-compatibility bridge for virtual
modular characters. -/
theorem virtualModularCharacter_decomposition_eq_character_restriction
    (lift : PrimeToPRoot p k →* Kˣ) (y : R₀[K](G)) :
    _root_.Representation.virtualModularCharacter
        (PrimeToPRoot.toFieldLift lift) ((decompositionHom B K G) y) =
      (finiteRepGrothendieckCharacter K G y : G → K) ∘ Subtype.val := by
  -- Route correction: descend Serre's stable-lattice comparison through the Grothendieck quotient,
  -- matching the Chapter `18.3.1` regular-branch proof route.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is sent to the zero character on both sides.
    ext s
    simp
  · intro E
    obtain ⟨L⟩ := Representation.exists_stableLattice B E.ρ
    -- On a generator `[E]₀`, evaluate `decompositionHom` using a stable lattice and apply the
    -- source comparison between its reduced modular character and the ordinary character upstairs.
    ext s
    change
      (_root_.Representation.virtualModularCharacter (PrimeToPRoot.toFieldLift lift)
          ((decompositionHom B K G) [E]₀)) s =
        ((finiteRepGrothendieckCharacter K G [E]₀ : R[K](G)) : G → K) s.1
    rw [decompositionHom_finiteRepClass_eq (A := B) (K := K) (G := G) E L,
      _root_.Representation.virtualModularCharacter_class, finiteRepGrothendieckCharacter_class]
    simpa using
      (modularCharacter_stableLatticeReduction_eq_character_restriction
        (p := p) (A := B) (K := K) (G := G) lift E.ρ L s)
  · intro a ha
    -- Additive functoriality transports the established equality through negation.
    ext s
    simpa [Function.comp, map_neg] using congrArg Neg.neg (congrFun ha s)
  · intro a b ha hb
    -- Additive functoriality transports the established equality through sums.
    ext s
    simpa [Function.comp, map_add] using congrArg₂ HAdd.hAdd (congrFun ha s) (congrFun hb s)

end LocalChapter18Comparisons

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

/-
Domain-style sampling for Exercise `18-18.3-2`:
* primary domain: modular representation theory of finite groups, combining the projective
  scalar-extension owner `projectiveGrothendieckScalarExtensionHom A K`, the Chapter `16`
  Grothendieck-character owner `finiteRepGrothendieckCharacter`, the Chapter `12`
  scalar-extension owner `A ⊗R[K](G)`, and the Cartan owners `cartanCokernel` and
  `cartanMatrix`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `characterRingOverFieldAlgebraScalarExtension`,
  `cartanCokernel`,
  `cartanMatrix`.

Layer triage:
* source-facing: the projective-character span inside `A ⊗R[K](G)` and the invariant-factor
  formulas indexed by `p`-regular conjugacy-class representatives;
* core/canonical: the owner declarations
  `projectiveGrothendieckScalarExtensionHom A K`, `finiteRepGrothendieckCharacter K G`,
  `A ⊗R[K](G)`, `cartanCokernel`, and `cartanMatrix`;
* bridge/view: the codomain restriction from `R₀[K](G)` to `A ⊗R[K](G)` obtained from
  `finiteRepGrothendieckCharacter K G` and the canonical inclusion `R[K](G) ⊆ A ⊗R[K](G)`.

Ordinary-character regime check:
* the source-facing span in part `(1)` lives in the characteristic-zero ordinary-character setting
  used nearby in Chapter `18`;
* its primitive definition inside `A ⊗R[K](G)` needs only `[CharZero K]`, but the membership
  criterion below must stay in the standard large-field regime
  `[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, matching the Chapter `16` image criterion and
  neighboring Theorem `18-18.3-1`.
-/
local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance finiteGroupFintype_projectiveCriterion : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 18-18.3-2: restricting the ordinary character of a virtual class
`y : R₀[K](G)` to a chosen `p`-regular representative recovers the virtual modular character of
its decomposition class at that representative. -/
theorem regularRestriction_finiteRepGrothendieckCharacter_eq_virtualModularCharacterOnPRegular
    (lift : PrimeToPRoot p k →* Kˣ) (y : R₀[K](G))
    (s : { g : G // IsPRegular p g }) :
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      ⟨finiteRepGrothendieckCharacter K G y,
        mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
          (finiteRepGrothendieckCharacter K G y).property⟩
      (PRegularConjClass.ofSubtype (G := G) p s) =
      _root_.Representation.virtualModularCharacter
        (PrimeToPRoot.toFieldLift lift) ((decompositionHom A K G) y) s := by
  -- Evaluate the regular restriction at the chosen representative and then invoke the virtual
  -- modular-character comparison on the regular locus.
  rw [regularRestriction_ofSubtype (p := p) (A := A) (K := K) (G := G)]
  simpa using (congrFun
    (virtualModularCharacter_decomposition_eq_character_restriction
      (p := p) (B := A) (K := K) (G := G) lift y) s).symm

/-- Helper for Exercise 18-18.3-2: the sum of two projective Grothendieck generator classes is
again represented by an actual finite projective module. -/
private theorem exists_projective_class_sum_rep
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule R G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule R G, [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  -- Compress the sum of two projective generators into the class of the product module.
  let W0 : ModuleCat (MonoidAlgebra R G) := ModuleCat.of (MonoidAlgebra R G) (P.V × Q.V)
  have hfinite : Module.Finite (MonoidAlgebra R G) W0 := by
    change Module.Finite (MonoidAlgebra R G) (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat (MonoidAlgebra R G) := ⟨W0, hfinite⟩
  have hproj : Module.Projective (MonoidAlgebra R G) Wfg := by
    change Module.Projective (MonoidAlgebra R G) (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule R G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl (MonoidAlgebra R G) P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd (MonoidAlgebra R G) P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst (MonoidAlgebra R G) P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr (MonoidAlgebra R G) P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule R G) :=
    ShortComplex.mk f g (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.snd (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inl (MonoidAlgebra R G) P.V Q.V) x) =
          0
      simp)
  have hsplit : T.Splitting := by
    -- The standard inclusions and projections split the product short complex.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.fst (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inl (MonoidAlgebra R G) P.V Q.V) x) =
          x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change
        (LinearMap.snd (MonoidAlgebra R G) P.V Q.V)
            ((LinearMap.inr (MonoidAlgebra R G) P.V Q.V) x) =
          x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl (MonoidAlgebra R G) P.V Q.V
              ((LinearMap.fst (MonoidAlgebra R G) P.V Q.V) (x, y)) +
            LinearMap.inr (MonoidAlgebra R G) P.V Q.V
              ((LinearMap.snd (MonoidAlgebra R G) P.V Q.V) (x, y))) =
          (x, y)
      simp
  -- Translate the split short exact sequence into the Grothendieck relation.
  refine ⟨W, ?_⟩
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := R) (G := G) T hsplit.shortExact

/-- Helper for Exercise 18-18.3-2: every class in the projective Grothendieck group is a
difference of two actual projective generator classes. -/
private theorem exists_projective_class_difference_rep
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : Type u} [Group G] [Finite G]
    (x : P₀[R](G)) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule R G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  -- Flatten the free-abelian presentation of `P₀[R](G)` to a single difference of generators.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule R G),
        (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    simp
  · intro P
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := R) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, hW⟩ := exists_projective_class_sum_rep (P := P) (Q := P')
    obtain ⟨Z, hZ⟩ := exists_projective_class_sum_rep (P := Q) (Q := Q')
    refine ⟨W, Z, ?_⟩
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) (a + b) =
          QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) a +
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) b := by
              rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 18-18.3-2: Serre's base-change owner sends a difference of actual
projective generator classes to the corresponding difference of scalar-extension classes. -/
private theorem projectiveGrothendieckBaseChangeHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckBaseChangeHom K ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.scalarExtension K]₀ - [R.scalarExtension K]₀ := by
  -- Expand the additive map on a difference and evaluate it on each actual projective generator.
  rw [map_sub, projectiveGrothendieckBaseChangeHom_projectiveClass_eq,
    projectiveGrothendieckBaseChangeHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: reduction sends a difference of actual lifted projective
generator classes to the corresponding difference of residue-field generator classes. -/
private theorem projectiveGrothendieckReductionHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckReductionHom (A := A) (G := G) ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.residueFieldReduction]ₚ₀ - [R.residueFieldReduction]ₚ₀ := by
  -- Expand the additive reduction map on a difference and evaluate it on each actual projective
  -- generator.
  rw [map_sub, projectiveGrothendieckReductionHom_projectiveClass_eq,
    projectiveGrothendieckReductionHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: the Cartan homomorphism sends a difference of projective
generator classes to the corresponding difference of finite-representation classes. -/
private theorem cartanHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule k G) :
    cartanHom k G ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.toFiniteRep]₀ - [R.toFiniteRep]₀ := by
  -- Expand the additive map on a difference and then read it on each projective generator class.
  rw [map_sub, cartanHom_projectiveClass_eq, cartanHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: applying the Cartan map to the reduction classes of two
lifted projectives gives the difference of the corresponding reduced finite-representation
classes. -/
private theorem cartanHom_sub_residueFieldReduction_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule A G) :
    cartanHom k G ([Q.residueFieldReduction]ₚ₀ - [R.residueFieldReduction]ₚ₀) =
      [Q.residueFieldReduction.toFiniteRep]₀ - [R.residueFieldReduction.toFiniteRep]₀ := by
  -- This is just the Cartan difference formula applied after reducing the lifted projectives.
  simpa using
    cartanHom_sub_projectiveClass_eq Q.residueFieldReduction R.residueFieldReduction

/-- Helper for Exercise 18-18.3-2: if a characteristic-zero model of a lifted projective class is
equipped with a stable lattice whose reduction class is the expected residue-field projective,
then the decomposition class of that characteristic-zero model is the Cartan class of the reduced
projective. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (V : FDRep K G)
    (hV : [V]₀ = [Q.scalarExtension K]₀)
    (L : StableLattice A V.ρ)
    (hL : [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- First rewrite the scalar-extension class through the chosen characteristic-zero model `V`.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ = decompositionHom A K G [V]₀ := by
      rw [hV]
    -- Then evaluate `decompositionHom` using the supplied stable lattice `L`.
    _ = [FDRep.of L.reductionRepresentation]₀ :=
      decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L
    -- The remaining input is exactly the promised identification of the reduced lattice.
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := hL
    -- Finally translate the reduced projective class back through the Cartan generator formula.
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
      symm
      simpa using (cartanHom_projectiveClass_eq k G Q.residueFieldReduction)

/-- Helper for Exercise 18-18.3-2: if the literal scalar extension `Q.scalarExtension K` carries
a stable lattice reducing to `Q.residueFieldReduction`, then its decomposition class is the
Cartan class of that reduction. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (L : StableLattice A (Q.scalarExtension K).ρ)
    (hL : [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- Reuse the Chapter `16` support owner packaging the projective-generator case of Serre's
  -- triangle.
  exact
    decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Exercise 18-18.3-2: a projective lift whose reduction class is `[P]ₚ₀` has scalar
extension class is equal to the Cartan image of the reduced finite-representation class. -/
private theorem cartanHom_residueFieldReduction_projectiveClass_eq
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    :
    cartanHom k G [Q.residueFieldReduction]ₚ₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The Cartan homomorphism is defined on projective generators by forgetting to the underlying
  -- finite-dimensional representation.
  simpa using (cartanHom_projectiveClass_eq k G Q.residueFieldReduction)

/-- Helper for Exercise 18-18.3-2: two lifted projective classes satisfying the usual
scalar-extension and reduction identities also satisfy Serre's `c = d ∘ e` triangle on their
Grothendieck difference. -/
private theorem decompositionHom_baseChange_sub_eq_cartan_sub_of_lift_data
    (Q R : FiniteProjectiveGroupAlgebraModule A G)
    (VQ : FDRep K G)
    (hVQ : [VQ]₀ = [Q.scalarExtension K]₀)
    (LQ : StableLattice A VQ.ρ)
    (hLQ : [FDRep.of LQ.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀)
    (VR : FDRep K G)
    (hVR : [VR]₀ = [R.scalarExtension K]₀)
    (LR : StableLattice A VR.ρ)
    (hLR : [FDRep.of LR.reductionRepresentation]₀ = [R.residueFieldReduction.toFiniteRep]₀) :
    decompositionHom A K G
      ((projectiveGrothendieckBaseChangeHom K) ([Q]ₚ₀ - [R]ₚ₀)) =
      cartanHom k G ([Q.residueFieldReduction]ₚ₀ - [R.residueFieldReduction]ₚ₀) := by
  -- Expand both additive maps on the Grothendieck difference of two actual lifted projectives.
  rw [projectiveGrothendieckBaseChangeHom_sub_projectiveClass_eq, map_sub, map_sub]
  -- Each scalar-extension term is converted to the corresponding Cartan class by the lift data.
  rw [decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
      (A := A) (K := K) (G := G) Q VQ hVQ LQ hLQ]
  rw [decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
      (A := A) (K := K) (G := G) R VR hVR LR hLR]

/-- Helper for Exercise 18-18.3-2: once a lifted projective `Q` supplies the scalar-extension and
reduction data for a residue-field projective generator `P`, the generator case of Serre's
`c = d ∘ e` triangle follows formally. -/
private theorem
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_generator_of_lift_data
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (V : FDRep K G)
    (hV : [V]₀ = [Q.scalarExtension K]₀)
    (L : StableLattice A V.ρ)
    (hL : [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀)
    (hscalar :
      (projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀ = [Q.scalarExtension K]₀)
    (hred : [Q.residueFieldReduction]ₚ₀ = [P]ₚ₀) :
    decompositionHom A K G
      ((projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀) =
      cartanHom k G [P]ₚ₀ := by
  -- Rewrite Serre's scalar-extension class through the chosen lifted projective `Q`.
  calc
    decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀) =
        decompositionHom A K G [Q.scalarExtension K]₀ := by
          rw [hscalar]
    -- The previous helper turns the decomposition of that lifted class into its Cartan class.
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ :=
      decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
        (A := A) (K := K) (G := G) Q V hV L hL
    -- The last step is the promised identification of the reduced projective generator.
    _ = cartanHom k G [P]ₚ₀ := by
      rw [hred]

/-- Helper for Exercise 18-18.3-2: the projective-generator case of Serre's `c = d ∘ e`
triangle. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_generator
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    decompositionHom A K G
      ((projectiveGrothendieckScalarExtensionHom A K) [P]ₚ₀) =
    cartanHom k G [P]ₚ₀ := by
  -- Route correction: the Chapter `16` support file already packages the generator case of the
  -- projective triangle, so only specialization to `[P]ₚ₀` remains.
  simpa using
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
      (A := A) (K := K) (G := G) [P]ₚ₀

/-- Helper for Exercise 18-18.3-2: the `c = d ∘ e` compatibility in Serre's `cde` triangle. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
    (x : P₀[k](G)) :
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom A K) x) =
      cartanHom k G x := by
  -- Reuse the additive support theorem directly, keeping the downstream regular-restriction proof
  -- in the same source-faithful route.
  exact
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
      (A := A) (K := K) (G := G) x

/-- Helper for Exercise 18-18.3-2: the regular restriction of a projective scalar-extension
character agrees with the Brauer character of its Cartan image on each chosen `p`-regular
representative. -/
theorem regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegular_cartan
    (lift : PrimeToPRoot p k →* Kˣ) (x : P₀[k](G))
    (s : { g : G // IsPRegular p g }) :
    regularRestriction (p := p) (A := A) (K := K) (G := G)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)
      (PRegularConjClass.ofSubtype (G := G) p s) =
      _root_.Representation.virtualModularCharacter
        (PrimeToPRoot.toFieldLift lift) (cartanHom k G x) s := by
  -- Route correction: once the ordinary/projective scalar-extension character is rewritten as a
  -- Grothendieck character, the remaining comparison is exactly the regular-restriction bridge
  -- followed by the `c = d ∘ e` identity.
  simpa [projectiveCharacterScalarExtension,
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
      (A := A) (K := K) (G := G) x] using
    regularRestriction_finiteRepGrothendieckCharacter_eq_virtualModularCharacterOnPRegular
      (p := p) (A := A) (K := K) (G := G) lift (e x) s

/-- Helper for Exercise 18-18.3-2: the source of a projective envelope of a simple `k[G]`-module
is cyclic, hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero vector, so the image cannot vanish.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the canonical map from `k[G]` is surjective.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 18-18.3-2: every simple finite-dimensional `k[G]`-representation admits a
finite projective envelope in the canonical owner of projective modules. -/
private theorem exists_finite_projectiveEnvelope_of_simple
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    -- Expose the ambient `k[G]`-module structure carried by `τ`.
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity gives irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Move simplicity to the `k[G]`-module owner required by the envelope theorem.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  -- Use the Artinian envelope existence theorem, then repackage the source as a finite projective
  -- `k[G]`-module.
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple
      (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  let f : P.V →ₗ[k[G]] asModule τ.ρ := by
    simpa [P, ρ] using f'.hom
  refine ⟨P, f, ?_⟩
  -- The bundled `ModuleCat` envelope is definitionally the same linear-map envelope on `P.V`.
  simpa [P, ρ, f] using hf'

/-- Helper for Exercise 18-18.3-2: choose a complete simple family together with projective
envelopes for each chosen simple. -/
private theorem exists_complete_simple_family_with_projective_envelopes :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (π : ι → FDRep k G),
      PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π ∧
        ∃ P : ι → FiniteProjectiveGroupAlgebraModule k G,
          ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope := by
  classical
  have hsimple :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support
  rcases hsimple with
    ⟨ι, π, hπ_pairwise, hπ_complete⟩
  have hP_exists :
      ∀ i, ∃ P : FiniteProjectiveGroupAlgebraModule k G,
        ∃ f : P.V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope := by
    intro i
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    -- Use the canonical projective envelope of the chosen simple module indexed by `i`.
    exact exists_finite_projectiveEnvelope_of_simple (τ := π i)
  choose P hP using hP_exists
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  exact ⟨ι, Fintype.ofFinite ι, π, hπ_pairwise, hπ_complete, P, hP⟩

/-- Helper for Exercise 18-18.3-2: the Jacobson-radical quotient of a chosen projective envelope
source is the corresponding simple target. -/
private theorem projectiveEnvelope_jacobson_quotient_linearEquiv_target
    {ι : Type (u + 1)}
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) :
    Nonempty (((P i).V ⧸ Module.jacobson k[G] (P i).V) ≃ₗ[k[G]] asModule (π i).ρ) := by
  letI : Simple (π i) := hπ_complete.isSimple i
  let ρi : Representation k G (π i) := (π i).ρ
  let M : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π i))
  let f : (P i).V →ₗ[k[G]] M := by
    simpa [M, Rep.toModuleMonoidAlgebra] using (Classical.choose (hP_envelope i))
  have hf : f.IsProjectiveEnvelope := by
    simpa [M, Rep.toModuleMonoidAlgebra] using (Classical.choose_spec (hP_envelope i))
  letI : f.IsProjectiveEnvelope := hf
  have hsimple :
      IsSimpleModule k[G] M := by
    have hρi_irred : Representation.IsIrreducible ρi := by
      simpa [ρi] using (FDRep.isIrreducible_of_simple (π i))
    simpa [M, Rep.toModuleMonoidAlgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρi).mp hρi_irred
  letI : IsSimpleModule k[G] M := hsimple
  have hjac_le : Module.jacobson k[G] (P i).V ≤ LinearMap.ker f := by
    -- The simple target has trivial Jacobson radical, so every map from the source radical is
    -- forced to vanish.
    have hcomap :
        Module.jacobson k[G] (P i).V ≤ Submodule.comap f (Module.jacobson k[G] M) :=
      Module.le_comap_jacobson (f := f)
    have hEq : Submodule.comap f (Module.jacobson k[G] M) = LinearMap.ker f := by
      rw [IsSimpleModule.jacobson_eq_bot (R := k[G]) (M := M), LinearMap.ker]
    exact hEq ▸ hcomap
  have hker_le : LinearMap.ker f ≤ Module.jacobson k[G] (P i).V := by
    -- Essentiality of the envelope map puts its kernel inside the Jacobson radical.
    exact hf.toIsEssential.ker_le_jacobson hf.surjective
  have hker : Module.jacobson k[G] (P i).V = LinearMap.ker f := le_antisymm hjac_le hker_le
  refine ⟨?_⟩
  -- After identifying the kernel with the Jacobson radical, the quotient map is exactly the
  -- projective envelope onto the chosen simple target.
  simpa [M, Rep.toModuleMonoidAlgebra] using
    (Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective f hf.surjective)

/-- Helper for Exercise 18-18.3-2: an `FDRep` morphism space is canonically the corresponding
equivariant module-Hom space on the underlying `k[G]`-modules. -/
private noncomputable def fdRep_homLinearEquiv_moduleHomSpace
    {L : Type u} [Field L]
    {G : Type u} [Group G]
    (M N : FDRep L G) :
    (M ⟶ N) ≃ₗ[L] (asModule M.ρ →ₗ[MonoidAlgebra L G] asModule N.ρ) := by
  letI : Module L (asModule M.ρ) := representation_asModuleModule (ρ := M.ρ)
  letI : Module L (asModule N.ρ) := representation_asModuleModule (ρ := N.ρ)
  letI : IsScalarTower L (MonoidAlgebra L G) (asModule M.ρ) :=
    representation_asModule_isScalarTower (ρ := M.ρ)
  letI : IsScalarTower L (MonoidAlgebra L G) (asModule N.ρ) :=
    representation_asModule_isScalarTower (ρ := N.ρ)
  -- Forget `FDRep` morphisms to `Rep`, then read intertwiners as raw equivariant maps.
  exact
    ((FDRep.forget₂HomLinearEquiv M N).symm).trans
      ((Rep.homLinearEquiv
          ((forget₂ (FDRep L G) (Rep L G)).obj M)
          ((forget₂ (FDRep L G) (Rep L G)).obj N)).trans
        (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := N.ρ)))

/-- Helper for Exercise 18-18.3-2: an `FDRep` morphism space is canonically the corresponding
intertwining space on the underlying representations. -/
private noncomputable def fdRep_homLinearEquiv_intertwiningSpace
    {L : Type u} [Field L]
    {G : Type u} [Group G]
    (M N : FDRep L G) :
    (M ⟶ N) ≃ₗ[L] Representation.IntertwiningMap M.ρ N.ρ := by
  exact
    ((FDRep.forget₂HomLinearEquiv M N).symm).trans
      (Rep.homLinearEquiv
        ((forget₂ (FDRep L G) (Rep L G)).obj M)
        ((forget₂ (FDRep L G) (Rep L G)).obj N))

/-- Helper for Exercise 18-18.3-2: any equivariant map into a simple `k[G]`-module kills the
Jacobson radical of its source. -/
private theorem jacobson_le_ker_of_simple_target
    {M : Type u} [AddCommGroup M] [Module k[G] M]
    {N : Type u} [AddCommGroup N] [Module k[G] N] [IsSimpleModule k[G] N]
    (f : M →ₗ[k[G]] N) :
    Module.jacobson k[G] M ≤ LinearMap.ker f := by
  -- Route correction: use the target's trivial Jacobson radical directly, instead of trying to
  -- force the vanishing through a projective-envelope calculation.
  have hcomap :
      Module.jacobson k[G] M ≤ Submodule.comap f (Module.jacobson k[G] N) :=
    Module.le_comap_jacobson (f := f)
  have hEq : Submodule.comap f (Module.jacobson k[G] N) = LinearMap.ker f := by
    rw [IsSimpleModule.jacobson_eq_bot (R := k[G]) (M := N), LinearMap.ker]
  exact hEq ▸ hcomap

/-- Helper for Exercise 18-18.3-2: a nonzero morphism between simple `FDRep`s is already an
isomorphism. -/
private theorem fdRep_nonempty_iso_of_hom_ne_zero
    {X Y : FDRep k G} [Simple X] [Simple Y]
    (f : X ⟶ Y) (hf : f ≠ 0) :
    Nonempty (X ≅ Y) := by
  letI : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  letI : Representation.IsIrreducible Y.ρ := FDRep.isIrreducible_of_simple Y
  let Xrep : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj X
  let Yrep : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj Y
  let fRep : Xrep ⟶ Yrep := (forget₂ (FDRep k G) (Rep k G)).map f
  let fint : Representation.IntertwiningMap X.ρ Y.ρ := by
    simpa [Xrep, Yrep, FDRep.forget₂_ρ] using (Rep.homLinearEquiv Xrep Yrep) fRep
  have hfint : fint ≠ 0 := by
    intro hzero
    have hfRep : fRep = 0 := by
      apply (Rep.homLinearEquiv Xrep Yrep).injective
      simpa [Xrep, Yrep, FDRep.forget₂_ρ] using hzero
    apply hf
    exact (forget₂ (FDRep k G) (Rep k G)).map_injective hfRep
  have hbij :
      Function.Bijective fint :=
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := X.ρ) (σ := Y.ρ) fint).resolve_right hfint
  -- Schur's lemma upgrades the nonzero intertwiner to a categorical isomorphism.
  exact ⟨(fint.ofBijective hbij).toFDRepIso⟩

/-- Helper for Exercise 18-18.3-2: the Hom space between two chosen simple modules has the
expected Kronecker-delta dimension. -/
private theorem simple_fdRep_hom_finrank_eq_delta
    {ι : Type (u + 1)}
    [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i j : ι) :
    Module.finrank k ((π i) ⟶ π j) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    letI : Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    let scalarMap : k →ₗ[k] Representation.IntertwiningMap (π i).ρ (π i).ρ :=
      { toFun := fun c ↦ c • (1 : Representation.IntertwiningMap (π i).ρ (π i).ρ)
        map_add' := by
          intro a b
          simp [add_smul]
        map_smul' := by
          intro a b
          simp [smul_smul] }
    have hscalar_bijective : Function.Bijective scalarMap := by
      simpa [scalarMap] using
        (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
          (ρ := (π i).ρ))
    let eScalar :
        k ≃ₗ[k] Representation.IntertwiningMap (π i).ρ (π i).ρ :=
      LinearEquiv.ofBijective scalarMap hscalar_bijective
    have hfdrep_to_intertwining :
        Module.finrank k ((π i) ⟶ π i) =
          Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) := by
      simpa using
        (LinearEquiv.finrank_eq
          (fdRep_homLinearEquiv_intertwiningSpace (L := k) (G := G) (π i) (π i)))
    have hintertwining :
        Module.finrank k (Representation.IntertwiningMap (π i).ρ (π i).ρ) = 1 := by
      simpa using (LinearEquiv.finrank_eq eScalar).symm
    -- The self-Hom space is one-dimensional because every endomorphism is a scalar.
    simpa using hfdrep_to_intertwining.trans hintertwining
  · letI : Simple (π i) := hπ_complete.isSimple i
    letI : Simple (π j) := hπ_complete.isSimple j
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
    have hzero : ∀ f : (π i) ⟶ π j, f = 0 := by
      intro f
      by_contra hf
      have hIso : Nonempty (π i ≅ π j) :=
        fdRep_nonempty_iso_of_hom_ne_zero (G := G) f hf
      have hnot := hπ_pairwise hij
      exact hnot hIso
    have hSub : Subsingleton ((π i) ⟶ π j) := by
      refine ⟨fun f g ↦ ?_⟩
      rw [hzero f, hzero g]
    -- Off the diagonal the Hom space is trivial, so its dimension is zero.
    have hfin0 :
        Module.finrank k (π i ⟶ π j) = 0 :=
      Module.finrank_eq_zero_of_subsingleton (R := k) (M := (π i ⟶ π j))
    simpa [hij] using hfin0

/-- Helper for Exercise 18-18.3-2: maps from a chosen projective-envelope source into a simple
target factor uniquely through the Jacobson-radical quotient, so the resulting Hom-space finrank
is the same as for the corresponding simple source. -/
private theorem projectiveEnvelope_hom_finrank_eq_simple_hom_finrank
    {ι : Type (u + 1)}
    [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i j : ι) :
    Module.finrank k (((P i).toFiniteRep) ⟶ π j) =
      Module.finrank k ((π i) ⟶ π j) := by
  -- Route correction: the source proof first factors every map `(P i).V → π j` through the
  -- Jacobson-radical quotient and only then transports that quotient to `π i`.
  let ρi : Representation k G (π i) := (π i).ρ
  let ρj : Representation k G (π j) := (π j).ρ
  let Mi : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π i))
  let Mj : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj (π j))
  letI : Simple (π j) := hπ_complete.isSimple j
  letI : Representation.IsIrreducible ρj := by
    simpa [ρj] using (FDRep.isIrreducible_of_simple (π j))
  have hMj_simple : IsSimpleModule k[G] Mj := by
    simpa [Mj, Rep.toModuleMonoidAlgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρj).mp inferInstance
  letI : IsSimpleModule k[G] Mj := hMj_simple
  let J : Submodule k[G] (P i).V := Module.jacobson k[G] (P i).V
  let precompQ :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) →ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) := by
    refine
      { toFun := fun g ↦ LinearMap.comp g (Submodule.mkQ J)
        map_add' := ?_
        map_smul' := ?_ }
    · intro g h
      ext x
      rfl
    · intro a g
      ext x
      rfl
  have hprecompQ_bijective : Function.Bijective precompQ := by
    constructor
    · intro g h hEq
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn' x ?_
      intro y
      simpa [precompQ, LinearMap.comp_apply] using LinearMap.congr_fun hEq y
    · intro f
      have hJker : J ≤ LinearMap.ker f := by
        change Module.jacobson k[G] (P i).V ≤ LinearMap.ker f
        exact jacobson_le_ker_of_simple_target (M := (P i).V) (N := Mj) f
      refine ⟨J.liftQ f hJker, ?_⟩
      simpa [precompQ] using
        (Submodule.liftQ_mkQ J f hJker)
  let liftQEquiv :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) ≃ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) :=
    LinearEquiv.ofBijective precompQ hprecompQ_bijective
  let eQuot :
      ((P i).V ⧸ J) ≃ₗ[k[G]] Mi := by
    simpa [Mi, Rep.toModuleMonoidAlgebra] using
      (Classical.choice <|
        projectiveEnvelope_jacobson_quotient_linearEquiv_target
          π hπ_complete P hP_envelope i)
  let quotTargetHomEquiv :
      (((P i).V ⧸ J) →ₗ[k[G]] Mj) ≃ₗ[k]
        (Mi →ₗ[k[G]] Mj) :=
    LinearEquiv.congrLeft (M := Mj) k eQuot
  let eP :
      (P i).toRep.ρ.asModule ≃ₗ[k[G]] (P i).V := by
    simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.counitIso (P i).V).toLinearEquiv
  let projectiveOwnerHomEquiv :
      ((P i).toRep.ρ.asModule →ₗ[k[G]] Mj) ≃ₗ[k]
        ((P i).V →ₗ[k[G]] Mj) :=
    LinearEquiv.congrLeft (M := Mj) k eP
  -- First read the `FDRep` Homs as raw `k[G]`-linear maps, then pass through the quotient-factor
  -- equivalence and finally transport the quotient to the simple target `π i`.
  calc
    Module.finrank k (((P i).toFiniteRep) ⟶ π j) =
        Module.finrank k ((P i).toRep.ρ.asModule →ₗ[k[G]] Mj) := by
          simpa [Mj, Rep.toModuleMonoidAlgebra,
            FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
            (LinearEquiv.finrank_eq
              (fdRep_homLinearEquiv_moduleHomSpace (L := k) (G := G)
                ((P i).toFiniteRep) (π j)))
    _ = Module.finrank k ((P i).V →ₗ[k[G]] Mj) := by
          exact LinearEquiv.finrank_eq projectiveOwnerHomEquiv
    _ = Module.finrank k (((P i).V ⧸ J) →ₗ[k[G]] Mj) := by
          symm
          exact LinearEquiv.finrank_eq liftQEquiv
    _ = Module.finrank k (Mi →ₗ[k[G]] Mj) := by
          exact LinearEquiv.finrank_eq quotTargetHomEquiv
    _ = Module.finrank k ((π i) ⟶ π j) := by
          simpa [Mi, Mj, Rep.toModuleMonoidAlgebra] using
            (LinearEquiv.finrank_eq
              (fdRep_homLinearEquiv_moduleHomSpace (L := k) (G := G) (π i) (π j))).symm

/-- Helper for Exercise 18-18.3-2: the regular restriction of projective scalar-extension
characters is additive on `P₀[k](G)`. -/
private noncomputable def regularRestrictionProjectiveCharacterAddHom :
    P₀[k](G) →+ (PRegularConjClass G p → K) :=
  (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G)).toAddMonoidHom.comp
    { toFun := projectiveCharacterScalarExtension (A := A) (K := K) (G := G)
      map_zero' := by
        apply Subtype.ext
        ext g
        simp [projectiveCharacterScalarExtension]
      map_add' := by
        intro x y
        apply Subtype.ext
        ext g
        simp [projectiveCharacterScalarExtension] }

/-- Helper for Exercise 18-18.3-2: once Serre's divisibility statement is known on the canonical
projective-envelope generators, it extends to every projective class by the projective-envelope
basis of `P₀[k](G)`. -/
private theorem regularRestriction_projectiveCharacter_mem_of_projectiveEnvelope_generators
    {ι : Type (u + 1)} [Fintype ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hgen :
      ∀ i : ι,
        regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (x : P₀[k](G)) :
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
  let f := regularRestrictionProjectiveCharacterAddHom (p := p) (A := A) (K := K) (G := G)
  have hfx :
      f x =
        ∑ i, (bP.repr x i) • f (bP i) := by
    -- Expand `x` in the projective-envelope basis and push the additive regular-restriction map
    -- through that expansion.
    symm
    calc
      ∑ i, (bP.repr x i) • f (bP i) = ∑ i, f ((bP.repr x i) • bP i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [map_zsmul]
      _ = f (∑ i, (bP.repr x i) • bP i) := by
        rw [map_sum]
      _ = f x := by
        rw [bP.sum_repr x]
  change f x ∈ regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  rw [hfx]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hi_mem : f (bP i) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    simpa [f, bP, projectiveEnvelope_classes_basis_of_complete_family_apply] using hgen i
  exact
    (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)).toAddSubgroup.zsmul_mem
      hi_mem (bP.repr x i)

/-- Helper for Exercise 18-18.3-2: zero-extending the regular restriction of a projective
character generator recovers the ordinary projective lift character of that projective module. -/
private theorem regularRestriction_projectiveCharacter_zeroExtension_eq_projectiveLiftCharacter
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    (fun s : G ↦
      if hs : IsPRegular p s then
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P]ₚ₀)
          (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
      else 0) =
      FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter P e := by
  funext s
  by_cases hs : IsPRegular p s
  · -- On the regular locus, the zero extension is literally the regular restriction value.
    change
      (if hs' : IsPRegular p s then
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P]ₚ₀)
          (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs'⟩)
      else 0) =
        (finiteRepGrothendieckCharacter K G (e [P]ₚ₀) : G → K) s
    simp [hs, regularRestriction_ofSubtype, projectiveCharacterScalarExtension]
  · -- Away from the regular locus, projective characters vanish by the Chapter `18.3.1` criterion.
    have hP_range :
        e [P]ₚ₀ ∈
          (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range :=
      ⟨[P]ₚ₀, rfl⟩
    have hzero :=
      (mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
        (A := A) (K := K) (G := G) (p := p) (e [P]ₚ₀)).1 hP_range s hs
    change
      (if hs' : IsPRegular p s then
        regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P]ₚ₀)
          (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs'⟩)
      else 0) =
        (finiteRepGrothendieckCharacter K G (e [P]ₚ₀) : G → K) s
    simpa [hs, projectiveCharacterScalarExtension] using hzero.symm

/-- Helper for Exercise 18-18.3-2: the chosen projective-envelope generators and Brauer
characters satisfy Serre's Kronecker-delta pairing relation. -/
private theorem projectiveEnvelope_regular_pairing_eq_delta
    {ι : Type (u + 1)} [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (lift : PrimeToPRoot p k →* Kˣ)
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i j : ι) :
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s =
      if i = j then (1 : K) else 0 := by
  have hpair :=
    intertwining_finrank_eq_projectiveLiftCharacter_pairing
      (p := p) (A := A) (K := K) (G := G) (lift := lift) (E := π j) (F := P i)
  have hproj :
      (fun s : G ↦
        if hs : IsPRegular p (s⁻¹) then
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
            (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
        else 0) =
        fun s : G ↦ FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (P i) e (s⁻¹) := by
    funext s
    simpa using congrFun
      (regularRestriction_projectiveCharacter_zeroExtension_eq_projectiveLiftCharacter
        (p := p) (A := A) (K := K) (G := G) (P := P i)) (s⁻¹)
  have hfdrep_finrank :
      Module.finrank k (((P i).toFiniteRep) ⟶ π j) =
        Module.finrank k (((P i).toRep.ρ).IntertwiningMap (FDRep.ρ (π j))) := by
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (LinearEquiv.finrank_eq
        (fdRep_homLinearEquiv_intertwiningSpace (L := k) (G := G) ((P i).toFiniteRep) (π j)))
  have hsum :
      ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s =
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter (P i) e (s⁻¹) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    exact congrArg
      (fun z : K ↦ z * FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s)
      (congrFun hproj s)
  -- Route correction: package Serre's projective-lift pairing as an explicit `PRegularConjClass`
  -- delta statement before attempting the later basis expansion.
  calc
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s
        =
        (Module.finrank k (((P i).toRep.ρ).IntertwiningMap (FDRep.ρ (π j))) : K) := by
          rw [hsum]
          simpa [mul_comm] using hpair.symm
    _ = (Module.finrank k (((P i).toFiniteRep) ⟶ π j) : K) := by
          norm_num [hfdrep_finrank]
    _ = (Module.finrank k ((π i) ⟶ π j) : K) := by
          norm_num [projectiveEnvelope_hom_finrank_eq_simple_hom_finrank
            (G := G) (π := π) (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope)
            i j]
    _ = if i = j then (1 : K) else 0 := by
          norm_num [simple_fdRep_hom_finrank_eq_delta
            (G := G) (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i j]

namespace ConjClasses

/-- Helper for Exercise 18-18.3-2: the centralizer order attached to a conjugacy class is
the centralizer order of a chosen representative. This is the source-side scalar Serre later
splits into its `p`-part and prime-to-`p` part. -/
noncomputable def centralizerCard (c : ConjClasses G) : ℕ :=
  Nat.card (Subgroup.centralizer ({Classical.choose (ConjClasses.mk_surjective c)} : Set G))

/-- Helper for Exercise 18-18.3-2: Serre's centralizer order on a conjugacy class factors as the
centralizer `p`-part times its prime-to-`p` complement. -/
theorem centralizerCard_eq_centralizerPPart_mul_ordCompl
    (c : ConjClasses G) :
    centralizerCard c = centralizerPPart p c * ordCompl[p] (centralizerCard c) := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  -- On the chosen representative, this is exactly the standard `ordProj`/`ordCompl`
  -- factorization, and the class-level `p`-part is computed on the same representative.
  calc
    centralizerCard c =
        Nat.card (Subgroup.centralizer ({g} : Set G)) := by
          simp [ConjClasses.centralizerCard, g]
    _ =
        Representation.centralizerPPart p g *
          ordCompl[p] (Nat.card (Subgroup.centralizer ({g} : Set G))) := by
          simpa [Representation.centralizerPPart] using
            (Nat.ordProj_mul_ordCompl_eq_self
              (Nat.card (Subgroup.centralizer ({g} : Set G))) p).symm
    _ =
        ConjClasses.centralizerPPart p c * ordCompl[p] (centralizerCard c) := by
          have hppart : Representation.centralizerPPart p g = ConjClasses.centralizerPPart p c := by
            rw [← hg, ConjClasses.centralizerPPart_mk]
          have hcard :
              centralizerCard c = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
            simp [ConjClasses.centralizerCard, g]
          rw [hppart, hcard]

end ConjClasses

/-- Helper for Exercise 18-18.3-2: regular-class point masses use classical equality on
`PRegularConjClass G p`. -/
local instance decidableEqPRegularConjClass : DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: the prime-to-`p` factor in the centralizer order of a
`p`-regular class is a unit in the coefficient ring `A`. This is the source-side rescaling input
used to pass between the full indicator and the scaled indicator. -/
private theorem ordCompl_centralizerCard_isUnit
    (c : PRegularConjClass G p) :
    IsUnit ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A)) := by
  -- Reduce unitness in the local ring `A` to nonvanishing in the residue field, then use the
  -- fact that the prime-to-`p` part is not divisible by `p`.
  refine
    (IsLocalRing.residue_ne_zero_iff_isUnit
      ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A))).1 ?_
  intro hzero
  have hpdiv : p ∣ ordCompl[p] (ConjClasses.centralizerCard c.1) := by
    exact (CharP.cast_eq_zero_iff k p _).mp hzero
  have hcard_ne : ConjClasses.centralizerCard c.1 ≠ 0 := by
    dsimp [ConjClasses.centralizerCard]
    exact
      (Finite.card_pos
        (α := Subgroup.centralizer ({Classical.choose (ConjClasses.mk_surjective c.1)} : Set G))).ne'
  exact Nat.not_dvd_ordCompl (Fact.out : Nat.Prime p) hcard_ne hpdiv

/-- Helper for Exercise 18-18.3-2: Serre's full regular indicator at `c` is the point mass whose
single nonzero value is the full centralizer order of `c`. -/
private noncomputable def full_regular_indicator
    (c : PRegularConjClass G p) : PRegularConjClass G p → K :=
  Pi.single c (algebraMap A K (ConjClasses.centralizerCard c.1 : A))

/-- Helper for Exercise 18-18.3-2: Serre's prime-to-`p` regular indicator at `c` is the
`A`-valued point mass whose single nonzero value is the prime-to-`p` factor of the centralizer
order. Pairing this function with projective envelopes is the source-faithful route to the
`p`-part divisibility statement. -/
private noncomputable def primeToP_regular_indicator
    (c : PRegularConjClass G p) : PRegularConjClass G p → A :=
  Pi.single c (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)

/-- Helper for Exercise 18-18.3-2: evaluating Serre's prime-to-`p` point mass at a `p`-regular
representative of the supporting class returns the prime-to-`p` factor of the centralizer order.
This is the positive branch of the source point-mass calculation. -/
private theorem primeToP_regular_indicator_ofSubtype_eq_ordCompl
    (c : PRegularConjClass G p) {s : G} (hs : IsPRegular p s)
    (hmk : ConjClasses.mk s = c.1) :
    primeToP_regular_indicator (p := p) (A := A) (G := G) c
        (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩) =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  -- Rewrite the chosen representative back to the supporting `p`-regular conjugacy class `c`.
  have hEq : PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩ = c := Subtype.ext hmk
  -- Evaluating the point mass at its support returns the defining coefficient.
  simpa [primeToP_regular_indicator, Pi.single_apply, hEq]

/-- Helper for Exercise 18-18.3-2: evaluating Serre's prime-to-`p` point mass at a `p`-regular
representative outside the supporting class gives `0`. This is the negative branch of the source
point-mass calculation. -/
private theorem primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
    (c : PRegularConjClass G p) {s : G} (hs : IsPRegular p s)
    (hmk : ConjClasses.mk s ≠ c.1) :
    primeToP_regular_indicator (p := p) (A := A) (G := G) c
        (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩) =
      0 := by
  -- A representative of a different conjugacy class cannot land on the support of the point mass.
  have hNe : PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩ ≠ c := by
    intro hEq
    exact hmk (by simpa [PRegularConjClass.coe_ofSubtype] using congrArg Subtype.val hEq)
  -- Evaluating the point mass away from its support is zero.
  simpa [primeToP_regular_indicator, Pi.single_apply, hNe]

/-- Helper for Exercise 18-18.3-2: summing a function constant on conjugacy classes over `G`
equals summing it over conjugacy classes weighted by class size. This is the bookkeeping step used
to collapse Serre's prime-to-`p` point masses. -/
private theorem sum_over_group_eq_sum_over_conjClasses
    (a : ConjClasses G → K) :
    ∑ x : G, a (ConjClasses.mk x) =
      ∑ c : ConjClasses G, (Nat.card c.carrier : K) * a c := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let F : G → ConjClasses G := ConjClasses.mk
  have himage : (Finset.univ : Finset G).image F = (Finset.univ : Finset (ConjClasses G)) := by
    ext c
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      exact Finset.mem_image.mpr ⟨g, by simp [F]⟩
  have hfiberwise :
      ∑ c ∈ (Finset.univ : Finset G).image F,
          ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x)
        =
      ∑ x : G, a (F x) := by
    simpa [F] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset G))
        (t := (Finset.univ : Finset G).image F)
        (g := F)
        (fun x hx ↦ Finset.mem_image_of_mem F hx)
        (fun x : G ↦ a (F x)))
  have hcoeff (c : ConjClasses G) :
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) =
        (Nat.card c.carrier : K) * a c := by
    let fiber : Finset G := (Finset.univ : Finset G).filter (fun x ↦ F x = c)
    have hfiber_mem : ∀ x : G, x ∈ fiber ↔ x ∈ c.carrier := by
      intro x
      simp [fiber, F, ConjClasses.mem_carrier_iff_mk_eq]
    have hsum_const :
        ∑ x ∈ fiber, a (F x) = (fiber.card : K) * a c := by
      calc
        ∑ x ∈ fiber, a (F x) = ∑ x ∈ fiber, a c := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hx' : F x = c := by
            simpa [fiber] using hx
          simpa [hx']
        _ = (fiber.card : K) * a c := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : fiber.card = Nat.card c.carrier := by
      let _ : Fintype c.carrier := Fintype.ofFinset fiber (hfiber_mem ·)
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset fiber (hfiber_mem ·)).symm
    -- On each conjugacy class fiber, the summand is constant.
    calc
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) = ∑ x ∈ fiber, a (F x) := by
        rfl
      _ = (fiber.card : K) * a c := hsum_const
      _ = (Nat.card c.carrier : K) * a c := by
        rw [hcard]
  -- Partition `G` by the fibers of `ConjClasses.mk`.
  calc
    ∑ x : G, a (ConjClasses.mk x) =
        ∑ c ∈ (Finset.univ : Finset G).image F,
          ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) := by
          simpa [F] using hfiberwise.symm
    _ = ∑ c : ConjClasses G, (Nat.card c.carrier : K) * a c := by
          rw [himage]
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact hcoeff c

/-- Helper for Exercise 18-18.3-2: the zero extension of Serre's prime-to-`p` point mass at `c`
has total mass equal to the size of the conjugacy class times the prime-to-`p` factor of the
centralizer order. This is the source-side class-sum calculation needed before the orthogonality
comparison. -/
private theorem sum_primeToP_regular_indicator_zeroExtension_eq_class_card_mul
    (c : PRegularConjClass G p) :
    ∑ s : G,
      (if hs : IsPRegular p s then
        algebraMap A K
          ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
            (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
      else 0) =
      (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let a : ConjClasses G → K := fun d ↦
    if h : d = c.1 then
      algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
    else 0
  have hsum :
      ∑ s : G,
        (if hs : IsPRegular p s then
          algebraMap A K
            ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
        else 0) =
        ∑ s : G, a (ConjClasses.mk s) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsp : IsPRegular p s
    · by_cases hmk : ConjClasses.mk s = c.1
      · -- On the supporting conjugacy class, the point mass takes its unique nonzero value.
        rw [if_pos hsp,
          primeToP_regular_indicator_ofSubtype_eq_ordCompl
            (p := p) (A := A) (G := G) c hsp hmk]
        simp [a, hmk]
      · -- Away from the supporting conjugacy class, the point mass vanishes.
        rw [if_pos hsp,
          primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
            (p := p) (A := A) (G := G) c hsp hmk]
        simp [a, hmk]
    · by_cases hmk : ConjClasses.mk s = c.1
      · have hs_reg : IsPRegular p s := by
          exact c.2 s (by simpa [ConjClasses.mem_carrier_iff_mk_eq] using hmk)
        exact (hsp hs_reg).elim
      · simp [a, hsp, hmk]
  -- Collapse the group sum to the unique conjugacy class supporting the point mass.
  rw [hsum, sum_over_group_eq_sum_over_conjClasses (G := G) (K := K) a]
  classical
  have hc_mem : c.1 ∈ (Finset.univ : Finset (ConjClasses G)) := by simp
  rw [Finset.sum_eq_single c.1]
  · simp [a]
  · intro d hd hdc
    simp [a, hdc]
  · intro hc
    exact (hc hc_mem).elim

/-- Helper for Exercise 18-18.3-2: inverting a conjugacy class does not change the order of the
centralizer of a representative. This isolates the only stable class-level datum needed to repair
the remaining `s⁻¹` pairing convention in Serre's orthogonality formula. -/
private theorem nat_card_centralizer_eq_of_isConj
    {g h : G} (hgh : IsConj g h) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card (Subgroup.centralizer ({h} : Set G)) := by
  rcases hgh with ⟨u, hu⟩
  have hh : h = (u : G) * g * (u : G)⁻¹ := by
    symm
    exact mul_inv_eq_iff_eq_mul.mpr hu
  -- Conjugation by the witness carries `C_G(g)` isomorphically onto `C_G(h)`.
  let e :
      Subgroup.centralizer ({g} : Set G) ≃*
        Subgroup.centralizer ({(u : G) * g * (u : G)⁻¹} : Set G) :=
    { toFun := fun x ↦
        ⟨(u : G) * x * (u : G)⁻¹, by
          have hx : (x : G) * g = g * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G) * t * (u : G)⁻¹) hx⟩
      invFun := fun x ↦
        ⟨(u : G)⁻¹ * x * (u : G), by
          have hx :
              (x : G) * ((u : G) * g * (u : G)⁻¹) =
                ((u : G) * g * (u : G)⁻¹) * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G)⁻¹ * t * (u : G)) hx⟩
      left_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      right_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      map_mul' := fun x y ↦ Subtype.ext <| by
        simp [mul_assoc] }
  have hcard :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card (Subgroup.centralizer ({(u : G) * g * (u : G)⁻¹} : Set G)) := by
    simpa using Nat.card_congr e.toEquiv
  simpa [hh] using hcard

/-- Helper for Exercise 18-18.3-2: inverting a conjugacy class does not change the order of the
centralizer of a representative. This isolates the only stable class-level datum needed to repair
the remaining `s⁻¹` pairing convention in Serre's orthogonality formula. -/
private theorem ConjClasses.centralizerCard_inv
    (c : ConjClasses G) :
    ConjClasses.centralizerCard c⁻¹ = ConjClasses.centralizerCard c := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  let h : G := Classical.choose (ConjClasses.mk_surjective c⁻¹)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  have hh : ConjClasses.mk h = c⁻¹ := Classical.choose_spec (ConjClasses.mk_surjective c⁻¹)
  have hhgInv : ConjClasses.mk h = ConjClasses.mk g⁻¹ := by
    calc
      ConjClasses.mk h = c⁻¹ := hh
      _ = (ConjClasses.mk g)⁻¹ := by rw [hg]
      _ = ConjClasses.mk g⁻¹ := by simp [ConjClasses.inv_mk]
  have hconj : IsConj h g⁻¹ := (ConjClasses.mk_eq_mk_iff_isConj).1 hhgInv
  have hcent :
      Subgroup.centralizer ({g⁻¹} : Set G) = Subgroup.centralizer ({g} : Set G) := by
    ext x
    have hcomm : x * g⁻¹ = g⁻¹ * x ↔ x * g = g * x := by
      constructor
      · intro hx
        have hx' : x = g⁻¹ * x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g) hx
        have hx'' : g * x = x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => g * t) hx'
        simpa [eq_comm] using hx''
      · intro hx
        have hx' : x = g * x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hx
        have hx'' : g⁻¹ * x = x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => g⁻¹ * t) hx'
        simpa [eq_comm] using hx''
    simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm
  -- Compare the chosen representative of `c⁻¹` with `g⁻¹`, then use the equality
  -- `C_G(g⁻¹) = C_G(g)` to return to the original class.
  calc
    ConjClasses.centralizerCard c⁻¹ =
        Nat.card (Subgroup.centralizer ({h} : Set G)) := by
          simp [ConjClasses.centralizerCard, h]
    _ = Nat.card (Subgroup.centralizer ({g⁻¹} : Set G)) :=
        nat_card_centralizer_eq_of_isConj hconj
    _ = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
          simp [hcent]
    _ = ConjClasses.centralizerCard c := by
          simp [ConjClasses.centralizerCard, g]

/-- Helper for Exercise 18-18.3-2: the inverse of a `p`-regular conjugacy class is again
`p`-regular. This lets the source proof keep the `s⁻¹` pairing convention explicit. -/
private noncomputable def inversePRegularConjClass
    (c : PRegularConjClass G p) : PRegularConjClass G p :=
  ⟨c.1⁻¹, by
    intro x hx
    have hxmk : ConjClasses.mk x = c.1⁻¹ :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hx
    have hxinv : ConjClasses.mk x⁻¹ = c.1 := by
      simpa [ConjClasses.inv_mk] using congrArg Inv.inv hxmk
    have hxinv_mem : x⁻¹ ∈ c.1.carrier :=
      ConjClasses.mem_carrier_iff_mk_eq.mpr hxinv
    have hxinv_reg : IsPRegular p x⁻¹ := c.2 _ hxinv_mem
    simpa [IsPRegular, orderOf_inv] using hxinv_reg⟩

/-- Helper for Exercise 18-18.3-2: forgetting the inverse regular class recovers the inverse
ambient conjugacy class. -/
@[simp] private theorem inversePRegularConjClass_val
    (c : PRegularConjClass G p) :
    ((inversePRegularConjClass (p := p) c : PRegularConjClass G p) : ConjClasses G) = c.1⁻¹ := by
  rfl

/-- Helper for Exercise 18-18.3-2: inverting a regular class twice returns the original class. -/
@[simp] private theorem inversePRegularConjClass_involutive
    (c : PRegularConjClass G p) :
    inversePRegularConjClass (p := p) (inversePRegularConjClass (p := p) c) = c := by
  apply Subtype.ext
  simp [inversePRegularConjClass]

/-- Helper for Exercise 18-18.3-2: the centralizer `p`-part is unchanged by inverting a regular
conjugacy class. -/
@[simp] private theorem ConjClasses.centralizerPPart_inv
    (c : ConjClasses G) :
    ConjClasses.centralizerPPart p c⁻¹ = ConjClasses.centralizerPPart p c := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  have hgInv : ConjClasses.mk g⁻¹ = c⁻¹ := by
    simpa [ConjClasses.inv_mk] using congrArg Inv.inv hg
  have hcent :
      Subgroup.centralizer ({g⁻¹} : Set G) = Subgroup.centralizer ({g} : Set G) := by
    ext x
    have hcomm : x * g⁻¹ = g⁻¹ * x ↔ x * g = g * x := by
      constructor
      · intro hx
        have hx' : x = g⁻¹ * x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g) hx
        have hx'' : g * x = x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => g * t) hx'
        simpa [eq_comm] using hx''
      · intro hx
        have hx' : x = g * x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hx
        have hx'' : g⁻¹ * x = x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => g⁻¹ * t) hx'
        simpa [eq_comm] using hx''
    simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm
  calc
    ConjClasses.centralizerPPart p c⁻¹ = Representation.centralizerPPart p g⁻¹ := by
      rw [← hgInv, ConjClasses.centralizerPPart_mk]
    _ = Representation.centralizerPPart p g := by
      simp [Representation.centralizerPPart, hcent]
    _ = ConjClasses.centralizerPPart p c := by
      rw [← hg, ConjClasses.centralizerPPart_mk]

/-- Helper for Exercise 18-18.3-2: the full regular indicator is the prime-to-`p` factor times
the scaled indicator. This is the source-faithful normalization step used before the two dual
expansions. -/
private theorem full_regular_indicator_eq_ordCompl_smul_scaled_regular_indicator
    (c : PRegularConjClass G p) :
    Pi.single c (algebraMap A K (ConjClasses.centralizerCard c.1 : A)) =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) •
        scaled_regular_indicator (p := p) (A := A) (K := K) c := by
  classical
  ext c'
  by_cases h : c' = c
  · subst c'
    -- At the distinguished class, rewrite the full centralizer order using the `p`-part split.
    have hcard :
        ConjClasses.centralizerCard c.1 =
          ConjClasses.centralizerPPart p c.1 *
            ordCompl[p] (ConjClasses.centralizerCard c.1) :=
      ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
        (p := p) (G := G) c.1
    have hcast :
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
          algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
            algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
      simpa [map_mul] using congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard
    calc
      full_regular_indicator c c =
          algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simp [full_regular_indicator]
      _ =
          algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
            algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := hcast
      _ =
          algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) *
            algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) := by
              rw [mul_comm]
      _ =
          ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A) •
            scaled_regular_indicator (p := p) (A := A) (K := K) c) c := by
              simp [scaled_regular_indicator, Algebra.smul_def]
  · -- Off the distinguished class, both point masses vanish.
    simp [full_regular_indicator, scaled_regular_indicator, h]

/-- Helper for Exercise 18-18.3-2: choose residue-field representatives in `A` for the
prime-to-`p` roots appearing in the coefficient-ring Brauer basis. -/
private noncomputable def primeToPRoot_residue_section :
    PrimeToPRoot p k → A :=
  fun ζ ↦ Classical.choose (IsLocalRing.residue_surjective (R := A) (ζ : k))

/-- Helper for Exercise 18-18.3-2: the chosen residue-field representatives really lift the
underlying prime-to-`p` roots of unity. -/
@[simp] private theorem residue_primeToPRoot_residue_section
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A
        (primeToPRoot_residue_section (p := p) (A := A) ζ) =
      (ζ : k) := by
  exact Classical.choose_spec (IsLocalRing.residue_surjective (R := A) (ζ : k))

/-- Helper for Exercise 18-18.3-2: the chosen residue-field section on prime-to-`p` roots is
injective, so it can serve as the coefficient-ring lift required by Exercise `18-18.2-9`. -/
private theorem primeToPRoot_residue_section_injective :
    Function.Injective (primeToPRoot_residue_section (p := p) (A := A)) := by
  intro ζ ξ hζξ
  apply Subtype.ext
  apply Units.ext
  have hres := congrArg (IsLocalRing.residue A) hζξ
  simpa using hres

/-- Helper for Exercise 18-18.3-2: every prime-to-`p` root of unity in the residue field lifts to
an actual root of the same order in the Henselian coefficient ring `A`. This is the fixed-order
Hensel step needed before packaging a source-faithful multiplicative lift. -/
private theorem exists_primeToPRoot_pow_lift
    (ζ : PrimeToPRoot p k) :
    ∃ a : A,
      a ^ orderOf (ζ : kˣ) = 1 ∧
        IsLocalRing.residue A a = (ζ : k) := by
  have hcop : Nat.Coprime p (orderOf (ζ : kˣ)) := by
    exact ζ.2
  have hn_ne : orderOf (ζ : kˣ) ≠ 0 := by
    -- A `p`-regular root of unity has finite order prime to `p`, hence nonzero order.
    intro hn0
    have hp_one : p = 1 := by
      simpa [hn0] using hcop
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  have hpow : (ζ : k) ^ orderOf (ζ : kˣ) = 1 := by
    -- The residue-field root already satisfies its defining cyclotomic equation.
    simpa using congrArg ((↑) : kˣ → k) (pow_orderOf_eq_one (ζ : kˣ))
  let f : Polynomial A := Polynomial.X ^ orderOf (ζ : kˣ) - 1
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (1 : A)) hn_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma bundled in mathlib's TFAE.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (ζ : k) f = 0 := by
    -- The target residue root is a simple root of `X^n - 1` in the residue field.
    simpa [Polynomial.aeval_def, f, sub_eq_zero] using hpow
  have hderiv_ne : Polynomial.aeval (ζ : k) (Polynomial.derivative f) ≠ 0 := by
    have hn_not_dvd : ¬ p ∣ orderOf (ζ : kˣ) :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
    have hn_cast_ne : ((orderOf (ζ : kˣ) : ℕ) : k) ≠ 0 :=
      (NeZero.of_not_dvd (R := k) hn_not_dvd).out
    have hzeta_ne : (ζ : k) ≠ 0 := Units.ne_zero _
    -- The derivative is `n * X^(n-1)`, and both factors stay nonzero at a root of unity.
    rw [show Polynomial.aeval (ζ : k) (Polynomial.derivative f) =
        ((orderOf (ζ : kˣ) : k) * (ζ : k) ^ (orderOf (ζ : kˣ) - 1)) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ orderOf (ζ : kˣ)) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact mul_ne_zero hn_cast_ne (pow_ne_zero _ hzeta_ne)
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (ζ : k) hroot0 hderiv_ne
  refine ⟨a, ?_, ha_res⟩
  -- Unfold the polynomial root condition back to the concrete order equation.
  have hroot_eq : a ^ orderOf (ζ : kˣ) - 1 = 0 := by
    simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
  exact sub_eq_zero.mp hroot_eq

/-- Helper for Exercise 18-18.3-2: if `a^m = 1`, then `a^n = 1` for every multiple `n` of `m`.
This isolates the fixed-order bookkeeping used when comparing different chosen lifts at a common
exponent. -/
private theorem pow_eq_one_of_pow_eq_one_of_dvd
    {a : A} {m n : ℕ} (ha : a ^ m = 1) (hmn : m ∣ n) :
    a ^ n = 1 := by
  rcases hmn with ⟨r, rfl⟩
  rw [pow_mul, ha, one_pow]

/-- Helper for Exercise 18-18.3-2: the order of a prime-to-`p` root of unity is nonzero. This is
the input needed to turn its fixed-order lift into a unit. -/
private theorem primeToPRoot_order_ne_zero
    (ζ : PrimeToPRoot p k) :
    orderOf (ζ : kˣ) ≠ 0 := by
  intro hzero
  have hcop : Nat.Coprime p 0 := hzero ▸ ζ.2
  have hp_one : p = 1 := (Nat.coprime_zero_right p).mp hcop
  exact (Fact.out : Nat.Prime p).ne_one hp_one

/-- Helper for Exercise 18-18.3-2: choose the fixed-order Hensel lift attached to a prime-to-`p`
root of unity in the residue field. -/
private noncomputable def primeToPRoot_powLift :
    PrimeToPRoot p k → A :=
  fun ζ ↦ Classical.choose (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)

/-- Helper for Exercise 18-18.3-2: the chosen fixed-order lift satisfies the expected order
equation in `A`. -/
@[simp] private theorem primeToPRoot_powLift_pow_orderOf
    (ζ : PrimeToPRoot p k) :
    primeToPRoot_powLift (p := p) (A := A) ζ ^ orderOf (ζ : kˣ) = 1 := by
  exact (Classical.choose_spec (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)).1

/-- Helper for Exercise 18-18.3-2: the chosen fixed-order lift reduces to the original residue
root of unity. -/
@[simp] private theorem residue_primeToPRoot_powLift
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A (primeToPRoot_powLift (p := p) (A := A) ζ) = (ζ : k) := by
  exact (Classical.choose_spec (exists_primeToPRoot_pow_lift (p := p) (A := A) ζ)).2

/-- Helper for Exercise 18-18.3-2: the fixed-order lift is automatically a unit because a
nontrivial power of it equals `1`. -/
private noncomputable def primeToPRoot_unitLift
    (ζ : PrimeToPRoot p k) : Aˣ :=
  (IsUnit.of_pow_eq_one
    (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
    (primeToPRoot_order_ne_zero (p := p) (A := A) ζ)).unit

/-- Helper for Exercise 18-18.3-2: coercing the chosen unit lift back to `A` recovers the fixed
order lift chosen above. -/
@[simp] private theorem primeToPRoot_unitLift_val
    (ζ : PrimeToPRoot p k) :
    ((primeToPRoot_unitLift (p := p) (A := A) ζ : Aˣ) : A) =
      primeToPRoot_powLift (p := p) (A := A) ζ := by
  exact IsUnit.unit_spec
    (IsUnit.of_pow_eq_one
      (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
      (primeToPRoot_order_ne_zero (p := p) (A := A) ζ))

/-- Helper for Exercise 18-18.3-2: the chosen unit lift still reduces to the original prime-to-`p`
root of unity. -/
@[simp] private theorem residue_primeToPRoot_unitLift
    (ζ : PrimeToPRoot p k) :
    IsLocalRing.residue A ((primeToPRoot_unitLift (p := p) (A := A) ζ : Aˣ) : A) = (ζ : k) := by
  simpa using residue_primeToPRoot_powLift (p := p) (A := A) ζ

/-- Helper for Exercise 18-18.3-2: an `n`-th root of unity in the coefficient ring that reduces
to `1` is already `1` when `n` is prime to `p`. This is the uniqueness input behind the canonical
prime-to-`p` lift. -/
private theorem unit_eq_one_of_pow_eq_one_of_residue_eq_one
    {u : Aˣ} {n : ℕ} (hn : Nat.Coprime p n)
    (hu : ((u : A) ^ n) = 1)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    u = 1 := by
  let s : A := ∑ i ∈ Finset.range n, (u : A) ^ i
  have hn_not_dvd : ¬ p ∣ n :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hn
  have hn_cast_ne : ((n : ℕ) : k) ≠ 0 :=
    (NeZero.of_not_dvd (R := k) hn_not_dvd).out
  have hs_res :
      IsLocalRing.residue A s = (n : k) := by
    -- The geometric sum reduces to the constant sum `1 + ... + 1 = n`.
    calc
      IsLocalRing.residue A s
          = ∑ i ∈ Finset.range n,
              IsLocalRing.residue A ((u : A) ^ i) := by
                simp [s]
      _ = ∑ i ∈ Finset.range n, (1 : k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_pow]
            simpa [hres]
      _ = (n : k) := by simp
  have hs_unit : IsUnit s := by
    have hs_res_ne : IsLocalRing.residue A s ≠ 0 := by
      simpa [hs_res] using hn_cast_ne
    have hs_not_mem : s ∉ IsLocalRing.maximalIdeal A := by
      intro hs_mem
      exact hs_res_ne ((IsLocalRing.residue_eq_zero_iff s).2 hs_mem)
    exact (IsLocalRing.notMem_maximalIdeal).1 hs_not_mem
  have hgeom : s * ((u : A) - 1) = 0 := by
    -- Rewrite the standard geometric-series identity using `u^n = 1`.
    simpa [s, hu] using (geom_sum_mul (u : A) n)
  have hsub : (u : A) - 1 = 0 := by
    exact (IsUnit.mul_right_eq_zero hs_unit).1 hgeom
  apply Units.ext
  exact sub_eq_zero.mp hsub

/-- Helper for Exercise 18-18.3-2: the fixed-order lift of a prime-to-`p` root of unity is unique
once its residue and a common prime-to-`p` exponent are prescribed. -/
private theorem primeToPRoot_powLift_unique
    {a b : A} {n : ℕ} (hn : Nat.Coprime p n)
    (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hres : IsLocalRing.residue A a = IsLocalRing.residue A b) :
    a = b := by
  have hn_ne : n ≠ 0 := by
    intro hzero
    have hcop : Nat.Coprime p 0 := hzero ▸ hn
    have hp_one : p = 1 := (Nat.coprime_zero_right p).mp hcop
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  rcases IsUnit.of_pow_eq_one ha hn_ne with ⟨ua, rfl⟩
  rcases IsUnit.of_pow_eq_one hb hn_ne with ⟨ub, rfl⟩
  have hub_res_ne : IsLocalRing.residue A (ub : A) ≠ 0 := by
    simpa using (Units.ne_zero (Units.map (IsLocalRing.residue A).toMonoidHom ub))
  have hua_pow : ua ^ n = 1 := by
    apply Units.ext
    simpa using ha
  have hub_pow : ub ^ n = 1 := by
    apply Units.ext
    simpa using hb
  have hu_pow :
      ((((ua * ub⁻¹ : Aˣ) : A)) ^ n) = 1 := by
    have hu_pow_units : (ua * ub⁻¹ : Aˣ) ^ n = 1 := by
      rw [mul_pow, hua_pow, inv_pow, hub_pow]
      simp
    simpa using congrArg (fun z : Aˣ ↦ (z : A)) hu_pow_units
  have hu_res :
      IsLocalRing.residue A (((ua * ub⁻¹ : Aˣ) : A)) = 1 := by
    calc
      IsLocalRing.residue A (((ua * ub⁻¹ : Aˣ) : A))
          = IsLocalRing.residue A (ua : A) *
              (IsLocalRing.residue A (ub : A))⁻¹ := by
                simp
      _ = IsLocalRing.residue A (ub : A) *
            (IsLocalRing.residue A (ub : A))⁻¹ := by
              rw [hres]
      _ = 1 := by
            rw [mul_inv_cancel₀ hub_res_ne]
  have hu_eq_one : (ua * ub⁻¹ : Aˣ) = 1 :=
    unit_eq_one_of_pow_eq_one_of_residue_eq_one
      (p := p) (A := A) hn hu_pow hu_res
  -- Multiply back by `ub` to recover the equality of the two chosen lifts.
  have hua_eq_ub : ua = ub := by
    simpa [mul_assoc] using congrArg (fun z : Aˣ ↦ z * ub) hu_eq_one
  simpa using congrArg (fun z : Aˣ ↦ (z : A)) hua_eq_ub

/-- Helper for Exercise 18-18.3-2: the canonical fixed-order lift packages into a multiplicative
map on prime-to-`p` roots of unity. This is the source-faithful replacement for the earlier
arbitrary residue section. -/
private noncomputable def primeToPRoot_unitsLift :
    PrimeToPRoot p k →* Aˣ where
  toFun := primeToPRoot_unitLift (p := p) (A := A)
  map_one' := by
    apply Units.ext
    rw [primeToPRoot_unitLift_val]
    exact
      primeToPRoot_powLift_unique (p := p) (A := A)
        (n := 1) (Nat.coprime_one_right p)
        (by simpa using primeToPRoot_powLift_pow_orderOf (p := p) (A := A) (1 : PrimeToPRoot p k))
        (by simp)
        (by simpa using residue_primeToPRoot_powLift (p := p) (A := A) (1 : PrimeToPRoot p k))
  map_mul' ζ ξ := by
    apply Units.ext
    let n : ℕ := orderOf (ζ : kˣ) * orderOf (ξ : kˣ)
    have hn : Nat.Coprime p n := by
      dsimp [n]
      rw [Nat.coprime_mul_iff_right]
      exact ⟨ζ.2, ξ.2⟩
    have hζ_pow :
        (primeToPRoot_unitLift (p := p) (A := A) ζ : A) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ζ)
          (dvd_mul_right (orderOf (ζ : kˣ)) (orderOf (ξ : kˣ)))
    have hξ_pow :
        (primeToPRoot_unitLift (p := p) (A := A) ξ : A) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) ξ)
          (by
            simpa [Nat.mul_comm] using
              (dvd_mul_left (orderOf (ξ : kˣ)) (orderOf (ζ : kˣ))))
    have hmul_pow :
        (((primeToPRoot_unitLift (p := p) (A := A) ζ : A) *
              (primeToPRoot_unitLift (p := p) (A := A) ξ : A)) ^ n) = 1 := by
      calc
        (((primeToPRoot_unitLift (p := p) (A := A) ζ : A) *
              (primeToPRoot_unitLift (p := p) (A := A) ξ : A)) ^ n)
            =
              (primeToPRoot_unitLift (p := p) (A := A) ζ : A) ^ n *
                (primeToPRoot_unitLift (p := p) (A := A) ξ : A) ^ n := by
                  rw [mul_pow]
        _ = 1 * 1 := by rw [hζ_pow, hξ_pow]
        _ = 1 := by simp
    have hprod_pow :
        primeToPRoot_powLift (p := p) (A := A) (ζ * ξ) ^ n = 1 := by
      dsimp [n]
      exact
        pow_eq_one_of_pow_eq_one_of_dvd
          (primeToPRoot_powLift_pow_orderOf (p := p) (A := A) (ζ * ξ))
          (Commute.orderOf_mul_dvd_mul_orderOf (Commute.all (ζ : kˣ) (ξ : kˣ)))
    rw [primeToPRoot_unitLift_val]
    exact
      primeToPRoot_powLift_unique (p := p) (A := A) hn hprod_pow hmul_pow <| by
        simpa [map_mul, primeToPRoot_unitLift_val]

/-- Helper for Exercise 18-18.3-2: forgetting the unit structure on the canonical lift is still
injective because reduction to the residue field recovers the original root of unity. -/
private theorem primeToPRoot_unitsLift_injective :
    Function.Injective fun ζ : PrimeToPRoot p k ↦
      ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A) := by
  intro ζ ξ hζξ
  apply Subtype.ext
  apply Units.ext
  calc
    ((ζ : kˣ) : k)
        = IsLocalRing.residue A ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A) := by
            symm
            exact residue_primeToPRoot_unitLift (p := p) (A := A) ζ
    _ =
        IsLocalRing.residue A ((primeToPRoot_unitsLift (p := p) (A := A) ξ : Aˣ) : A) := by
          exact congrArg (IsLocalRing.residue A) hζξ
    _ = ((ξ : kˣ) : k) := residue_primeToPRoot_unitLift (p := p) (A := A) ξ

/-- Helper for Exercise 18-18.3-2: the canonical source-faithful coefficient-ring lift used in the
Brauer basis is obtained by forgetting the unit structure on `primeToPRoot_unitsLift`. -/
private noncomputable def primeToPRoot_canonicalLift :
    PrimeToPRoot p k → A :=
  fun ζ ↦ ((primeToPRoot_unitsLift (p := p) (A := A) ζ : Aˣ) : A)

/-- Helper for Exercise 18-18.3-2: once the full regular indicator is known to lie in the mapped
projective-character span, dividing by the prime-to-`p` unit recovers the scaled indicator. -/
private theorem scaled_regular_indicator_mem_of_full_regular_indicator_mem
    (c : PRegularConjClass G p)
    (hfull :
      full_regular_indicator (p := p) (A := A) (K := K) (G := G) c ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))) :
    scaled_regular_indicator (p := p) (A := A) (K := K) c ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  rcases ordCompl_centralizerCard_isUnit (p := p) (A := A) (G := G) c with ⟨u, hu⟩
  have hscaled :
      ((↑u⁻¹ : A) •
          full_regular_indicator (p := p) (A := A) (K := K) (G := G) c) ∈
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) :=
    Submodule.smul_mem _ _ hfull
  have hfull_eq :
      full_regular_indicator (p := p) (A := A) (K := K) (G := G) c =
        ((↑u : A) • scaled_regular_indicator (p := p) (A := A) (K := K) c) := by
    simpa [full_regular_indicator, hu] using
      (full_regular_indicator_eq_ordCompl_smul_scaled_regular_indicator
        (p := p) (A := A) (K := K) (G := G) c)
  have hrewrite :
      ((↑u⁻¹ : A) •
          full_regular_indicator (p := p) (A := A) (K := K) (G := G) c) =
        scaled_regular_indicator (p := p) (A := A) (K := K) c := by
    rw [hfull_eq]
    simp [smul_smul]
  -- Route correction: isolate the unit-rescaling step so the remaining blocker is exactly the
  -- source-faithful projective-envelope expansion of `full_regular_indicator`.
  exact hrewrite ▸ hscaled

/-- Helper for Exercise 18-18.3-2: the centralizer `p`-part of a regular class has nonzero image
in the characteristic-zero coefficient field. This is the denominator that gets inverted in the
source orthogonality computation. -/
private theorem algebraMap_centralizerPPart_ne_zero
    (c : PRegularConjClass G p) :
    algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) ≠ 0 := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c.1)
  have hg : ConjClasses.mk g = c.1 := Classical.choose_spec (ConjClasses.mk_surjective c.1)
  have hpos : 0 < ConjClasses.centralizerPPart p c.1 := by
    rw [← hg, ConjClasses.centralizerPPart_mk, Representation.centralizerPPart]
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _
  have hneK : ((ConjClasses.centralizerPPart p c.1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  simpa using hneK

/-- Helper for Exercise 18-18.3-2: in the coefficient field, the centralizer order of a regular
class splits as its `p`-part times its prime-to-`p` complement. -/
private theorem centralizerCard_cast_eq_centralizerPPart_mul_ordCompl_cast
    (c : PRegularConjClass G p) :
    algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  -- Rewrite Serre's class-level factorization and then map it into the characteristic-zero
  -- coefficient field.
  have hcard :
      ConjClasses.centralizerCard c.1 =
        ConjClasses.centralizerPPart p c.1 *
          ordCompl[p] (ConjClasses.centralizerCard c.1) :=
    ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
      (p := p) (G := G) c.1
  simpa [map_mul] using congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard

/-- Helper for Exercise 18-18.3-2: after casting to the coefficient field, the orbit-stabilizer
identity for a regular conjugacy class becomes `|c| * |C_G(s)| = |G|`. -/
private theorem card_carrier_mul_centralizerCard_cast_eq_groupCard
    (c : PRegularConjClass G p) :
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      (Fintype.card G : K) := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c.1)
  have hg : ConjClasses.mk g = c.1 := Classical.choose_spec (ConjClasses.mk_surjective c.1)
  letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite (ConjClasses.mk g).carrier
  letI : Fintype (MulAction.stabilizer (ConjAct G) g) :=
    Fintype.ofFinite (MulAction.stabilizer (ConjAct G) g)
  have hcard_mul_nat :
      Nat.card c.1.carrier * ConjClasses.centralizerCard c.1 = Fintype.card G := by
    calc
      Nat.card c.1.carrier * ConjClasses.centralizerCard c.1 =
          Fintype.card (ConjClasses.mk g).carrier *
            Nat.card (Subgroup.centralizer ({g} : Set G)) := by
              simp [hg, ConjClasses.centralizerCard, g]
      _ =
          Fintype.card (ConjClasses.mk g).carrier *
            Nat.card (MulAction.stabilizer (ConjAct G) g) := by
              rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
      _ = Fintype.card G := by
            simpa [ConjAct.orbit_eq_carrier_conjClasses] using
              (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g)
  -- Move the natural-number identity directly into `K`, keeping the centralizer-card cast explicit.
  calc
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
      (Nat.card c.1.carrier : K) * (ConjClasses.centralizerCard c.1 : K) := by
        simp
    _ = (Fintype.card G : K) := by
        exact_mod_cast hcard_mul_nat

/-- Helper for Exercise 18-18.3-2: the class-size factor and the prime-to-`p` part of the
centralizer order combine to the inverse of the centralizer `p`-part. This is the scalar identity
used after collapsing Serre's orthogonality sum to one conjugacy class. -/
private theorem class_card_mul_ordCompl_eq_card_mul_centralizerPPart_inv
    (c : PRegularConjClass G p) :
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      (Fintype.card G : K) *
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ := by
  let x : K := algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)
  let y : K := algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
  have hmul :
      (Nat.card c.1.carrier : K) * (x * y) =
        (Fintype.card G : K) := by
    -- First rewrite the centralizer factorization in `K`, then insert the orbit-stabilizer cast.
    calc
      (Nat.card c.1.carrier : K) * (x * y) =
        (Nat.card c.1.carrier : K) *
          algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simp [x, y,
              centralizerCard_cast_eq_centralizerPPart_mul_ordCompl_cast
                (p := p) (A := A) (K := K) (G := G) c]
      _ = (Fintype.card G : K) := by
            exact
              card_carrier_mul_centralizerCard_cast_eq_groupCard
                (p := p) (A := A) (K := K) (G := G) c
  have hx_ne : x ≠ 0 := by
    -- The `p`-part is a positive power of `p`, so its image stays nonzero in the fraction field.
    exact algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) c
  calc
    (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) =
      (Nat.card c.1.carrier : K) * y := by
        simp [y]
    _ =
      ((Nat.card c.1.carrier : K) * y) * (x * x⁻¹) := by
        rw [mul_inv_cancel₀ hx_ne, mul_one]
    _ = ((Nat.card c.1.carrier : K) * (x * y)) * x⁻¹ := by
        ring
    _ = (Fintype.card G : K) * x⁻¹ := by
          rw [hmul]
    _ = (Fintype.card G : K) *
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ := by
          simp [x]

/-- Helper for Exercise 18-18.3-2: Serre's pairing with the prime-to-`p` indicator at `c`
collapses to the inverse-class regular value scaled by the inverse centralizer `p`-part. This is
the class-sum half of the orthogonality argument for part `(a)`. -/
private theorem projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
    (i : FiniteProjectiveGroupAlgebraModule k G)
    (c : PRegularConjClass G p) :
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K
                ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
        regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
          (inversePRegularConjClass (p := p) c) := by
  classical
  let Φ :=
    regularRestriction (p := p)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [i]ₚ₀)
  let a : ConjClasses G → K := fun d ↦
    if h : d = c.1 then
      Φ (inversePRegularConjClass (p := p) c) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
    else 0
  have hsum :
      ∑ s : G,
        (if hs : IsPRegular p (s⁻¹) then
          Φ (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
        else 0) *
          (if hs : IsPRegular p s then
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0) =
        ∑ s : G, a (ConjClasses.mk s) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hmk : ConjClasses.mk s = c.1
    · have hs_reg : IsPRegular p s := by
        exact c.2 s (by simpa [ConjClasses.mem_carrier_iff_mk_eq] using hmk)
      have hs_inv : IsPRegular p (s⁻¹) := by
        simpa [IsPRegular, orderOf_inv] using hs_reg
      have hInvClass :
          PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs_inv⟩ =
            inversePRegularConjClass (p := p) c := by
        apply Subtype.ext
        simpa [ConjClasses.inv_mk] using congrArg Inv.inv hmk
      -- The source sum only receives a contribution from the supporting regular class.
      rw [if_pos hs_inv, if_pos hs_reg,
        primeToP_regular_indicator_ofSubtype_eq_ordCompl
          (p := p) (A := A) (G := G) c hs_reg hmk]
      simp [a, hmk, hInvClass]
    · by_cases hs_reg : IsPRegular p s
      · -- Outside the supporting class, the point mass kills the second factor.
        rw [if_pos hs_reg,
          primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
            (p := p) (A := A) (G := G) c hs_reg hmk]
        simp [a, hmk]
      · simp [a, hmk, hs_reg]
  rw [hsum, sum_over_group_eq_sum_over_conjClasses (G := G) (K := K) a]
  have hc_mem : c.1 ∈ (Finset.univ : Finset (ConjClasses G)) := by
    simp
  rw [Finset.sum_eq_single c.1]
  · calc
      (Fintype.card G : K)⁻¹ *
          ((Nat.card c.1.carrier : K) *
            (Φ (inversePRegularConjClass (p := p) c) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)))
          =
        (Fintype.card G : K)⁻¹ *
          (((Nat.card c.1.carrier : K) *
              algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)) *
            Φ (inversePRegularConjClass (p := p) c)) := by
              ring
      _ =
        (Fintype.card G : K)⁻¹ *
          (((Fintype.card G : K) *
              (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
            Φ (inversePRegularConjClass (p := p) c)) := by
              rw [class_card_mul_ordCompl_eq_card_mul_centralizerPPart_inv
                (p := p) (A := A) (K := K) (G := G) c]
      _ =
        (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          Φ (inversePRegularConjClass (p := p) c) := by
            have hcardG_ne : (Fintype.card G : K) ≠ 0 := by
              exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
            calc
              (Fintype.card G : K)⁻¹ *
                  (((Fintype.card G : K) *
                      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                    Φ (inversePRegularConjClass (p := p) c))
                  =
                (((Fintype.card G : K)⁻¹ * (Fintype.card G : K)) *
                    (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹) *
                  Φ (inversePRegularConjClass (p := p) c) := by
                    ring
              _ =
                (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
                  Φ (inversePRegularConjClass (p := p) c) := by
                    simp [hcardG_ne]
  · intro d hd hdc
    simp [a, hdc]
  · intro hc
    exact (hc hc_mem).elim

/-- Helper for Exercise 18-18.3-2: evaluating the Brauer-basis expansion of Serre's prime-to-`p`
indicator at a regular class reads the point mass as the sum of its basis coefficients times the
corresponding basis values. -/
private theorem primeToP_regular_indicator_apply_eq_sum_basis_repr
    {ι : Type (u + 1)} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (c c' : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
    (primeToP_regular_indicator (p := p) (A := A) (G := G) c) c' =
      ∑ j, ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) * bA j c' := by
  classical
  dsimp
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
  have hsum_repr :=
    congrFun
      (bA.sum_repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c))
      c'
  -- Evaluate the basis expansion at `c'` and rewrite the scalar action pointwise as
  -- multiplication in `A`.
  simpa [bA, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hsum_repr

variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Helper for Exercise 18-18.3-2: after transporting the canonical `A`-valued Brauer basis
through `algebraMap A K`, Serre's projective-envelope pairing with its `j`-th basis vector is the
Kronecker delta. This is the source-faithful bridge from the Exercise `18.4` basis to the
characteristic-zero orthogonality relation. -/
private theorem projectiveEnvelope_pairing_primeToP_indicator_eq_basis_repr
    {ι : Type (u + 1)} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i j : ι) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
    (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
      if i = j then (1 : K) else 0 := by
  classical
  dsimp
  let liftK : PrimeToPRoot p k →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hbA_apply :
      algebraMap A (PRegularConjClass G p → K) bA j =
        FDRep.modularCharacterOnPRegularConjClass (p := p) (π j)
          (PrimeToPRoot.toFieldLift liftK) := by
    -- Transport the canonical `A`-valued Exercise `18.4` basis vector to the `K`-valued Brauer
    -- character used by Serre's orthogonality formula.
    ext c
    simp [exercise_18_18_2_9_irreducible_modular_characters_basis_apply,
      PrimeToPRoot.toFieldLift, primeToPRoot_canonicalLift, liftK]
  have hsum :
      ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            (if hs : IsPRegular p s then
              algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            else 0) =
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
            FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift liftK) s := by
    -- Rewrite the transported basis vector as the zero extension of the corresponding modular
    -- character, so the pairing can be collapsed by `projectiveEnvelope_regular_pairing_eq_delta`.
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsp : IsPRegular p s
    · simp [FDRep.modularCharacterZeroExtension, hsp]
      simpa [hsp] using
        congrArg
          (fun f : PRegularConjClass G p → K ↦
            f (PRegularConjClass.ofSubtype (G := G) p ⟨s, hsp⟩))
          hbA_apply
    · simp [FDRep.modularCharacterZeroExtension, hsp]
  rw [hsum]
  -- Now apply the already-proved projective-envelope/Brauer orthogonality relation.
  simpa [liftK] using
    (projectiveEnvelope_regular_pairing_eq_delta
      (p := p) (A := A) (K := K) (G := G)
      (lift := liftK) (π := π) (hπ_pairwise := hπ_pairwise)
      (hπ_complete := hπ_complete) (P := P) (hP_envelope := hP_envelope) i j)

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
already satisfies Serre's coordinatewise divisibility condition. -/
private theorem projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
    {ι : Type (u + 1)} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (i : ι) (c : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
        (inversePRegularConjClass (p := p) c) =
      algebraMap A K
        ((ConjClasses.centralizerPPart p c.1 : A) *
          ((bA.repr
            (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i)) := by
  classical
  dsimp
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
  have hpair_eq :
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
            (inversePRegularConjClass (p := p) c) =
        algebraMap A K
          ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
    have hindicator :
        ∀ s : G,
          (if hs : IsPRegular p s then
            algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0) =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                (if hs : IsPRegular p s then
                  algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) := by
      intro s
      by_cases hs : IsPRegular p s
      · have hsum :=
          primeToP_regular_indicator_apply_eq_sum_basis_repr
            (p := p) (A := A) (G := G)
            (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
            c (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
        -- Expand Serre's prime-to-`p` indicator in the canonical `A`-valued Brauer basis, then
        -- transport the resulting coefficient formula through `algebraMap A K`.
        simp only [hs, dif_pos]
        calc
          algebraMap A K
              ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
            =
              algebraMap A K
                (∑ j,
                  (bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c) j) *
                    bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)) := by
                  simpa [bA] using congrArg (fun x : A ↦ algebraMap A K x) hsum
          _ =
              ∑ j,
                algebraMap A K
                    ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                  algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)) := by
                  simp [map_sum, map_mul]
          _ =
              ∑ j,
                algebraMap A K
                    ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                  (if hs' : IsPRegular p s then
                    algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs'⟩))
                  else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simp [hs]
      · simp [hs]
    have h_expand :
        (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) =
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
      -- Replace Serre's prime-to-`p` indicator by its canonical Brauer-basis expansion, then
      -- collapse each basis pairing by the previous Kronecker-delta helper.
      calc
        (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0)
          =
            (Fintype.card G : K)⁻¹ *
              ∑ s : G,
                (if hs : IsPRegular p (s⁻¹) then
                  regularRestriction (p := p)
                    (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                    (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                else 0) *
                  ∑ j,
                    algebraMap A K
                        ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro s hs
                rw [hindicator s]
        _ =
            (Fintype.card G : K)⁻¹ *
              ∑ j,
                ∑ s : G,
                  algebraMap A K
                      ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                    ((if hs : IsPRegular p (s⁻¹) then
                      regularRestriction (p := p)
                        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                        (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0)) := by
                congr 1
                rw [Finset.sum_mul_sum, Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro j hj
                refine Finset.sum_congr rfl ?_
                intro s hs
                ring
        _ =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                ((Fintype.card G : K)⁻¹ *
                  ∑ s : G,
                    (if hs : IsPRegular p (s⁻¹) then
                      regularRestriction (p := p)
                        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                        (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
                    else 0) *
                      (if hs : IsPRegular p s then
                        algebraMap A K (bA j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                      else 0)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [← mul_assoc]
        _ =
            ∑ j,
              algebraMap A K
                  ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) j) *
                (if i = j then (1 : K) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                congr 1
                simpa [bA] using
                  (projectiveEnvelope_pairing_primeToP_indicator_eq_basis_repr
                    (p := p) (A := A) (K := K) (G := G)
                    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
                    (P := P) (hP_envelope := hP_envelope) i j)
        _ =
            algebraMap A K
              ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
                simpa using
                  Finsupp.total_apply_single
                    (bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i
    calc
      (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
            (inversePRegularConjClass (p := p) c)
        =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  algebraMap A K
                    ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
                      (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
                else 0) := by
            -- This is the source class-sum computation that isolates the inverse-class value.
            symm
            exact
              projectiveEnvelope_pairing_primeToP_indicator_eq_inverse_regularRestriction
                (p := p) (A := A) (K := K) (G := G) (i := P i) c
      _ =
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := h_expand
  have hppart_ne :=
    algebraMap_centralizerPPart_ne_zero (p := p) (A := A) (K := K) (G := G) c
  apply (mul_left_injective₀ hppart_ne)
  -- Clear the invertible denominator `ConjClasses.centralizerPPart p c.1` to recover Serre's
  -- divisibility statement itself.
  calc
    algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
        regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
          (inversePRegularConjClass (p := p) c)
      =
        algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
          (algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)) *
            ((algebraMap A K (ConjClasses.centralizerPPart p c.1 : A))⁻¹ *
              regularRestriction (p := p)
                (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀)
                (inversePRegularConjClass (p := p) c)) := by
          field_simp
    _ =
        algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
          algebraMap A K
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i) := by
          rw [hpair_eq]
          field_simp [hppart_ne]
    _ =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            ((bA.repr (primeToP_regular_indicator (p := p) (A := A) (G := G) c)) i)) := by
          simp [map_mul]

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
already satisfies Serre's coordinatewise divisibility condition. -/
private theorem regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
    (x : P₀[k](G)) :
    regularRestriction (p := p)
      (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  classical
  have hfamilies :
      ∃ (ι : Type (u + 1)) (_ : Fintype ι) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧
          IsCompleteIrreducibleFamily π ∧
          ∃ P : ι → FiniteProjectiveGroupAlgebraModule k G,
            ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope :=
    exists_complete_simple_family_with_projective_envelopes
  rcases hfamilies with
    ⟨ι, _, π, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  -- Route correction: first reduce the arbitrary projective class to the canonical
  -- projective-envelope basis used by Serre, then isolate the source orthogonality calculation on
  -- those generators.
  refine
    regularRestriction_projectiveCharacter_mem_of_projectiveEnvelope_generators
      (p := p) (A := A) (K := K) (G := G) (π := π)
      hπ_pairwise hπ_complete (P := P) hP_envelope ?_ x
  intro i
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  have hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)
      (regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀))).2 ?_
  intro c
  refine
    ⟨(bA.repr
      (primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c))) i, ?_⟩
  simpa [liftA, hliftA, bA, mul_comm, inversePRegularConjClass_involutive,
    ConjClasses.centralizerPPart_inv] using
    (projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) i
      (inversePRegularConjClass (p := p) c))

/-- Helper for Exercise 18-18.3-2: Serre's full indicator should first be written as an explicit
combination of the projective-envelope restrictions before passing to the scaled indicator by a
unit rescaling. -/
private theorem full_regular_indicator_eq_sum_projectiveEnvelope_restriction
    {ι : Type (u + 1)} [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (c : PRegularConjClass G p) :
    let liftA := primeToPRoot_residue_section (p := p) (A := A)
    full_regular_indicator (p := p) (A := A) (K := K) (G := G) c =
      ∑ i,
        (FDRep.modularCharacterOnPRegularConjClass (p := p) (π i) liftA
          (inversePRegularConjClass (p := p) c)) •
          regularRestriction (p := p)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀) := by
  -- Route correction: package Serre's reverse direction as an exact equality first, so the image
  -- theorem below becomes a formal `Submodule.sum_mem` corollary instead of another membership
  -- loop.
  classical
  dsimp
  ext c'
  let hliftA : Function.Injective (primeToPRoot_residue_section (p := p) (A := A)) :=
    primeToPRoot_residue_section_injective (p := p) (A := A)
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) (A := A)
      (primeToPRoot_residue_section (p := p) (A := A)) hliftA π hπ_pairwise hπ_complete
  have hsum_repr :=
    congrFun
      (bA.sum_repr
        (primeToP_regular_indicator
          (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')))
      (inversePRegularConjClass (p := p) c)
  simp only [Finset.sum_apply, Pi.mul_apply, Algebra.smul_def]
  have hvalue (i : ι) :
      regularRestriction (p := p)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P i]ₚ₀) c' =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c'.1 : A) *
            bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) := by
    simpa [bA, inversePRegularConjClass_involutive, ConjClasses.centralizerPPart_inv] using
      (projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
        (p := p) (A := A) (K := K) (G := G)
        (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (P := P) (hP_envelope := hP_envelope) i
        (inversePRegularConjClass (p := p) c'))
  simp_rw [hvalue]
  have hcoeff :
      ∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c) := by
    calc
      ∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)
          =
        ∑ i,
          (ConjClasses.centralizerPPart p c'.1 : A) *
            (bA.repr
              (primeToP_regular_indicator
                (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i *
              bA i (inversePRegularConjClass (p := p) c)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          ∑ i,
            bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i *
              bA i (inversePRegularConjClass (p := p) c) := by
            rw [Finset.mul_sum]
      _ =
        (ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c) := by
            congr 1
            simpa [bA, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hsum_repr
  symm
  calc
    ∑ i,
        (algebraMap A (PRegularConjClass G p → K))
            (FDRep.modularCharacterOnPRegularConjClass (p := p) (π i)
              (primeToPRoot_residue_section (p := p) (A := A))
              (inversePRegularConjClass (p := p) c)) c' *
          algebraMap A K
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)
        =
      ∑ i,
        algebraMap A K (bA i (inversePRegularConjClass (p := p) c)) *
          algebraMap A K
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [bA]
    _ =
      ∑ i,
        algebraMap A K
          ((bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [map_mul]
    _ =
      algebraMap A K
        (∑ i,
          (bA i (inversePRegularConjClass (p := p) c)) *
            ((ConjClasses.centralizerPPart p c'.1 : A) *
              bA.repr
                (primeToP_regular_indicator
                  (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c')) i)) := by
          simp [map_sum]
    _ = algebraMap A K
        ((ConjClasses.centralizerPPart p c'.1 : A) *
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) c'))
            (inversePRegularConjClass (p := p) c)) := by
          rw [hcoeff]
  by_cases hcc' : c' = c
  · subst c'
    have hcard :
        ConjClasses.centralizerCard c.1 =
          ConjClasses.centralizerPPart p c.1 *
            ordCompl[p] (ConjClasses.centralizerCard c.1) :=
      ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
        (p := p) (G := G) c.1
    calc
      algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) c))
              (inversePRegularConjClass (p := p) c))
          =
        algebraMap A K
          ((ConjClasses.centralizerPPart p c.1 : A) *
            (ordCompl[p]
              (ConjClasses.centralizerCard
                (inversePRegularConjClass (p := p) c : PRegularConjClass G p).1) : A)) := by
              simp [primeToP_regular_indicator]
      _ = algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simpa [map_mul, ConjClasses.centralizerCard_inv] using
              congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard.symm
      _ = full_regular_indicator (p := p) (A := A) (K := K) (G := G) c c := by
            simp [full_regular_indicator]
  · have hcc'_inv :
        inversePRegularConjClass (p := p) c' ≠ inversePRegularConjClass (p := p) c := by
      intro hInv
      exact hcc' (by
        simpa [inversePRegularConjClass_involutive] using
          congrArg (inversePRegularConjClass (p := p)) hInv)
    simp [full_regular_indicator, primeToP_regular_indicator, hcc', hcc'_inv]

/-- Helper for Exercise 18-18.3-2: each projective-character generator already lies in the
projective-character span by construction. -/
private theorem projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
    (x : P₀[k](G)) :
    projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x ∈
      projectiveCharacterSubmodule (A := A) (K := K) (G := G) := by
  -- The span owner is generated exactly by the range of `projectiveCharacterScalarExtension`.
  exact Submodule.subset_span ⟨x, rfl⟩

/-- Helper for Exercise 18-18.3-2: the regular restriction of each projective-character generator
lies in the mapped projective-character span. -/
private theorem regularRestriction_projectiveCharacter_mem_projectiveCharacter_map
    (x : P₀[k](G)) :
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  -- Use the generator itself as the witness in the mapped span.
  refine Submodule.mem_map.2 ?_
  refine
    ⟨projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x,
      projectiveCharacterScalarExtension_mem_projectiveCharacterSubmodule
        (A := A) (K := K) (G := G) x, rfl⟩

/-- Helper for Exercise 18-18.3-2: Serre's full indicator should first be written as an explicit
combination of the projective-envelope restrictions before passing to the scaled indicator by a
unit rescaling. -/
private theorem full_regular_indicator_mem_projectiveCharacter_map
    (c : PRegularConjClass G p) :
    full_regular_indicator (p := p) (A := A) (K := K) (G := G) c ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  classical
  have hfamilies :
      ∃ (ι : Type (u + 1)) (_ : Fintype ι) (π : ι → FDRep k G),
        PairwiseNonisomorphic π ∧
          IsCompleteIrreducibleFamily π ∧
          ∃ P : ι → FiniteProjectiveGroupAlgebraModule k G,
            ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope :=
    exists_complete_simple_family_with_projective_envelopes
  rcases hfamilies with
    ⟨ι, _, π, hπ_pairwise, hπ_complete, P, hP_envelope⟩
  -- Route correction: once the exact full-indicator expansion is available, this is only span
  -- bookkeeping inside the mapped projective-character submodule.
  rw [full_regular_indicator_eq_sum_projectiveEnvelope_restriction
    (p := p) (A := A) (K := K) (G := G)
    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
    (P := P) (hP_envelope := hP_envelope) c]
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact Submodule.smul_mem _ _
    (regularRestriction_projectiveCharacter_mem_projectiveCharacter_map
      (p := p) (A := A) (K := K) (G := G) [P i]ₚ₀)

/-- Helper for Exercise 18-18.3-2: each scaled regular indicator should be realized as the
regular restriction of an explicit `A`-linear combination of projective-envelope characters. -/
private theorem scaled_regular_indicator_mem_projectiveCharacter_map
    (c : PRegularConjClass G p) :
    scaled_regular_indicator (p := p) (A := A) (K := K) c ∈
      Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
  refine
    scaled_regular_indicator_mem_of_full_regular_indicator_mem
      (p := p) (A := A) (K := K) (G := G) c ?_
  exact full_regular_indicator_mem_projectiveCharacter_map
    (p := p) (A := A) (K := K) (G := G) c

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span maps exactly onto the coordinatewise divisibility lattice. -/
theorem projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  apply le_antisymm
  · -- Route correction: reduce the forward inclusion to the generator case of the projective span.
    rw [projectiveCharacterSubmodule, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    exact
      regularRestriction_projectiveCharacter_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) y
  · -- Route correction: reduce the reverse inclusion to Serre's scaled point-mass generators.
    rw [regularValueDivisibilitySubmodule_eq_span_scaled_regular_indicator
      (p := p) (A := A) (K := K) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact
      scaled_regular_indicator_mem_projectiveCharacter_map
        (p := p) (A := A) (K := K) (G := G) c

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span is controlled entirely by the regular-value divisibility condition once the
`p`-singular vanishing half is fixed. -/
theorem mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
    (Φ : A ⊗R[K](G))
    (hzero : ∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) :
    Φ ∈ projectiveCharacterSubmodule ↔
      regularRestriction (p := p) Φ ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hΦ
    -- Push a projective character through the regular-restriction map and rewrite the image using
    -- the already identified diagonal lattice.
    have hmap :
        regularRestriction (p := p) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
      exact Submodule.mem_map.2 ⟨Φ, hΦ, rfl⟩
    simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
      (p := p) (A := A) (K := K) (G := G)] using hmap
  · intro hreg
    -- Pick a projective character with the same regular restriction, then use the zero-extension
    -- formula to show it coincides with `Φ` on all of `G`.
    have hmap :
        regularRestriction (p := p) Φ ∈
          Submodule.map
            (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
            (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) := by
      simpa [projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G)] using hreg
    rcases Submodule.mem_map.1 hmap with ⟨Ψ, hΨ, hΨreg⟩
    have hzeroΨ :
        ∀ g : G, ¬ IsPRegular p g → (Ψ : G → K) g = 0 :=
      projectiveCharacterSubmodule_zero_on_pSingular (p := p) (A := A) (K := K) (G := G) hΨ
    have hΦext :=
      (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Φ).1 hzero
    have hΨext :=
      (regular_restriction_zero_extension_iff (p := p) (A := A) (K := K) (G := G) Ψ).1 hzeroΨ
    have hEq : Φ = Ψ := by
      apply Subtype.ext
      funext g
      rw [hΦext g, hΨext g]
      by_cases hg : IsPRegular p g
      · rw [dif_pos hg, dif_pos hg]
        have hregEq :=
          congrFun hΨreg (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩)
        simpa [regularRestrictionLinearMap] using hregEq.symm
      · simp [hg]
    simpa [hEq] using hΨ

/-- Helper for Exercise 18-18.3-2: after restricting to `PRegularConjClass G p`, the projective
character span should identify with the coordinatewise divisibility lattice. -/
theorem mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        regularRestriction (p := p) Φ ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hΦ
    refine ⟨?_, ?_⟩
    · exact projectiveCharacterSubmodule_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) hΦ
    · exact
        (mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
          (p := p) (A := A) (K := K) (G := G) Φ
          (projectiveCharacterSubmodule_zero_on_pSingular
            (p := p) (A := A) (K := K) (G := G) hΦ)).1 hΦ
  · rintro ⟨hzero, hreg⟩
    exact
      (mem_projectiveCharacterSubmodule_iff_regularRestriction_mem_of_zero_on_pSingular
        (p := p) (A := A) (K := K) (G := G) Φ hzero).2 hreg

-- Proof sketch: Exercise `18.4` identifies the regular restrictions of projective characters with
-- the `A`-span of the irreducible modular characters, and Exercise `18-18.2-9` makes those
-- modular characters a basis of regular class functions. The orthogonality relations then show
-- that an element of `A ⊗R[K](G)` lies in the projective span exactly when it vanishes on the
-- `p`-singular
-- locus and each regular value is divisible by the `p`-part of the corresponding centralizer.
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Exercise 18-18.3-2 (1): an element of the canonical Chapter `12` owner `A ⊗R[K](G)` belongs
to the projective-character span
`projectiveCharacterSubmodule` if and only if it vanishes on the `p`-singular elements and each
value at a `p`-regular element is divisible in `A` by the order of a `p`-Sylow subgroup of the
centralizer of that element, in the standard Chapter `18` ordinary-character regime
`[CharZero K] [HasEnoughRootsOfUnity K (Monoid.exponent G)]`. Here
`k = IsLocalRing.ResidueField A`. -/
theorem
    mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regular_values_divisible
    (Φ : A ⊗R[K](G)) :
    Φ ∈ projectiveCharacterSubmodule ↔
      (∀ g : G, ¬ IsPRegular p g → (Φ : G → K) g = 0) ∧
        ∀ g : G, IsPRegular p g →
          ∃ a : A, (Φ : G → K) g = algebraMap A K ((centralizerPPart p g : A) * a) :=
  by
    rw [mem_projectiveCharacterSubmodule_iff_zero_off_pRegular_and_regularRestriction_mem
      (p := p) (A := A) (K := K) (G := G) Φ]
    constructor
    · rintro ⟨hzero, hreg⟩
      refine ⟨hzero, ?_⟩
      intro g hg
      rcases
            (mem_regularValueDivisibilitySubmodule_iff
              (p := p) (A := A) (K := K) (G := G)
              (regularRestriction (p := p) Φ)).1 hreg
            (PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩) with
        ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha
    · rintro ⟨hzero, hdiv⟩
      refine ⟨hzero, ?_⟩
      refine
        (mem_regularValueDivisibilitySubmodule_iff
          (p := p) (A := A) (K := K) (G := G)
          (regularRestriction (p := p) Φ)).2 ?_
      intro c
      rcases c with ⟨c, hc⟩
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      have hg : IsPRegular p g := hc g (by simp [ConjClasses.mem_carrier_iff_mk_eq])
      have hsubtype :
          (⟨ConjClasses.mk g, hc⟩ : PRegularConjClass G p) =
            PRegularConjClass.ofSubtype (G := G) p ⟨g, hg⟩ := by
        apply Subtype.ext
        rfl
      rcases hdiv g hg with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [hsubtype, regularRestriction_ofSubtype, ConjClasses.centralizerPPart_mk] using ha

end ProjectiveCharacterCriterion

section LocalGramSupport

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 18-18.3-2: once a mixed-character local-ring model is fixed, the Chapter
`16` support theorem already supplies the Gram factorization needed later; the determinant
argument does not need the extra injectivity tail carried by that support theorem. -/
private theorem cartanMatrix_source_faithful_gram_eq_of_support
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    [Finite ι] [Fintype ι] [DecidableEq ι]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  -- The support theorem already packages the source-faithful Gram factorization, so only the
  -- equality component is retained here for the later determinant-sign step.
  obtain ⟨κ, hκ, hκ_dec, E, hGram, _⟩ :=
    cartanMatrix_source_faithful_gram_data_support
      (A := A) (K := K) (G := G) π P hπ_pairwise hπ_complete hP_envelope
  exact ⟨κ, hκ, hκ_dec, E, hGram⟩

end LocalGramSupport

section CartanCokernel

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable {ι : Type x}

local instance :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: the identity conjugacy class is always `p`-regular, so the
canonical owner `PRegularConjClass G p` is nonempty. -/
private theorem nonempty_pRegularConjClass :
    Nonempty (PRegularConjClass G p) := by
  -- The class of `1` gives the canonical witness needed in later cardinality arguments.
  exact ⟨PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩⟩

/-- Helper for Exercise 18-18.3-2: over the field owner used in the Cartan-cokernel branch, the
source of a projective envelope of a simple `k[G]`-module is finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_field
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero vector, so the image cannot vanish.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the canonical map from `k[G]` is surjective.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 18-18.3-2: over the field owner used in the Cartan-cokernel branch, every
simple finite-dimensional `k[G]`-representation admits a finite projective envelope. -/
private theorem exists_finite_projectiveEnvelope_of_simple_field
    (τ : FDRep k G) [CategoryTheory.Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G τ := τ.ρ
  letI : Module k[G] τ := by
    -- Expose the ambient `k[G]`-module structure carried by `τ`.
    simpa using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity gives irreducibility of the underlying representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule k[G] τ := by
    -- Move simplicity to the `k[G]`-module owner required by the envelope theorem.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] τ
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  -- Use the Artinian envelope existence theorem, then repackage the source as a finite projective
  -- `k[G]`-module.
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_field
      (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    exact (show Module.Projective k[G] P' from inferInstance)
  refine ⟨⟨Pfg, hproj⟩, ?_⟩
  refine ⟨f'.hom, ?_⟩
  simpa [Pfg, M, Rep.toModuleMonoidAlgebra] using hf'

/-- Helper for Exercise 18-18.3-2: choose a complete simple family whose index type already has
the same cardinality as `PRegularConjClass G p`. This isolates the stable cardinality input needed
for later coordinate constructions. -/
private theorem exists_complete_simple_family_with_pRegular_card :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (π : κ → FDRep k G),
      PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π ∧
        Fintype.card κ = Fintype.card (PRegularConjClass G p) := by
  classical
  obtain ⟨κ, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  letI : Finite κ := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype κ := Fintype.ofFinite κ
  refine ⟨κ, inferInstance, π, hπ_pairwise, hπ_complete, ?_⟩
  -- Corollary `18-18.2-5` identifies the simple-family cardinal with the `p`-regular
  -- conjugacy-class count.
  simpa [Nat.card_eq_fintype_card] using
    (card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
      (p := p) (E := π) hπ_pairwise hπ_complete)

/-- Helper for Exercise 18-18.3-2: choose a complete simple family together with an explicit
reindexing equivalence from its index type to the canonical owner `PRegularConjClass G p` of
`p`-regular conjugacy classes. -/
private theorem exists_complete_simple_family_reindexed_by_pRegular_classes :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (π : κ → FDRep k G),
      PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π ∧
        Nonempty (κ ≃ PRegularConjClass G p) := by
  classical
  obtain ⟨κ, _, π, hπ_pairwise, hπ_complete, hcard⟩ :=
    exists_complete_simple_family_with_pRegular_card (p := p) (k := k) (G := G)
  letI : DecidableEq κ := Classical.decEq κ
  -- The cardinality comparison from Corollary `18-18.2-5` now upgrades to an explicit reindexing
  -- equivalence that later coordinate constructions can reuse directly.
  refine ⟨κ, inferInstance, inferInstance, π, hπ_pairwise, hπ_complete, ?_⟩
  exact ⟨Fintype.equivOfCardEq hcard⟩

/-- Helper for Exercise 18-18.3-2: choose a complete simple family indexed directly by the
canonical owner `PRegularConjClass G p` of `p`-regular conjugacy classes. -/
private theorem exists_complete_simple_family_on_pRegular_classes :
    ∃ π : PRegularConjClass G p → FDRep k G,
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  rcases
      exists_complete_simple_family_reindexed_by_pRegular_classes
        (p := p) (k := k) (G := G) with
    ⟨κ, _, _, π, hπ_pairwise, hπ_complete, ⟨eκ⟩⟩
  refine ⟨π ∘ eκ.symm, ?_, ?_⟩
  · -- Reindex the pairwise-nonisomorphic family along the chosen equivalence.
    intro c c' hcc' hIso
    apply hπ_pairwise
    · intro h
      apply hcc'
      exact eκ.symm.injective h
    · simpa [Function.comp] using hIso
  · -- The same equivalence transports completeness to the canonical `p`-regular index.
    refine ⟨?_, ?_⟩
    · intro c
      simpa [Function.comp] using hπ_complete.1 (eκ.symm c)
    · intro τ hτ
      rcases hπ_complete.2 τ hτ with ⟨i, hi⟩
      refine ⟨eκ i, ?_⟩
      simpa [Function.comp] using hi

/-- Helper for Exercise 18-18.3-2: the ring-style additive owner on `R₀[k](G)` and the quotient
presentation owner used by the simple-family basis API are identified by the identity map. -/
private theorem finiteRepGrothendieck_add_owner_equiv :
    Nonempty
      (@AddEquiv (R₀[k](G)) (R₀[k](G))
        CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd) := by
  let eR₀_toEquiv : R₀[k](G) ≃ R₀[k](G) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine
    ⟨@AddEquiv.mk (R₀[k](G)) (R₀[k](G))
      CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd
      eR₀_toEquiv ?_⟩
  -- Route correction: isolate the additive-owner mismatch before composing with the simple-family
  -- basis coordinates used later in part `(b)`.
  intro x y
  show (id (x + y) : R₀[k](G)) = id x + id y
  rfl

/-- Helper for Exercise 18-18.3-2: choose simple-class coordinates on `R₀[k](G)` indexed by the
canonical owner `PRegularConjClass G p` of `p`-regular conjugacy classes. -/
private theorem finiteRepGrothendieck_add_owner_equiv_symm :
    Nonempty
      (@AddEquiv (R₀[k](G)) (R₀[k](G))
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd
        CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd) := by
  rcases finiteRepGrothendieck_add_owner_equiv (k := k) (G := G) with ⟨e⟩
  -- The owner bridge is symmetric, so the reverse identity transport is immediate.
  exact ⟨e.symm⟩

/-- Helper for Exercise 18-18.3-2: the canonical `p`-regular index set carries a simple-class
basis of the quotient-presentation owner of `R₀[k](G)`. -/
private theorem exists_simple_basis_on_pRegular_classes :
    ∃ b :
      @Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G))
        Int.instSemiring
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
        (AddCommGroup.toIntModule R₀[k](G)),
      ∀ c : PRegularConjClass G p, ∃ E : FDRep k G, Simple E ∧ b c = [E]₀ := by
  classical
  rcases
      exists_complete_simple_family_on_pRegular_classes
        (p := p) (k := k) (G := G) with
    ⟨π, hπ_pairwise, hπ_complete⟩
  refine
    ⟨simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete, ?_⟩
  intro c
  refine ⟨π c, hπ_complete.isSimple c, ?_⟩
  -- The source-faithful basis vector at `c` is exactly the class of the chosen simple module.
  simp [simple_finiteRep_classes_basis_of_complete_family_apply]

/-- Helper for Exercise 18-18.3-2: the quotient-owner simple basis transports to the ring-owner
Grothendieck group once the identity add-owner bridge is made explicit as a `ℤ`-linear
equivalence. -/
private theorem simple_basis_on_pRegular_classes_ring_owner :
    ∃ b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)),
      ∀ c : PRegularConjClass G p, ∃ E : FDRep k G, Simple E ∧ b c = [E]₀ := by
  classical
  rcases exists_simple_basis_on_pRegular_classes (p := p) (k := k) (G := G) with ⟨b, hb⟩
  let eR₀_toEquiv : R₀[k](G) ≃ R₀[k](G) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e :
      @AddEquiv (R₀[k](G)) (R₀[k](G))
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd
        CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd :=
    @AddEquiv.mk (R₀[k](G)) (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd
      CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd
      eR₀_toEquiv
      (by
        intro x y
        change (id (x + y) : R₀[k](G)) = id x + id y
        rfl)
  let eL :=
    @AddEquiv.toIntLinearEquiv
      (R₀[k](G)) (R₀[k](G))
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G))
      (finiteRepGrothendieckGroup_commRing k G).toAddCommGroup
      (AddCommGroup.toIntModule (R₀[k](G))) (by infer_instance) e
  let b' : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)) :=
    @Module.Basis.map (PRegularConjClass G p) ℤ (R₀[k](G)) (R₀[k](G))
      Int.instSemiring
      (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid
      (AddCommGroup.toIntModule (R₀[k](G)))
      CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAddCommMonoid
      (by infer_instance)
      b eL
  refine ⟨b', ?_⟩
  intro c
  rcases hb c with ⟨E, hEsimple, hE⟩
  have heL_apply (x : R₀[k](G)) : eL x = x := by
    -- The chosen owner transport is the identity on the underlying Grothendieck group.
    rfl
  refine ⟨E, hEsimple, ?_⟩
  -- Route correction: transport the quotient-owner basis by the literal identity equivalence, so
  -- the chosen simple-class basis vectors remain the same classes in the ring owner.
  simpa [b', Module.Basis.map_apply, heL_apply] using hE

/-- Helper for Exercise 18-18.3-2: transported simple-basis coordinates on the ring-owner
Grothendieck group. -/
noncomputable def regularClassCoordinateAddEquiv :
    R₀[k](G) ≃+ (PRegularConjClass G p → ℤ) :=
  LinearEquiv.toAddEquiv
    ((Classical.choose
      (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G))).equivFun)

/-- Helper for Exercise 18-18.3-2: any `PRegularConjClass`-indexed basis vector is sent by its
coordinate equivalence to the corresponding integer point mass. -/
private theorem basis_coordinateAddEquiv_apply_basis_eq_single
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
    (c : PRegularConjClass G p) :
    LinearEquiv.toAddEquiv b.equivFun (b c) =
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
  funext c'
  -- Unfold the coordinate equivalence and then read the `c'`-coordinate of the `c`-th basis
  -- vector by `repr_self`.
  change
    (b.equivFun (b c)) c' =
      (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) c'
  rw [Module.Basis.equivFun_apply]
  rw [b.repr_self]
  by_cases h : c' = c
  · subst h
    simp [Finsupp.single_apply, Pi.single_apply]
  · simp [Finsupp.single_apply, Pi.single_apply, h]

/-- Helper for Exercise 18-18.3-2: the fixed regular-class coordinate equivalence sends the
chosen simple class at `c` to the coordinate point mass at `c`. -/
private theorem regularClassCoordinateAddEquiv_chosen_simple_eq_single
    (c : PRegularConjClass G p) :
    ∃ E : FDRep k G, Simple E ∧
      regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [E]₀ =
        (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
  classical
  let hbasis :=
    simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G)
  let b := Classical.choose hbasis
  rcases (Classical.choose_spec hbasis c) with ⟨E, hEsimple, hE⟩
  refine ⟨E, hEsimple, ?_⟩
  -- Rewrite the chosen basis vector as the corresponding simple class before applying the basis
  -- coordinate computation.
  rw [← hE]
  simpa [regularClassCoordinateAddEquiv, b] using
    basis_coordinateAddEquiv_apply_basis_eq_single (p := p) (k := k) (G := G) b c

/-- Helper for Exercise 18-18.3-2: choose one simple module on each regular-class coordinate axis
together with a projective envelope. This isolates the normalization data needed before repairing
the Cartan generator theorem. -/
private theorem exists_coordinate_normalized_simples_with_projective_envelopes :
    ∃ π : PRegularConjClass G p → FDRep k G,
      (∀ c, Simple (π c)) ∧
        (∀ c,
          regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
          ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
  classical
  choose π hπ_simple hπ_coord using
    regularClassCoordinateAddEquiv_chosen_simple_eq_single (p := p) (k := k) (G := G)
  have hP_exists :
      ∀ c : PRegularConjClass G p,
        ∃ P : FiniteProjectiveGroupAlgebraModule k G,
          ∃ f : P.V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
    intro c
    letI : Simple (π c) := hπ_simple c
    -- Once the coordinate-normalized simple is fixed, use its canonical projective envelope.
    exact exists_finite_projectiveEnvelope_of_simple_field (G := G) (τ := π c)
  choose P hP using hP_exists
  refine ⟨π, hπ_simple, hπ_coord, P, ?_⟩
  intro c
  exact hP c

/-- Helper for Exercise 18-18.3-2: once the Cartan cokernel is transported to the diagonal
regular-class quotient, its cardinality is the product of the centralizer `p`-parts. -/
theorem card_cartanCokernel_eq_prod_centralizerPPart_of_nonempty_addEquiv_regularIntegerQuotient
    (h :
      Nonempty
        (cartanCokernel k G ≃+
          ((PRegularConjClass G p → ℤ) ⧸
            regularIntegerDiagonalSubmodule (p := p) (G := G)))) :
    Nat.card (cartanCokernel k G) =
      ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
  rcases h with ⟨e⟩
  -- Transport cardinality across the additive equivalence, then invoke the explicit quotient size.
  calc
    Nat.card (cartanCokernel k G) =
      Nat.card
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G)) := by
        exact Nat.card_congr e.toEquiv
    _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 :=
      card_regularIntegerQuotient_eq_prod_centralizerPPart (p := p) (G := G)

/-- Helper for Exercise 18-18.3-2: the Cartan map followed by the fixed regular-class coordinate
equivalence. -/
private noncomputable def cartanCoordinateAddHom :
    P₀[k](G) →+ (PRegularConjClass G p → ℤ) :=
  (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom.comp
    (cartanHom k G)

/-- Helper for Exercise 18-18.3-2: once the Cartan class of `x` is identified with the
centralizer-`p`-part multiple of the coordinate-normalized simple class `[π c]₀`, its image under
`cartanCoordinateAddHom` is exactly the scaled indicator at `c`. -/
private theorem cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : P₀[k](G)) (c : PRegularConjClass G p)
    (hx : cartanHom k G x = (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    cartanCoordinateAddHom (p := p) (k := k) (G := G) x =
      scaled_regular_integer_indicator (p := p) (G := G) c := by
  -- First rewrite the Cartan class through the promised scalar multiple of `[π c]₀`.
  change regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) (cartanHom k G x) =
    scaled_regular_integer_indicator (p := p) (G := G) c
  rw [hx, map_zsmul, hπ_coord c]
  -- Then evaluate the resulting multiple of the point mass coordinatewise.
  ext c'
  by_cases h : c' = c
  · subst h
    simp [scaled_regular_integer_indicator]
  · simp [scaled_regular_integer_indicator, h]

/-- Helper for Exercise 18-18.3-2: once Serre's Cartan class identity is known for a
coordinate-normalized projective-envelope family, the generator formula is a formal rewrite
through `cartanCoordinateAddHom`. This isolates the remaining mixed-character work to the
transported class identity itself. -/
private theorem coordinate_normalized_cartan_generator_formula_of_cartan_class
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    ∀ c : PRegularConjClass G p,
      cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
        scaled_regular_integer_indicator (p := p) (G := G) c := by
  intro c
  -- Read the promised Cartan class for `[P c]ₚ₀` through the already isolated coordinate lemma.
  exact
    cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord [P c]ₚ₀ c (hcartan c)

/-- Helper for Exercise 18-18.3-2: if a transported projective/simple family has the same
Grothendieck classes as the fixed coordinate-normalized family, then Serre's Cartan class identity
rewrites back to the original family indexwise. -/
private theorem transport_coordinate_normalized_cartan_class_across_class_equalities
    (π π₀ : PRegularConjClass G p → FDRep k G)
    (P P₀ : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hπ_class :
      ∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀)
    (hP_class :
      ∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀)
    (hcartan₀ :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P₀ c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀) :
    ∀ c : PRegularConjClass G p,
      cartanHom k G [P c]ₚ₀ =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  intro c
  -- Read Serre's class identity on the transported family and rewrite both sides through the
  -- indexwise class equalities.
  calc
    cartanHom k G [P c]ₚ₀ = cartanHom k G [P₀ c]ₚ₀ := by
      rw [← hP_class c]
    _ = (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀ := hcartan₀ c
    _ = (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
      rw [hπ_class c]

/-- Helper for Exercise 18-18.3-2: once the scalar-extended residue-owner family is identified
with the fixed coordinate-normalized `k`-family on Grothendieck classes, Serre's Cartan class
identity transports forward to the scalar-extended projective envelopes. -/
private theorem scalarExtension_coordinate_normalized_cartan_class_from_residue_owner
    (π π₀ : PRegularConjClass G p → FDRep k G)
    (P P₀ : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hπ_class :
      ∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀)
    (hP_class :
      ∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀)
    (hcartan :
      ∀ c : PRegularConjClass G p,
        cartanHom k G [P c]ₚ₀ =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    ∀ c : PRegularConjClass G p,
      cartanHom k G [P₀ c]ₚ₀ =
        (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀ := by
  intro c
  -- Read Serre's class identity on the reference `k`-family and rewrite both sides through the
  -- scalar-extension class equalities.
  calc
    cartanHom k G [P₀ c]ₚ₀ = cartanHom k G [P c]ₚ₀ := by
      rw [hP_class c]
    _ = (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := hcartan c
    _ = (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀ := by
      rw [← hπ_class c]

/-- Helper for Exercise 18-18.3-2: if a `PRegularConjClass`-indexed simple family is normalized
by the fixed coordinate map, then the indexing is already rigid up to isomorphism. -/
private theorem pairwiseNonisomorphic_of_regularClassCoordinate_single
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    PairwiseNonisomorphic π := by
  intro c c' hcc' hIso
  have hclass :
      ([π c]₀ : R₀[k](G)) = [π c']₀ :=
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hIso
  have hcoord_eq :=
    congrArg (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)) hclass
  rw [hπ_coord c, hπ_coord c'] at hcoord_eq
  have hvalue := congrArg (fun f : PRegularConjClass G p → ℤ ↦ f c) hcoord_eq
  simpa [Pi.single_apply, hcc'] using hvalue

/-- Helper for Exercise 18-18.3-2: a simple family whose Grothendieck classes are the fixed
coordinate point masses is already complete. -/
private theorem complete_irreducible_family_of_regularClassCoordinate_single
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    IsCompleteIrreducibleFamily π := by
  classical
  choose E hE_simple hE_coord using
    regularClassCoordinateAddEquiv_chosen_simple_eq_single (p := p) (k := k) (G := G)
  have hE_pairwise :
      PairwiseNonisomorphic E :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := E) hE_coord
  have hE_complete : IsCompleteIrreducibleFamily E := by
    rcases
        exists_complete_simple_family_on_pRegular_classes
          (p := p) (k := k) (G := G) with
      ⟨σ, hσ_pairwise, hσ_complete⟩
    let d : PRegularConjClass G p → PRegularConjClass G p := fun c ↦
      Classical.choose (hσ_complete.exists_iso (E c) (hE_simple c))
    have hd_iso :
        ∀ c, Nonempty (E c ≅ σ (d c)) := by
      intro c
      exact Classical.choose_spec (hσ_complete.exists_iso (E c) (hE_simple c))
    have hd_injective : Function.Injective d := by
      intro c c' hcc'
      by_contra hneq
      rcases hd_iso c with ⟨ec⟩
      have hc' : Nonempty (E c' ≅ σ (d c)) := by
        simpa [hcc'] using hd_iso c'
      rcases hc' with ⟨ec'⟩
      exact hE_pairwise hneq ⟨ec.trans ec'.symm⟩
    have hd_surjective : Function.Surjective d := by
      exact
        (Fintype.bijective_iff_injective_and_card d).mpr
          ⟨hd_injective, rfl⟩ |>.surjective
    refine ⟨hE_simple, ?_⟩
    intro τ hτ
    rcases hσ_complete.exists_iso τ hτ with ⟨cσ, hτσ⟩
    rcases hd_surjective cσ with ⟨c, rfl⟩
    rcases hτσ with ⟨eτσ⟩
    rcases hd_iso c with ⟨eEσ⟩
    -- Compare an arbitrary simple object with the complete reference family `σ`, then pull it
    -- back through the finite bijection from the normalized family `E`.
    exact ⟨c, ⟨eτσ.trans eEσ.symm⟩⟩
  refine ⟨hπ_simple, ?_⟩
  intro τ hτ
  rcases hE_complete.exists_iso τ hτ with ⟨c, hτE⟩
  have hclass :
      ([π c]₀ : R₀[k](G)) = [E c]₀ := by
    apply (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).injective
    rw [hπ_coord c, hE_coord c]
  have hsemiπ : IsSemisimpleRepresentation (π c).ρ := by
    letI : Simple (π c) := hπ_simple c
    letI : Representation.IsIrreducible (π c).ρ := FDRep.isIrreducible_of_simple (π c)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  have hsemiE : IsSemisimpleRepresentation (E c).ρ := by
    letI : Simple (E c) := hE_simple c
    letI : Representation.IsIrreducible (E c).ρ := FDRep.isIrreducible_of_simple (E c)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  have hπE :
      Nonempty (π c ≅ E c) :=
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple
      (E := π c) (E' := E c) hsemiπ hsemiE).mp hclass
  rcases hτE with ⟨eτE⟩
  rcases hπE with ⟨eπE⟩
  -- The normalized family `π` has the same Grothendieck classes as the complete reference family
  -- `E`, so completeness transports along those simple isomorphisms.
  exact ⟨c, ⟨eτE.trans eπE.symm⟩⟩

/-- Helper for Exercise 18-18.3-2: two complete pairwise-nonisomorphic simple families over the
same field differ only by an index reordering, and that reordering identifies the corresponding
Grothendieck classes. -/
private theorem exists_reindexing_of_complete_family_classes
    [Fintype ι] [DecidableEq ι]
    {κ : Type x} [Fintype κ] [DecidableEq κ]
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (σ : κ → FDRep k G)
    (hσ_pairwise : PairwiseNonisomorphic σ)
    (hσ_complete : IsCompleteIrreducibleFamily σ) :
    ∃ e : ι ≃ κ, ∀ i : ι, ([σ (e i)]₀ : R₀[k](G)) = [π i]₀ := by
  classical
  let e0 : ι → κ := fun i ↦
    Classical.choose (hσ_complete.exists_iso (π i) (hπ_complete.1 i))
  have he0_iso : ∀ i : ι, Nonempty (π i ≅ σ (e0 i)) := by
    intro i
    exact Classical.choose_spec (hσ_complete.exists_iso (π i) (hπ_complete.1 i))
  have he0_injective : Function.Injective e0 := by
    intro i j hij
    by_contra hij_ne
    rcases he0_iso i with ⟨ei⟩
    rcases he0_iso j with ⟨ej⟩
    -- Compare both families through the chosen target index and use pairwise nonisomorphism of
    -- the source family to force equality of indices.
    exact hπ_pairwise hij_ne ⟨ei.trans (by simpa [hij] using ej.symm)⟩
  have hcard :
      Fintype.card ι = Fintype.card κ := by
    calc
      Fintype.card ι = Nat.card (PRegularConjClass G p) := by
        simpa [Nat.card_eq_fintype_card] using
          card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
            (p := p) (E := π) hπ_pairwise hπ_complete
      _ = Fintype.card κ := by
        simpa [Nat.card_eq_fintype_card] using
          (card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
            (p := p) (E := σ) hσ_pairwise hσ_complete).symm
  have he0_bijective : Function.Bijective e0 :=
    (Fintype.bijective_iff_injective_and_card e0).mpr ⟨he0_injective, hcard⟩
  let e : ι ≃ κ := Equiv.ofBijective e0 he0_bijective
  refine ⟨e, ?_⟩
  intro i
  -- After fixing the reindexing equivalence, each slot is identified by the chosen simple
  -- isomorphism, hence by equality of Grothendieck classes.
  simpa [e, e0] using
    (finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G) (he0_iso i)).symm

/-- Helper for Exercise 18-18.3-2: bundle the chosen coordinate-normalized simple family with the
pairwise-nonisomorphic and completeness facts that are already forced by its coordinate formulas.
This isolates the remaining mixed-character work to the Cartan generator identity itself. -/
private theorem exists_coordinate_normalized_complete_family_with_projective_envelopes :
    ∃ π : PRegularConjClass G p → FDRep k G,
      (∀ c, Simple (π c)) ∧
        (∀ c,
          regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
        PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π ∧
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
          ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope := by
  classical
  rcases
      exists_coordinate_normalized_simples_with_projective_envelopes
        (p := p) (k := k) (G := G) with
    ⟨π, hπ_simple, hπ_coord, P, hP_envelope⟩
  have hπ_pairwise :
      PairwiseNonisomorphic π :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) π hπ_coord
  have hπ_complete :
      IsCompleteIrreducibleFamily π :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) π hπ_simple hπ_coord
  -- The coordinate-normalized family already carries all basis-theoretic structure needed later;
  -- only the mixed-character Cartan generator formula remains to be transported.
  exact ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩

/-- Helper for Exercise 18-18.3-2: if two `PRegularConjClass`-indexed families hit the same
regular-class coordinate point masses, then their Grothendieck classes agree indexwise. -/
private theorem finiteRepClass_eq_of_coordinate_normalized_families
    (π₀ π : PRegularConjClass G p → FDRep k G)
    (hπ₀_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π₀ c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    ∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀ := by
  intro c
  -- The regular-class coordinate equivalence is injective, so the common point mass at `c`
  -- already pins down the underlying Grothendieck class.
  apply (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).injective
  rw [hπ₀_coord c, hπ_coord c]

/-- Helper for Exercise 18-18.3-2: an isomorphism in `FDRep k G` induces the corresponding
`k[G]`-linear equivalence on the underlying owner modules. -/
private theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso
    {σ τ : FDRep k G}
    (hστ : Nonempty (σ ≅ τ)) :
    Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ) := by
  rcases hστ with ⟨e⟩
  -- Forget the `FDRep` isomorphism to `Rep`, then read its image in `ModuleCat k[G]`.
  exact ⟨by
    simpa using
      (((forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra
        (k := k) (G := G)).mapIso e).toLinearEquiv⟩

/-- Helper for Exercise 18-18.3-2: once the simple targets agree classwise, the corresponding
projective-envelope sources have the same projective Grothendieck classes. -/
private theorem finiteProjectiveClass_eq_of_projectiveEnvelope_simple_class_eq
    {ι : Type x}
    (π₀ π : ι → FDRep k G)
    (hπ₀_simple : ∀ i, Simple (π₀ i))
    (hπ_simple : ∀ i, Simple (π i))
    (P₀ P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP₀_envelope :
      ∀ i, ∃ f₀ : (P₀ i).V →ₗ[k[G]] asModule (π₀ i).ρ, f₀.IsProjectiveEnvelope)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hπ_class : ∀ i, ([π₀ i]₀ : R₀[k](G)) = [π i]₀) :
    ∀ i, ([P₀ i]ₚ₀ : P₀[k](G)) = [P i]ₚ₀ := by
  intro i
  have hsemi₀ : IsSemisimpleRepresentation (π₀ i).ρ := by
    letI : Simple (π₀ i) := hπ₀_simple i
    letI : Representation.IsIrreducible (π₀ i).ρ := FDRep.isIrreducible_of_simple (π₀ i)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  have hsemi : IsSemisimpleRepresentation (π i).ρ := by
    letI : Simple (π i) := hπ_simple i
    letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  have hπ_iso : Nonempty (π₀ i ≅ π i) :=
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple
      (E := π₀ i) (E' := π i) hsemi₀ hsemi).mp (hπ_class i)
  rcases
      nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso
        (k := k) (G := G) hπ_iso with
    ⟨eTarget⟩
  let f₀ : (P₀ i).V →ₗ[k[G]] asModule (π₀ i).ρ := Classical.choose (hP₀_envelope i)
  have hf₀ : f₀.IsProjectiveEnvelope := Classical.choose_spec (hP₀_envelope i)
  let f : (P i).V →ₗ[k[G]] asModule (π i).ρ := Classical.choose (hP_envelope i)
  have hf : f.IsProjectiveEnvelope := Classical.choose_spec (hP_envelope i)
  let f' : (P i).V →ₗ[k[G]] asModule (π₀ i).ρ := eTarget.symm.toLinearMap.comp f
  have hf' : f'.IsProjectiveEnvelope := by
    letI : f'.IsEssential := by
      refine ⟨?_⟩
      intro N hN
      -- Transport essentiality across the target equivalence before invoking uniqueness.
      have hmap : (N.map f).map eTarget.symm.toLinearMap = ⊤ := by
        simpa [f', Submodule.map_comp] using hN
      have hmap_top : N.map f = ⊤ := by
        exact (Submodule.map_eq_top_iff (p := N.map f) (e := eTarget.symm)).1 hmap
      exact hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
    -- Surjectivity of the projective envelope is preserved by the same target transport.
    refine LinearMap.IsProjectiveEnvelope.mk ?_
    intro y
    obtain ⟨x, hx⟩ := hf.surjective (eTarget y)
    refine ⟨x, ?_⟩
    simpa [f', hx]
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hf₀ hf'
  have hP_iso : Nonempty (P₀ i ≅ P i) := by
    -- Two projective envelopes of isomorphic simple targets are isomorphic on their sources.
    exact
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (A := k) (G := G) (P₀ i) (P i)).2 ⟨eSrc⟩
  -- Read the resulting source isomorphism in the projective Grothendieck group.
  exact
    finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
      (A := k) (G := G) hP_iso

/-- Helper for Exercise 18-18.3-2: part `(b)` only needs the transported Cartan-range equality on
regular classes, not a generator-level projective-envelope formula. -/
private theorem exists_mixed_character_model_over_algClosed_residueField :
    ∃ (A0 : Type u) (_ : CommRing A0) (_ : IsLocalRing A0) (_ : HenselianLocalRing A0)
      (_ : IsDomain A0) (_ : IsDiscreteValuationRing A0)
      (K0 : Type u) (_ : Field K0) (_ : Algebra A0 K0) (_ : IsFractionRing A0 K0)
      (_ : CharZero K0) (_ : HasEnoughRootsOfUnity K0 (Monoid.exponent G)),
        IsLocalRing.ResidueField A0 ≃+* k := by
  -- Route correction: both remaining part `(b)` gaps are blocked by the same source-faithful
  -- owner package, namely a mixed-character DVR with residue field `k`.
  obtain ⟨A1, _, _, _, _, _, _, K1, _, _, _, _, e1, ζp, hζp⟩ :=
    exists_totally_ramified_p_power_root_extension_over_wittVector (p := p) (k := k) (G := G)
  let _ : IsAlgClosed (IsLocalRing.ResidueField A1) :=
    IsAlgClosed.of_ringEquiv _ e1.symm
  let _ : CharP (IsLocalRing.ResidueField A1) p :=
    charP_of_injective_ringHom e1.injective p
  let n := Monoid.exponent G
  let m := ordCompl[p] n
  have hn_ne : n ≠ 0 := by
    simpa [n] using (show Monoid.exponent G ≠ 0 from NeZero.ne (Monoid.exponent G))
  have hm_ne : m ≠ 0 := (Nat.ordCompl_pos p hn_ne).ne'
  have hm_coprime : Nat.Coprime p m := Nat.coprime_ordCompl (Fact.out : Nat.Prime p) hn_ne
  have hm_not_dvd : ¬ p ∣ m :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hm_coprime
  let _ : NeZero ((m : ℕ) : IsLocalRing.ResidueField A1) :=
    NeZero.of_not_dvd (R := IsLocalRing.ResidueField A1) hm_not_dvd
  obtain ⟨ξ0, hξ0⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (IsLocalRing.ResidueField A1) m
  let ξ :
      PrimeToPRoot p (IsLocalRing.ResidueField A1) :=
    PrimeToPRoot.ofRootsOfUnity hm_coprime hξ0.toRootsOfUnity
  have hξ_residue :
      IsPrimitiveRoot
        ((ξ : PrimeToPRoot p (IsLocalRing.ResidueField A1)) :
          (IsLocalRing.ResidueField A1)ˣ) m := by
    -- The chosen prime-to-`p` root comes directly from a primitive `m`-th root in the residue
    -- field, so it keeps the same order there.
    change
      IsPrimitiveRoot
        ((hξ0.toRootsOfUnity : rootsOfUnity m (IsLocalRing.ResidueField A1)) :
          (IsLocalRing.ResidueField A1)ˣ) m
    simpa using hξ0.isUnit_unit hm_ne
  have hprimeToP_inj :
      Function.Injective (primeToPRoot_unitsLift (p := p) (A := A1)) := by
    intro ζ ξ hζξ
    apply primeToPRoot_unitsLift_injective (p := p) (A := A1)
    exact congrArg (fun u : A1ˣ ↦ (u : A1)) hζξ
  have hξ_A1 :
      IsPrimitiveRoot
        (primeToPRoot_unitsLift (p := p) (A := A1) ξ) m :=
    hξ_residue.map_of_injective hprimeToP_inj
  let ξK1u : K1ˣ :=
    Units.map (algebraMap A1 K1).toMonoidHom
      (primeToPRoot_unitsLift (p := p) (A := A1) ξ)
  have hξ_K1u : IsPrimitiveRoot ξK1u m :=
    hξ_A1.map_of_injective <|
      Units.map_injective (f := (algebraMap A1 K1).toMonoidHom)
        (IsFractionRing.injective A1 K1)
  have hξ_K1 : IsPrimitiveRoot (ξK1u : K1) m := by
    exact IsPrimitiveRoot.coe_units_iff.mpr hξ_K1u
  have hp_pow_coprime :
      Nat.Coprime (p ^ Nat.factorization n p) m :=
    hm_coprime.pow_left (Nat.factorization n p)
  have hp_pow_ne : p ^ Nat.factorization n p ≠ 0 :=
    pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero
  let ζ : K1 :=
    ζp ^ ((p ^ Nat.factorization n p) / Nat.factorizationLCMLeft (p ^ Nat.factorization n p) m) *
      (ξK1u : K1) ^ (m / Nat.factorizationLCMRight (p ^ Nat.factorization n p) m)
  have hζ :
      IsPrimitiveRoot ζ (Nat.lcm (p ^ Nat.factorization n p) m) := by
    -- Serre's source route combines the `p`-power primitive root with the coprime prime-to-`p`
    -- lift into a primitive root of order the full exponent.
    simpa [ζ] using
      IsPrimitiveRoot.pow_mul_pow_lcm hζp hξ_K1 hp_pow_ne hm_ne
  have horder :
      Nat.lcm (p ^ Nat.factorization n p) m = n := by
    calc
      Nat.lcm (p ^ Nat.factorization n p) m =
          p ^ Nat.factorization n p * m := hp_pow_coprime.lcm_eq_mul
      _ = ordProj[p] n * ordCompl[p] n := by
            simp [m]
      _ = n := Nat.ordProj_mul_ordCompl_eq_self n p
  let hEnough : HasEnoughRootsOfUnity K1 n :=
    { prim := by
        refine ⟨ζ, horder ▸ hζ⟩
      cyc := rootsOfUnity.isCyclic K1 n }
  -- The assembled owner now has both the correct residue field and enough roots of unity for the
  -- Chapter `16` input.
  exact
    ⟨A1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      K1, inferInstance, inferInstance, inferInstance, inferInstance, hEnough, e1⟩

/-- Helper for Exercise 18-18.3-2: scalar extension along a field map carries a family of
projective envelopes to a family of projective envelopes over the scalar-extended simple family.
This isolates the already-solved module-level transport from the remaining residue-field
class-coordinate comparison. -/
private theorem scalarExtension_projectiveEnvelope_family
    {k₀ : Type u} [Field k₀] [Algebra k₀ k]
    {ι : Type x}
    (π : ι → FDRep k₀ G)
    (P : ι → FiniteProjectiveGroupAlgebraModule k₀ G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k₀[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ P₀ : ι → FiniteProjectiveGroupAlgebraModule k G,
      ∀ i, ∃ f₀ : (P₀ i).V →ₗ[k[G]] asModule (FDRep.scalarExtension (k := k) (π i)).ρ,
        f₀.IsProjectiveEnvelope := by
  classical
  let P₀ : ι → FiniteProjectiveGroupAlgebraModule k G := fun i ↦
    let V₀ : ModuleCat k[G] := ModuleCat.of k[G] (TensorProduct k₀ k (P i).V)
    let hfinite : Module.Finite k[G] V₀ := by
      change Module.Finite k[G] (TensorProduct k₀ k (P i).V)
      infer_instance
    let Vfg : FGModuleCat k[G] := ⟨V₀, hfinite⟩
    let hproj : Module.Projective k[G] Vfg := by
      change Module.Projective k[G] (TensorProduct k₀ k (P i).V)
      infer_instance
    ⟨Vfg, hproj⟩
  refine ⟨P₀, ?_⟩
  intro i
  refine ⟨(Classical.choose (hP_envelope i)).baseChange k, ?_⟩
  -- The projective-envelope property is already preserved by base change along the field map.
  simpa [P₀] using (Classical.choose_spec (hP_envelope i)).baseChange k

/-- Helper for Exercise 18-18.3-2: once the residue-field owner `e0` is fixed, the remaining
source-faithful step for part `(b)` is to compare the scalar-extended residue-owner
coordinate-normalized family with the fixed `k`-family on Grothendieck classes and then transport
Serre's Cartan class identity across those equalities. -/
private theorem residueField_equiv_transport_coordinate_normalized_family_data
    {A0 : Type u} [CommRing A0] [IsLocalRing A0]
    (e0 : IsLocalRing.ResidueField A0 ≃+* k)
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (πr : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A0) G)
    (hπr_simple : ∀ c, Simple (πr c))
    (hπr_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A0) (G := G) [πr c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (Pr : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A0) G)
    (hPr_envelope :
      ∀ c, ∃ f : (Pr c).V →ₗ[(IsLocalRing.ResidueField A0)[G]] asModule (πr c).ρ,
        f.IsProjectiveEnvelope)
    (π₀ : PRegularConjClass G p → FDRep k G)
    (hπ₀_def : π₀ = fun c ↦ FDRep.scalarExtension (k := k) (πr c))
    (P₀ : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP₀_envelope :
      ∀ c, ∃ f : (P₀ c).V →ₗ[k[G]] asModule (π₀ c).ρ, f.IsProjectiveEnvelope) :
    (∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀) ∧
      (∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀) ∧
        (∀ c : PRegularConjClass G p,
          cartanHom k G [P₀ c]ₚ₀ =
            (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀) := by
  -- Route correction: the only remaining source-faithful task is the coordinate-rigidity
  -- comparison between the scalar-extended residue-owner family and the fixed normalized
  -- `k`-family, after which the Cartan class identity is transported verbatim.
  have hπ₀_simple : ∀ c, Simple (π₀ c) := by
    intro c
    rw [hπ₀_def]
    letI : Simple (πr c) := hπr_simple c
    infer_instance
  let _ := e0
  let _ := hπ_simple
  let _ := hπ_coord
  let _ := hP_envelope
  let _ := hπr_simple
  let _ := hπr_coord
  let _ := hPr_envelope
  let _ := hπ₀_def
  let _ := hP₀_envelope
  have hπ_class_of_coord :
      (∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π₀ c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) →
        ∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀ := by
    intro hπ₀_coord
    -- Once the transported family is shown to hit the same coordinate axes, class equality is
    -- rigid.
    exact
      finiteRepClass_eq_of_coordinate_normalized_families
        (p := p) (k := k) (G := G) π₀ π hπ₀_coord hπ_coord
  have hP_class_of_coord :
      (∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π₀ c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) →
        ∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀ := by
    intro hπ₀_coord
    -- After the simple classes match, projective-envelope uniqueness supplies the projective
    -- class comparison formally.
    exact
      finiteProjectiveClass_eq_of_projectiveEnvelope_simple_class_eq
        (k := k) (G := G) π₀ π
        hπ₀_simple hπ_simple P₀ P hP₀_envelope hP_envelope
        (hπ_class_of_coord hπ₀_coord)
  have hcartan₀_of_coord :
      (∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π₀ c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) →
        (∀ c : PRegularConjClass G p,
          cartanHom k G [P c]ₚ₀ =
            (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) →
          ∀ c : PRegularConjClass G p,
            cartanHom k G [P₀ c]ₚ₀ =
              (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀ := by
    intro hπ₀_coord hcartan
    -- Once the scalar-extended simple and projective classes are identified, the Cartan class
    -- formula moves forward by pure rewriting.
    exact
      scalarExtension_coordinate_normalized_cartan_class_from_residue_owner
        (p := p) (k := k) (G := G) (π := π) (π₀ := π₀) (P := P) (P₀ := P₀)
        (hπ_class_of_coord hπ₀_coord) (hP_class_of_coord hπ₀_coord) hcartan
  let _ := hπ_class_of_coord
  let _ := hP_class_of_coord
  let _ := hcartan₀_of_coord
  -- TODO: prove the remaining scalar-extension coordinate bridge
  -- `hπ₀_coord : ∀ c, regularClassCoordinateAddEquiv [π₀ c]₀ = Pi.single c 1`
  -- by the source-faithful route from the re-plan:
  -- 1. compare `FDRep.modularCharacterOnPRegularConjClass` for `π₀ c` and `π c`;
  -- 2. turn that Brauer-character equality into `([π₀ c]₀ : R₀[k](G)) = [π c]₀` via
  --    `finiteRepGrothendieckClass_eq_of_modularCharacterOnPRegularConjClass_eq`;
  -- 3. recover the coordinate-single formula by rewriting with `hπ_coord`;
  -- 4. if a source Cartan-class identity for one normalized family is available, transport the
  --    projective-envelope classes and the Cartan class identity formally via
  --    `hP_class_of_coord` and `hcartan₀_of_coord`.
  sorry

/-- Helper for Exercise 18-18.3-2: once the same residue-field comparison identifies the
scalar-extended residue-owner complete family with the given complete family, the Chapter `16`
Gram factorization rewrites directly to the target Cartan matrix. -/
private theorem residueField_equiv_transport_complete_family_gram_data
    {A0 : Type u} [CommRing A0] [IsLocalRing A0] [HenselianLocalRing A0]
    {K0 : Type u} [Field K0] [Algebra A0 K0] [IsFractionRing A0 K0] [CharZero K0]
    (e0 : IsLocalRing.ResidueField A0 ≃+* k)
    [HasEnoughRootsOfUnity K0 (Monoid.exponent G)]
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (πr : ι → FDRep (IsLocalRing.ResidueField A0) G)
    (hπr_pairwise : CategoryTheory.PairwiseNonisomorphic πr)
    (hπr_complete : IsCompleteIrreducibleFamily πr)
    (Pr : ι → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A0) G)
    (hPr_envelope :
      ∀ i, ∃ f : (Pr i).V →ₗ[(IsLocalRing.ResidueField A0)[G]] asModule (πr i).ρ,
        f.IsProjectiveEnvelope)
    (π₀ : ι → FDRep k G)
    (hπ₀_def : π₀ = fun i ↦ FDRep.scalarExtension (k := k) (πr i))
    (P₀ : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP₀_envelope :
      ∀ i, ∃ f : (P₀ i).V →ₗ[k[G]] asModule (π₀ i).ρ, f.IsProjectiveEnvelope) :
    ∃ hπ₀_pairwise : CategoryTheory.PairwiseNonisomorphic π₀,
      ∃ hπ₀_complete : IsCompleteIrreducibleFamily π₀,
        (∀ i : ι, ([π₀ i]₀ : R₀[k](G)) = [π i]₀) ∧
          (∀ i : ι, ([P₀ i]ₚ₀ : P₀[k](G)) = [P i]ₚ₀) ∧
            ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
              cartanMatrix k G
                  (projectiveEnvelope_classes_basis_of_complete_family
                    π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope)
                  (simple_finiteRep_classes_basis_of_complete_family
                    π₀ hπ₀_pairwise hπ₀_complete) =
                E.transpose * E := by
  -- Route correction: the mixed-character owner and the Chapter `16` support theorem are already
  -- fixed; the remaining source-faithful blocker is only the class comparison that rewrites the
  -- scalar-extended residue-owner family back to the chosen `k`-family.
  -- The current statement is only usable once an explicit index alignment between the arbitrary
  -- complete family `π` and the transported family `π₀` has been supplied. The unresolved work is
  -- therefore structural transport, not matrix theory.
  let _ := e0
  let _ := hπ_pairwise
  let _ := hπ_complete
  let _ := hP_envelope
  let _ := hπr_pairwise
  let _ := hπr_complete
  let _ := hPr_envelope
  let _ := hπ₀_def
  let _ := hP₀_envelope
  -- TODO: the old pointwise comparison shape was too strong. The next step is now explicit:
  -- first use `exists_reindexing_of_complete_family_classes` to align the arbitrary complete
  -- family `π` with the transported family `π₀` by an equivalence of index types, then rewrite
  -- the Cartan matrix across that reindexing before applying
  -- `cartanMatrix_eq_of_complete_family_class_equalities`.
  sorry

/-- Helper for Exercise 18-18.3-2: after choosing the coordinate-normalized simple family, Serre's
mixed-character argument should supply projective envelopes whose Cartan images are the scaled
regular indicators. This is the exact generator package needed by the generic range theorem
already proved below. -/
private theorem
    exists_coordinate_normalized_projective_family_with_cartan_generator_formula :
    ∃ π : PRegularConjClass G p → FDRep k G,
      (∀ c, Simple (π c)) ∧
        (∀ c,
          regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
            (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
        ∃ P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G,
          (∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope) ∧
            (∀ c : PRegularConjClass G p,
              cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
                scaled_regular_integer_indicator (p := p) (G := G) c) := by
  -- Route correction: the source proof only needs Cartan generators on the chosen regular-class
  -- axes, not a stronger theorem about all projective envelopes at once.
  obtain ⟨A0, _, _, _, _, _, K0, _, _, _, _, _, e0⟩ :=
    exists_mixed_character_model_over_algClosed_residueField (p := p) (A := A) (K := K) (G := G)
  obtain ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope⟩ :=
    exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := k) (G := G)
  let _ : Algebra (IsLocalRing.ResidueField A0) k := e0.toRingHom.toAlgebra
  let _ : IsAlgClosed (IsLocalRing.ResidueField A0) :=
    IsAlgClosed.of_ringEquiv _ e0
  let _ : CharP (IsLocalRing.ResidueField A0) p :=
    charP_of_injective_ringHom e0.injective p
  obtain ⟨πr, hπr_simple, hπr_coord, hπr_pairwise, hπr_complete, Pr, hPr_envelope⟩ :=
    exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := IsLocalRing.ResidueField A0) (G := G)
  let π₀ : PRegularConjClass G p → FDRep k G := fun c ↦
    FDRep.scalarExtension (k := k) (πr c)
  have hπ₀_simple : ∀ c, Simple (π₀ c) := by
    intro c
    letI : Simple (πr c) := hπr_simple c
    infer_instance
  obtain ⟨P₀, hP₀_envelope⟩ :=
    scalarExtension_projectiveEnvelope_family
      (k := k) (G := G) (π := πr) (P := Pr) hPr_envelope
  refine ⟨π, hπ_simple, hπ_coord, P, hP_envelope, ?_⟩
  -- Route correction: the existential packaging is now reduced to the single transported class
  -- identity `cartanHom [P c]ₚ₀ = centralizerPPart(c) • [π c]₀` for the fixed normalized family.
  refine
    coordinate_normalized_cartan_generator_formula_of_cartan_class
      (p := p) (k := k) (G := G) (π := π) hπ_coord (P := P) ?_
  have htransport :
      (∀ c : PRegularConjClass G p, ([π₀ c]₀ : R₀[k](G)) = [π c]₀) ∧
        (∀ c : PRegularConjClass G p, ([P₀ c]ₚ₀ : P₀[k](G)) = [P c]ₚ₀) ∧
          (∀ c : PRegularConjClass G p,
            cartanHom k G [P₀ c]ₚ₀ =
              (ConjClasses.centralizerPPart p c.1 : ℤ) • [π₀ c]₀) :=
    residueField_equiv_transport_coordinate_normalized_family_data
      (p := p) (k := k) (G := G) (A0 := A0) e0
      π hπ_simple hπ_coord P hP_envelope
      πr hπr_simple hπr_coord Pr hPr_envelope
      π₀ rfl P₀ hP₀_envelope
  rcases htransport with ⟨hπ_class, hP_class, hcartan₀⟩
  -- Once the transported family is rewritten back by class equality, the fixed normalized family
  -- inherits the same Cartan class formula.
  exact
    transport_coordinate_normalized_cartan_class_across_class_equalities
      (p := p) (k := k) (G := G) (π := π) (π₀ := π₀) (P := P) (P₀ := P₀)
      hπ_class hP_class hcartan₀

/-- Helper for Exercise 18-18.3-2: once the Cartan generator images are identified, the full
Cartan range becomes the diagonal lattice by a formal basis expansion. -/
private theorem cartan_range_map_eq_regularIntegerDiagonal_of_generator_formula
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[k[G]] asModule (π c).ρ, f.IsProjectiveEnvelope)
    (hgen :
      ∀ c : PRegularConjClass G p,
        cartanCoordinateAddHom (p := p) (k := k) (G := G) [P c]ₚ₀ =
          scaled_regular_integer_indicator (p := p) (G := G) c) :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family π hπ_pairwise hπ_complete P hP_envelope
  let f := cartanCoordinateAddHom (p := p) (k := k) (G := G)
  apply AddSubgroup.toIntSubmodule.injective
  apply le_antisymm
  · intro y hy
    rcases AddSubgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    change f x ∈ regularIntegerDiagonalSubmodule (p := p) (G := G)
    have hfx :
        f x = ∑ c, (bP.repr x c) • f (bP c) := by
      -- Expand `x` in the projective-envelope basis and push the additive Cartan-coordinate map
      -- through that basis expansion.
      symm
      calc
        ∑ c, (bP.repr x c) • f (bP c) = ∑ c, f ((bP.repr x c) • bP c) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [map_zsmul]
        _ = f (∑ c, (bP.repr x c) • bP c) := by
          rw [map_sum]
        _ = f x := by
          rw [bP.sum_repr x]
    rw [hfx]
    refine Submodule.sum_mem _ ?_
    intro c hc
    have hc_eq :
        f (bP c) = scaled_regular_integer_indicator (p := p) (G := G) c := by
      simpa [f, bP, cartanCoordinateAddHom,
        projectiveEnvelope_classes_basis_of_complete_family_apply] using hgen c
    rw [hc_eq]
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator (p := p) (G := G)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator (p := p) (G := G)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    change scaled_regular_integer_indicator (p := p) (G := G) c ∈
      ((cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom).toIntSubmodule
    have hc_mem :
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanHom k G).range.map
            (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom := by
      rw [← hgen c]
      exact AddSubgroup.mem_map.2 ⟨cartanHom k G [P c]ₚ₀, ⟨[P c]ₚ₀, rfl⟩, rfl⟩
    exact hc_mem

/-- Helper for Exercise 18-18.3-2: part `(b)` only needs the transported Cartan-range equality on
regular classes, not a generator-level projective-envelope formula. -/
private theorem
    regularClassCoordinateAddEquiv_map_cartan_range_eq_regularIntegerDiagonalSubmodule_direct :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  rcases
      exists_coordinate_normalized_projective_family_with_cartan_generator_formula
        (p := p) (k := k) (G := G) with
    ⟨π, hπ_simple, hπ_coord, P, hP_envelope, hgen⟩
  have hπ_pairwise :
      PairwiseNonisomorphic π :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) π hπ_coord
  have hπ_complete : IsCompleteIrreducibleFamily π :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) π hπ_simple hπ_coord
  -- Once the mixed-character generator formula is available for the normalized family, the range
  -- equality is exactly the generic basis argument already packaged above.
  exact
    cartan_range_map_eq_regularIntegerDiagonal_of_generator_formula
      (p := p) (k := k) (G := G) π hπ_pairwise hπ_complete P hP_envelope hgen

/-- Helper for Exercise 18-18.3-2: once the Cartan image is identified with the diagonal lattice,
the cokernel becomes the corresponding quotient of regular-class functions. -/
theorem regularClassCoordinateAddEquiv_map_cartan_range_eq_regularIntegerDiagonalSubmodule :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  -- Reuse the direct range-level theorem so the public statement matches the source-facing
  -- subgroup equality needed for the cokernel computation.
  exact
    regularClassCoordinateAddEquiv_map_cartan_range_eq_regularIntegerDiagonalSubmodule_direct
      (p := p) (k := k) (G := G)

/-- Helper for Exercise 18-18.3-2: once the Cartan image is identified with the diagonal lattice,
the cokernel becomes the corresponding quotient of regular-class functions. -/
theorem exists_regular_class_coordinate_equiv_with_cartan_range_diagonal :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  let e := regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
  refine ⟨e, ?_⟩
  -- The coordinate equivalence is fixed explicitly, so only the transported Cartan-image equality
  -- from the previous helper remains.
  simpa [e] using
    regularClassCoordinateAddEquiv_map_cartan_range_eq_regularIntegerDiagonalSubmodule
      (p := p) (k := k) (G := G)

/-- Helper for Exercise 18-18.3-2: once the Cartan image is identified with the diagonal lattice,
the cokernel becomes the corresponding quotient of regular-class functions. -/
theorem cartanCokernel_nonempty_addEquiv_regularIntegerQuotient :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          regularIntegerDiagonalSubmodule (p := p) (G := G))) := by
  rcases
      exists_regular_class_coordinate_equiv_with_cartan_range_diagonal
        (p := p) (k := k) (G := G) with
    ⟨e, he⟩
  -- Transport the Cartan cokernel across the coordinate equivalence once its image is diagonal.
  refine ⟨?_⟩
  simpa [cartanCokernel] using
    (QuotientAddGroup.congr
      (cartanHom k G).range
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
      e he)

-- Proof sketch: part `(1)` computes the invariant factors of the Cartan map on the canonical
-- owner `PRegularConjClass G p` by evaluating projective characters classwise on the `p`-regular
-- conjugacy classes. Passing to Smith normal form gives a decomposition of the cokernel into the
-- corresponding cyclic groups.
/-- Exercise 18-18.3-2 (2): the cokernel of the Cartan homomorphism `c : P_k(G) → R_k(G)` is
isomorphic to the product, over the canonical owner `PRegularConjClass G p`, of the cyclic groups
`ℤ / ConjClasses.centralizerPPart p c.1 ℤ`. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  by
    -- Route correction: the formal quotient splitting is handled separately by
    -- `regularIntegerQuotient_addEquiv_pi_centralizerPPart`, so only the Cartan-image transport
    -- remains in theorem `(1)`.
    rcases
        cartanCokernel_nonempty_addEquiv_regularIntegerQuotient (p := p) (k := k) (G := G) with
      ⟨e⟩
    -- Compose the Cartan-image quotient equivalence with the coordinatewise cyclic splitting.
    exact
      ⟨e.trans
        (regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G))⟩

-- Proof sketch: the previous cokernel decomposition identifies the invariant factors of the
-- distinguished Cartan matrix with the centralizer `p`-parts attached to the `p`-regular
-- conjugacy classes of `G`. Since the determinant of an integer matrix in Smith normal form is
-- the product of its invariant factors, the determinant of the canonical Cartan matrix attached to
-- a complete simple family and its projective envelopes is the product of these classwise
-- integers, equivalently `p ^ (∑ z(s))` in Serre's notation after choosing representatives.
/-- Helper for Exercise 18-18.3-2: once the Cartan cokernel is transported to the diagonal
regular-class quotient, the absolute value of the distinguished Cartan determinant is the product
of the centralizer `p`-parts. -/
theorem cartanMatrix_det_natAbs_eq_prod_centralizerPPart
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    by
      letI : Finite ι := by
        letI : Nonempty (PRegularConjClass G p) :=
          nonempty_pRegularConjClass (p := p) (G := G)
        have hcard :
            Nat.card ι = Nat.card (PRegularConjClass G p) :=
          card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
            (p := p) (E := π) hπ_pairwise hπ_complete
        exact Nat.finite_of_card_ne_zero <| by
          rw [hcard]
          exact Nat.card_pos.ne'
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
      letI : DecidableEq (PRegularConjClass G p) := Classical.decEq (PRegularConjClass G p)
      exact
        Int.natAbs
          (Matrix.det
            (cartanMatrix k G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete))) =
          ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1
  := by
    letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    let bP :=
      projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope
    let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
    have hdet_card :
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G) := by
      have hcartan : Function.Injective (cartanHom k G) :=
        Representation.cartanHom_injective
      let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
        AddMonoidHom.ofInjective hcartan
      let bRange : Module.Basis ι ℤ (cartanHom k G).range :=
        Module.Basis.map bP eRange.toIntLinearEquiv
      have hindex :
          (cartanHom k G).range.index =
            Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) := by
        -- Compare the range index with the determinant in the distinguished Cartan bases.
        rw [AddSubgroup.index_eq_natAbs_det bR (cartanHom k G).range bRange]
        congr 1
        have hbRange :
            (fun i ↦ ((bRange i : (cartanHom k G).range) : R₀[k](G))) =
              (cartanHom k G) ∘ bP := by
          ext i
          change ↑(eRange (bP i)) = cartanHom k G (bP i)
          simpa [eRange] using
            (AddMonoidHom.ofInjective_apply (f := cartanHom k G) hcartan (x := bP i))
        rw [hbRange, Module.Basis.det_apply]
        congr
        ext i j
        simp [cartanMatrix, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
      -- The Cartan cokernel is exactly the quotient by the Cartan-image subgroup.
      calc
        Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
            (cartanHom k G).range.index := hindex.symm
        _ = Nat.card (cartanCokernel k G) := by
          simpa [cartanCokernel] using
            (AddSubgroup.index_eq_card (H := (cartanHom k G).range) (G := R₀[k](G)))
    -- Replace the Cartan-cokernel cardinality by the already established diagonal quotient size.
    calc
      Int.natAbs (Matrix.det (cartanMatrix k G bP bR)) =
          Nat.card (cartanCokernel k G) := hdet_card
      _ = ∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 := by
          exact
            card_cartanCokernel_eq_prod_centralizerPPart_of_nonempty_addEquiv_regularIntegerQuotient
              (p := p) (k := k) (G := G)
              (cartanCokernel_nonempty_addEquiv_regularIntegerQuotient
                (p := p) (k := k) (G := G))

/-- Helper for Exercise 18-18.3-2: once the determinant is known to be nonnegative, the
corresponding `Int.natAbs` identity upgrades to an equality in `ℤ`. -/
theorem int_eq_natAbs_of_nonneg {z : ℤ} {n : ℕ}
    (hnatAbs : Int.natAbs z = n) (hz : 0 ≤ z) :
    z = n := by
  -- Replace `Int.natAbs z` by `z` using nonnegativity, then rewrite with the known absolute-value
  -- formula.
  calc
    z = (Int.natAbs z : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = n := by rw [hnatAbs]

/-- Helper for Exercise 18-18.3-2: any integral Gram matrix has nonnegative determinant. -/
private theorem Matrix.int_gram_det_nonneg
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (E : Matrix κ η ℤ) :
    0 ≤ Matrix.det (E.transpose * E) := by
  let Eℝ : Matrix κ η ℝ := E.map (Int.castRingHom ℝ)
  have hpsd : Matrix.PosSemidef (Eℝ.transpose * Eℝ) := by
    -- After casting to `ℝ`, a Gram matrix is visibly positive semidefinite.
    simpa [Eℝ] using Matrix.posSemidef_conjTranspose_mul_self Eℝ
  have hmap :
      (E.transpose * E).map (Int.castRingHom ℝ) = Eℝ.transpose * Eℝ := by
    -- Entrywise casting commutes with transpose and matrix multiplication.
    ext i j
    simp [Eℝ, Matrix.mul_apply]
  have hdet_nonneg : 0 ≤ Matrix.det (Eℝ.transpose * Eℝ) :=
    Matrix.PosSemidef.det_nonneg hpsd
  have hcast :
      (((Matrix.det (E.transpose * E) : ℤ)) : ℝ) =
        Matrix.det (Eℝ.transpose * Eℝ) := by
    -- Rewrite the determinant after casting the integral entries to `ℝ`.
    rw [Int.cast_det]
    simpa [hmap] using congrArg Matrix.det hmap
  have hreal : 0 ≤ (((Matrix.det (E.transpose * E) : ℤ)) : ℝ) := by
    rw [hcast]
    exact hdet_nonneg
  exact_mod_cast hreal

/-- Helper for Exercise 18-18.3-2: once the source-faithful Cartan argument produces a Gram
factorization `C = Eᵀ * E`, determinant nonnegativity is a pure integral matrix fact. -/
private theorem Matrix.int_det_nonneg_of_eq_transpose_mul_self
    {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]
    (C : Matrix η η ℤ) (E : Matrix κ η ℤ)
    (hC : C = E.transpose * E) :
    0 ≤ Matrix.det C := by
  -- Replace `C` by the exhibited Gram matrix and apply the previous determinant-sign lemma.
  simpa [hC] using Matrix.int_gram_det_nonneg E

/-- Helper for Exercise 18-18.3-2: if two complete simple/projective families represent the same
Grothendieck basis classes indexwise, then their distinguished Cartan matrices coincide. -/
private theorem cartanMatrix_eq_of_complete_family_class_equalities
    [Fintype ι] [DecidableEq ι]
    (π π₀ : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ₀_pairwise : CategoryTheory.PairwiseNonisomorphic π₀)
    (hπ₀_complete : IsCompleteIrreducibleFamily π₀)
    (P P₀ : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope)
    (hP₀_envelope :
      ∀ i, ∃ f : (P₀ i).V →ₗ[k[G]] asModule (π₀ i).ρ, f.IsProjectiveEnvelope)
    (hπ_class : ∀ i : ι, ([π₀ i]₀ : R₀[k](G)) = [π i]₀)
    (hP_class : ∀ i : ι, ([P₀ i]ₚ₀ : P₀[k](G)) = [P i]ₚ₀) :
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete) := by
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let bP₀ :=
    projectiveEnvelope_classes_basis_of_complete_family
      π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR₀ :=
    simple_finiteRep_classes_basis_of_complete_family π₀ hπ₀_pairwise hπ₀_complete
  have hbP : bP = bP₀ := by
    ext i
    -- The projective-envelope bases are identical once their basis vectors agree classwise.
    simpa [bP, bP₀, projectiveEnvelope_classes_basis_of_complete_family_apply] using
      (hP_class i).symm
  have hbR : bR = bR₀ := by
    ext i
    -- The same indexwise class equality identifies the complete-family simple bases.
    simpa [bR, bR₀, simple_finiteRep_classes_basis_of_complete_family_apply] using
      (hπ_class i).symm
  -- After the two basis families are identified, the Cartan matrices are definitionally the
  -- same matrix.
  rw [hbP, hbR]

/-- Helper for Exercise 18-18.3-2: when the local ring is already a field, its residue field is
canonically the same field. This isolates the residue-field transport that remains available even
before the mixed-character model is constructed. -/
private noncomputable def residueField_ringEquiv_of_field
    (k : Type u) [Field k] :
    IsLocalRing.ResidueField k ≃+* k := by
  classical
  refine
    { toFun := IsLocalRing.ResidueField.lift (RingHom.id k)
      invFun := IsLocalRing.residue k
      left_inv := ?_
      right_inv := ?_
      map_mul' := by simp
      map_add' := by simp }
  · -- Every residue-field element comes from some field element, so the two maps cancel on
    -- representatives.
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := k) x
    simp
  · -- On the field itself, reducing and then lifting along the identity changes nothing.
    intro x
    simp

/-- Helper for Exercise 18-18.3-2: the canonical residue-field equivalence equips `k` with the
expected algebra structure over `ResidueField k`. This is the scalar input needed for later
transport steps in the determinant branch. -/
@[reducible]
private noncomputable def residueField_algebra_of_field :
    Algebra (IsLocalRing.ResidueField k) k :=
  (residueField_ringEquiv_of_field k).toRingHom.toAlgebra

/-- Helper for Exercise 18-18.3-2: under the canonical residue-field algebra on a field, the
algebra map is exactly the residue-field equivalence itself. -/
@[simp]
private theorem residueField_algebraMap_eq_ringEquiv_of_field :
    algebraMap (IsLocalRing.ResidueField k) k =
      (residueField_ringEquiv_of_field k).toRingHom := by
  rfl

/-- Helper for Exercise 18-18.3-2: the canonical field-residue equivalence sends the residue
class of a field element back to that element. This is the normalization step later transport
arguments use when `e0` specializes to an identity owner. -/
@[simp]
private theorem residueField_ringEquiv_of_field_apply_residue (x : k) :
    residueField_ringEquiv_of_field k (IsLocalRing.residue k x) = x := by
  -- Reduce to the defining left-right inverse data of the canonical residue-field equivalence.
  simp [residueField_ringEquiv_of_field]

/-- Helper for Exercise 18-18.3-2: the Chapter `16` Gram factorization should be transportable
directly to an algebraically closed residue field `k` of characteristic `p`. -/
private theorem cartanMatrix_source_faithful_gram_data_via_mixed_character_model
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  -- Route correction: the determinant branch shares the same mixed-character owner as the Cartan
  -- range theorem, so the remaining work is to instantiate the Chapter `16` support theorem over
  -- that owner and transport the resulting Gram identity back to `k`.
  obtain ⟨A0, _, _, _, _, _, K0, _, _, _, _, _, e0⟩ :=
    exists_mixed_character_model_over_algClosed_residueField (p := p) (A := A) (K := K) (G := G)
  let _ : Algebra (IsLocalRing.ResidueField A0) k := e0.toRingHom.toAlgebra
  let _ : IsAlgClosed (IsLocalRing.ResidueField A0) :=
    IsAlgClosed.of_ringEquiv _ e0
  let _ : CharP (IsLocalRing.ResidueField A0) p :=
    charP_of_injective_ringHom e0.injective p
  obtain ⟨πr, hπr_simple, hπr_coord, hπr_pairwise, hπr_complete, Pr, hPr_envelope⟩ :=
    exists_coordinate_normalized_complete_family_with_projective_envelopes
      (p := p) (k := IsLocalRing.ResidueField A0) (G := G)
  let π₀ : ι → FDRep k G := fun i ↦ FDRep.scalarExtension (k := k) (πr i)
  obtain ⟨P₀, hP₀_envelope⟩ :=
    scalarExtension_projectiveEnvelope_family
      (k := k) (G := G) (π := πr) (P := Pr) hPr_envelope
  obtain ⟨hπ₀_pairwise, hπ₀_complete, hπ_class, hP_class, κ, hκ, hκ_dec, E, hGram₀⟩ :=
    residueField_equiv_transport_complete_family_gram_data
      (p := p) (k := k) (G := G) (ι := ι) (A0 := A0) (K0 := K0) e0
      (π := π) hπ_pairwise hπ_complete (P := P) hP_envelope
      (πr := πr) hπr_pairwise hπr_complete (Pr := Pr) hPr_envelope
      π₀ rfl P₀ hP₀_envelope
  refine ⟨κ, hκ, hκ_dec, E, ?_⟩
  -- Rewrite the transported Gram identity back to the original complete family through the
  -- already isolated basis-class equalities.
  calc
    cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete P hP_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete) =
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete P₀ hP₀_envelope)
        (simple_finiteRep_classes_basis_of_complete_family
          π₀ hπ₀_pairwise hπ₀_complete) := by
            exact
              cartanMatrix_eq_of_complete_family_class_equalities
                (p := p) (k := k) (G := G)
                (π := π) (π₀ := π₀)
                hπ_pairwise hπ_complete hπ₀_pairwise hπ₀_complete
                (P := P) (P₀ := P₀) hP_envelope hP₀_envelope hπ_class hP_class
    _ = E.transpose * E := hGram₀

/-- Helper for Exercise 18-18.3-2: the Chapter `16` Gram factorization should be transportable
directly to an algebraically closed residue field `k` of characteristic `p`. -/
private theorem cartanMatrix_source_faithful_gram_data_over_algClosed_residueField
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (_ : DecidableEq κ) (E : Matrix κ ι ℤ),
      cartanMatrix k G
        (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete) =
        E.transpose * E := by
  -- Delegate to the mixed-character transport front so the public determinant argument only sees
  -- the final Gram identity it needs.
  exact
    cartanMatrix_source_faithful_gram_data_via_mixed_character_model
      (p := p) (k := k) (G := G) π hπ_pairwise hπ_complete P hP_envelope

/-- Helper for Exercise 18-18.3-2: the distinguished Cartan determinant is nonnegative. -/
theorem cartanMatrix_det_nonneg
    [Fintype ι] [DecidableEq ι]
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    0 ≤
      Matrix.det
        (cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete)) := by
  obtain ⟨κ, _, _, E, hGram⟩ :=
    cartanMatrix_source_faithful_gram_data_over_algClosed_residueField
      π hπ_pairwise hπ_complete P hP_envelope
  -- Once the mixed-character bridge exposes `C = Eᵀ * E`, determinant nonnegativity is a pure
  -- integral Gram-matrix argument.
  exact
    Matrix.int_det_nonneg_of_eq_transpose_mul_self
      (C :=
        cartanMatrix k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope)
          (simple_finiteRep_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete))
      E hGram

/-- Helper for Exercise 18-18.3-2: the product of the centralizer `p`-parts in `ℤ` is just the
coercion of the corresponding product in `ℕ`. -/
theorem int_prod_centralizerPPart_eq_natCast :
    (∏ c : PRegularConjClass G p, (ConjClasses.centralizerPPart p c.1 : ℤ)) =
      ((∏ c : PRegularConjClass G p, ConjClasses.centralizerPPart p c.1 : ℕ) : ℤ) := by
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  -- Move the coercion across the finite product coordinatewise.
  symm
  simpa using
    (Nat.cast_prod (R := ℤ) (s := Finset.univ)
      (f := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1))

/-- Exercise 18-18.3-2 (3): the determinant of the distinguished Cartan matrix written in the
canonical simple and projective-envelope bases is the product, over the canonical owner
`PRegularConjClass G p`, of the centralizer `p`-parts of the `p`-regular conjugacy classes of
`G`. -/
theorem cartanMatrix_det_eq_prod_centralizerPPart
    (π : ι → FDRep k G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : ι → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    by
      letI : Finite ι := by
        letI : Nonempty (PRegularConjClass G p) :=
          nonempty_pRegularConjClass (p := p) (G := G)
        have hcard :
            Nat.card ι = Nat.card (PRegularConjClass G p) :=
          card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
            (p := p) (E := π) hπ_pairwise hπ_complete
        exact Nat.finite_of_card_ne_zero <| by
          rw [hcard]
          exact Nat.card_pos.ne'
      letI : Fintype ι := Fintype.ofFinite ι
      letI : DecidableEq ι := Classical.decEq ι
      letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
      letI : DecidableEq (PRegularConjClass G p) := Classical.decEq (PRegularConjClass G p)
      exact
        Matrix.det
            (cartanMatrix k G
              (projectiveEnvelope_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete P hP_envelope)
              (simple_finiteRep_classes_basis_of_complete_family
                π hπ_pairwise hπ_complete)) =
          ∏ c : PRegularConjClass G p, (ConjClasses.centralizerPPart p c.1 : ℤ)
  := by
    letI : Finite ι := by
      letI : Nonempty (PRegularConjClass G p) :=
        nonempty_pRegularConjClass (p := p) (G := G)
      have hcard :
          Nat.card ι = Nat.card (PRegularConjClass G p) :=
        card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
          (p := p) (E := π) hπ_pairwise hπ_complete
      exact Nat.finite_of_card_ne_zero <| by
        rw [hcard]
        exact Nat.card_pos.ne'
    letI : Fintype ι := Fintype.ofFinite ι
    letI : DecidableEq ι := Classical.decEq ι
    -- Rewrite the determinant through its absolute value, then use the nonnegativity bridge to
    -- remove `Int.natAbs` and rewrite the right-hand side from `ℕ` to `ℤ`.
    rw [int_prod_centralizerPPart_eq_natCast (p := p) (G := G)]
    simpa using
      int_eq_natAbs_of_nonneg
        (cartanMatrix_det_natAbs_eq_prod_centralizerPPart
          (p := p) (k := k) (G := G) (ι := ι)
          π hπ_pairwise hπ_complete P hP_envelope)
        (cartanMatrix_det_nonneg
          π hπ_pairwise hπ_complete P hP_envelope)

end CartanCokernel

end Representation
