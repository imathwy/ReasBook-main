import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCharacterSpan
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.DecompositionComparison

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
-- Serre's Chapter 18 modular system uses a *complete* DVR `A`; the projective scalar-extension
-- owner `projectiveCharacterScalarExtension` requires adic completeness of the maximal ideal.
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
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
local instance instFintypeGProjectiveTriangle : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 18-18.3-2: restricting the ordinary character of a virtual class
`y : R₀[K](G)` to a chosen `p`-regular representative recovers the virtual modular character of
its decomposition class at that representative. -/
theorem regularRestriction_finiteRepGrothendieckCharacter_eq_virtualModularCharacterOnPRegular
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (y : R₀[K](G))
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
      (p := p) (B := A) (K := K) (G := G) lift hred hω y) s).symm

/-- Helper for Exercise 18-18.3-2: the sum of two projective Grothendieck generator classes is
again represented by an actual finite projective module. -/
theorem exists_projective_class_sum_rep
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
      (A := R) (G := G) T ⟨LinearEquiv.refl (MonoidAlgebra R G) (P.V × Q.V)⟩

/-- Helper for Exercise 18-18.3-2: every class in the projective Grothendieck group is a
difference of two actual projective generator classes. -/
theorem exists_projective_class_difference_rep
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
theorem projectiveGrothendieckBaseChangeHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckBaseChangeHom K ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.scalarExtension K]₀ - [R.scalarExtension K]₀ := by
  -- Expand the additive map on a difference and evaluate it on each actual projective generator.
  rw [map_sub, projectiveGrothendieckBaseChangeHom_projectiveClass_eq,
    projectiveGrothendieckBaseChangeHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: reduction sends a difference of actual lifted projective
generator classes to the corresponding difference of residue-field generator classes. -/
theorem projectiveGrothendieckReductionHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckReductionHom (A := A) (G := G) ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.residueFieldReduction]ₚ₀ - [R.residueFieldReduction]ₚ₀ := by
  -- Expand the additive reduction map on a difference and evaluate it on each actual projective
  -- generator.
  rw [map_sub, projectiveGrothendieckReductionHom_projectiveClass_eq,
    projectiveGrothendieckReductionHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: the Cartan homomorphism sends a difference of projective
generator classes to the corresponding difference of finite-representation classes. -/
theorem cartanHom_sub_projectiveClass_eq
    (Q R : FiniteProjectiveGroupAlgebraModule k G) :
    cartanHom k G ([Q]ₚ₀ - [R]ₚ₀) =
      [Q.toFiniteRep]₀ - [R.toFiniteRep]₀ := by
  -- Expand the additive map on a difference and then read it on each projective generator class.
  rw [map_sub, cartanHom_projectiveClass_eq, cartanHom_projectiveClass_eq]

/-- Helper for Exercise 18-18.3-2: applying the Cartan map to the reduction classes of two
lifted projectives gives the difference of the corresponding reduced finite-representation
classes. -/
theorem cartanHom_sub_residueFieldReduction_projectiveClass_eq
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
theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_of_lift_data
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
theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class
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
theorem cartanHom_residueFieldReduction_projectiveClass_eq
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
theorem decompositionHom_baseChange_sub_eq_cartan_sub_of_lift_data
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

/-- Helper for Exercise 18-18.3-2: the pointwise `d ∘ e = c` triangle packaged as an equality of
additive homomorphisms. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_hom :
    (decompositionHom A K G).comp
        (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)) =
      cartanHom k G := by
  apply AddMonoidHom.ext
  intro x
  exact
    decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
      (A := A) (K := K) (G := G) x

/-- Helper for Exercise 18-18.3-2: under the decomposition map, the range of the projective
Grothendieck scalar-extension homomorphism is exactly the Cartan range. -/
theorem decompositionHom_map_projectiveGrothendieckScalarExtensionHom_range_eq_cartanHom_range :
    (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range.map
        (decompositionHom A K G) =
      (cartanHom k G).range := by
  ext y
  constructor
  · intro hy
    rcases AddSubgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    exact
      ⟨x,
        (decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
          (A := A) (K := K) (G := G) x).symm⟩
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact AddSubgroup.mem_map.2
      ⟨(projectiveGrothendieckScalarExtensionHom A K) x, ⟨x, rfl⟩,
        decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
          (A := A) (K := K) (G := G) x⟩

/-- Helper for Exercise 18-18.3-2: regular restriction of projective scalar-extension characters,
viewed as an additive homomorphism on the projective Grothendieck group. -/
noncomputable def projectiveCharacterRegularRestrictionHom :
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

/-- Helper for Exercise 18-18.3-2: mapping the projective-character span by regular restriction
is the `A`-submodule spanned by the additive range of projective regular-restriction rows. -/
theorem projectiveCharacterSubmodule_map_regularRestriction_eq_span_projectiveCharacterRegularRestrictionHom_range :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      Submodule.span A
        ((projectiveCharacterRegularRestrictionHom (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) := by
  rw [projectiveCharacterSubmodule, Submodule.map_span]
  apply congrArg (Submodule.span A)
  ext f
  constructor
  · rintro ⟨Φ, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact
      ⟨projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x,
        ⟨x, rfl⟩, rfl⟩

/-- Helper for Exercise 18-18.3-2: the regular restriction of a projective scalar-extension
character agrees with the Brauer character of its Cartan image on each chosen `p`-regular
representative. -/
theorem regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegular_cartan
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (x : P₀[k](G))
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
      (p := p) (A := A) (K := K) (G := G) lift hred hω (e x) s

/-- Helper for Exercise 18-18.3-2: the regular-restriction row of a projective scalar-extension
character is the descended virtual modular character of its Cartan image. -/
theorem
    regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegularConjClass_cartan
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (x : P₀[k](G)) :
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift lift) (cartanHom k G x) := by
  ext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  rw [← hs, virtualModularCharacterOnPRegularConjClass_ofSubtype]
  exact
    regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegular_cartan
      (p := p) (A := A) (K := K) (G := G) lift hred hω x s

/-- Helper for Exercise 18-18.3-2: the projective regular-restriction additive homomorphism is
the descended virtual modular character map after the Cartan homomorphism. -/
theorem projectiveCharacterRegularRestrictionHom_eq_virtualModularCharacterOnPRegularConjClass_comp_cartanHom
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) :
    projectiveCharacterRegularRestrictionHom (p := p) (A := A) (K := K) (G := G) =
      (virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift lift)).comp (cartanHom k G) := by
  apply AddMonoidHom.ext
  intro x
  ext c
  simpa [projectiveCharacterRegularRestrictionHom] using
    congrFun
      (regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegularConjClass_cartan
        (p := p) (A := A) (K := K) (G := G) lift hred hω x) c

/-- Helper for Exercise 18-18.3-2: the range of projective regular-restriction rows is the image
of the Cartan range under the descended virtual modular character map. -/
theorem
    projectiveCharacterRegularRestrictionHom_range_eq_virtualModularCharacterOnPRegularConjClass_cartanHom_range
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) :
    (projectiveCharacterRegularRestrictionHom (p := p) (A := A) (K := K) (G := G)).range =
      (cartanHom k G).range.map
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift lift)) := by
  rw [projectiveCharacterRegularRestrictionHom_eq_virtualModularCharacterOnPRegularConjClass_comp_cartanHom
    (p := p) (A := A) (K := K) (G := G) lift hred hω]
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact AddSubgroup.mem_map.2 ⟨cartanHom k G x, ⟨x, rfl⟩, rfl⟩
  · intro hf
    rcases AddSubgroup.mem_map.1 hf with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Exercise 18-18.3-2: after regular restriction, the projective-character span is
the `A`-span of the Cartan range as read by descended virtual modular characters. -/
theorem
    projectiveCharacterSubmodule_map_regularRestriction_eq_span_virtualModularCharacterOnPRegularConjClass_cartanHom_range
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      Submodule.span A
        (((cartanHom k G).range.map
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift lift))) :
          Set (PRegularConjClass G p → K)) := by
  rw [projectiveCharacterSubmodule_map_regularRestriction_eq_span_projectiveCharacterRegularRestrictionHom_range
    (p := p) (A := A) (K := K) (G := G)]
  rw [projectiveCharacterRegularRestrictionHom_range_eq_virtualModularCharacterOnPRegularConjClass_cartanHom_range
    (p := p) (A := A) (K := K) (G := G) lift hred hω]
end ProjectiveCharacterCriterion

end Representation
