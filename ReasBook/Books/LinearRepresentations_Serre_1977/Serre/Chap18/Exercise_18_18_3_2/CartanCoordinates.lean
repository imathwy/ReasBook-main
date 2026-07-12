import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibility
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.DiagonalQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

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
theorem nonempty_pRegularConjClass :
    Nonempty (PRegularConjClass G p) := by
  -- The class of `1` gives the canonical witness needed in later cardinality arguments.
  exact ⟨PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩⟩

/-- Helper for Exercise 18-18.3-2: over the field owner used in the Cartan-cokernel branch, the
source of a projective envelope of a simple `k[G]`-module is finitely generated. -/
theorem moduleFinite_of_projectiveEnvelope_simple_field
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
simple finite-dimensional `k[G]`-representation has a finite projective envelope. -/
theorem exists_finite_projectiveEnvelope_of_simple_field
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
theorem exists_complete_simple_family_with_pRegular_card :
    ∃ (κ : Type (u + 1)) (_ : Fintype κ) (π : κ → FDRep k G),
      PairwiseNonisomorphic π ∧
        IsCompleteIrreducibleFamily π ∧
        Fintype.card κ = Fintype.card (PRegularConjClass G p) := by
  classical
  obtain ⟨κ, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_basis_support (k := k) (G := G)
  -- Route correction: in characteristic `p` the index type is finite because the Brauer
  -- characters form a basis of the finite-dimensional regular class-function space.
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite κ :=
    Module.Finite.finite_basis
      (irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
        π hπ_pairwise hπ_complete)
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
theorem exists_complete_simple_family_reindexed_by_pRegular_classes :
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
theorem exists_complete_simple_family_on_pRegular_classes :
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
theorem finiteRepGrothendieck_add_owner_equiv :
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
theorem finiteRepGrothendieck_add_owner_equiv_symm :
    Nonempty
      (@AddEquiv (R₀[k](G)) (R₀[k](G))
        (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAdd
        CommRing.toNonUnitalCommRing.toNonUnitalNonAssocCommRing.toNonUnitalNonAssocSemiring.toAdd) := by
  rcases finiteRepGrothendieck_add_owner_equiv (k := k) (G := G) with ⟨e⟩
  -- The owner bridge is symmetric, so the reverse identity transport is immediate.
  exact ⟨e.symm⟩

/-- Helper for Exercise 18-18.3-2: the canonical `p`-regular index set carries a simple-class
basis of the quotient-presentation owner of `R₀[k](G)`. -/
theorem exists_simple_basis_on_pRegular_classes :
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
theorem simple_basis_on_pRegular_classes_ring_owner :
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
theorem basis_coordinateAddEquiv_apply_basis_eq_single
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
theorem regularClassCoordinateAddEquiv_chosen_simple_eq_single
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
theorem exists_coordinate_normalized_simples_with_projective_envelopes :
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
noncomputable def cartanCoordinateAddHom :
    P₀[k](G) →+ (PRegularConjClass G p → ℤ) :=
  (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom.comp
    (cartanHom k G)

/-- Helper for Exercise 18-18.3-2: once the Cartan class of `x` is identified with the
centralizer-`p`-part multiple of the coordinate-normalized simple class `[π c]₀`, its image under
`cartanCoordinateAddHom` is exactly the scaled indicator at `c`. -/
theorem cartanCoordinateAddHom_eq_scaled_regular_integer_indicator_of_cartan_class
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
theorem coordinate_normalized_cartan_generator_formula_of_cartan_class
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
theorem transport_coordinate_normalized_cartan_class_across_class_equalities
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
theorem scalarExtension_coordinate_normalized_cartan_class_from_residue_owner
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
theorem pairwiseNonisomorphic_of_regularClassCoordinate_single
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
theorem complete_irreducible_family_of_regularClassCoordinate_single
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

include p in
/-- Helper for Exercise 18-18.3-2: two complete pairwise-nonisomorphic simple families over the
same field differ only by an index reordering, and that reordering identifies the corresponding
Grothendieck classes. -/
theorem exists_reindexing_of_complete_family_classes
    [Fintype ι] [DecidableEq ι]
    {κ : Type w} [Fintype κ] [DecidableEq κ]
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
theorem exists_coordinate_normalized_complete_family_with_projective_envelopes :
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
theorem finiteRepClass_eq_of_coordinate_normalized_families
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
theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso
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
theorem finiteProjectiveClass_eq_of_projectiveEnvelope_simple_class_eq
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
  obtain ⟨eSrc, _⟩ :=
    @LinearMap.isProjectiveEnvelope_unique k[G] _ (asModule (π₀ i).ρ) _
      (Representation.instModuleMonoidAlgebraAsModule (ρ := (π₀ i).ρ))
      _ _ _ _ _ _ f₀ f' hf₀ hf'
  have hP_iso : Nonempty (P₀ i ≅ P i) := by
    -- Two projective envelopes of isomorphic simple targets are isomorphic on their sources.
    exact
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (A := k) (G := G) (P₀ i) (P i)).2 ⟨eSrc⟩
  -- Read the resulting source isomorphism in the projective Grothendieck group.
  exact
    finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
      (A := k) (G := G) hP_iso
end CartanCokernel

end Representation
