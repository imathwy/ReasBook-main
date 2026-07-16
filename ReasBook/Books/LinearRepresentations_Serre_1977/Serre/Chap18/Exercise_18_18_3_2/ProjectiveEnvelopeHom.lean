import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Corollary_18_18_2_5
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveTriangle

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
local instance instFintypeGProjectiveEnvelopeHom : Fintype G := Fintype.ofFinite G

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

/-- Helper for Exercise 18-18.3-2: every simple finite-dimensional `k[G]`-representation has a
finite projective envelope in the canonical owner of projective modules. -/
theorem exists_finite_projectiveEnvelope_of_simple
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

include p in
/-- Helper for Exercise 18-18.3-2: choose a complete simple family together with projective
envelopes for each chosen simple. -/
theorem exists_complete_simple_family_with_projective_envelopes :
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
  -- Route correction: in characteristic `p` the index type is finite because the Brauer
  -- characters form a basis of the finite-dimensional regular class-function space (the
  -- semisimple `finite_index` owner needs `NeZero (|G| : k)`, unavailable here).
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite ι :=
    Module.Finite.finite_basis
      (irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
        π hπ_pairwise hπ_complete)
  exact ⟨ι, Fintype.ofFinite ι, π, hπ_pairwise, hπ_complete, P, hP⟩

/-- Helper for Exercise 18-18.3-2: the Jacobson-radical quotient of a chosen projective envelope
source is the corresponding simple target. -/
theorem projectiveEnvelope_jacobson_quotient_linearEquiv_target
    {ι : Type x}
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
noncomputable def fdRep_homLinearEquiv_moduleHomSpace
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
noncomputable def fdRep_homLinearEquiv_intertwiningSpace
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
theorem jacobson_le_ker_of_simple_target
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
theorem fdRep_nonempty_iso_of_hom_ne_zero
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
theorem simple_fdRep_hom_finrank_eq_delta
    {ι : Type x}
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
theorem projectiveEnvelope_hom_finrank_eq_simple_hom_finrank
    {ι : Type x}
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
noncomputable def regularRestrictionProjectiveCharacterAddHom :
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
theorem regularRestriction_projectiveCharacter_mem_of_projectiveEnvelope_generators
    {ι : Type x} [Fintype ι]
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
theorem regularRestriction_projectiveCharacter_zeroExtension_eq_projectiveLiftCharacter
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
    have hzero :=
      projectiveLiftCharacter_eq_zero_of_not_isPRegular
        (A := A) (K := K) (G := G) (p := p) P hs
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
theorem projectiveEnvelope_regular_pairing_eq_delta
    {ι : Type x} [DecidableEq ι]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
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
      (p := p) (A := A) (K := K) (G := G) (lift := lift) hred hω (E := π j) (F := P i)
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
end ProjectiveCharacterCriterion

end Representation
