import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_19_19_1_1 (from Chap19) -/
open scoped Representation

namespace Representation

/- Domain-style sampling for Theorem 19-19.1-1:
* primary domain: finite-group characters and realizability of finite-dimensional representations
  over smaller coefficient fields.
* inspected owner declarations in this domain:
  `IsRealizableOver`,
  `isRealizableOver_of_hasEnoughRootsOfUnity`,
  `exists_character_eq_of_isRealizableOver`,
  `groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`.
* best owner abstractions:
  `IsRealizableOver K ρ` for the realizability clause, and
  `groupFunctionPairingOverField_character_eq_finrank_intertwiningMap` for the character-pairing
  clause.
* source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977 applies these theorems to the Artin character;
  core/canonical: the Chapter `12` owners above;
  bridge/view: a chosen complex Artin realization `ArtinRep : FDRep ℂ G` would only be an
    auxiliary view used to specialize those owners.

Primitive data versus derived API:
in the minimal API closure of this file, the project does not yet provide a source-facing owner
for "LinearRepresentations_Serre_1977's Artin class function" itself. A theorem quantified over an arbitrary `ArtinRep :
FDRep ℂ G` therefore changes the source semantics: it no longer says anything specifically about
the Artin character. The faithful refinement is recall-only. The Chapter `12` owners are the real
mathematical statements, and the Artin application is obtained by specializing them to whichever
complex realization of the Artin character is available upstream. -/

/- Theorem 19-19.1-1, realizability clause: LinearRepresentations_Serre_1977's Artin character application is a direct
specialization of the Chapter `12` owner theorem saying that every finite-dimensional complex
representation of a finite group is realizable over any field with enough roots of unity. The
textbook equality of characters over `K` is the bridge companion
`exists_character_eq_of_isRealizableOver`, not a separate owner in this file. -/
recall isRealizableOver_of_hasEnoughRootsOfUnity

/- Theorem 19-19.1-1, pairing clause: the integrality of the Artin-character pairing is the
specialization to the chosen Artin realization of the canonical character-pairing owner theorem,
which identifies the normalized pairing with the natural-number-valued dimension of the
intertwining space. -/
recall groupFunctionPairingOverField_character_eq_finrank_intertwiningMap

end Representation

/-! ### Remark_19_19_2_1 (from Chap19) -/
namespace Representation

/- Remark 19-19.2-1 (1): the reference [26] proves part (i) of Theorem 44 by a somewhat more
complicated method, but that method yields the stronger conclusion that the algebra `Q_l[G]` is
quasisplit (cf. 12.2). In the chapter/project API the relevant core owner is the Chapter 12
predicate `Representation.IsQuasisplitGroupAlgebra`; this remark adds no new local owner or bridge
beyond pointing to that canonical notion. -/
recall IsQuasisplitGroupAlgebra

/- Remark 19-19.2-1 (2): one can deduce part (ii) of Theorem 44 from part (i) together with the
Fong-Swan theorem (Theorem 38). In the project API the source-facing theorem-level owner for the
lifting clause used here is the Chapter 16 theorem
`Representation.satisfiesConditionRPrime_of_isPSolvable`; the
remark adds no parallel local implication theorem. -/
recall satisfiesConditionRPrime_of_isPSolvable

/- Remark 19-19.2-1 (3): both the Artin and Swan representations are handled by the Chapter 12
realizability owner theorem
`Representation.isRealizableOver_of_hasEnoughRootsOfUnity`: any chosen finite-dimensional complex
realization is realizable over a field `K` with `HasEnoughRootsOfUnity K (Monoid.exponent G)`,
including Fontaine's Witt-vector field in the source application. The remark adds no Artin- or
Swan-specific wrapper theorem beyond that canonical owner. -/
recall isRealizableOver_of_hasEnoughRootsOfUnity

end Representation

/-! ### Definition_19_19_3_1 (from Chap19) -/
noncomputable section

universe u

open CategoryTheory
open Rep

namespace Representation

namespace FiniteProjectiveGroupAlgebraModule

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling:
* Primary domain: finite-dimensional `k[G]`-representations and finite projective `k[G]`-modules.
* Relevant owner declarations sampled in this domain:
  `FiniteProjectiveGroupAlgebraModule.toFiniteRep`,
  `Rep.homLinearEquiv`,
  `FDRep.forget₂HomLinearEquiv`,
  and Chapter `18`'s pairing theorem
  `intertwining_finrank_eq_projectiveLiftCharacter_pairing`.
* Best owner abstraction: the categorical `FDRep` Hom-space `P.toFiniteRep ⟶ M`.
* Source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977's invariant `b[SwG](M)`;
  core/canonical: `Module.finrank k (P.toFiniteRep ⟶ M)`;
  bridge/view: the canonical linear equivalence between that Hom-space and the representation-level
    intertwining space `P.toRep.ρ.IntertwiningMap (FDRep.ρ M)`.
* Primitive data: the objects `P.toFiniteRep` and `M` of `FDRep k G`.
* Derived API: the intertwining-space comparison theorem and the notation `b[SwG](M)`.
-/

/-- Definition 19-19.3-1: the core/canonical owner for LinearRepresentations_Serre_1977's invariant is the multiplicity of a
finite-dimensional `k[G]`-module `M` in a finite projective `k[G]`-module `P`, measured by the
`k`-dimension of the equivariant Hom-space `Hom^G(P, M)`. -/
abbrev intertwiningMultiplicity
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) : ℕ :=
  Module.finrank k (P.toFiniteRep ⟶ M)

/-- Helper for Definition 19-19.3-1: intertwining maps of the underlying representations are
canonically the same as morphisms in `FDRep`. -/
private noncomputable abbrev intertwiningMap_linearEquiv_hom
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    P.toRep.ρ.IntertwiningMap (FDRep.ρ M) ≃ₗ[k] (P.toFiniteRep ⟶ M) :=
  ((homLinearEquiv
      ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep)
      ((forget₂ (FDRep k G) (Rep k G)).obj M)).symm).trans
    (FDRep.forget₂HomLinearEquiv P.toFiniteRep M)

/-- Helper for Definition 19-19.3-1: the `FDRep` Hom-space and the representation-level
intertwining space have the same `k`-dimension. This is the form used by Chapter `18`'s
character-pairing formulas. -/
private theorem hom_finrank_eq_finrank_intertwiningMap
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    Module.finrank k (P.toFiniteRep ⟶ M) =
      Module.finrank k (P.toRep.ρ.IntertwiningMap (FDRep.ρ M)) := by
  -- Transport the dimension across the canonical comparison equivalence.
  simpa using (intertwiningMap_linearEquiv_hom (P := P) (M := M)).finrank_eq.symm

/-- Helper for Definition 19-19.3-1: the `FDRep` Hom-space and the representation-level
intertwining space have the same `k`-dimension. This is the form used by Chapter `18`'s
character-pairing formulas. -/
theorem intertwiningMultiplicity_eq_finrank_intertwiningMap
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    P.intertwiningMultiplicity M =
      Module.finrank k (P.toRep.ρ.IntertwiningMap (FDRep.ρ M)) := by
  -- Route correction: factor the API conversion through a dedicated bridge equivalence so the
  -- dimension transport is a single stable step.
  -- Unfold the owner definition and reuse the finrank comparison lemma.
  simpa [intertwiningMultiplicity] using
    hom_finrank_eq_finrank_intertwiningMap (P := P) (M := M)

scoped[Representation] notation:max "b[" SwG "](" M ")" =>
  FiniteProjectiveGroupAlgebraModule.intertwiningMultiplicity SwG M

open scoped Representation

/-- Helper for Definition 19-19.3-1: the source-facing invariant `b(M)` is the `k`-dimension of
the equivariant Hom-space from the chosen Swan module `SwG` to `M`. -/
theorem swanMultiplicity_eq_finrank_hom
    (SwG : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    b[SwG](M) = Module.finrank k (SwG.toFiniteRep ⟶ M) :=
  rfl

end

end FiniteProjectiveGroupAlgebraModule

end Representation

/-! ### Proposition_19_19_3_2 (from Chap19) -/
open CategoryTheory
open scoped BigOperators Representation

noncomputable section

universe u

namespace Representation

section Additivity

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 19-19.3-2: forget a finite-dimensional representation of `G` to its
ambient `k[G]`-module. -/
private abbrev fdRepToModuleMonoidAlgebra :
    FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
  (forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra

/-- Helper for Proposition 19-19.3-2: the left map of a short exact sequence of representations,
viewed on the underlying `k[G]`-modules. -/
private abbrev shortExactModuleLeftMap (S : ShortComplex (FDRep k G)) :
    asModule S.X₁.ρ →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ :=
  ModuleCat.Hom.hom ((S.map (fdRepToModuleMonoidAlgebra (k := k) (G := G))).f)

/-- Helper for Proposition 19-19.3-2: the right map of a short exact sequence of representations,
viewed on the underlying `k[G]`-modules. -/
private abbrev shortExactModuleRightMap (S : ShortComplex (FDRep k G)) :
    asModule S.X₂.ρ →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ :=
  ModuleCat.Hom.hom ((S.map (fdRepToModuleMonoidAlgebra (k := k) (G := G))).g)

/-- Helper for Proposition 19-19.3-2: the `k[G]`-linear Hom-space from the projective source `P`
to the module underlying a finite-dimensional representation. -/
private abbrev moduleHomSpace
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :=
  P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule M.ρ

/-- Helper for Proposition 19-19.3-2: the ambient `k[G]`-linear Hom-space carries its natural
`k`-module structure. -/
instance moduleHomSpaceModule
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    Module k (moduleHomSpace (k := k) (G := G) P M) := by
  delta moduleHomSpace
  letI : Module k P.toRep.ρ.asModule :=
    representation_asModuleModule (k := k) (G := G) P.toRep.ρ
  letI : Module k (asModule M.ρ) :=
    representation_asModuleModule (k := k) (G := G) M.ρ
  letI : IsScalarTower k (MonoidAlgebra k G) P.toRep.ρ.asModule :=
    representation_asModule_isScalarTower (k := k) (G := G) P.toRep.ρ
  letI : IsScalarTower k (MonoidAlgebra k G) (asModule M.ρ) :=
    representation_asModule_isScalarTower (k := k) (G := G) M.ρ
  infer_instance

/-- Helper for Proposition 19-19.3-2: the owner `FDRep` Hom-space and the ambient `k[G]`-linear
Hom-space are canonically linearly equivalent. -/
private noncomputable abbrev homLinearEquiv_moduleHomSpace
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    (P.toFiniteRep ⟶ M) ≃ₗ[k] moduleHomSpace (k := k) (G := G) P M :=
  ((FDRep.forget₂HomLinearEquiv P.toFiniteRep M).symm).trans
    ((Rep.homLinearEquiv
        ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep)
        ((forget₂ (FDRep k G) (Rep k G)).obj M)).trans
      (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := P.toRep.ρ) (σ := M.ρ)))

/-- Helper for Proposition 19-19.3-2: transport the additive-group structure from the owner
`FDRep` Hom-space to the ambient `k[G]`-linear model. -/
noncomputable instance moduleHomSpaceAddCommGroup
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    AddCommGroup (moduleHomSpace (k := k) (G := G) P M) :=
  Equiv.addCommGroup (homLinearEquiv_moduleHomSpace (k := k) (G := G) P M).symm.toEquiv

/-- Helper for Proposition 19-19.3-2: postcomposition with the left map of a short exact sequence
acts `k`-linearly on equivariant module maps out of `P`. -/
private abbrev moduleHomCompRightLeft
    (P : FiniteProjectiveGroupAlgebraModule k G) (S : ShortComplex (FDRep k G)) :
    moduleHomSpace (k := k) (G := G) P S.X₁ →ₗ[k]
      moduleHomSpace (k := k) (G := G) P S.X₂ :=
  LinearMap.compRight k (shortExactModuleLeftMap (k := k) (G := G) S)

/-- Helper for Proposition 19-19.3-2: postcomposition with the right map of a short exact
sequence acts `k`-linearly on equivariant module maps out of `P`. -/
private abbrev moduleHomCompRightRight
    (P : FiniteProjectiveGroupAlgebraModule k G) (S : ShortComplex (FDRep k G)) :
    moduleHomSpace (k := k) (G := G) P S.X₂ →ₗ[k]
      moduleHomSpace (k := k) (G := G) P S.X₃ :=
  LinearMap.compRight k (shortExactModuleRightMap (k := k) (G := G) S)

/-- Helper for Proposition 19-19.3-2: the `k`-linear Hom-space owner attached to a term of the
short exact sequence. -/
private abbrev moduleHomModule
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) : ModuleCat k :=
  by
    let hAdd :
        AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule M.ρ) :=
      show AddCommGroup (moduleHomSpace (k := k) (G := G) P M) from
        moduleHomSpaceAddCommGroup (k := k) (G := G) P M
    let hMod : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule M.ρ) :=
      show Module k (moduleHomSpace (k := k) (G := G) P M) from
        moduleHomSpaceModule (k := k) (G := G) P M
    exact @ModuleCat.of k inferInstance
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule M.ρ) hAdd hMod

/-- Helper for Proposition 19-19.3-2: the left postcomposition map, viewed as a morphism in
`ModuleCat k`. -/
private abbrev moduleHomLeftHom
    (P : FiniteProjectiveGroupAlgebraModule k G) (S : ShortComplex (FDRep k G)) :
    moduleHomModule (k := k) (G := G) P S.X₁ ⟶
      moduleHomModule (k := k) (G := G) P S.X₂ :=
  by
    let hAdd₁ :
        AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ) :=
      show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₁) from
        moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₁
    let hMod₁ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ) :=
      show Module k (moduleHomSpace (k := k) (G := G) P S.X₁) from
        moduleHomSpaceModule (k := k) (G := G) P S.X₁
    let hAdd₂ :
        AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ) :=
      show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₂) from
        moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₂
    let hMod₂ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ) :=
      show Module k (moduleHomSpace (k := k) (G := G) P S.X₂) from
        moduleHomSpaceModule (k := k) (G := G) P S.X₂
    exact @ModuleCat.ofHom k inferInstance
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ)
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ)
      hAdd₁ hMod₁ hAdd₂ hMod₂
      (moduleHomCompRightLeft (k := k) (G := G) P S)

/-- Helper for Proposition 19-19.3-2: the right postcomposition map, viewed as a morphism in
`ModuleCat k`. -/
private abbrev moduleHomRightHom
    (P : FiniteProjectiveGroupAlgebraModule k G) (S : ShortComplex (FDRep k G)) :
    moduleHomModule (k := k) (G := G) P S.X₂ ⟶
      moduleHomModule (k := k) (G := G) P S.X₃ :=
  by
    let hAdd₂ :
        AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ) :=
      show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₂) from
        moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₂
    let hMod₂ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ) :=
      show Module k (moduleHomSpace (k := k) (G := G) P S.X₂) from
        moduleHomSpaceModule (k := k) (G := G) P S.X₂
    let hAdd₃ :
        AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
      show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₃) from
        moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₃
    let hMod₃ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
      show Module k (moduleHomSpace (k := k) (G := G) P S.X₃) from
        moduleHomSpaceModule (k := k) (G := G) P S.X₃
    exact @ModuleCat.ofHom k inferInstance
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₂.ρ)
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ)
      hAdd₂ hMod₂ hAdd₃ hMod₃
      (moduleHomCompRightRight (k := k) (G := G) P S)

/-- Helper for Proposition 19-19.3-2: the packaged `asModule` owner of `P.toRep` is projective
over `k[G]`. -/
private theorem toRep_asModule_projective
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective (MonoidAlgebra k G) P.toRep.ρ.asModule := by
  -- Compare `P.toRep.ρ.asModule` with the original projective `k[G]`-module `P.V`.
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
    (Module.Projective.of_equiv'
      ((Rep.counitIso P.V).toLinearEquiv.symm) :
      Module.Projective (MonoidAlgebra k G)
        ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj P.V))

/-- Helper for Proposition 19-19.3-2: a map into the middle term whose composite with the right
map vanishes factors through the left map after applying `Hom_{k[G]}(P,-)`. -/
private theorem moduleHom_compRight_factor_through_left_of_shortExact
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact)
    (ψ : moduleHomSpace (k := k) (G := G) P S.X₂)
    (hψ : moduleHomCompRightRight (k := k) (G := G) P S ψ = 0) :
    ∃ φ : moduleHomSpace (k := k) (G := G) P S.X₁,
      moduleHomCompRightLeft (k := k) (G := G) P S φ = ψ := by
  let F : FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
    fdRepToModuleMonoidAlgebra (k := k) (G := G)
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to the ambient `k[G]`-modules preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let f := shortExactModuleLeftMap (k := k) (G := G) S
  let g := shortExactModuleRightMap (k := k) (G := G) S
  have hf : Function.Injective f := by
    -- The left map stays injective on the underlying `k[G]`-modules.
    simpa [f] using hSF.moduleCat_injective_f
  have hExact : Function.Exact f g := by
    -- In `ModuleCat k[G]`, short exactness is exactness of the underlying linear maps.
    simpa [F, f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hRangeKer : LinearMap.range f = LinearMap.ker g := by
    -- Exactness identifies the image of `f` with the kernel of `g`.
    simpa [f, g] using hExact.linearMap_ker_eq.symm
  let ψrange : P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] LinearMap.range f :=
    ψ.codRestrict (LinearMap.range f) fun x => by
      have hxZero : g (ψ x) = 0 := by
        -- The hypothesis `g ∘ ψ = 0` gives a pointwise kernel condition.
        simpa [moduleHomCompRightRight, g] using LinearMap.congr_fun hψ x
      rw [hRangeKer]
      simpa [LinearMap.mem_ker, g] using hxZero
  let e : asModule S.X₁.ρ ≃ₗ[MonoidAlgebra k G] LinearMap.range f :=
    LinearEquiv.ofInjective f hf
  refine ⟨e.symm.toLinearMap.comp ψrange, ?_⟩
  -- Route correction: lift into `range f` first, then pull back through the image equivalence.
  ext x
  change f (((e.symm.toLinearMap.comp ψrange) x)) = ψ x
  exact Subtype.ext_iff.mp (e.apply_symm_apply (ψrange x))

/-- Helper for Proposition 19-19.3-2: the Hom-sequence obtained by postcomposing with a short
exact sequence is exact. -/
private theorem moduleHom_compRight_exact_of_shortExact
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    Function.Exact
      (moduleHomCompRightLeft (k := k) (G := G) P S)
      (moduleHomCompRightRight (k := k) (G := G) P S) := by
  have hcomp :
      (moduleHomCompRightRight (k := k) (G := G) P S).comp
        (moduleHomCompRightLeft (k := k) (G := G) P S) = 0 := by
    -- The composite vanishes because the original short complex has zero composite.
    let F : FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
      fdRepToModuleMonoidAlgebra (k := k) (G := G)
    have hzero :
        (shortExactModuleRightMap (k := k) (G := G) S).comp
          (shortExactModuleLeftMap (k := k) (G := G) S) = 0 := by
      simpa [F, shortExactModuleLeftMap, shortExactModuleRightMap] using
        congrArg ModuleCat.Hom.hom (S.map F).zero
    ext φ x
    simpa [moduleHomCompRightLeft, moduleHomCompRightRight] using
      LinearMap.congr_fun hzero (φ x)
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range hcomp ?_
  intro ψ hψ
  rcases moduleHom_compRight_factor_through_left_of_shortExact
      (k := k) (G := G) P S hS ψ (by simpa [LinearMap.mem_ker] using hψ) with ⟨φ, hφ⟩
  exact ⟨φ, hφ⟩

/-- Helper for Proposition 19-19.3-2: the right postcomposition map on `Hom_{k[G]}(P,-)` is
surjective because `P` is projective. -/
private theorem moduleHom_compRight_surjective_of_shortExact
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    Function.Surjective
      (moduleHomCompRightRight (k := k) (G := G) P S) := by
  let F : FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
    fdRepToModuleMonoidAlgebra (k := k) (G := G)
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to the ambient `k[G]`-modules preserves short exactness.
    simpa [F] using hS.map_of_exact F
  let g := shortExactModuleRightMap (k := k) (G := G) S
  have hg : Function.Surjective g := by
    -- The right map is surjective on the underlying `k[G]`-modules.
    simpa [g] using hSF.moduleCat_surjective_g
  let _ : Module.Projective (MonoidAlgebra k G) P.toRep.ρ.asModule :=
    toRep_asModule_projective (k := k) (G := G) P
  intro ψ
  obtain ⟨φ, hφ⟩ :=
    Module.projective_lifting_property g ψ hg
  -- Projectivity of `P` lifts each target map `ψ` through the surjection `g`.
  refine ⟨φ, ?_⟩
  simpa [moduleHomCompRightRight, g] using hφ

/-- Helper for Proposition 19-19.3-2: the postcomposition maps form a short complex of
`k`-vector spaces. -/
private theorem moduleHom_shortComplex_zero
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) :
    moduleHomLeftHom (k := k) (G := G) P S ≫
      moduleHomRightHom (k := k) (G := G) P S = 0 := by
  let F : FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
    fdRepToModuleMonoidAlgebra (k := k) (G := G)
  have hzero :
      (shortExactModuleRightMap (k := k) (G := G) S).comp
        (shortExactModuleLeftMap (k := k) (G := G) S) = 0 := by
    -- The original short complex still has zero composite after forgetting to `ModuleCat k[G]`.
    simpa [F, shortExactModuleLeftMap, shortExactModuleRightMap] using
      congrArg ModuleCat.Hom.hom (S.map F).zero
  apply ModuleCat.hom_ext
  change
    (moduleHomCompRightRight (k := k) (G := G) P S).comp
        (moduleHomCompRightLeft (k := k) (G := G) P S) = 0
  ext ψ x
  -- Evaluate the vanished composite on `ψ x`.
  simpa [moduleHomCompRightLeft, moduleHomCompRightRight] using
    LinearMap.congr_fun hzero (ψ x)

/-- Helper for Proposition 19-19.3-2: the short complex of Hom-spaces obtained by
postcomposition. -/
private abbrev moduleHomShortComplex
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) :
    ShortComplex (ModuleCat k) :=
  ShortComplex.mk
    (moduleHomLeftHom (k := k) (G := G) P S)
    (moduleHomRightHom (k := k) (G := G) P S)
    (moduleHom_shortComplex_zero (k := k) (G := G) P S)

/-- Helper for Proposition 19-19.3-2: `Hom_{k[G]}(P,-)` sends a short exact sequence of
representations to a short exact sequence of `k`-vector spaces. -/
private theorem moduleHom_shortExact_of_shortExact
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    (moduleHomShortComplex (k := k) (G := G) P S).ShortExact := by
  let F : FDRep k G ⥤ ModuleCat (MonoidAlgebra k G) :=
    fdRepToModuleMonoidAlgebra (k := k) (G := G)
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat k[G]` exposes the injective/surjective owners used below.
    simpa [F] using hS.map_of_exact F
  let f := shortExactModuleLeftMap (k := k) (G := G) S
  have hf : Function.Injective f := by
    simpa [f] using hSF.moduleCat_injective_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Exactness is the factor-through-left statement proved above.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [moduleHomShortComplex, moduleHomLeftHom, moduleHomRightHom] using
      moduleHom_compRight_exact_of_shortExact (k := k) (G := G) P S hS
  · -- Injectivity is checked pointwise using injectivity of the original left map.
    rw [ModuleCat.mono_iff_injective]
    simpa [moduleHomShortComplex, moduleHomLeftHom, moduleHomRightHom] using
      (show Function.Injective (moduleHomCompRightLeft (k := k) (G := G) P S) from by
        intro φ₁ φ₂ hφ
        ext x
        exact hf (LinearMap.congr_fun hφ x))
  · -- Surjectivity comes from projectivity of `P`.
    rw [ModuleCat.epi_iff_surjective]
    simpa [moduleHomShortComplex, moduleHomLeftHom, moduleHomRightHom] using
      moduleHom_compRight_surjective_of_shortExact (k := k) (G := G) P S hS

/-- Helper for Proposition 19-19.3-2: the middle Hom-space in the exact sequence
`Hom_{k[G]}(P,S.X₁) → Hom_{k[G]}(P,S.X₂) → Hom_{k[G]}(P,S.X₃)` splits as the product of the
outer two spaces. -/
private theorem moduleHom_middle_linearEquiv_prod_of_shortExact
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    Nonempty
      ((moduleHomSpace (k := k) (G := G) P S.X₁ ×
          moduleHomSpace (k := k) (G := G) P S.X₃) ≃ₗ[k]
        moduleHomSpace (k := k) (G := G) P S.X₂) := by
  let e₁ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₁
  let e₂ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₂
  let e₃ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₃
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₁) :=
    (LinearMap.finite_iff_of_bijective e₁.symm.toLinearMap e₁.symm.bijective).2 inferInstance
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₂) :=
    (LinearMap.finite_iff_of_bijective e₂.symm.toLinearMap e₂.symm.bijective).2 inferInstance
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₃) :=
    (LinearMap.finite_iff_of_bijective e₃.symm.toLinearMap e₃.symm.bijective).2 inferInstance
  let hAdd₃ :
      AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₃) from
      moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₃
  let hMod₃ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    show Module k (moduleHomSpace (k := k) (G := G) P S.X₃) from
      moduleHomSpaceModule (k := k) (G := G) P S.X₃
  let _ : Module.Free k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    @Module.Free.of_divisionRing k
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ)
      inferInstance hAdd₃ hMod₃
  let _ : Module.Projective k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    Module.Projective.of_free
  -- The packaged Hom short complex splits because its right term is a vector space over `k`.
  simpa [moduleHomShortComplex, moduleHomModule] using
    (moduleCat_shortExact_middle_nonempty_linearEquiv_prod
      (R := k) (S := moduleHomShortComplex (k := k) (G := G) P S)
      (moduleHom_shortExact_of_shortExact (k := k) (G := G) P S hS))

/-- Helper for Proposition 19-19.3-2: `intertwiningMultiplicity` is the `k`-dimension of the
ambient `k[G]`-linear Hom-space out of `P`. -/
private theorem intertwiningMultiplicity_eq_finrank_moduleHomSpace
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    P.intertwiningMultiplicity M =
      Module.finrank k (moduleHomSpace (k := k) (G := G) P M) := by
  -- Transport the owner-level Hom dimension to the underlying `k[G]`-linear Hom-space once.
  simpa [FiniteProjectiveGroupAlgebraModule.intertwiningMultiplicity] using
    (homLinearEquiv_moduleHomSpace (k := k) (G := G) P M).finrank_eq

-- Proof sketch: `intertwiningMultiplicity P M` is the dimension of `Hom^G(P, M)`, and
-- `Hom^G(P, -)` is exact on short exact sequences because `P` is projective.
/-- Proposition 19-19.3-2 (1): the additive clause is a generic projective-module statement.
Specializing `P` to LinearRepresentations_Serre_1977's mod-`l` Swan module `\overline{\mathrm{Sw}}_G` recovers the source
formula for `b(M)`. This is the core/canonical owner-level statement. -/
theorem intertwiningMultiplicity_add_of_shortExactSequence
    (P : FiniteProjectiveGroupAlgebraModule k G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    P.intertwiningMultiplicity S.X₂ =
      P.intertwiningMultiplicity S.X₁ + P.intertwiningMultiplicity S.X₃ := by
  let e₁ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₁
  let e₂ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₂
  let e₃ := homLinearEquiv_moduleHomSpace (k := k) (G := G) P S.X₃
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₁) :=
    (LinearMap.finite_iff_of_bijective e₁.symm.toLinearMap e₁.symm.bijective).2 inferInstance
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₂) :=
    (LinearMap.finite_iff_of_bijective e₂.symm.toLinearMap e₂.symm.bijective).2 inferInstance
  let _ : Module.Finite k (moduleHomSpace (k := k) (G := G) P S.X₃) :=
    (LinearMap.finite_iff_of_bijective e₃.symm.toLinearMap e₃.symm.bijective).2 inferInstance
  let hAdd₁ :
      AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ) :=
    show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₁) from
      moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₁
  let hMod₁ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ) :=
    show Module k (moduleHomSpace (k := k) (G := G) P S.X₁) from
      moduleHomSpaceModule (k := k) (G := G) P S.X₁
  let hAdd₃ :
      AddCommGroup (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    show AddCommGroup (moduleHomSpace (k := k) (G := G) P S.X₃) from
      moduleHomSpaceAddCommGroup (k := k) (G := G) P S.X₃
  let hMod₃ : Module k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    show Module k (moduleHomSpace (k := k) (G := G) P S.X₃) from
      moduleHomSpaceModule (k := k) (G := G) P S.X₃
  let _ : Module.Free k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ) :=
    @Module.Free.of_divisionRing k
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₁.ρ)
      inferInstance hAdd₁ hMod₁
  let _ : Module.Free k (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ) :=
    @Module.Free.of_divisionRing k
      (P.toRep.ρ.asModule →ₗ[MonoidAlgebra k G] asModule S.X₃.ρ)
      inferInstance hAdd₃ hMod₃
  obtain ⟨e⟩ := moduleHom_middle_linearEquiv_prod_of_shortExact
    (k := k) (G := G) P S hS
  -- Rewrite the invariant as a Hom-space dimension, split the middle term, and convert back.
  calc
    P.intertwiningMultiplicity S.X₂ =
        Module.finrank k (moduleHomSpace (k := k) (G := G) P S.X₂) := by
          simpa using intertwiningMultiplicity_eq_finrank_moduleHomSpace
            (k := k) (G := G) P S.X₂
    _ =
        Module.finrank k
          (moduleHomSpace (k := k) (G := G) P S.X₁ ×
            moduleHomSpace (k := k) (G := G) P S.X₃) := by
          simpa using e.finrank_eq.symm
    _ =
        Module.finrank k (moduleHomSpace (k := k) (G := G) P S.X₁) +
          Module.finrank k (moduleHomSpace (k := k) (G := G) P S.X₃) := by
          simpa using
            (Module.finrank_prod
              (R := k)
              (M := moduleHomSpace (k := k) (G := G) P S.X₁)
              (M' := moduleHomSpace (k := k) (G := G) P S.X₃))
    _ = P.intertwiningMultiplicity S.X₁ + P.intertwiningMultiplicity S.X₃ := by
          rw [← intertwiningMultiplicity_eq_finrank_moduleHomSpace
                (k := k) (G := G) P S.X₁,
            ← intertwiningMultiplicity_eq_finrank_moduleHomSpace
                (k := k) (G := G) P S.X₃]

end Additivity

section ProjectivePairing

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R_K(G))

local instance : Fintype G := Fintype.ofFinite G

/-- Classical decidability for `p`-regularity on `G`, used to write the zero-extension of the
modular character. -/
local instance isPRegularDecidablePred : DecidablePred (IsPRegular p : G → Prop) :=
  Classical.decPred _

-- Proof sketch: combine the owner-level identification of `intertwiningMultiplicity` with the
-- Chapter `18` projective-character pairing formula.
/-- Proposition 19-19.3-2 (2): clause (ii) is the bridge/view specialization of the Chapter `18`
projective-character pairing formula to LinearRepresentations_Serre_1977's Swan module. The canonical owners are
`b[SwG](M)` for LinearRepresentations_Serre_1977's invariant,
`FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter SwG e` for the Swan class function,
`FDRep.modularCharacterZeroExtension` for the modular character
of `M`. -/
theorem swanMultiplicity_eq_pairing_with_modularCharacter
    (lift : PrimeToPRoot p k →* Kˣ)
    (SwG : FiniteProjectiveGroupAlgebraModule k G)
    (M : FDRep k G) :
    (b[SwG](M) : K) =
      ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter SwG e,
        FDRep.modularCharacterZeroExtension M (PrimeToPRoot.toFieldLift lift)⟫ := by
  -- Rewrite `b(M)` as the intertwining-space dimension, then apply the Chapter `18` pairing
  -- formula for projective lift characters and modular characters.
  calc
    (b[SwG](M) : K) =
        (Module.finrank k (SwG.toRep.ρ.IntertwiningMap (FDRep.ρ M)) : K) := by
          exact_mod_cast
            FiniteProjectiveGroupAlgebraModule.intertwiningMultiplicity_eq_finrank_intertwiningMap
              (P := SwG) (M := M)
    _ = (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter SwG e (s⁻¹) *
              FDRep.modularCharacterZeroExtension M (PrimeToPRoot.toFieldLift lift) s := by
          simpa using
            intertwining_finrank_eq_projectiveLiftCharacter_pairing
              (p := p) (A := A) (K := K) (G := G) (lift := lift) M SwG
    _ =
        ⟪FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter SwG e,
          FDRep.modularCharacterZeroExtension M (PrimeToPRoot.toFieldLift lift)⟫ := by
          rfl

-- Proof sketch: expand the pairing in clause `(2)` using the defining formula
-- `⟪φ, ψ⟫ = |G|⁻¹ ∑ s, φ(s⁻¹) ψ(s)`.
/-- Proposition 19-19.3-2 (3): source clause (ii) in expanded form: after zero-extending the
modular character away from the `p`-regular locus, `b(M)` is the averaged sum attached to the
projective lift character of the Swan module and the modular character of `M`. -/
theorem swanMultiplicity_eq_regular_sum
    (lift : PrimeToPRoot p k →* Kˣ)
    (SwG : FiniteProjectiveGroupAlgebraModule k G)
    (M : FDRep k G) :
    (b[SwG](M) : K) =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          FiniteProjectiveGroupAlgebraModule.projectiveLiftCharacter SwG e s⁻¹ *
            FDRep.modularCharacterZeroExtension M (PrimeToPRoot.toFieldLift lift) s := by
  -- Unfold the normalized pairing from clause `(2)` to recover LinearRepresentations_Serre_1977's averaged sum.
  simpa [Representation.groupFunctionPairingOverField] using
    swanMultiplicity_eq_pairing_with_modularCharacter
      (p := p) (A := A) (K := K) (G := G) lift SwG M

end ProjectivePairing

section LowerRamificationFiltration

variable {G : Type u} [Group G] [Finite G]

/-- A source-facing lower ramification filtration on `G`: the ramification groups start at `G`,
are normal, decrease with the index, and are eventually trivial. The numerical weights `g_i` from
LinearRepresentations_Serre_1977 are then the derived cardinalities `|Gi i|`, so they are not kept as separate primitive
data. -/
class IsLowerRamificationFiltration (Gi : ℕ → Subgroup G) : Prop where
  zero_eq_top : Gi 0 = ⊤
  normal : ∀ i, (Gi i).Normal
  antitone : Antitone Gi
  eventually_bot : ∃ n, Gi n = ⊥

namespace IsLowerRamificationFiltration

variable {G : Type u} [Group G]
variable {Gi : ℕ → Subgroup G} [IsLowerRamificationFiltration Gi]

theorem eq_bot_of_ge {n i : ℕ} (hn : Gi n = ⊥) (hni : n ≤ i) : Gi i = ⊥ := by
  apply le_antisymm
  · rw [← hn]
    exact IsLowerRamificationFiltration.antitone hni
  · exact bot_le

theorem exists_bot_tail : ∃ n, ∀ i ≥ n, Gi i = ⊥ := by
  rcases (inferInstance : IsLowerRamificationFiltration Gi).eventually_bot with ⟨n, hn⟩
  exact ⟨n, fun i hi ↦ IsLowerRamificationFiltration.eq_bot_of_ge hn hi⟩

end IsLowerRamificationFiltration

end LowerRamificationFiltration

section RamificationFormulaStatement

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem finsum_eq_sum_Icc_of_eventuallyEq_zero
    {α : Type*} [AddCommMonoid α]
    (term : ℕ → α) (hzero : ∃ n, ∀ i ≥ n, term i = 0) :
    ∃ n, ∑ᶠ (i) (_ : 0 < i), term i = ∑ i ∈ Finset.Icc 1 n, term i := by
  rcases hzero with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  exact finsum_cond_eq_sum_of_cond_iff term <| by
    intro i hi
    constructor
    · intro hpos
      refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hpos, ?_⟩
      by_contra hle
      exact hi (hn i (lt_of_not_ge hle).le)
    · intro hiIcc
      have hle1 : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
      exact lt_of_lt_of_le Nat.zero_lt_one hle1

/-- The `i`-th positive-index contribution to the lower-ramification multiplicity formula. -/
def lowerRamificationTerm
    (Gi : ℕ → Subgroup G) (M : FDRep k G) (i : ℕ) : ℚ :=
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (Gi i) := Fintype.ofFinite (Gi i)
  ((Fintype.card (Gi i) : ℚ) / Fintype.card G) *
    Module.finrank k (M ⧸ invariants (M.ρ.comp (Gi i).subtype))

theorem lowerRamificationTerm_eq_zero_of_eq_bot
    (Gi : ℕ → Subgroup G) (M : FDRep k G) {i : ℕ} (hi : Gi i = ⊥) :
    lowerRamificationTerm Gi M i = 0 := by
  have htriv : IsTrivial (M.ρ.comp (⊥ : Subgroup G).subtype) := by
    refine ⟨?_⟩
    intro g
    ext x
    have hg : g = 1 := Subsingleton.elim _ _
    simp [hg]
  have hinv : invariants (M.ρ.comp (Gi i).subtype) = ⊤ := by
    rw [hi]
    simpa using Representation.invariants_eq_top (M.ρ.comp (⊥ : Subgroup G).subtype)
  simp [lowerRamificationTerm, hinv]

/-- The source-facing ramification-side expression for LinearRepresentations_Serre_1977's modular invariant `b(M)` attached
to a lower ramification filtration `Gi`. This is the canonical filtration-side owner: it is the
positive-index finite ramification sum, and a projective module represents LinearRepresentations_Serre_1977's mod-`l` Swan
module over a coefficient field of characteristic `l` for `Gi` only after an explicit bridge
identifies its intertwining multiplicity with this functional. -/
def lowerRamificationMultiplicity
    (Gi : ℕ → Subgroup G) [IsLowerRamificationFiltration Gi] (M : FDRep k G) : ℚ :=
  ∑ᶠ (i) (_ : 0 < i), lowerRamificationTerm Gi M i

theorem lowerRamificationMultiplicity_eq_sum
    (Gi : ℕ → Subgroup G) [hGi : IsLowerRamificationFiltration Gi]
    (M : FDRep k G) :
    ∃ n,
      lowerRamificationMultiplicity Gi M = ∑ i ∈ Finset.Icc 1 n, lowerRamificationTerm Gi M i := by
  have htailGi : ∃ n, ∀ i ≥ n, Gi i = ⊥ := IsLowerRamificationFiltration.exists_bot_tail
  have hzero : ∃ n, ∀ i ≥ n, lowerRamificationTerm Gi M i = 0 := by
    rcases htailGi with ⟨n, hn⟩
    exact ⟨n, fun i hi ↦ lowerRamificationTerm_eq_zero_of_eq_bot Gi M (hn i hi)⟩
  simpa [lowerRamificationMultiplicity] using
    finsum_eq_sum_Icc_of_eventuallyEq_zero (lowerRamificationTerm Gi M) hzero

end RamificationFormulaStatement

section SwanModuleRamificationFormula

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

-- Proof sketch: clause `(iii)` is a bridge/view statement: once the source module `SwG` is known
-- to realize LinearRepresentations_Serre_1977's lower-ramification multiplicity functional for the chosen filtration `Gi`,
-- unfold that functional.
/-- Proposition 19-19.3-2 (4): source clause (iii): if LinearRepresentations_Serre_1977's mod-`l` Swan module `SwG`
realizes the lower-ramification multiplicity functional for `Gi`, then `b(M)` is the weighted
finite sum of the dimensions of the quotients by the fixed subspaces, with weight `|Gi i| / |G|`
at each positive stage `i`. -/
theorem swanMultiplicity_eq_ramification_weighted_finsum
    (Gi : ℕ → Subgroup G)
    [IsLowerRamificationFiltration Gi]
    (SwG : FiniteProjectiveGroupAlgebraModule k G)
    (hSwG :
      ∀ M : FDRep k G,
        (b[SwG](M) : ℚ) = lowerRamificationMultiplicity Gi M)
    (M : FDRep k G) :
    (b[SwG](M) : ℚ) =
      ∑ᶠ (i) (_ : 0 < i), lowerRamificationTerm Gi M i := by
  simpa [lowerRamificationMultiplicity] using hSwG M

end SwanModuleRamificationFormula

section TamenessCriterion

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 19-19.3-2: each positive-index ramification contribution is
nonnegative. -/
theorem lowerRamificationTerm_nonneg
    (Gi : ℕ → Subgroup G) (M : FDRep k G) (i : ℕ) :
    0 ≤ lowerRamificationTerm Gi M i := by
  -- The ramification weight and the quotient dimension are both nonnegative.
  rw [lowerRamificationTerm]
  positivity

/-- Helper for Proposition 19-19.3-2: the lower-ramification multiplicity can be truncated at a
stage that still includes the first ramification subgroup. -/
theorem lowerRamificationMultiplicity_eq_sum_Icc_with_one
    (Gi : ℕ → Subgroup G)
    [IsLowerRamificationFiltration Gi]
    (M : FDRep k G) :
    ∃ n, 1 ≤ n ∧
      lowerRamificationMultiplicity Gi M = ∑ i ∈ Finset.Icc 1 n, lowerRamificationTerm Gi M i := by
  rcases IsLowerRamificationFiltration.exists_bot_tail (Gi := Gi) with ⟨n, hn⟩
  let N := max 1 n
  refine ⟨N, le_max_left _ _, ?_⟩
  -- The eventual `⊥`-tail is unchanged after replacing the cutoff by `max 1 n`.
  have hsum :
      ∑ᶠ (i) (_ : 0 < i), lowerRamificationTerm Gi M i =
        ∑ i ∈ Finset.Icc 1 N, lowerRamificationTerm Gi M i := by
    exact finsum_cond_eq_sum_of_cond_iff (lowerRamificationTerm Gi M) <| by
      intro i hi
      constructor
      · intro hpos
        refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hpos, ?_⟩
        by_contra hNi
        have hNle : N ≤ i := le_of_not_ge hNi
        have hni : n ≤ i := le_trans (le_max_right 1 n) hNle
        exact hi (lowerRamificationTerm_eq_zero_of_eq_bot Gi M (hn i hni))
      · intro hiIcc
        exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hiIcc).1
  simpa [lowerRamificationMultiplicity, N] using hsum

/-- Helper for Proposition 19-19.3-2: a ramification contribution vanishes exactly when the
representation restricted to that ramification subgroup is trivial. -/
theorem lowerRamificationTerm_eq_zero_iff_isTrivial_restriction
    (Gi : ℕ → Subgroup G) (M : FDRep k G) (i : ℕ) :
    lowerRamificationTerm Gi M i = 0 ↔ IsTrivial (M.ρ.comp (Gi i).subtype) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (Gi i) := Fintype.ofFinite (Gi i)
  constructor
  · intro hzero
    -- Vanishing of the weighted term forces the quotient by invariants to have dimension `0`.
    have hquotQ :
        (Module.finrank k (M ⧸ invariants (M.ρ.comp (Gi i).subtype)) : ℚ) = 0 := by
      rw [lowerRamificationTerm] at hzero
      have hcoeff : ((Fintype.card (Gi i) : ℚ) / Fintype.card G) ≠ 0 := by
        exact div_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact (mul_eq_zero.mp hzero).resolve_left hcoeff
    have hquot : Module.finrank k (M ⧸ invariants (M.ρ.comp (Gi i).subtype)) = 0 := by
      exact_mod_cast hquotQ
    -- Rank-nullity upgrades the zero quotient dimension to `invariants = ⊤`.
    have hinvariants_finrank :
        Module.finrank k (invariants (M.ρ.comp (Gi i).subtype)) = Module.finrank k M := by
      simpa [hquot] using
        (Submodule.finrank_quotient_add_finrank (invariants (M.ρ.comp (Gi i).subtype)))
    have hinvariants_top : invariants (M.ρ.comp (Gi i).subtype) = ⊤ :=
      Submodule.eq_top_of_finrank_eq hinvariants_finrank
    -- Once every vector is invariant, the restricted representation is trivial.
    refine ⟨fun g => LinearMap.ext fun x => ?_⟩
    have hx : x ∈ invariants (M.ρ.comp (Gi i).subtype) := by
      rw [hinvariants_top]
      trivial
    exact (mem_invariants (ρ := M.ρ.comp (Gi i).subtype) x).1 hx g
  · intro htriv
    -- Triviality makes the invariant subspace all of `M`, so the quotient term vanishes.
    have hinvariants_top : invariants (M.ρ.comp (Gi i).subtype) = ⊤ := by
      apply eq_top_iff.2
      intro x _
      exact fun g => by
        exact congrArg (fun f => f x) (htriv.out g)
    simp [lowerRamificationTerm, hinvariants_top]

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

/-- Helper for Proposition 19-19.3-2: triviality along a subgroup restriction descends further
along subgroup inclusion. -/
theorem isTrivial_restriction_of_le
    (M : FDRep k G) {H K : Subgroup G} (hHK : H ≤ K) :
    IsTrivial (M.ρ.comp K.subtype) → IsTrivial (M.ρ.comp H.subtype) := by
  intro htriv
  -- Restrict the trivial action on `K` along the inclusion `H ≤ K`.
  refine ⟨fun g => LinearMap.ext fun x => ?_⟩
  have hgx : M.ρ ↑g = LinearMap.id := htriv.out ⟨g, hHK g.2⟩
  simpa using congrArg (fun f => f x) hgx

end

-- Proof sketch: unfold the source-facing lower-ramification multiplicity functional as a sum of
-- nonnegative terms and isolate the first ramification subgroup contribution.
/-- The lower-ramification multiplicity functional vanishes exactly when the restriction of `M`
to the first ramification subgroup `Gi 1` is trivial. -/
theorem lowerRamificationMultiplicity_eq_zero_iff_isTrivial_on_firstRamificationGroup
    (Gi : ℕ → Subgroup G)
    [IsLowerRamificationFiltration Gi]
    (M : FDRep k G) :
    lowerRamificationMultiplicity Gi M = 0 ↔ IsTrivial (M.ρ.comp (Gi 1).subtype) := by
  constructor
  · intro hzero
    rcases lowerRamificationMultiplicity_eq_sum_Icc_with_one Gi M with ⟨n, hn, hsum⟩
    -- The finite positive-index expansion forces every nonnegative summand to vanish.
    have hterm_zero : ∀ i ∈ Finset.Icc 1 n, lowerRamificationTerm Gi M i = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 ?_
      · intro i hi
        exact lowerRamificationTerm_nonneg Gi M i
      · simpa [hsum] using hzero
    -- The first ramification contribution lies in the range, so its vanishing gives tameness.
    have hfirst : lowerRamificationTerm Gi M 1 = 0 := by
      exact hterm_zero 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
    exact (lowerRamificationTerm_eq_zero_iff_isTrivial_restriction Gi M 1).1 hfirst
  · intro htriv
    rcases lowerRamificationMultiplicity_eq_sum_Icc_with_one Gi M with ⟨n, hn, hsum⟩
    rw [hsum]
    -- Triviality on `Gi 1` descends to every later ramification subgroup, killing each summand.
    apply Finset.sum_eq_zero
    intro i hi
    apply (lowerRamificationTerm_eq_zero_iff_isTrivial_restriction Gi M i).2
    have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hi).1
    have hle : Gi i ≤ Gi 1 :=
      IsLowerRamificationFiltration.antitone (Nat.succ_le_of_lt hi_pos)
    exact isTrivial_restriction_of_le M hle htriv

-- Proof sketch: use the bridge/view identification of `SwG.intertwiningMultiplicity` with the
-- source-facing lower-ramification multiplicity functional, then apply the vanishing criterion for
-- that functional.
/-- Proposition 19-19.3-2 (5): source clause (iv): if LinearRepresentations_Serre_1977's mod-`l` Swan module `SwG` realizes
the lower-ramification multiplicity functional for `Gi`, then `b(M)` vanishes exactly when the
restriction of `M` to the first ramification subgroup `Gi 1` is trivial, i.e. when the action is
tame. -/
theorem swanMultiplicity_eq_zero_iff_isTrivial_on_firstRamificationGroup
    (Gi : ℕ → Subgroup G)
    [IsLowerRamificationFiltration Gi]
    (SwG : FiniteProjectiveGroupAlgebraModule k G)
    (hSwG :
      ∀ M : FDRep k G,
        (b[SwG](M) : ℚ) = lowerRamificationMultiplicity Gi M)
    (M : FDRep k G) :
    b[SwG](M) = 0 ↔ IsTrivial (M.ρ.comp (Gi 1).subtype) := by
  have hM :
      (b[SwG](M) : ℚ) = lowerRamificationMultiplicity Gi M :=
    hSwG M
  constructor
  · intro hzero
    have hzeroQ : (b[SwG](M) : ℚ) = 0 := by
      exact_mod_cast hzero
    rw [hM] at hzeroQ
    exact
      (lowerRamificationMultiplicity_eq_zero_iff_isTrivial_on_firstRamificationGroup Gi M).1
        hzeroQ
  · intro htriv
    have hzeroQ : lowerRamificationMultiplicity Gi M = 0 :=
      (lowerRamificationMultiplicity_eq_zero_iff_isTrivial_on_firstRamificationGroup Gi M).2 htriv
    rw [← hM] at hzeroQ
    exact_mod_cast hzeroQ

end TamenessCriterion

end Representation
