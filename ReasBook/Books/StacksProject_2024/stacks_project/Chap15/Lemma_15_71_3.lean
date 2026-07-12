import Mathlib
import StacksProject_2024.Chap15.Definition_15_71_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open ModuleCat
open ShortComplex

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

/- The free-factorization clause is an owner-level bridge: it depends only on the commutative-ring
owner `Module.IsIdealProjective` and the canonical equivalence between projective and free
factorizations. -/
/-- The chapter owner `Module.IsIdealProjective I M` is equivalent to requiring that, for every
`a ∈ I`, the scalar-action endomorphism `m ↦ (a : R) • m` factors through a free `R`-module. -/
theorem isIdealProjective_iff_smul_endomorphism_factorsThroughFree (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Module.IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree := by
  refine ⟨?_, ?_⟩
  · intro hI a
    exact
      (LinearMap.factorsThroughProjective_iff_factorsThroughFree
        (LinearMap.lsmul R M (a : R))).mp (hI.factorsThroughProjective a)
  · intro hFree
    refine ⟨fun a ↦ ?_⟩
    exact
      (LinearMap.factorsThroughProjective_iff_factorsThroughFree
        (LinearMap.lsmul R M (a : R))).mpr (hFree a)

end

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : ModuleCat.{max u v} R}

/-- Helper for Lemma 15.71.3: the `ModuleCat` morphism attached to scalar multiplication on `M`
is the scalar multiple of the identity. -/
lemma ofHom_lsmul_eq_smul_id (a : R) :
    ModuleCat.ofHom (LinearMap.lsmul R M a) = a • 𝟙 M := by
  -- Compare the two endomorphisms on the underlying `R`-module.
  ext x
  rfl

/-- Helper for Lemma 15.71.3: precomposition on `Ext¹` by the scalar endomorphism of `M`
is the usual scalar action. -/
lemma mk₀_lsmul_comp_ext_eq_smul (N : ModuleCat.{max u v} R) (a : R) (e : Ext M N 1) :
    (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M a))).comp e (zero_add 1) = a • e := by
  -- Rewrite the scalar endomorphism as `a • 𝟙_M` and then use the source-side linearity API.
  calc
    (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M a))).comp e (zero_add 1)
        = (mk₀ (a • 𝟙 M)).comp e (zero_add 1) := by
            rw [ofHom_lsmul_eq_smul_id (M := M) (R := R) a]
    _ = (a • mk₀ (𝟙 M)).comp e (zero_add 1) := by
      simpa using congrArg (fun α : Ext M M 0 ↦ α.comp e (zero_add 1)) (mk₀_smul a (𝟙 M))
    _ = a • ((mk₀ (𝟙 M)).comp e (zero_add 1)) := by
      rw [smul_comp]
    _ = a • e := by
      rw [mk₀_id_comp]

/-- Helper for Lemma 15.71.3: an `I`-projective module has `Ext¹` annihilated by `I`
against every target module. -/
lemma ext_annihilator_of_isIdealProjective (hM : Module.IsIdealProjective I M) :
    ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) := by
  intro N a ha
  rw [Module.mem_annihilator]
  intro e
  let aI : I := ⟨a, ha⟩
  rcases hM.factorsThroughProjective aI with ⟨P, hPAdd, hPModule, hP, f, g, hfg⟩
  letI : AddCommMonoid P := hPAdd
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  letI : Module R P := hPModule
  let P' : ModuleCat.{max u v} R := ModuleCat.of R P
  let f' : M ⟶ P' := ModuleCat.ofHom f
  let g' : P' ⟶ M := ModuleCat.ofHom g
  let e' : Ext P' N 1 := (mk₀ g').comp e (zero_add 1)
  have he' : e' = 0 := by
    letI : Module.Projective R P := hP
    letI : Projective P' := by
      simpa [P'] using (inferInstance : Projective (ModuleCat.of R P))
    exact e'.eq_zero_of_projective
  have hfg' : ModuleCat.ofHom (LinearMap.lsmul R M a) = f' ≫ g' := by
    simpa [f', g'] using congrArg ModuleCat.ofHom hfg
  -- Re-express scalar multiplication through the chosen projective factorization.
  calc
    a • e = (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M a))).comp e (zero_add 1) := by
      symm
      simpa using mk₀_lsmul_comp_ext_eq_smul (R := R) (M := M) N a e
    _ = (mk₀ (f' ≫ g')).comp e (zero_add 1) := by
      rw [hfg']
    _ = ((mk₀ f').comp (mk₀ g') (zero_add 0)).comp e (zero_add 1) := by
      rw [Ext.mk₀_comp_mk₀]
    _ = (mk₀ f').comp ((mk₀ g').comp e (zero_add 1)) (show 0 + 1 = 1 from rfl) := by
      simpa using
        (Ext.comp_assoc (mk₀ f') (mk₀ g') e (zero_add 0) (zero_add 1)
          (show 0 + 0 + 1 = 1 from rfl)).symm
    _ = 0 := by
      simp [e', he']

/-- Helper for Lemma 15.71.3: vanishing of the Yoneda product with the extension class lifts an
endomorphism of the cokernel object through the projective middle term. -/
lemma factorsThroughProjective_of_mk₀_comp_extClass_zero
    {S : ShortComplex (ModuleCat.{max u v} R)} (hS : S.ShortExact)
    (hX₂ : Projective S.X₂) (φ : S.X₃ ⟶ S.X₃)
    (hφ : (mk₀ φ).comp hS.extClass (zero_add 1) = 0) :
    φ.hom.FactorsThroughProjective := by
  -- Exactness lifts the degree-zero class `mk₀ φ` to a morphism into the middle term.
  obtain ⟨ψExt, hψExt⟩ := covariant_sequence_exact₃ _ hS (mk₀ φ) (zero_add 1) hφ
  obtain ⟨ψ, rfl⟩ := homEquiv₀.symm.surjective ψExt
  have hcomp : ψ ≫ S.g = φ := by
    -- Translate the lifted `Ext⁰` class back to an equality of morphisms.
    apply homEquiv₀.symm.injective
    simpa [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using hψExt
  letI : Projective S.X₂ := hX₂
  letI : Module.Projective R S.X₂ := by
    infer_instance
  have hfactor : φ.hom = S.g.hom.comp ψ.hom := by
    simpa using (ModuleCat.hom_ext_iff.mp hcomp).symm
  exact ⟨S.X₂, inferInstance, inferInstance, inferInstance, ψ.hom, S.g.hom, hfactor⟩

/-- Helper for Lemma 15.71.3: if `I` annihilates all `Ext¹_R(M, -)`, then every scalar
endomorphism by an element of `I` factors through a projective module. -/
lemma lsmul_factorsThroughProjective_of_ext_annihilator
    (hAnn : ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1)) :
    ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughProjective := by
  intro a
  let q : Projective.over M ⟶ M := Projective.π M
  let S : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk (Limits.kernel.ι q) q (Limits.kernel.condition q)
  have hS : S.ShortExact := by
    -- The kernel short complex of the chosen projective presentation is short exact.
    refine { exact := ShortComplex.exact_kernel q }
  have hX₂ : Projective S.X₂ := by
    -- The middle term is the chosen projective cover.
    simpa [S, q] using (inferInstance : Projective (Projective.over M))
  have ha :
      (a : R) ∈ Module.annihilator R (Ext M S.X₁ 1) :=
    hAnn S.X₁ a.2
  have hsmul : (a : R) • hS.extClass = 0 := by
    exact Module.mem_annihilator.mp ha hS.extClass
  have hcomp :
      (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M (a : R)))).comp hS.extClass (zero_add 1) = 0 := by
    -- Rewrite the annihilator hypothesis as the exactness input for the scalar endomorphism.
    rw [mk₀_lsmul_comp_ext_eq_smul (R := R) (M := M) S.X₁ (a : R) hS.extClass]
    exact hsmul
  simpa using
    factorsThroughProjective_of_mk₀_comp_extClass_zero (R := R) (S := S) hS hX₂
      (ModuleCat.ofHom (LinearMap.lsmul R M (a : R))) hcomp

/-
Domain-style sampling:
* primary domain: ideal-projective modules, expressed by pointwise factorization of the scalar-action
  endomorphisms `LinearMap.lsmul R M (a : R)`, together with the induced annihilation
  criterion on `Ext¹` in `ModuleCat R`;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.FactorsThroughFree`,
  `LinearMap.factorsThroughProjective_iff_factorsThroughFree`,
  `Module.annihilator`,
  `Ext`;
* best owner abstraction: the source-facing projective clause is already owned by
  `Module.IsIdealProjective I M`, whose primitive data are the pointwise factorizations of the maps
  `LinearMap.lsmul R M (a : R)` through `LinearMap.FactorsThroughProjective`; the
  free-factorization clause is
  the companion bridge through `LinearMap.FactorsThroughFree`, while the Ext-annihilation clause is
  owned canonically by the annihilator containment
  `I ≤ Module.annihilator R (Ext M N 1)`;
* layer triage:
  this TFAE is `source-facing`,
  `Module.IsIdealProjective I M` is the chapter source-facing owner for clause `(1)`,
  the `LinearMap` factorization API is the canonical bridge for the scalar-action endomorphisms,
  and the `Ext¹`-annihilation clause is derived API;
* primitive data: the ideal `I`, the module object `M`, and for each `a : I` a factorization of
  the action endomorphism `LinearMap.lsmul R M (a : R)` through a projective module;
* derived API: by factoring identities on projective modules through free modules via
  `LinearMap.factorsThroughProjective_iff_factorsThroughFree`, one gets the free-factorization
  clause expressed by `LinearMap.FactorsThroughFree`, and the unpacked pointwise statement
  `∀ (N) (a : I) (e : Ext M N 1), (a : R) • e = 0`, which is equivalent to the annihilator owner
  clause.
-/

-- Proof sketch: for `(1) ↔ (2)`, if the action map `m ↦ (a : R) • m` factors through a
-- projective module `P`, factor `𝟙 P` through a free module using
-- `LinearMap.factorsThroughProjective_iff_factorsThroughFree` and compose with the given
-- pointwise factorization. For the equivalence with the `Ext¹` annihilation statement, compare
-- extension classes with short exact sequences `0 ⟶ N ⟶ P ⟶ M ⟶ 0`: the action map by `a`
-- factors through a projective module exactly when the pushforward/pullback of every such
-- extension by that map is split, i.e. when `(a : R)` acts trivially on every class in `Ext M N
-- 1`.
/-- Lemma 15.71.3: for an ideal `I` of a commutative ring `R` and an `R`-module `M`, the
following are equivalent: for every `a ∈ I`, the multiplication map `m ↦ (a : R) • m` factors
through a projective module, for every `a ∈ I` it factors through a free module, and for every
`R`-module `N` the ideal `I` is contained in the annihilator of `Ext^1_R(M, N)`. -/
theorem smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext
    (I : Ideal R) (M : ModuleCat.{max u v} R) :
    List.TFAE
      [ Module.IsIdealProjective I M
      , ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree
      , ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1)
      ] := by
  let P : Prop := Module.IsIdealProjective I M
  let F : Prop := ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree
  let E : Prop := ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1)
  change List.TFAE [P, F, E]
  have hPF : P ↔ F := by
    -- The free-factorization clause is exactly the bridge proved just above.
    simpa [P, F] using isIdealProjective_iff_smul_endomorphism_factorsThroughFree I M
  have hPE : P ↔ E := by
    constructor
    · -- An `I`-projective module makes every scalar endomorphism act trivially on `Ext¹`.
      intro hM
      change ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1)
      intro N a ha
      rw [Module.mem_annihilator]
      intro e
      let aI : I := ⟨a, ha⟩
      rcases hM.factorsThroughProjective aI with ⟨P', hPAdd, hPModule, hP, f, g, hfg⟩
      letI : AddCommMonoid P' := hPAdd
      letI : AddCommGroup P' := Module.addCommMonoidToAddCommGroup R
      letI : Module R P' := hPModule
      let P'' : ModuleCat.{max u v} R := ModuleCat.of R P'
      let f' : M ⟶ P'' := ModuleCat.ofHom f
      let g' : P'' ⟶ M := ModuleCat.ofHom g
      let e' : Ext P'' N 1 := (mk₀ g').comp e (zero_add 1)
      have he' : e' = 0 := by
        letI : Module.Projective R P' := hP
        letI : Projective P'' := by
          simpa [P''] using (inferInstance : Projective (ModuleCat.of R P'))
        exact e'.eq_zero_of_projective
      have hfg' : ModuleCat.ofHom (LinearMap.lsmul R M a) = f' ≫ g' := by
        simpa [f', g'] using congrArg ModuleCat.ofHom hfg
      calc
        a • e = (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M a))).comp e (zero_add 1) := by
          symm
          simpa using mk₀_lsmul_comp_ext_eq_smul (R := R) (M := M) N a e
        _ = (mk₀ (f' ≫ g')).comp e (zero_add 1) := by
          rw [hfg']
        _ = ((mk₀ f').comp (mk₀ g') (zero_add 0)).comp e (zero_add 1) := by
          rw [Ext.mk₀_comp_mk₀]
        _ = (mk₀ f').comp ((mk₀ g').comp e (zero_add 1)) (show 0 + 1 = 1 from rfl) := by
          simpa using
            (Ext.comp_assoc (mk₀ f') (mk₀ g') e (zero_add 0) (zero_add 1)
              (show 0 + 0 + 1 = 1 from rfl)).symm
        _ = 0 := by
          simp [e', he']
    · -- Route correction: recover the scalar factorization from a projective presentation of `M`.
      intro hAnn
      change Module.IsIdealProjective I M
      refine ⟨fun a ↦ ?_⟩
      let q : Projective.over M ⟶ M := Projective.π M
      let S : ShortComplex (ModuleCat.{max u v} R) :=
        ShortComplex.mk (Limits.kernel.ι q) q (Limits.kernel.condition q)
      have hS : S.ShortExact := by
        refine { exact := ShortComplex.exact_kernel q }
      have hX₂ : Projective S.X₂ := by
        simpa [S, q] using (inferInstance : Projective (Projective.over M))
      have ha :
          (a : R) ∈ Module.annihilator R (Ext M S.X₁ 1) :=
        hAnn S.X₁ a.2
      have hsmul : (a : R) • hS.extClass = 0 := by
        exact Module.mem_annihilator.mp ha hS.extClass
      have hcomp :
          (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R M (a : R)))).comp hS.extClass (zero_add 1) = 0 := by
        rw [mk₀_lsmul_comp_ext_eq_smul (R := R) (M := M) S.X₁ (a : R) hS.extClass]
        exact hsmul
      simpa using
        factorsThroughProjective_of_mk₀_comp_extClass_zero (R := R) (S := S) hS hX₂
          (ModuleCat.ofHom (LinearMap.lsmul R M (a : R))) hcomp
  have hFE : F ↔ E := by
    exact hPF.symm.trans hPE
  have hFE_tfae : List.TFAE [F, E] := by
    rw [List.tfae_cons_of_mem (a := F) (b := E) (l := [E]) (by simp)]
    exact ⟨hFE, List.tfae_singleton E⟩
  rw [List.tfae_cons_of_mem (a := P) (b := F) (l := [F, E]) (by simp)]
  exact ⟨hPF, hFE_tfae⟩

/-- Companion projection of Lemma `15.71.3`: an `R`-module is `I`-projective exactly when `I`
annihilates `Ext^1_R(M, N)` for every `R`-module `N`. -/
theorem isIdealProjective_iff_ext_annihilator
    (I : Ideal R) (M : ModuleCat.{max u v} R) :
    Module.IsIdealProjective I M ↔
      ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) :=
  (smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext I M).out 0 2

end
