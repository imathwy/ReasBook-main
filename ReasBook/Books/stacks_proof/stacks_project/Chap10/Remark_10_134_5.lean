import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_134_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits
open ULift
open scoped NaiveCotangent

noncomputable section

section

variable (A : Type u) (B : Type u) (C : Type u)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

private noncomputable def restrictOfIso
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (M : Type u) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] :
    (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M) ≅ ModuleCat.of B M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M)) ≃ₗ[B] M from
      { __ := AddEquiv.refl _
        map_smul' _ _ := by simp }).toModuleIso

/-- Helper for Chap10 Remark 10 134 5: the canonical restriction-of-scalars identification acts
as the identity on elements. -/
private theorem restrictOfIso_hom_apply
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    {M : Type u} [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M]
    (m : (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M)) :
    (restrictOfIso (B := B) (C := C) M).hom m = m := rfl

/-- Helper for Chap10 Remark 10 134 5: the inverse restriction-of-scalars identification also
acts as the identity on elements. -/
private theorem restrictOfIso_inv_apply
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    {M : Type u} [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M]
    (m : M) :
    (restrictOfIso (B := B) (C := C) M).inv m = m := rfl

local notation:max "NL_{" S "⁄" R "}↾[" T "]" =>
  Algebra.Extension.naiveCotangentChainComplexRestrictScalars
    (Generators.toExtension (Generators.self R S)) T

/- Domain triage:
* primary domain: naive cotangent complexes and chain homotopies for composable maps of
  commutative rings;
* sampled owner declarations:
  - `Algebra.naiveCotangent`,
  - `Generators.self`,
  - `Algebra.Extension.naiveCotangentChainComplex`,
  - `Algebra.Extension.naiveCotangentChainComplexRestrictScalars`,
  - `Algebra.Extension.self`,
  - `Extension.CotangentSpace.map_comp_cotangentComplex`,
  - `Extension.Cotangent.map_sub_map` and `Extension.CotangentSpace.map_sub_map`,
  - `Homotopy.nullHomotopy'`;
* best owner abstraction: the public source-facing item is the canonical comparison
  `NL_{B/A} → NL_{C/A} → NL_{C/B}` on the owner complexes `NL_{B⁄A}` and `NL_{C⁄B}↾[B]`;
  the self-presentation extensions are primitive implementation data, while the comparison morphism
  and its explicit homotopy are derived API. -/

private noncomputable def naiveCotangentComparisonHom :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  (Generators.defaultHom
    (Generators.self A B : Generators A B B)
    (Generators.self B C : Generators B C C)).toExtensionHom

private noncomputable def naiveCotangentConstantHom :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  ((Generators.ofComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B)).comp
    (Generators.toComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B))).toExtensionHom

private noncomputable def naiveCotangentComparisonHomotopyLinear :
    ((Generators.self A B).toExtension).CotangentSpace →ₗ[B]
      ULift.{u, u} ((Generators.self B C).toExtension).Cotangent := by
  exact moduleEquiv.symm.toLinearMap ∘ₗ
    ((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))

/-- Helper for Chap10 Remark 10 134 5: the down-shape relation from degree `1` to degree `0`. -/
private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

/-- Helper for Chap10 Remark 10 134 5: the down-shape relation from degree `2` to degree `1`. -/
private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

/-- Helper for Chap10 Remark 10 134 5: degree `0` has no incoming differential in the down
shape. -/
private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  simp [ComplexShape.down]

/-- Helper for Chap10 Remark 10 134 5: the constant presentation map factors through the
coefficient inclusion `B → B[C]`. -/
private theorem naiveCotangentConstantHom_toAlgHom (p : (Generators.self A B).Ring) :
    (naiveCotangentConstantHom A B C).toAlgHom p = MvPolynomial.C (algebraMap _ _ p) := by
  -- Unfold the composite `ofComp ∘ toComp`, then use the standard rename-to-coefficients bridge.
  unfold naiveCotangentConstantHom
  rw [Generators.Hom.toExtensionHom_toAlgHom_apply]
  rw [Generators.Hom.toAlgHom_comp_apply]
  rw [Generators.toComp_toAlgHom]
  exact Generators.toAlgHom_ofComp_rename
    (Generators.self B C : Generators B C C)
    (Generators.self A B : Generators A B B) p

/-- Helper for Chap10 Remark 10 134 5: the constant presentation map induces the zero map on
cotangent spaces. -/
private theorem naiveCotangentConstantHom_cotangentSpaceMap_eq_zero :
    CotangentSpace.map (naiveCotangentConstantHom A B C) = 0 := by
  -- Check the map on the canonical basis `d[X_b]`; the constant hom sends `X_b` to `C b`, whose
  -- differential vanishes.
  let b := (Generators.self A B).cotangentSpaceBasis
  apply b.ext
  intro i
  apply (Generators.self B C).cotangentSpaceBasis.repr.injective
  apply Finsupp.ext
  intro j
  -- Compare the image of the basis vector in the target basis, where the derivative of a
  -- constant polynomial vanishes.
  have h :=
    Generators.repr_CotangentSpaceMap
      (((Generators.ofComp
          (Generators.self B C : Generators B C C)
          (Generators.self A B : Generators A B B)).comp
        (Generators.toComp
          (Generators.self B C : Generators B C C)
          (Generators.self A B : Generators A B B))) :
        Generators.Hom (Generators.self A B) (Generators.self B C)) i j
  simpa [naiveCotangentConstantHom, naiveCotangentConstantHom_toAlgHom, MvPolynomial.pderiv_C]
    using h

/-- Helper for Chap10 Remark 10 134 5: the constant presentation map induces the zero map on the
conormal modules. -/
private theorem naiveCotangentConstantHom_toAlgHom_eq_zero_of_mem_ker
    (x : ((Generators.self A B).toExtension).ker) :
    (naiveCotangentConstantHom A B C).toAlgHom x.1 = 0 := by
  -- Rewrite the constant map to a constant polynomial, then use the kernel equation in `B`.
  rw [naiveCotangentConstantHom_toAlgHom]
  have hx : (algebraMap (Generators.self A B).Ring B) x.1 = 0 := by
    simpa using x.2
  rw [hx, map_zero]
  rfl

/-- Helper for Chap10 Remark 10 134 5: the constant presentation map induces the zero map on the
conormal modules. -/
private theorem naiveCotangentConstantHom_cotangentMap_eq_zero :
    Cotangent.map (naiveCotangentConstantHom A B C) = 0 := by
  -- Every conormal class is represented by a relation `x` with `x ↦ 0` in `B`, hence the
  -- coefficient-only map sends it to zero in `B[C]`.
  ext y
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective y
  -- Read the image of a conormal generator through `Cotangent.map_mk`, then show that the target
  -- kernel representative is literally the zero polynomial.
  change Extension.Cotangent.map (naiveCotangentConstantHom A B C) (Extension.Cotangent.mk x) = 0
  rw [Extension.Cotangent.map_mk, Extension.Cotangent.mk_eq_zero_iff]
  change
    (naiveCotangentConstantHom A B C).toAlgHom x.1 ∈
      ((((Generators.self B C).toExtension).ker) ^ 2 : Ideal _)
  rw [naiveCotangentConstantHom_toAlgHom]
  have hx : (algebraMap (Generators.self A B).Ring B) x.1 = 0 := by
    simpa using x.2
  rw [hx]
  -- Once the representative is the zero polynomial, ideal membership is immediate.
  change (MvPolynomial.C (0 : B)) ∈ ((((Generators.self B C).toExtension).ker) ^ 2 : Ideal _)
  rw [map_zero]
  exact Submodule.zero_mem _

/-- The canonical comparison
`NL_{B/A} → NL_{C/A} → NL_{C/B}`, viewed as a morphism of naive cotangent complexes over `B`. -/
noncomputable def naiveCotangentComparison_comp :
    NL_{B⁄A} ⟶ NL_{C⁄B}↾[B] := by
  let f₀ :
      (NL_{B⁄A}).X 0 ⟶ (NL_{C⁄B}↾[B]).X 0 :=
    ModuleCat.ofHom (CotangentSpace.map (naiveCotangentComparisonHom A B C)) ≫
      (restrictOfIso ((Generators.self B C).toExtension).CotangentSpace).inv
  let f₁ :
      (NL_{B⁄A}).X 1 ⟶ (NL_{C⁄B}↾[B]).X 1 :=
    ModuleCat.ofHom
        (moduleEquiv.symm.toLinearMap ∘ₗ
          Cotangent.map (naiveCotangentComparisonHom A B C) ∘ₗ
            moduleEquiv.toLinearMap) ≫
      (restrictOfIso (ULift.{u, u} ((Generators.self B C).toExtension).Cotangent)).inv
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · ext x
    rcases x with ⟨x⟩
    simp [f₀, f₁, Algebra.Extension.naiveCotangentChainComplexRestrictScalars,
      Algebra.Extension.naiveCotangentChainComplex, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      LinearMap.comp_assoc]
    simpa [LinearMap.comp_assoc] using
      LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex
        (naiveCotangentComparisonHom A B C)).symm x
  · -- Above degree `1`, both naive cotangent complexes have zero differential, so the tail data
    -- for `mkHom` is the zero morphism.
    intro n _
    refine ⟨0, ?_⟩
    -- The restricted target and the source both become the zero-tail two-term complex in higher
    -- degrees, so the compatibility condition is automatic.
    rw [Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ
      ((Generators.self B C).toExtension) B n]
    rw [Extension.naiveCotangentChainComplex_d_succ_succ ((Generators.self A B).toExtension) n]
    simpa using
      (zero_comp :
        (0 : (NL_{B⁄A}).X (n + 2) ⟶ (NL_{C⁄B}↾[B]).X (n + 2)) ≫
          (0 : (NL_{C⁄B}↾[B]).X (n + 2) ⟶ (NL_{C⁄B}↾[B]).X (n + 1)) =
        0)

/-- The explicit degree-`1` homotopy map for Remark 10.134.5. It is zero away from bidegree
`(1,0)`, where it sends `d[X_b]` to the class of `X_{\phi(b)} - b` in the conormal module of
`B[C] → C`. -/
noncomputable def naiveCotangentComparison_comp_homotopyMap
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    (NL_{B⁄A}).X i ⟶ (NL_{C⁄B}↾[B]).X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (naiveCotangentComparisonHomotopyLinear A B C) ≫
            (restrictOfIso (ULift.{u, u} ((Generators.self B C).toExtension).Cotangent)).inv
      | succ j =>
          exact 0
  · exact 0

private noncomputable def naiveCotangentComparison_comp_nullHomotopicMap :
    NL_{B⁄A} ⟶ NL_{C⁄B}↾[B] :=
  Homotopy.nullHomotopicMap' (naiveCotangentComparison_comp_homotopyMap A B C)

/-- Helper for Chap10 Remark 10 134 5: the comparison chain map has zero components in every
higher degree `n + 2`. -/
private theorem naiveCotangentComparison_comp_f_succ_succ (n : ℕ) :
    (naiveCotangentComparison_comp A B C).f (n + 2) = 0 := by
  -- Above degree `1`, the `mkHom` tail data for the comparison map is definitionally zero.
  simpa [naiveCotangentComparison_comp]

/-- Helper for Chap10 Remark 10 134 5: the null-homotopic comparison map also vanishes in every
higher degree `n + 2`. -/
private theorem naiveCotangentComparison_comp_nullHomotopicMap_f_succ_succ (n : ℕ) :
    (naiveCotangentComparison_comp_nullHomotopicMap A B C).f (n + 2) = 0 := by
  -- Expose the local abbreviation only at this component, then use the standard null-homotopy
  -- component formula.
  have rel_succ : (ComplexShape.down ℕ).Rel (n + 3) (n + 2) := by
    simp [ComplexShape.down]
  have rel_prev : (ComplexShape.down ℕ).Rel (n + 2) (n + 1) := by
    simp [ComplexShape.down]
  rw [naiveCotangentComparison_comp_nullHomotopicMap]
  rw [Homotopy.nullHomotopicMap'_f rel_succ rel_prev
    (naiveCotangentComparison_comp_homotopyMap A B C)]
  -- In higher degrees, both homotopy components and differentials vanish.
  simp [naiveCotangentComparison_comp_homotopyMap,
    Extension.naiveCotangentChainComplex_d_succ_succ]
  simpa using
    (zero_add (0 : (NL_{B⁄A}).X (n + 2) ⟶ (NL_{C⁄B}↾[B]).X (n + 2)))

/-- Helper for Chap10 Remark 10 134 5: the degree-`1` component of the null-homotopic comparison
map evaluates to the explicit subtraction formula on cotangent classes. -/
private theorem naiveCotangentComparison_comp_degreeOne_rhs_apply
    (x : ((Generators.self A B).toExtension).Cotangent) :
    (ModuleCat.Hom.hom
        ((NL_{B⁄A}).d 1 0 ≫
            naiveCotangentComparison_comp_homotopyMap A B C 0 1 naiveCotangent_rel10 +
          naiveCotangentComparison_comp_homotopyMap A B C 1 2 naiveCotangent_rel21 ≫
            (NL_{C⁄B}↾[B]).d 2 1))
      { down := x } =
      ULift.up
        (((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
          (((Generators.self A B).toExtension).cotangentComplex x)) := by
  -- Normalize the degree-`1` differential formula first, so only the `(0,1)` homotopy component
  -- survives and the restriction-of-scalars isomorphism becomes the identity on elements.
  rw [Extension.naiveCotangentChainComplex_d_1_0 ((Generators.self A B).toExtension)]
  rw [Extension.naiveCotangentChainComplexRestrictScalars_d_succ_succ
    ((Generators.self B C).toExtension) B 0]
  -- After those owner-level rewrites, the comparison is definitionally the explicit subtraction
  -- map plus the vanished higher-degree term.
  change
    ULift.up
        (((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
          (((Generators.self A B).toExtension).cotangentComplex x)) + 0 =
      ULift.up
        (((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
          (((Generators.self A B).toExtension).cotangentComplex x))
  simp

/-- Helper for Chap10 Remark 10 134 5: the explicit subtraction formula on conormal classes is the
comparison cotangent map because the constant term vanishes. -/
private theorem naiveCotangentComparison_comp_degreeOne_sub_apply
    (x : ((Generators.self A B).toExtension).Cotangent) :
    ULift.up
        (((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
          (((Generators.self A B).toExtension).cotangentComplex x)) =
      ULift.up (Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x) := by
  have hsub :
      ((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
          (((Generators.self A B).toExtension).cotangentComplex x) =
        ((Extension.Cotangent.map (naiveCotangentComparisonHom A B C) -
            Extension.Cotangent.map (naiveCotangentConstantHom A B C)) x) := by
    -- `Cotangent.map_sub_map` is the canonical owner-level subtraction identity.
    simpa [LinearMap.sub_apply] using
      (LinearMap.congr_fun
        (Extension.Cotangent.map_sub_map
          (naiveCotangentComparisonHom A B C)
          (naiveCotangentConstantHom A B C)).symm x)
  have hzero :
      Extension.Cotangent.map (naiveCotangentConstantHom A B C) x = 0 := by
    -- The constant presentation map was already shown to vanish on the conormal module.
    simpa using
      LinearMap.congr_fun (naiveCotangentConstantHom_cotangentMap_eq_zero (A := A) (B := B)
        (C := C)) x
  -- Work in the underlying cotangent module to avoid transport noise from `ULift.up`.
  apply ULift.down_injective
  change
    ((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
        (((Generators.self A B).toExtension).cotangentComplex x) =
      Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x
  -- Combine the subtraction identity with the vanishing constant term.
  calc
    ((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))
        (((Generators.self A B).toExtension).cotangentComplex x) =
      ((Extension.Cotangent.map (naiveCotangentComparisonHom A B C) -
          Extension.Cotangent.map (naiveCotangentConstantHom A B C)) x) := hsub
    _ = Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x -
        Extension.Cotangent.map (naiveCotangentConstantHom A B C) x := by
        rw [LinearMap.sub_apply]
    _ = Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x - 0 := by
        rw [hzero]
    _ = Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x := by
        simp

private theorem naiveCotangentComparison_comp_eq_nullHomotopicMap :
    naiveCotangentComparison_comp A B C =
      naiveCotangentComparison_comp_nullHomotopicMap A B C := by
  -- Compare the chain maps degreewise: degrees `0` and `1` are the explicit homotopy formulas,
  -- while every higher component is zero on both sides.
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      rw [naiveCotangentComparison_comp_nullHomotopicMap]
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        naiveCotangent_rel10
        naiveCotangent_not_rel0
        (naiveCotangentComparison_comp_homotopyMap A B C)]
      ext x
      -- The degree-`0` branch is the cotangent-space subtraction identity with the constant part
      -- already known to vanish.
      simpa [naiveCotangentComparison_comp, naiveCotangentComparison_comp_nullHomotopicMap,
        naiveCotangentComparison_comp_homotopyMap, naiveCotangentComparisonHomotopyLinear,
        Algebra.Extension.naiveCotangentChainComplex,
        Algebra.Extension.naiveCotangentChainComplexRestrictScalars,
        CategoryTheory.Functor.mapHomologicalComplex_obj_d, LinearMap.comp_assoc,
        restrictOfIso_inv_apply, naiveCotangentConstantHom_cotangentSpaceMap_eq_zero] using
        LinearMap.congr_fun
          (Extension.CotangentSpace.map_sub_map
            (naiveCotangentComparisonHom A B C)
            (naiveCotangentConstantHom A B C)) x
  | succ i =>
      cases i with
      | zero =>
          change (naiveCotangentComparison_comp A B C).f 1 =
            (naiveCotangentComparison_comp_nullHomotopicMap A B C).f 1
          rw [naiveCotangentComparison_comp_nullHomotopicMap]
          rw [Homotopy.nullHomotopicMap'_f
            naiveCotangent_rel21
            naiveCotangent_rel10
            (naiveCotangentComparison_comp_homotopyMap A B C)]
          ext x
          rcases x with ⟨x⟩
          -- Route correction: replace the transported `ModuleCat` composite by a dedicated
          -- degree-`1` adapter lemma, then finish in the single `Extension.Cotangent.map` world.
          change ULift.up (Extension.Cotangent.map (naiveCotangentComparisonHom A B C) x) =
            (ModuleCat.Hom.hom
                ((NL_{B⁄A}).d 1 0 ≫
                    naiveCotangentComparison_comp_homotopyMap A B C 0 1
                      naiveCotangent_rel10 +
                  naiveCotangentComparison_comp_homotopyMap A B C 1 2
                    naiveCotangent_rel21 ≫
                    (NL_{C⁄B}↾[B]).d 2 1))
              { down := x }
          rw [naiveCotangentComparison_comp_degreeOne_rhs_apply (A := A) (B := B) (C := C) x]
          rw [naiveCotangentComparison_comp_degreeOne_sub_apply (A := A) (B := B) (C := C) x]
      | succ n =>
          rw [naiveCotangentComparison_comp_f_succ_succ (A := A) (B := B) (C := C) n]
          rw [naiveCotangentComparison_comp_nullHomotopicMap_f_succ_succ
            (A := A) (B := B) (C := C) n]

/-- Chap10 Remark 10 134 5: for ring maps `A → B → C`, the comparison
`NL_{B/A} → NL_{C/A} → NL_{C/B}` coming from the canonical self-presentations is chain-homotopic
to zero. The explicit homotopy sends `d[X_b]` to the class of `X_{\phi(b)} - b` in
`ker(B[C] → C) / ker(B[C] → C)^2`. -/
@[stacks 07VC]
noncomputable def naiveCotangentComparison_comp_homotopy :
    Homotopy (naiveCotangentComparison_comp A B C) 0 := by
  let h :
      Homotopy (naiveCotangentComparison_comp_nullHomotopicMap A B C) 0 :=
    Homotopy.nullHomotopy' fun i j hij ↦
      naiveCotangentComparison_comp_homotopyMap A B C i j hij
  exact (naiveCotangentComparison_comp_eq_nullHomotopicMap A B C) ▸ h

end
