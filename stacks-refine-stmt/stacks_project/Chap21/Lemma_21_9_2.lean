import Mathlib
import stacks_project.Chap12.Definition_12_12_1
import stacks_project.Chap21.Definition_21_8_1
import stacks_project.Chap21.Lemma_21_9_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

/-- The Čech-complex functor on abelian presheaves on `C`, obtained by restriction to `Over U`
and then applying the Čech complex attached to `family`. -/
abbrev cechComplexOnPresheaves :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ CochainComplex AddCommGrpCat ℕ :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat).obj (Over.forget U).op ⋙
    cechComplexFunctor family

-- Proof sketch: evaluate `cechComplexOnPresheaves` on `F`, unfold the composite, and compare with
-- the definition of `cechComplex U family F` from Definition 21.8.1.
/-- The composite restriction-plus-Čech functor evaluates to the Čech complex `cechComplex`. -/
theorem cechComplexOnPresheaves_obj (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    (cechComplexOnPresheaves U family).obj F = cechComplex U family F := sorry

/-- The composite restriction-plus-Čech complex functor is additive. -/
noncomputable instance cechComplexOnPresheaves_additive :
    (cechComplexOnPresheaves U family).Additive := sorry

-- Proof sketch: restriction to `Over U` is exact because limits and colimits in functor
-- categories are computed pointwise, and Lemma 21.9.1 says the Čech complex functor on `Over U`
-- is exact. Therefore a short exact sequence of abelian presheaves maps to a short exact
-- sequence of Čech complexes.
/-- A short exact sequence of abelian presheaves induces a short exact sequence of Čech
complexes. -/
theorem cechComplexOnPresheaves_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    (S.map (cechComplexOnPresheaves U family)).ShortExact := sorry

/-- The degree-`n` Čech cohomology functor associated to `family`. -/
abbrev cechCohomologyDegree (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤+ AddCommGrpCat :=
  AdditiveFunctor.of
    (cechComplexOnPresheaves U family ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n)

-- Proof sketch: `cechCohomologyDegree` is defined by composing `cechComplexOnPresheaves` with the
-- degree-`n` homology functor, whereas `cechCohomology` is the objectwise version of the same
-- construction from Definition 21.8.1.
/-- The degree-`n` functor evaluates to the Čech cohomology group `cechCohomology`. -/
theorem cechCohomologyDegree_obj (n : ℕ) (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    (cechCohomologyDegree U family n).obj.obj F = cechCohomology U family F n := sorry

/-- The connecting morphism in degree `n` attached to a short exact sequence of abelian
presheaves. -/
noncomputable def cechCohomologyConnectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (cechCohomologyDegree U family n).obj.obj S.X₃ ⟶
      (cechCohomologyDegree U family (n + 1)).obj.obj S.X₁ :=
  (cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

-- Proof sketch: unfold `cechCohomologyConnectingMorphism`; it is defined to be the standard
-- connecting morphism in the homology sequence of the mapped short exact sequence of Čech
-- complexes.
/-- The Čech cohomology connecting morphism is the canonical homology-sequence boundary map of the
mapped short exact sequence of Čech complexes. -/
theorem cechCohomologyConnectingMorphism_def
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n =
      (cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl) := sorry

-- Proof sketch: apply the first exactness statement in the homology sequence of the short exact
-- sequence of Čech complexes attached to `hS`.
/-- In degree `0`, the induced map on Čech cohomology is a monomorphism. -/
theorem cechCohomology_mono_map_f_zero
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    Mono ((cechCohomologyDegree U family 0).obj.map S.f) := sorry

-- Proof sketch: this is the relation `H^n(S.X₂) ⟶ H^n(S.X₃) ⟶ H^{n+1}(S.X₁) = 0` in the
-- homology sequence of the short exact sequence of Čech complexes attached to `hS`.
/-- The Čech cohomology connecting morphism kills the image of the middle map. -/
theorem cechCohomology_map_g_comp_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (cechCohomologyDegree U family n).obj.map S.g ≫
        cechCohomologyConnectingMorphism U family hS n =
      0 := sorry

-- Proof sketch: this is the next relation in the homology sequence of the mapped short exact
-- sequence of Čech complexes.
/-- The Čech cohomology connecting morphism factors through the kernel of the next `f`-map. -/
theorem cechCohomologyConnectingMorphism_comp_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n ≫
        (cechCohomologyDegree U family (n + 1)).obj.map S.f =
      0 := sorry

-- Proof sketch: exactness of the three-term segment
-- `H^n(S.X₁) ⟶ H^n(S.X₂) ⟶ H^n(S.X₃)` in the homology sequence of the short exact sequence of
-- Čech complexes yields the claim.
/-- In every degree, the mapped short complex on Čech cohomology is exact. -/
theorem cechCohomology_map_exact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (cechCohomologyDegree U family n).obj).Exact := sorry

-- Proof sketch: this is exactness at `\check H^n(\mathcal U, \mathcal F_3)` in the long exact
-- sequence obtained from the short exact sequence of Čech complexes.
/-- The sequence
`\check H^n(\mathcal U, \mathcal F_2) ⟶ \check H^n(\mathcal U, \mathcal F_3) ⟶
\check H^{n+1}(\mathcal U, \mathcal F_1)` is exact. -/
theorem cechCohomology_exact_map_g_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      ((cechCohomologyDegree U family n).obj.map S.g)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomology_map_g_comp_connectingMorphism U family hS n)).Exact := sorry

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, \mathcal F_1)` in the same long
-- exact sequence.
/-- The sequence
`\check H^n(\mathcal U, \mathcal F_3) ⟶ \check H^{n+1}(\mathcal U, \mathcal F_1) ⟶
\check H^{n+1}(\mathcal U, \mathcal F_2)` is exact. -/
theorem cechCohomology_exact_connectingMorphism_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      (cechCohomologyConnectingMorphism U family hS n)
      ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
      (cechCohomologyConnectingMorphism_comp_map_f U family hS n)).Exact := sorry

-- Proof sketch: a morphism of short exact sequences of abelian presheaves maps to a morphism of
-- short exact sequences of Čech complexes, and the naturality of the homology-sequence connecting
-- morphism gives the commutative square.
/-- The Čech cohomology connecting morphisms are natural in morphisms of short exact sequences of
abelian presheaves. -/
theorem cechCohomologyConnectingMorphism_naturality
    {S T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq
      ((cechCohomologyDegree U family n).obj.map φ.τ₃)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomologyConnectingMorphism U family hT n)
      ((cechCohomologyDegree U family (n + 1)).obj.map φ.τ₁) := sorry

/-- Lemma 21.9.2: for a family `family : ι → Over U`, the Čech cohomology functors
`F ↦ \check H^n(family, F)` form a cohomological `δ`-functor from the abelian category of
abelian presheaves on `C` to `AddCommGrpCat`, i.e. to the category of `\mathbf Z`-modules. -/
noncomputable def cechCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat) AddCommGrpCat where
  F := cechCohomologyDegree U family
  δ := fun {_} hS n ↦ cechCohomologyConnectingMorphism U family hS n
  mono_map_f_zero := fun {_} hS ↦ cechCohomology_mono_map_f_zero U family hS
  exact₅ := fun {_} hS n ↦
    CohomologicalDeltaFunctor.exact₅_of_adjacent_exactness
      (fun {_} hS n ↦ cechCohomology_map_g_comp_connectingMorphism U family hS n)
      (fun {_} hS n ↦ cechCohomologyConnectingMorphism_comp_map_f U family hS n)
      (fun {_} hS n ↦ cechCohomology_map_exact U family hS n)
      (fun {_} hS n ↦ cechCohomology_exact_map_g_connectingMorphism U family hS n)
      (fun {_} hS n ↦ cechCohomology_exact_connectingMorphism_map_f U family hS n)
      hS n
  δ_naturality := fun {_ _} hS hT φ n ↦
    cechCohomologyConnectingMorphism_naturality U family hS hT φ n

-- Proof sketch: unfold `cechCohomologyDeltaFunctor`; its degree-`n` term is defined to be
-- `cechCohomologyDegree U family n`.
/-- The degree-`n` term of the Čech cohomology `δ`-functor is `cechCohomologyDegree U family n`. -/
theorem cechCohomologyDeltaFunctor_F_eq (n : ℕ) :
    (cechCohomologyDeltaFunctor U family n).obj = (cechCohomologyDegree U family n).obj := sorry

end CategoryTheory
