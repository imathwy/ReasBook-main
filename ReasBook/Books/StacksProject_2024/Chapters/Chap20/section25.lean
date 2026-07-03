import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_25_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open DerivedCategory.TStructure
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/-- The underlying sheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditiveSheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))

/-- The underlying presheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditivePresheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ X.carrier.Presheaf AddCommGrpCat.{u} :=
  moduleUnderlyingAdditiveSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The global-sections functor on `\mathcal O_X`-modules, after forgetting the
`\Gamma(X, \mathcal O_X)`-module structure down to abelian groups. -/
abbrev moduleGlobalSectionsAdditiveFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  moduleUnderlyingAdditiveSheaf X ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules is additive. -/
instance moduleGlobalSectionsAdditiveFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsAdditiveFunctor X).Additive := sorry

/-- The functor sending an `\mathcal O_X`-module to the extended Čech complex of its underlying
additive presheaf. -/
abbrev moduleCechRowFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  moduleUnderlyingAdditivePresheaf X ⋙
    cechComplexFunctor 𝒰 ⋙
      (ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat.{u}

/-- The extended rowwise Čech functor preserves zero morphisms. -/
instance moduleCechRowFunctor_preservesZeroMorphisms
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (moduleCechRowFunctor X 𝒰).PreservesZeroMorphisms := sorry

/-- The rowwise Čech bicomplex associated to a cochain complex of `\mathcal O_X`-modules and an
indexed family of opens. -/
abbrev moduleCechDoubleComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{u}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (moduleCechRowFunctor X 𝒰).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total Čech complex functor on cochain complexes of `\mathcal O_X`-modules. -/
abbrev moduleTotalCechComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  moduleCechDoubleComplexFunctor X 𝒰 ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

-- Proof sketch: the Čech direction is supported in nonnegative degrees, and the input complex is
-- bounded below, so only finitely many summands contribute to sufficiently negative total degrees.
-- Hence the total complex remains bounded below.
/-- The total Čech complex of a bounded-below complex of `\mathcal O_X`-modules is again bounded
below. -/
theorem moduleTotalCechComplex_obj_mem (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    CochainComplex.plus AddCommGrpCat.{u}
      ((moduleTotalCechComplexFunctor X 𝒰).obj K.obj) := sorry

/-- The total Čech complex functor, restricted to bounded-below complexes. -/
abbrev moduleTotalCechComplexToPlus (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤ CochainComplex.Plus AddCommGrpCat.{u} :=
  ObjectProperty.lift
    (CochainComplex.plus AddCommGrpCat.{u})
    (CochainComplex.Plus.ι (RingedSpace.Modules X) ⋙ moduleTotalCechComplexFunctor X 𝒰)
    (moduleTotalCechComplex_obj_mem X 𝒰)

section DerivedComparison

variable (X)
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

/-- The bounded-below derived functor represented by total Čech complexes for the family `𝒰`. -/
abbrev moduleCechDerivedFunctor (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u} :=
  moduleTotalCechComplexToPlus X 𝒰 ⋙
    CategoryTheory.boundedBelowCochainComplexToDerivedBelow (𝟭 AddCommGrpCat.{u})

/-- The bounded-below derived global-sections functor on complexes of `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSectionsFunctor :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.boundedBelowCochainComplexToDerivedBelow
    (moduleGlobalSectionsAdditiveFunctor X)

-- Proof sketch: choose a bounded-below injective resolution of the input complex, form the
-- rowwise Čech double complex on that injective resolution, and compare both the total Čech
-- complex and the derived global-sections complex with the total complex of the double complex.
-- Injective sheaf modules are Čech-acyclic on an open cover, so the resulting comparison is a
-- quasi-isomorphism and is natural in the input complex.
/-- Lemma 20.25.1: for an open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space `X`,
there is a natural transformation from the total Čech complex functor on bounded-below complexes
of `\mathcal O_X`-modules to the bounded-below derived global-sections functor `RΓ(X,-)`. This
formalizes the canonical map
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet)) \to RΓ(X,\mathcal F^\bullet)`,
functorial in `\mathcal F^\bullet`. -/
theorem moduleCechDerivedFunctor_exists_natTrans_to_derivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      (moduleCechDerivedFunctor X 𝒰 :
        CochainComplex.Plus (RingedSpace.Modules X) ⥤
          CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat.{u}) ⟶
        moduleDerivedGlobalSectionsFunctor X,
      True := sorry

/-- The `E_2^{p,q}` term in the Čech-to-hypercohomology spectral sequence attached to the open
cover `𝒰` and a bounded-below complex `K`. -/
abbrev moduleCechHypercohomologyPageTwoTerm
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex.Plus (RingedSpace.Modules X))
    (p : ℕ) (q : ℤ) :
    AddCommGrpCat.{u} :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((cechComplexFunctor 𝒰).obj
      ((moduleUnderlyingAdditivePresheaf X).obj (K.obj.homology q)))

/-- The hypercohomology object `H^n(X, K)` computed via bounded-below derived global sections. -/
abbrev moduleDerivedGlobalSectionsCohomology
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (n : ℤ) :
    AddCommGrpCat.{u} :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((moduleDerivedGlobalSectionsFunctor X).obj K))

/-- A packaged cohomological spectral sequence computing hypercohomology from the Čech complexes
of the cohomology sheaves of a bounded-below complex. -/
structure CechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex.Plus (RingedSpace.Modules X)) where
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{u} 0
  /-- The `E_2`-page identifies with Čech cohomology of the cohomology sheaves `\underline H^q`.
  -/
  pageTwoIso :
    ∀ p : ℕ, ∀ q : ℤ,
      (spectralSequence.page 2).X (Int.ofNat p, q) ≅
        moduleCechHypercohomologyPageTwoTerm X 𝒰 K p q
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat.{u}
  /-- The abutment identifies with hypercohomology computed by `RΓ(X, K)`. -/
  targetIso :
    ∀ n : ℤ,
      abutment n ≅ moduleDerivedGlobalSectionsCohomology X K n

-- Proof sketch: choose a Cartan-Eilenberg resolution of the bounded-below complex `K`, apply the
-- Čech construction rowwise to obtain a triple complex, reinterpret it as a double complex, and
-- then take the second spectral sequence. The `E₂`-page identifies with Čech cohomology of the
-- cohomology sheaves, and convergence follows from the boundedness of the Cartan-Eilenberg model.
/-- A bounded-below Čech-to-hypercohomology spectral sequence for an open cover of a ringed space.
-/
theorem exists_moduleCechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    Nonempty (CechToDerivedGlobalSectionsSpectralSequence X 𝒰 K) := sorry

end DerivedComparison

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_25_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

/-- The finite intersection attached to a Čech multi-index of the cover `𝒰`. -/
abbrev cechCoverIntersection (𝒰 : ι → Opens X.carrier) {p : ℕ} (σ : Fin (p + 1) → ι) :
    Opens X.carrier :=
  ⨅ a, 𝒰 (σ a)

-- Proof sketch: apply the Čech-to-hypercohomology spectral sequence from Lemma `20.25.1`. The
-- hypothesis says that for every fixed internal degree `q`, the higher cohomology of `K.X q` on
-- every finite intersection of the cover vanishes, so the spectral sequence is concentrated on the
-- `p = 0` row. Therefore the edge comparison from the total Čech complex to derived global
-- sections is an isomorphism.
/-- Lemma 20.25.2: if every positive-degree cohomology group of each term `\mathcal F^q` of a
bounded-below complex vanishes on every finite intersection of the open cover `𝒰`, then the total
Čech complex of the cover is canonically isomorphic to the bounded-below derived global sections
`RΓ(X, \mathcal F^\bullet)`. -/
theorem moduleCechDerivedFunctor_obj_isomorphic_derivedGlobalSections_of_acyclic_on_intersections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : CochainComplex.Plus (RingedSpace.Modules X))
    (hacyclic : ∀ (i : ℕ), 0 < i → ∀ (p : ℕ) (σ : Fin (p + 1) → ι) (q : ℤ),
      IsZero (((moduleUnderlyingAdditiveSheaf X).obj (K.obj.X q)).H' i
        (cechCoverIntersection 𝒰 σ))) :
    IsIsomorphic ((moduleCechDerivedFunctor X 𝒰).obj K)
      ((moduleDerivedGlobalSectionsFunctor X).obj K) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_25_3 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {ι : Type u}
variable [EnoughInjectives (RingedSpace.Modules X)]
variable [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]

variable (𝒰 : ι → Opens X.carrier)

local notation "Dplus" => CategoryTheory.boundedBelowDerivedCategory AddCommGrpCat
local notation "CechF" =>
  (moduleCechDerivedFunctor X 𝒰 : CochainComplex.Plus (RingedSpace.Modules X) ⥤ Dplus)
local notation "RGammaF" => moduleDerivedGlobalSectionsFunctor X

-- Proof sketch: start with the comparison natural transformation from Lemma `20.25.1`. The
-- source shift is induced by the totalization-versus-bidegree-shift comparison of Remark
-- `12.18.5`, while the target shift is the canonical shift-commuting structure on the bounded-
-- below derived global-sections functor. Replacing a bounded-below complex by an injective
-- resolution reduces the square to the injective case, where the sign computation defining `γ`
-- gives commutativity.
/-- Remark 20.25.3: for an open covering `𝒰` of a ringed space `X`, the Čech-to-derived-global-
sections comparison of Lemma `20.25.1` can be chosen compatibly with every integer shift.
Equivalently, for every bounded-below complex `\mathcal F^\bullet` of `\mathcal O_X`-modules and
every integer `b`, the canonical map
`Tot(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet))[b] \to
R\Gamma(X, \mathcal F^\bullet)[b]` fits into the commutative shifted square described in the
remark. -/
theorem exists_moduleCechDerivedFunctor_comparison_commShift
    (h𝒰 : iSup 𝒰 = ⊤)
    [Functor.CommShift CechF ℤ]
    [Functor.CommShift RGammaF ℤ] :
    ∃ τ : CechF ⟶ RGammaF, NatTrans.CommShift τ ℤ := sorry

-- Proof sketch: this is the objectwise square expressing compatibility of `τ` with the shift.
-- It is exactly the specialization of `NatTrans.shift_app_comm` to the Čech comparison and the
-- bounded-below derived global-sections functor.
/-- A shift-compatible Čech-to-derived-global-sections comparison yields the commutative square on
each bounded-below complex and each integer shift. -/
theorem moduleCechDerivedFunctor_comparison_shift_app_comm
    [Functor.CommShift CechF ℤ]
    [Functor.CommShift RGammaF ℤ]
    {τ : CechF ⟶ RGammaF} [NatTrans.CommShift τ ℤ]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (b : ℤ) :
    (Functor.commShiftIso CechF b).hom.app K ≫ (τ.app K)⟦b⟧' =
      τ.app ((shiftFunctor (CochainComplex.Plus (RingedSpace.Modules X)) b).obj K) ≫
        (Functor.commShiftIso RGammaF b).hom.app K := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_25_4 (from Chap20) -/
/-
Domain-style sampling for Lemma 20.25.4:
- primary domain: compatibility between cohomological connecting morphisms, Čech cup products,
  and the total-complex sign rule;
- sampled owner declarations:
  `CategoryTheory.DeltaFunctor.connectingMorphism`,
  `AlgebraicGeometry.RingedSpace.ringedSpaceCechCohomologyConnectingMorphism`,
  `tensorObj_d_on_summand_eq`,
  `Functor.LaxMonoidal.μ`;
- best owner abstraction:
  `source-facing`: the signed boundary-cup compatibility relation itself;
  `core/canonical`: the connecting-morphism owners
    `CategoryTheory.DeltaFunctor.connectingMorphism` and
    `AlgebraicGeometry.RingedSpace.ringedSpaceCechCohomologyConnectingMorphism`, together with
    the total-complex differential formula `tensorObj_d_on_summand_eq` and the total Čech tensor
    comparison `Functor.LaxMonoidal.μ`;
  `bridge/view`: the theorem below, stated only in terms of the resulting boundary maps and cup
    pairings, without a parallel packaging wrapper.
- primitive data: the graded families `F₁`, `F₃`, `G₁`, `G₃`, `H` together with the two boundary
  maps and the two cup-product pairings.
- derived API: the signed boundary-cup compatibility statement below.

Source/core/bridge triage:
- `source-facing`: the textbook sign relation between the two ways of combining boundary maps and
  cup products;
- `core/canonical`: the chapter owners for connecting morphisms and total-complex tensor signs;
- `bridge/view`: this lemma, specialized to the source data and stated directly without a parallel
  setup wrapper.
-/

universe u

section

variable {F₁ F₃ G₁ G₃ H : ℕ → Type u}
variable [∀ k : ℕ, SMul ℤ (H k)]
variable
  (boundaryF : ∀ ⦃n : ℕ⦄, F₃ n → F₁ (n + 1))
  (boundaryG : ∀ ⦃m : ℕ⦄, G₁ m → G₃ (m + 1))
  (gamma₁ : ∀ ⦃n m : ℕ⦄, F₁ (n + 1) → G₁ m → H (n + m + 1))
  (gamma₃ : ∀ ⦃n m : ℕ⦄, F₃ n → G₃ (m + 1) → H (n + m + 1))

-- Proof sketch: in the source application, the comparison hypotheses identifying the abstract
-- boundary maps and cup products with the corresponding Čech and sheaf-cohomology constructions
-- are established upstream. After making those identifications, choose Čech cocycle
-- representatives for `a₃` and `b₁`, lift them to the middle terms of the two short exact
-- sequences, identify the resulting boundaries with representatives of `∂ a₃` and `∂ b₁`, and
-- apply the total-complex Leibniz rule
-- `d(α₂ ∪ β₂) = d α₂ ∪ β₂ + (-1)^n α₂ ∪ d β₂`.
/-- Lemma 20.25.4: after identifying the source boundary maps and cup products with the abstract
data `boundaryF`, `boundaryG`, `gamma₁`, and `gamma₃`, the pairing obtained from `γ₁` after taking
the boundary on the `\mathcal F`-side equals `(-1)^(n + 1)` times the pairing obtained from `γ₃`
after taking the boundary on the `\mathcal G`-side. -/
theorem gamma_boundary_cup_eq_signed_gamma_cup_boundary
    {n m : ℕ} (a₃ : F₃ n) (b₁ : G₁ m) :
    gamma₁ (boundaryF a₃) b₁ =
      ((-1 : ℤ) ^ (n + 1)) • gamma₃ a₃ (boundaryG b₁) := sorry

end

/-! ### Lemma_20_25_5 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopologicalSpace.SheafCohomology

variable {X : Type u} [TopologicalSpace X]

abbrev TopologicalSpaceSite (X : Type u) [TopologicalSpace X] : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

/-- The underlying `RingCat`-valued sheaf of a sheaf of commutative rings on `X`. -/
abbrev ringSheaf (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :
    Sheaf (TopologicalSpaceSite X) RingCat.{u} :=
  (sheafCompose (TopologicalSpaceSite X) (forget₂ CommRingCat RingCat.{u})).obj O

/-- The underlying sheaf of abelian groups of a sheaf of commutative rings on `X`. -/
abbrev additiveSheaf (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :
    Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u} :=
  (sheafCompose (TopologicalSpaceSite X)
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj O

/-- The additive-sheaf morphism underlying a morphism of sheaves of commutative rings on `X`. -/
abbrev additiveSheafMap
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}} (π : O' ⟶ O) :
    additiveSheaf O' ⟶ additiveSheaf O :=
  (sheafCompose (TopologicalSpaceSite X)
    (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).map π

/-- The underlying sheaf of abelian groups of a sheaf of modules over `O`. -/
abbrev moduleUnderlyingSheaf
    {O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (I : SheafOfModules (ringSheaf O)) :
    Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringSheaf O)).obj I

/-- The maximal open subset of `X`. -/
abbrev topOpen : Opens X :=
  ⟨Set.univ, isOpen_univ⟩

/-- The ring of global sections of a sheaf of commutative rings on `X`. -/
abbrev globalSectionsRing (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) :=
  O.obj.obj (op topOpen)

/-- Every open subset of `X` is contained in the maximal open. -/
theorem le_topOpen (U : Opens X) : U ≤ topOpen := by
  intro x hx
  simp [topOpen]

/-- A square-zero extension setup for the boundary derivation statement on a topological space. -/
structure SquareZeroBoundarySetup
    (O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}) where
  /-- The kernel ideal, viewed as a sheaf of `O`-modules. -/
  idealModule : SheafOfModules (ringSheaf O)
  /-- The surjection of sheaves of commutative rings `\mathcal O' \twoheadrightarrow \mathcal O`. -/
  quotient : O' ⟶ O
  /-- The inclusion of the underlying additive sheaf of the kernel ideal into `\mathcal O'`. -/
  idealInclusion :
    moduleUnderlyingSheaf idealModule ⟶ additiveSheaf O'
  /-- The inclusion lands in the kernel of the quotient map on underlying additive sheaves. -/
  zero_comp : idealInclusion ≫ additiveSheafMap quotient = 0
  /-- The additive short complex `0 ⟶ \mathcal I ⟶ \mathcal O' ⟶ \mathcal O` is short exact. -/
  shortExact :
    (ShortComplex.mk idealInclusion (additiveSheafMap quotient) zero_comp).ShortExact
  /-- The quotient map is an epimorphism of sheaves of commutative rings. -/
  quotient_epi : Epi quotient
  /-- Sectionwise, products of two local sections from the ideal vanish in `\mathcal O'`. -/
  square_zero :
    ∀ U : (Opens X)ᵒᵖ, ∀ x y : idealModule.val.obj U,
      ((show ↑(O'.obj.obj U) from idealInclusion.hom.app U x) *
        (show ↑(O'.obj.obj U) from idealInclusion.hom.app U y)) = 0
  /-- Multiplication by a lift in `\mathcal O'` induces the given `\mathcal O`-module structure on
  the kernel ideal via the quotient map. -/
  scalar_compat :
    ∀ U : (Opens X)ᵒᵖ, ∀ a : O'.obj.obj U, ∀ x : idealModule.val.obj U,
      (show ↑(O'.obj.obj U) from
        idealInclusion.hom.app U (((quotient.hom.app U) a) • x)) =
          a * (show ↑(O'.obj.obj U) from idealInclusion.hom.app U x)
  /-- A chosen `Γ(X, \mathcal O)`-module structure on `H^1(X, \mathcal I)`. -/
  cohomologyModule : ModuleCat (globalSectionsRing O)
  /-- The chosen module object has the correct underlying additive group. -/
  cohomologyIso :
    AddCommGrpCat.of cohomologyModule ≅
      AddCommGrpCat.of ((moduleUnderlyingSheaf idealModule).H 1)

/-- The additive map from `\mathbb Z` to an abelian-group object determined by a chosen element. -/
theorem uliftIntToAddCommGrp_map_add
    {A : Type u} [AddCommGroup A] (a : A) (m n : ULift ℤ) :
    (m + n).down • a = m.down • a + n.down • a := by
  simp [add_zsmul]

/-- The presheaf morphism classified by a chosen global section of a sheaf of commutative rings. -/
-- Proof sketch: both sides of the naturality identity are obtained by restricting the same global
-- section `r` from the maximal open to `U`, and scalar multiplication by `n.down` commutes with
-- the restriction morphisms in the underlying additive presheaf.
theorem sectionToConstantPresheafHom_naturality
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))).map f ≫
      AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun n : ULift ℤ ↦ n.down •
            (additiveSheaf O).obj.map (homOfLE (le_topOpen V.unop)).op r)
          (uliftIntToAddCommGrp_map_add
            ((additiveSheaf O).obj.map (homOfLE (le_topOpen V.unop)).op r))) =
      AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun n : ULift ℤ ↦ n.down •
            (additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r)
          (uliftIntToAddCommGrp_map_add
              ((additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r))) ≫
        (additiveSheaf O).obj.map f := sorry

/-- The presheaf morphism classified by a chosen global section of a sheaf of commutative rings. -/
def sectionToConstantPresheafHom
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (additiveSheaf O).obj where
  app U :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun n : ULift ℤ ↦ n.down •
          (additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r)
        (uliftIntToAddCommGrp_map_add
          ((additiveSheaf O).obj.map (homOfLE (le_topOpen U.unop)).op r))
  naturality _ _ f := sectionToConstantPresheafHom_naturality O r f

/-- The morphism from the constant abelian sheaf on `\mathbb Z` classified by a global section of
`O`. -/
noncomputable def sectionToConstantSheafHom
    (O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u})
    (r : globalSectionsRing O) :
    (constantSheaf (TopologicalSpaceSite X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
    additiveSheaf O :=
  ((sheafificationAdjunction (TopologicalSpaceSite X) AddCommGrpCat.{u}).homEquiv _ _).symm
    (sectionToConstantPresheafHom O r)

variable [HasSheafify (TopologicalSpaceSite X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (TopologicalSpaceSite X) AddCommGrpCat.{u})]

/-- The boundary class in `H^1(X, \mathcal I)` attached to a global section of `\mathcal O`. -/
noncomputable def squareZeroBoundaryClass
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (S : SquareZeroBoundarySetup O' O)
    (r : globalSectionsRing O) :
    (moduleUnderlyingSheaf S.idealModule).H 1 :=
  let extClass := S.shortExact.extClass
  let constantZ := (constantSheaf (TopologicalSpaceSite X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  (extClass.postcomp constantZ (rfl : 0 + 1 = 1))
    ((Abelian.Ext.addEquiv₀).symm (sectionToConstantSheafHom O r))

-- Proof sketch: view the short exact sequence
-- `0 ⟶ \mathcal I ⟶ \mathcal O' ⟶ \mathcal O ⟶ 0` in the abelian category of sheaves of
-- abelian groups. The connecting morphism sends a global section of `\mathcal O` to a class in
-- `H^1(X, \mathcal I)`. The square-zero hypothesis and the compatibility of the quotient action
-- with the `\mathcal O`-module structure on `\mathcal I` give the Leibniz rule after transporting
-- the codomain through the chosen `Γ(X, \mathcal O)`-module structure.
/-- Lemma 20.25.5: let `X` be a topological space, let `\mathcal O' \twoheadrightarrow \mathcal O`
be a surjection of sheaves of rings whose kernel ideal `\mathcal I` has square zero, and let
`R = \Gamma(X, \mathcal O)`. After choosing the induced `R`-module structure on `H^1(X,
\mathcal I)` as a bundled `R`-module `M`, the boundary map associated to
`0 \to \mathcal I \to \mathcal O' \to \mathcal O \to 0` is represented by a derivation
`R \to M`. -/
theorem exists_derivation_of_square_zero_boundary_map
    {O' O : Sheaf (TopologicalSpaceSite X) CommRingCat.{u}}
    (S : SquareZeroBoundarySetup O' O) :
    ∃ D : Derivation ℤ (globalSectionsRing O) S.cohomologyModule,
      ∀ r : globalSectionsRing O,
        S.cohomologyIso.hom (D r) = squareZeroBoundaryClass S r := sorry

end TopologicalSpace.SheafCohomology
