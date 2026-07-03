import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_29_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (ε : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [HasInjectiveResolutions ModX]
variable [ε.IsFlat]
variable [ε.modulePushforward.Additive]
variable [ε.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived ε) (ModuleQis X)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [IsWeakSerreClass A]

-- Proof sketch: push forward is assumed exact on the source weak LinearRepresentations_Serre_1977 full subcategory. Pull back
-- a five-term exact sequence in `A'`, apply weak-LinearRepresentations_Serre_1977 closure on `A`, and then use the unit
-- isomorphisms together with exact pushforward to transport the middle term back to `A'`.
/-- Lemma 21.29.1 (1): in the topology-comparison situation, if pullback identifies the target
subcategory `\mathcal A'` with a weak LinearRepresentations_Serre_1977 subcategory `\mathcal A` on the source and
pushforward is exact on the source subcategory, then `\mathcal A'` is a weak LinearRepresentations_Serre_1977 subcategory
of `\operatorname{Mod}(\mathcal O_{\tau'})`. This formalizes the target-side image of the
textbook subcategory `\mathcal A`. -/
theorem targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (ε.modulePullback.obj ℱ'))
    (hpush_mem : ∀ ⦃ℱ : ModX⦄, A ℱ → A' (ε.modulePushforward.obj ℱ))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory ε A' A hpull_mem)]
    (_hexact : CategoryTheory.exactFunctor A.FullSubcategory ModY
      (ObjectProperty.ι A ⋙ ε.modulePushforward))
    (adj : modulePullbackDerivedOfFlat ε ⊣ modulePushforwardDerived ε)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    IsWeakSerreClass A' := sorry

variable [IsWeakSerreClass A']

-- Proof sketch: apply the derived comparison theorem of Lemma `21.28.6` to the comparison
-- morphism `ε`. The bounded-cohomology basis hypotheses provide the local vanishing input, and
-- the unit isomorphisms on degree-zero objects identify the restricted right derived pushforward
-- as the quasi-inverse.
/-- Lemma 21.29.1 (2): assuming the target image subcategory is weak LinearRepresentations_Serre_1977 and the local
bounded-cohomology hypotheses needed for the comparison-topology argument, the exact pullback
along `\epsilon` induces the equivalence
`D_{\mathcal A'}(\mathcal O_{\tau'}) \simeq D_{\mathcal A}(\mathcal O_\tau)`, with quasi-inverse
given by the restricted right derived pushforward `R \epsilon_*`. -/
theorem topologyComparisonDerivedPullback_isEquivalence_of_boundedCohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (ε.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategory ε A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat ε ⊣ modulePushforwardDerived ε)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpull_mem) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_29_2 (from Chap21) -/
open CategoryTheory

universe v uC uA uSheaf uComplex

section

/-- A commutative square
`E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X`
used as a Mayer-Vietoris test square. -/
structure MayerVietorisTestSquare (C : Type uC) [Category.{v} C] where
  /-- The terminal object of the square. -/
  X : C
  /-- The upper-right object of the square. -/
  Y : C
  /-- The lower-left object of the square. -/
  Z : C
  /-- The upper-left object of the square. -/
  E : C
  /-- The map `E ⟶ Y`. -/
  e_to_y : E ⟶ Y
  /-- The map `E ⟶ Z`. -/
  e_to_z : E ⟶ Z
  /-- The map `Y ⟶ X`. -/
  y_to_x : Y ⟶ X
  /-- The map `Z ⟶ X`. -/
  z_to_x : Z ⟶ X
  /-- The square commutes. -/
  comm : e_to_y ≫ y_to_x = e_to_z ≫ z_to_x

variable {C : Type uC} [Category.{v} C]

-- Proof sketch: the forward implication is exactly the hypothesis that objects in the essential
-- image of `R ε_*` have isomorphic comparison maps. For the reverse implication, use the
-- adjunction triangle `K' ⟶ R ε_* ε⁻¹ K' ⟶ M' ⟶ K'[1]`, apply the two-out-of-three result for
-- the comparison maps to show that `M'` satisfies the same comparison condition, and then prove
-- by induction on the lowest nonvanishing cohomology sheaf that any bounded-below `M'` with
-- vanishing `ε⁻¹ M'` and satisfying the comparison condition must be zero.
/-- Lemma 21.29.2: for a family of commutative squares
`E_α ⟶ Y_α`, `E_α ⟶ Z_α`, `Y_α ⟶ X_α`, `Z_α ⟶ X_α`, assume that every `τ'`-sheaf whose sections
on each square satisfy the pullback condition
`F'(X_α) = F'(Z_α) ×_{F'(E_α)} F'(Y_α)` is already a `τ`-sheaf, and assume that every object in
the essential image of `R ε_*` has all comparison maps
`c^{K'}_{X_α,Z_α,Y_α,E_α}` isomorphisms. Then a bounded-below object `K'` lies in the essential
image of `R ε_*` if and only if all of these comparison maps are isomorphisms. -/
lemma essentialImage_iff_comparison_maps_areIso_of_mayerVietoris_family
    {A : Type uA} (squares : A → MayerVietorisTestSquare C)
    {Sheaf : Type uSheaf} {Complex : Type uComplex}
    (isTauSheaf : Sheaf → Prop)
    (hasPullbackSections : MayerVietorisTestSquare C → Sheaf → Prop)
    (comparisonMapIsIso : MayerVietorisTestSquare C → Complex → Prop)
    (inEssentialImage : Complex → Prop)
    (isBoundedBelow : Complex → Prop)
    (hSheaf :
      ∀ F' : Sheaf, (∀ α : A, hasPullbackSections (squares α) F') → isTauSheaf F')
    (hEssentialImage :
      ∀ ⦃K' : Complex⦄, inEssentialImage K' → ∀ α : A, comparisonMapIsIso (squares α) K')
    {K' : Complex} (hK' : isBoundedBelow K') :
    inEssentialImage K' ↔ ∀ α : A, comparisonMapIsIso (squares α) K' := sorry

end

/-! ### Lemma_21_29_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open CochainComplex
open CochainComplex.HomComplex

noncomputable section

universe u v u₁ v₁ u₂ v₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable (τ τ' : GrothendieckTopology C)
variable [HasWeakSheafify τ (Type (max u v))]

/-- Membership in the essential image of a functor. -/
private abbrev IsInEssentialImage
    {SourceDerived : Type u₁} {TargetDerived : Type u₂}
    [Category.{v₁} SourceDerived] [Category.{v₂} TargetDerived]
    (F : SourceDerived ⥤ TargetDerived) (K' : TargetDerived) : Prop :=
  ∃ K : SourceDerived, Nonempty (F.obj K ≅ K')

-- Proof sketch: the defining relation for `mappingCocone.lift` with the zero `(-1)`-cochain
-- reduces to the chain-map identity `α ≫ β = 0`.
/-- The zero `(-1)`-cochain satisfies the cocycle relation needed to define the canonical
comparison map into `mappingCocone β`. -/
private theorem mayerVietorisComparisonMap_condition
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    δ (-1) 0 (0 : Cochain IX IE (-1)) +
        Cochain.ofHom (α ≫ β) =
      0 := sorry

/-- The canonical comparison morphism from the left term of a short exact sequence of complexes
to the mapping cocone of the right-hand map. -/
noncomputable def mayerVietorisComparisonMap
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    IX ⟶ mappingCocone β :=
  mappingCocone.lift β α (0 : Cochain IX IE (-1))
    (mayerVietorisComparisonMap_condition α β hαβ)

-- Proof sketch: choose `K` and an isomorphism `derivedPushforward.obj K ≅ K'` from the essential
-- image hypothesis. Lemma `21.20.10` upgrades a K-injective representative of `K` to a
-- K-injective representative on the `τ'`-side, and Lemma `21.26.3` gives the short exact sequence
-- of complexes computing the Mayer-Vietoris comparison. The chosen identifications with
-- `RGammaX`, `RGammaZY`, and `RGammaE` show that the resulting canonical lift is exactly the
-- comparison map `c^{K'}_{X,Z,Y,E}`, hence it becomes an isomorphism in `D(\mathbf Z)`.
/-- Lemma 21.29.3: with `\epsilon : (\mathcal C_\tau, \mathcal O_\tau) \to
(\mathcal C_{\tau'}, \mathcal O_{\tau'})` as above, assume that `h_X^\#` is the pushout of
`h_E^\# \to h_Y^\#` and `h_E^\# \to h_Z^\#` for `\tau`-sheafification and that
`h_E^\# \to h_Y^\#` is injective. If `K'` lies in the essential image of the derived pushforward
formalizing `R \epsilon_*`, then the Mayer-Vietoris comparison map
`c^{K'}_{X,Z,Y,E}` of Lemma `21.26.1`, here modeled by the canonical
`mayerVietorisComparisonMap α β hαβ`, is an isomorphism in the derived category of abelian
groups. -/
theorem mayerVietorisComparison_isIso_of_mem_essentialImage
    {SourceDerived : Type u₁} {TargetDerived : Type u₂}
    [Category.{v₁} SourceDerived] [Category.{v₂} TargetDerived]
    {X Y Z E : C}
    (f : E ⟶ Y) (g : E ⟶ Z)
    (cocone :
      PushoutCocone (τ.sheafifiedRepresentableMap f) (τ.sheafifiedRepresentableMap g))
    (hX : cocone.pt ≅ τ.sheafifiedRepresentable X)
    (hcocone : IsColimit cocone)
    (hmono : Mono (τ.sheafifiedRepresentableMap f))
    (derivedPushforward : SourceDerived ⥤ TargetDerived)
    {K' : TargetDerived}
    (hK' : IsInEssentialImage derivedPushforward K')
    (RGammaX RGammaY RGammaZ RGammaE :
      TargetDerived ⥤ DerivedCategory AddCommGrpCat)
    (RGammaZY : TargetDerived ⥤ DerivedCategory AddCommGrpCat)
    (middleIso : ∀ K : TargetDerived, RGammaZY.obj K ≅ RGammaZ.obj K ⨯ RGammaY.obj K)
    {IX IZY IE : CochainComplex AddCommGrpCat ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0)
    (hexact : (ShortComplex.mk α β hαβ).ShortExact)
    (eX : Q.obj IX ≅ RGammaX.obj K')
    (eZY : Q.obj IZY ≅ RGammaZY.obj K')
    (eE : Q.obj IE ≅ RGammaE.obj K') :
    IsIso (Q.map (mayerVietorisComparisonMap α β hαβ)) := sorry

end

end CategoryTheory.GrothendieckTopology
