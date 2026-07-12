import StacksProject_2024.Chap21.Lemma_21_29_3

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open CochainComplex
open CochainComplex.HomComplex
open ComplexShape
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v u uA

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.29.2:
- primary domain: Mayer-Vietoris test squares on a site together with the comparison maps
  `c^{K'}_{X,Z,Y,E}` for the topology-comparison derived pushforward `R ε_*`;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `CategoryTheory.IsPullback`,
  `CategoryTheory.Functor.essImage`,
  `Functor.totalRightDerived`,
  `siteAbelianInverseImageDerived`;
- best owner abstraction:
  `source-facing`: the family of Mayer-Vietoris squares and the criterion that the specific maps
  `c^{K'}_{Xα,Zα,Yα,Eα}` for `R ε_*` are isomorphisms for all `α`;
  `core/canonical`: `CommSq` for the squares, `IsPullback` for the sectionwise pullback owner,
    the direct topology-comparison total right derived functor of
    `(𝟭 C).sheafPushforwardContinuous AddCommGrpCat τ' τ`,
    together with the stronger-assumption bridge to `siteAbelianInverseImageDerived τ' τ (𝟭 C)`,
    and `Functor.essImage` for essential-image membership;
  `bridge/view`: the cochain Mayer-Vietoris model data
    `IX ⟶ IZY ⟶ IE` together with the identification isomorphisms, the compatibility of those
    arrows with the canonical Mayer-Vietoris restriction maps for the square
    `Eα ⟶ Yα`, `Eα ⟶ Zα`, `Yα ⟶ Xα`, `Zα ⟶ Xα`, and the explicit equality exhibiting the
    comparison morphism as the canonical `mappingCocone.lift`, already introduced in
    Lemma `21.29.3`.

Primitive data are the square family, the topology-comparison pushforward `ε_*`, and the
comparison condition attached to the fixed object `K'`. The main statement should therefore be
about the actual topology-comparison derived pushforward and the corresponding source-facing
Mayer-Vietoris comparison morphisms, with the realization data kept as explicit bridge
hypotheses, while the Mayer-Vietoris square hypothesis is kept in the canonical
`IsPushout` form already used upstream in Lemma `21.26.3`, and the sections condition is kept in
the canonical `IsPullback` form rather than pullback-cone wrapper data.
-/

section

variable {A : Type uA}
variable {X Y Z E : A → C}
variable (e_to_y : ∀ α : A, E α ⟶ Y α)
variable (e_to_z : ∀ α : A, E α ⟶ Z α)
variable (y_to_x : ∀ α : A, Y α ⟶ X α)
variable (z_to_x : ∀ α : A, Z α ⟶ X α)
variable (hle : τ' ≤ τ)

variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (topologyComparisonPushforward τ τ' hle))
  (HomotopyCategory.quasiIso (SiteAbelianSheafCat τ) (up ℤ))]

variable {K' : DerivedCategory (SiteAbelianSheafCat τ')}
variable [HasWeakSheafify τ' AddCommGrpCat]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]

/-- Lemma 21.29.2: fix a family of commutative squares
`E_α ⟶ Y_α`, `E_α ⟶ Z_α`, `Y_α ⟶ X_α`, `Z_α ⟶ X_α`. Assume that every `τ'`-sheaf of sets whose
sections satisfy the pullback condition on each of these squares is already a `τ`-sheaf, and
assume that each square satisfies the Mayer-Vietoris pushout and monomorphism hypotheses of
Lemma `21.29.3`. Then a target object `K'` lies in the essential image of the topology-
comparison derived pushforward `R ε_*`, expressed by
`topologyComparisonPushforwardDerived τ τ' hle`, if and only if,
for every `α`, the canonical Mayer-Vietoris comparison map
`c^{K'}_{X_α,Z_α,Y_α,E_α}` is an isomorphism. The source-facing condition is expressed by
`mayerVietorisComparisonIsIso`, imported from Lemma `21.29.3`, while the cochain realizations of
that comparison remain internal bridge data behind this predicate. -/
@[stacks 0F18]
lemma essentialImage_iff_comparison_maps_areIso_of_mayerVietoris_family
    (hpushout :
      ∀ α : A,
        IsPushout
          (τ.sheafifiedRepresentableMap (e_to_y α))
          (τ.sheafifiedRepresentableMap (e_to_z α))
          (τ.sheafifiedRepresentableMap (y_to_x α))
          (τ.sheafifiedRepresentableMap (z_to_x α)))
    (hmono : ∀ α : A, Mono (τ.sheafifiedRepresentableMap (e_to_y α)))
    (hSheaf :
      ∀ ⦃F' : Cᵒᵖ ⥤ Type (max u v)⦄,
        Presheaf.IsSheaf τ' F' →
          (∀ α : A,
            IsPullback
              (F'.map (y_to_x α).op)
              (F'.map (z_to_x α).op)
              (F'.map (e_to_y α).op)
              (F'.map (e_to_z α).op)) →
            Presheaf.IsSheaf τ F') :
    Functor.essImage
      (topologyComparisonPushforwardDerived τ τ' hle)
      K' ↔
      ∀ α : A,
        mayerVietorisComparisonIsIso
          τ'
          (e_to_y α)
          (e_to_z α)
          (y_to_x α)
          (z_to_x α)
          K' := by
  constructor
  · intro hK' α
    exact
      mayerVietorisComparisonIsIso_of_mem_essentialImage
        τ τ'
        (e_to_y α) (e_to_z α) (y_to_x α) (z_to_x α)
        (hpushout α) (hmono α) hle K' hK'
  · -- TODO: finish the source-faithful reverse implication from the counit triangle
    -- `ε^{-1} K' ⟶ K' ⟶ M' ⟶` once the global derived comparison adjunction
    -- `ε^{-1} ⊣ R ε_*` and the resulting cone-vanishing lemma are available in reusable form.
    sorry

end

end

end CategoryTheory.GrothendieckTopology
