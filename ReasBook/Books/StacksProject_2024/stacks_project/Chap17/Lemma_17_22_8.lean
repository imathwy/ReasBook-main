import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_29_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_22_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.8:
- primary domain: filtered colimits of represented Hom functors on the owner category
  `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `colimit.post`,
  `coyoneda.obj`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings`;
- best owner abstraction: the source-facing theorem should be stated on `(RingedSpace.Modules X)`,
  with canonical comparison map `colimit.post ℱ (coyoneda.obj (op 𝒢))`;
- primitive data: a ringed space `X`, a finitely presented module `𝒢 : RingedSpace.Modules X`,
  and a filtered diagram `ℱ : Λ ⥤ RingedSpace.Modules X`;
- derived API: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma on `colim Hom_X(𝒢, ℱ_λ) → Hom_X(𝒢, colim ℱ_λ)`;
- `core/canonical`: `(RingedSpace.Modules X)`, `coyoneda.obj (op 𝒢)`, and `colimit.post`;
- `bridge/view`: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`. -/

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
local notation "JX" => Opens.grothendieckTopology X
local notation "ModX" => RingedSpace.Modules X

/-- Helper for Lemma 17.22.8: top-open sections of a module sheaf form the usual underlying
Type-valued sections functor on the opens site of `X`. -/
private abbrev topSectionsFunctor :
    ModX ⥤ Type (max u w) :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafForget JX ⋙
    (sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X))

/-- Helper for Lemma 17.22.8: a morphism from the unit sheaf into the internal-Hom object is the
same thing as a morphism out of `𝒢`. -/
private noncomputable def homEquivUnitInternalHom
    (𝒢 M : ModX) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ (ihom 𝒢).obj M) ≃ (𝒢 ⟶ M) := by
  -- Proof comment: uncurry the unit morphism through the internal-Hom adjunction and then remove
  -- the tensor unit by the left unitor.
  simpa using
    ((((ihom.adjunction 𝒢).homEquiv (SheafOfModules.unit X.ringCatSheaf) M).symm).trans
      (((λ_ 𝒢).symm.homCongr (Iso.refl M))))

/-- Helper for Lemma 17.22.8: top-open sections of the internal-Hom sheaf compute the represented
Hom-set `Hom_X(𝒢, M)`. -/
private noncomputable def homEquivTopSectionsInternalHom
    (𝒢 M : ModX) :
    (topSectionsFunctor (X := X)).obj ((ihom 𝒢).obj M) ≃ (𝒢 ⟶ M) := by
  -- Proof comment: first reinterpret a top-open section as a morphism from the unit sheaf, then
  -- apply the adjunction-level equivalence from `homEquivUnitInternalHom`.
  exact (((ihom 𝒢).obj M).unitHomEquiv).symm.trans
    (homEquivUnitInternalHom (X := X) 𝒢 M)

/-- Helper for Lemma 17.22.8: the unit-to-internal-Hom bridge is natural in the target module. -/
private theorem homEquivUnitInternalHom_naturality
    (𝒢 : ModX) {M N : ModX} (f : M ⟶ N) (g : 𝒢 ⟶ M) :
    (homEquivUnitInternalHom (X := X) 𝒢 N)
        ((homEquivUnitInternalHom (X := X) 𝒢 M).symm g ≫ (ihom 𝒢).map f) =
      g ≫ f := by
  -- Proof comment: this is exactly right naturality of the internal-Hom adjunction, followed by
  -- simplification of the left-unitor transport.
  dsimp [homEquivUnitInternalHom]
  rw [(ihom.adjunction 𝒢).homEquiv_naturality_right_symm]
  simp

/-- Helper for Lemma 17.22.8: the top-open-sections/internal-Hom equivalence is natural in the
target module. -/
private theorem homEquivTopSectionsInternalHom_naturality
    (𝒢 : ModX) {M N : ModX} (f : M ⟶ N) (g : 𝒢 ⟶ M) :
    (topSectionsFunctor (X := X)).map ((ihom 𝒢).map f)
        ((homEquivTopSectionsInternalHom (X := X) 𝒢 M).symm g) =
      (homEquivTopSectionsInternalHom (X := X) 𝒢 N).symm (g ≫ f) := by
  -- Proof comment: `unitHomEquiv` identifies the map on top sections with postcomposition by
  -- `(ihom 𝒢).map f`, so the claim reduces to the adjunction naturality above.
  change ((ihom 𝒢).obj N).unitHomEquiv
      ((homEquivUnitInternalHom (X := X) 𝒢 M).symm g ≫ (ihom 𝒢).map f) =
    ((ihom 𝒢).obj N).unitHomEquiv
      ((homEquivUnitInternalHom (X := X) 𝒢 N).symm (g ≫ f))
  congr 1
  exact homEquivUnitInternalHom_naturality (X := X) 𝒢 f g

/-- Helper for Lemma 17.22.8: the bridge from represented Hom-sets to top-open sections of the
internal-Hom sheaf is an isomorphism in `Type`. -/
private theorem homIsoTopSectionsInternalHom
    (𝒢 M : ModX) :
    (coyoneda.obj (op 𝒢)).obj M ≅ ((ihom 𝒢 ⋙ topSectionsFunctor (X := X)).obj M) := by
  -- Proof comment: in `Type`, any bijective function is an isomorphism, so the pointwise
  -- equivalence directly yields the desired component.
  letI : IsIso ((homEquivTopSectionsInternalHom (X := X) 𝒢 M).symm) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (homEquivTopSectionsInternalHom (X := X) 𝒢 M).symm.bijective
  exact asIso ((homEquivTopSectionsInternalHom (X := X) 𝒢 M).symm)

/-- Helper for Lemma 17.22.8: the represented functor `Hom_X(𝒢,-)` is naturally isomorphic to
top-open sections of the internal-Hom functor with source `𝒢`. -/
private theorem coyonedaIsoTopSectionsIhom
    (𝒢 : ModX) :
    coyoneda.obj (op 𝒢) ≅ ihom 𝒢 ⋙ topSectionsFunctor (X := X) := by
  -- Proof comment: the components are the pointwise internal-Hom/global-sections equivalences,
  -- and naturality is exactly `homEquivTopSectionsInternalHom_naturality`.
  refine NatIso.ofComponents (fun M ↦ homIsoTopSectionsInternalHom (X := X) 𝒢 M) ?_
  intro M N f
  ext g
  exact homEquivTopSectionsInternalHom_naturality (X := X) 𝒢 f g

/-- Helper for Lemma 17.22.8: the comparison map for the composite functor
`ihom 𝒢 ⋙ topSectionsFunctor` factors through the internal-Hom comparison followed by top-open
sections. -/
private theorem colimitPost_topSectionsIhom_eq
    (𝒢 : ModX) (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ] [HasColimit (ℱ ⋙ ihom 𝒢)]
    [HasColimit (ℱ ⋙ ihom 𝒢 ⋙ topSectionsFunctor (X := X))] :
    colimit.post ℱ (ihom 𝒢 ⋙ topSectionsFunctor (X := X)) =
      colimit.post (ℱ ⋙ ihom 𝒢) (topSectionsFunctor (X := X)) ≫
        (topSectionsFunctor (X := X)).map (colimit.post ℱ (ihom 𝒢)) := by
  -- Proof comment: both comparison morphisms agree on every stage generator of the colimit.
  apply colimit.hom_ext
  intro j
  ext x
  simp [Functor.assoc]

/-- Helper for Lemma 17.22.8: after transporting by the natural isomorphism
`coyoneda.obj (op 𝒢) ≅ ihom 𝒢 ⋙ topSectionsFunctor`, the represented-functor comparison map
matches the internal-Hom/top-sections comparison map. -/
private theorem colimitPost_coyoneda_eq_transport
    (𝒢 : ModX) (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ] [HasColimit (ℱ ⋙ coyoneda.obj (op 𝒢))]
    [HasColimit (ℱ ⋙ ihom 𝒢 ⋙ topSectionsFunctor (X := X))] :
    colimit.post ℱ (coyoneda.obj (op 𝒢)) ≫
        (coyonedaIsoTopSectionsIhom (X := X) 𝒢).hom.app (colimit ℱ) =
      (HasColimit.isoOfNatIso
          (Functor.isoWhiskerLeft ℱ (coyonedaIsoTopSectionsIhom (X := X) 𝒢))).hom ≫
        colimit.post ℱ (ihom 𝒢 ⋙ topSectionsFunctor (X := X)) := by
  -- Proof comment: precompose both sides with each stage coprojection and use naturality of the
  -- bridge isomorphism together with the standard `colimit.ι_post` formula.
  apply colimit.hom_ext
  intro j
  ext g
  rw [Category.assoc, colimit.ι_post]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [Category.assoc, colimit.ι_post]
  simpa using congrFun
    ((coyonedaIsoTopSectionsIhom (X := X) 𝒢).hom.naturality (colimit.ι ℱ j)) g

/-- Helper for Lemma 17.22.8: if postcomposition with `e` is bijective and `e` itself is
bijective, then the original map is bijective. -/
private theorem bijective_of_postcompose
    {A B C : Type (max u w)} (f : A → B) (e : B → C)
    (hComp : Function.Bijective (e ∘ f)) (he : Function.Bijective e) :
    Function.Bijective f := by
  -- Proof comment: injectivity is detected after applying the injective map `e`.
  constructor
  · intro x y hxy
    exact hComp.injective (by simpa using congrArg e hxy)
  · intro z
    -- Proof comment: surjectivity comes from lifting `e z` through `e ∘ f` and canceling `e`.
    obtain ⟨x, hx⟩ := hComp.surjective (e z)
    refine ⟨x, he.injective ?_⟩
    simpa using hx

/-- Helper for Lemma 17.22.8: the Chapter 6 top-open-sections comparison is an isomorphism for
the internal-Hom sheaf diagram attached to `𝒢` and `ℱ`. -/
private theorem topSectionsInternalHomComparison_isIso
    (hX : HasCofinalFiniteQuasiCompactOverlapCoverings JX (⊤ : Opens X))
    (𝒢 : ModX) (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ] [HasColimit (ℱ ⋙ ihom 𝒢)]
    [HasColimit (ℱ ⋙ ihom 𝒢 ⋙ topSectionsFunctor (X := X))] :
    IsIso
      (colimit.post
        (ℱ ⋙ ihom 𝒢 ⋙ SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafForget JX)
        ((sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))) := by
  let H : Λ ⥤ X.Sheaf (Type (max u w)) :=
    ℱ ⋙ ihom 𝒢 ⋙ SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafForget JX
  letI : HasColimit H := by
    infer_instance
  letI :
      HasColimit (H ⋙ (sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))) := by
    simpa [H, topSectionsFunctor, Functor.assoc] using
      (inferInstance : HasColimit (ℱ ⋙ ihom 𝒢 ⋙ topSectionsFunctor (X := X)))
  -- Proof comment: Chapter 6 identifies the top-open-sections comparison map with a bijection,
  -- so in `Type` the comparison map is automatically an isomorphism.
  have hBijective :
      Function.Bijective
        (colimit.post H ((sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))) := by
    simpa [H] using
      bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings
        (𝓕 := H)
        (U := (⊤ : Opens X)) hX
  exact (ConcreteCategory.isIso_iff_bijective _).2 hBijective

-- Proof sketch: identify `Hom_X(\mathcal G, -)` with global sections of the internal-Hom sheaf,
-- apply Lemma `17.22.7` to replace the internal Hom into `colim_\lambda \mathcal F_\lambda` by the
-- filtered colimit of the internal-Hom sheaves, and then apply Lemma `6.29.1` on the top open of
-- `X` using the cofinal finite-cover hypothesis.
/-- Lemma 17.22.8: if the top open of a ringed space `X` has a cofinal system of finite open
covers with quasi-compact pairwise intersections, then for a finitely presented
`\mathcal O_X`-module `\mathcal G` and a filtered diagram `\mathcal F_\lambda` of
`\mathcal O_X`-modules, the canonical map
`colim_\lambda Hom_X(\mathcal G, \mathcal F_\lambda) \to
Hom_X(\mathcal G, colim_\lambda \mathcal F_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hX : HasCofinalFiniteQuasiCompactOverlapCoverings JX (⊤ : Opens X))
    (𝒢 : ModX)
    [𝒢.IsFinitePresentation]
    (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ coyoneda.obj (op 𝒢))] :
    Function.Bijective (colimit.post ℱ (coyoneda.obj (op 𝒢))) := by
  -- Route correction: replace the explicit transport/cancellation tail by the owner-level
  -- preservation route already used in the Chapter 18 sibling lemma.
  let H : Λ ⥤ X.Sheaf (Type (max u w)) :=
    ℱ ⋙ ihom 𝒢 ⋙ SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafForget JX
  let K : ModX ⥤ Type (max u w) :=
    ihom 𝒢 ⋙ topSectionsFunctor (X := X)
  letI : HasColimit (ℱ ⋙ ihom 𝒢) := by
    infer_instance
  letI : HasColimit (ℱ ⋙ K) := by
    infer_instance
  letI : HasColimit H := by
    infer_instance
  letI :
      HasColimit (H ⋙ (sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))) := by
    simpa [H, K, topSectionsFunctor, Functor.assoc] using
      (inferInstance : HasColimit (ℱ ⋙ K))
  -- Proof comment: finite presentation upgrades the internal-Hom comparison to an isomorphism.
  have hInternalHom :
      IsIso (colimit.post ℱ (ihom 𝒢)) :=
    SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation 𝒢 ℱ
  letI : IsIso (colimit.post ℱ (ihom 𝒢)) := hInternalHom
  letI : PreservesColimit ℱ (ihom 𝒢) :=
    preservesColimit_of_isIso_post (F := ℱ) (G := ihom 𝒢)
  letI : IsIso (colimit.post H ((sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))) :=
    topSectionsInternalHomComparison_isIso (X := X) (Λ := Λ) hX 𝒢 ℱ
  letI :
      PreservesColimit H ((sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X))) :=
    preservesColimit_of_isIso_post
      (F := H) (G := (sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X)))
  -- Proof comment: normalize the sheaf-side preservation owner to the exact composite
  -- `ihom 𝒢 ⋙ topSectionsFunctor`.
  have hPreservesK : PreservesColimit ℱ K := by
    simpa [H, K, topSectionsFunctor, Functor.assoc] using
      (inferInstance :
        PreservesColimit H ((sheafSections JX (Type (max u w))).obj (op (⊤ : Opens X))))
  letI : PreservesColimit ℱ K := hPreservesK
  let e : coyoneda.obj (op 𝒢) ≅ K :=
    coyonedaIsoTopSectionsIhom (X := X) 𝒢
  letI : PreservesColimit ℱ (coyoneda.obj (op 𝒢)) :=
    preservesColimit_of_natIso e
  -- Proof comment: once the represented functor preserves the chosen filtered colimit, the
  -- canonical comparison morphism is an isomorphism and hence a bijection in `Type`.
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

end AlgebraicGeometry.RingedSpace
