import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_3_4

noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

-- Semantic recall via `Definition_17_1_1` and `lean_leansearch`: bifunctoriality here needs the
-- chain-map-induced outer morphisms to be the canonical maps coming from functoriality of tensor,
-- `ModuleCat.torFunctor`, `Ext`, and `Hom`, while only the middle morphism in the universal
-- coefficient short exact sequence is chosen.

/-- The canonical chain-map-induced morphism
`H_(n + 1)(X) ⊗ M ⟶ H_(n + 1)(Y) ⊗ M` on the tensor term. -/
abbrev universalCoefficientHomologyChainMapTensorMap
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℕ}
    (φ : X ⟶ Y) (M : ModuleCat R) (n : ℕ) :
    universalCoefficientHomologyTensorTerm R X M n ⟶
      universalCoefficientHomologyTensorTerm R Y M n :=
  HomologicalComplex.homologyMap φ (n + 1) ⊗ₘ 𝟙 M

/-- The canonical chain-map-induced morphism `Tor(H_n(X), M) ⟶ Tor(H_n(Y), M)` on the `Tor`
term. -/
abbrev universalCoefficientHomologyChainMapTorMap
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℕ}
    (φ : X ⟶ Y) (M : ModuleCat R) (n : ℕ) :
    universalCoefficientHomologyTorTerm R X M n ⟶
      universalCoefficientHomologyTorTerm R Y M n :=
  ((ModuleCat.torFunctor R).map (HomologicalComplex.homologyMap φ n)).app M

/-- The canonical chain-map-induced morphism
`Ext¹_R(H_(n - 1)(Y), M) ⟶ Ext¹_R(H_(n - 1)(X), M)` on the `Ext¹` term. -/
abbrev universalCoefficientCohomologyChainMapExtMap
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℤ}
    (φ : X ⟶ Y) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientExtTerm R Y M n ⟶ universalCoefficientExtTerm R X M n :=
  (forget₂ (ModuleCat R) AddCommGrpCat).map
    (((Ext R (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ (n - 1)).op).app
      M)

/-- The canonical chain-map-induced morphism
`Hom(H_n(Y), M) ⟶ Hom(H_n(X), M)` on the `Hom` term. -/
abbrev universalCoefficientCohomologyChainMapHomMap
    {R : Type u} [CommRing R] {X Y : ChainComplex (ModuleCat R) ℤ}
    (φ : X ⟶ Y) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientHomTerm R Y M n ⟶ universalCoefficientHomTerm R X M n :=
  (forget₂ (ModuleCat R) AddCommGrpCat).map
    (ModuleCat.ofHom (Linear.leftComp R _ (HomologicalComplex.homologyMap φ n)))

/-- A chosen family of homological universal coefficient sequences is functorial in chain maps if
every chain map induces a morphism of the chosen short complexes whose outer components are the
canonical tensor and `Tor` maps, natural in coefficient-module maps and compatible with
identities and composition. -/
structure UniversalCoefficientHomologyChainMapFunctorial
    (R : Type u) [CommRing R] (n : ℕ)
    (seq :
      ∀ (X : ChainComplex (ModuleCat R) ℕ),
        (∀ i : ℕ, Module.Flat R (X.X i)) →
          UniversalCoefficientHomologyNaturality R X n)
    (map :
      ∀ {X Y : ChainComplex (ModuleCat R) ℕ} (_ : X ⟶ Y)
        (hX : ∀ i : ℕ, Module.Flat R (X.X i))
        (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
        (M : ModuleCat R),
        ((seq X hX) M).toShortComplex ⟶ ((seq Y hY) M).toShortComplex) : Prop where
  map_tensor :
    ∀ {X Y : ChainComplex (ModuleCat R) ℕ} (φ : X ⟶ Y)
      (hX : ∀ i : ℕ, Module.Flat R (X.X i))
      (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
      (M : ModuleCat R),
      (map φ hX hY M).τ₁ = universalCoefficientHomologyChainMapTensorMap φ M n
  map_tor :
    ∀ {X Y : ChainComplex (ModuleCat R) ℕ} (φ : X ⟶ Y)
      (hX : ∀ i : ℕ, Module.Flat R (X.X i))
      (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
      (M : ModuleCat R),
      (map φ hX hY M).τ₃ = universalCoefficientHomologyChainMapTorMap φ M n
  map_natural :
    ∀ {X Y : ChainComplex (ModuleCat R) ℕ} (φ : X ⟶ Y)
      (hX : ∀ i : ℕ, Module.Flat R (X.X i))
      (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
      {M N : ModuleCat R} (f : M ⟶ N),
      UniversalCoefficientHomologyNaturality.map (seq X hX) f ≫ map φ hX hY N =
        map φ hX hY M ≫ UniversalCoefficientHomologyNaturality.map (seq Y hY) f
  map_id :
    ∀ (X : ChainComplex (ModuleCat R) ℕ) (hX : ∀ i : ℕ, Module.Flat R (X.X i))
      (M : ModuleCat R),
      map (𝟙 X) hX hX M = 𝟙 (((seq X hX) M).toShortComplex)
  map_comp :
    ∀ {X Y Z : ChainComplex (ModuleCat R) ℕ} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
      (hX : ∀ i : ℕ, Module.Flat R (X.X i))
      (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
      (hZ : ∀ i : ℕ, Module.Flat R (Z.X i))
      (M : ModuleCat R),
      map (φ ≫ ψ) hX hZ M = map φ hX hY M ≫ map ψ hY hZ M

/-- A chosen family of cohomological universal coefficient sequences is functorial in chain maps
if every chain map induces a morphism of the chosen short complexes whose outer components are the
canonical `Ext¹` and `Hom` maps, natural in coefficient-module maps and compatible with
identities and composition. -/
structure UniversalCoefficientCohomologyChainMapFunctorial
    (R : Type u) [CommRing R] (n : ℤ)
    (seq :
      ∀ (X : ChainComplex (ModuleCat R) ℤ),
        (∀ i : ℤ, Module.Free R (X.X i)) →
          UniversalCoefficientCohomologyNaturality R X n)
    (map :
      ∀ {X Y : ChainComplex (ModuleCat R) ℤ} (_ : X ⟶ Y)
        (hX : ∀ i : ℤ, Module.Free R (X.X i))
        (hY : ∀ i : ℤ, Module.Free R (Y.X i))
        (M : ModuleCat R),
        ((seq Y hY) M).toShortComplex ⟶ ((seq X hX) M).toShortComplex) : Prop where
  map_ext :
    ∀ {X Y : ChainComplex (ModuleCat R) ℤ} (φ : X ⟶ Y)
      (hX : ∀ i : ℤ, Module.Free R (X.X i))
      (hY : ∀ i : ℤ, Module.Free R (Y.X i))
      (M : ModuleCat R),
      (map φ hX hY M).τ₁ = universalCoefficientCohomologyChainMapExtMap φ M n
  map_hom :
    ∀ {X Y : ChainComplex (ModuleCat R) ℤ} (φ : X ⟶ Y)
      (hX : ∀ i : ℤ, Module.Free R (X.X i))
      (hY : ∀ i : ℤ, Module.Free R (Y.X i))
      (M : ModuleCat R),
      (map φ hX hY M).τ₃ = universalCoefficientCohomologyChainMapHomMap φ M n
  map_natural :
    ∀ {X Y : ChainComplex (ModuleCat R) ℤ} (φ : X ⟶ Y)
      (hX : ∀ i : ℤ, Module.Free R (X.X i))
      (hY : ∀ i : ℤ, Module.Free R (Y.X i))
      {M N : ModuleCat R} (f : M ⟶ N),
      UniversalCoefficientCohomologyNaturality.map (seq Y hY) f ≫ map φ hX hY N =
        map φ hX hY M ≫ UniversalCoefficientCohomologyNaturality.map (seq X hX) f
  map_id :
    ∀ (X : ChainComplex (ModuleCat R) ℤ) (hX : ∀ i : ℤ, Module.Free R (X.X i))
      (M : ModuleCat R),
      map (𝟙 X) hX hX M = 𝟙 (((seq X hX) M).toShortComplex)
  map_comp :
    ∀ {X Y Z : ChainComplex (ModuleCat R) ℤ} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
      (hX : ∀ i : ℤ, Module.Free R (X.X i))
      (hY : ∀ i : ℤ, Module.Free R (Y.X i))
      (hZ : ∀ i : ℤ, Module.Free R (Z.X i))
      (M : ModuleCat R),
      map (φ ≫ ψ) hX hZ M = map ψ hY hZ M ≫ map φ hX hY M

/-- Remark 17.4.4 (1). For the homological universal coefficient exact sequence, one may choose
the coefficient-natural sequences and chain-map morphisms of short complexes so that the tensor
and `Tor` components are the canonical chain-map-induced morphisms; together with
`UniversalCoefficientHomologyNaturality`, this yields the source's bifunctoriality statement. -/
theorem universalCoefficientHomologyBifunctorial
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ) :
    ∃ seq
        : ∀ (X : ChainComplex (ModuleCat R) ℕ),
            (∀ i : ℕ, Module.Flat R (X.X i)) →
              UniversalCoefficientHomologyNaturality R X n,
      ∃ map
        : ∀ {X Y : ChainComplex (ModuleCat R) ℕ} (φ : X ⟶ Y)
            (hX : ∀ i : ℕ, Module.Flat R (X.X i))
            (hY : ∀ i : ℕ, Module.Flat R (Y.X i))
            (M : ModuleCat R),
            ((seq X hX) M).toShortComplex ⟶ ((seq Y hY) M).toShortComplex,
          UniversalCoefficientHomologyChainMapFunctorial R n seq map := sorry

/-- Remark 17.4.4 (2). For the cohomological universal coefficient exact sequence, one may choose
the coefficient-natural sequences and chain-map morphisms of short complexes so that the `Ext¹`
and `Hom` components are the canonical chain-map-induced morphisms; together with
`UniversalCoefficientCohomologyNaturality`, this yields the source's bifunctoriality statement. -/
theorem universalCoefficientCohomologyBifunctorial
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℤ) :
    ∃ seq
        : ∀ (X : ChainComplex (ModuleCat R) ℤ),
            (∀ i : ℤ, Module.Free R (X.X i)) →
              UniversalCoefficientCohomologyNaturality R X n,
      ∃ map
        : ∀ {X Y : ChainComplex (ModuleCat R) ℤ} (φ : X ⟶ Y)
            (hX : ∀ i : ℤ, Module.Free R (X.X i))
            (hY : ∀ i : ℤ, Module.Free R (Y.X i))
            (M : ModuleCat R),
            ((seq Y hY) M).toShortComplex ⟶ ((seq X hX) M).toShortComplex,
          UniversalCoefficientCohomologyChainMapFunctorial R n seq map := sorry
