import stacks_project.Chap20.Lemma_20_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : RingedSpace.{u}}

/-- The source object `Lg^* Rf_* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeSource (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj K)

/-- The target object `R(f')_* L(g')^* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeTarget (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (moduleDerivedPushforward f').obj ((modulePullbackDerived g').obj K)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if,
after transposing along `L(f')^* ⊣ R(f')_*`, it is the pullback along `L(g')^*` of the counit
`Lf^* Rf_* K ⟶ K`, transported across the chosen comparison isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
def IsUnboundedDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [(modulePullback f).Additive]
    [(modulePullback f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adjf : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adjf' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (K : DerivedCategory (RingedSpace.Modules X))
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  ((adjf'.homEquiv (derivedBaseChangeSource f g K) ((modulePullbackDerived g').obj K)).symm τ) =
    (hpull.app ((moduleDerivedPushforward f).obj K)).hom ≫
      (modulePullbackDerived g').map (adjf.counit.app K)

-- Proof sketch: use the derived adjunction for `f'` to identify morphisms
-- `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` with morphisms
-- `L(f')^* Lg^* Rf_* K ⟶ L(g')^* K`. The latter is obtained by first transporting along the
-- chosen comparison isomorphism `hpull`, then applying `L(g')^*` to the counit
-- `Lf^* Rf_* K ⟶ K`.
/-- Remark 20.28.3: for morphisms of ringed spaces
`g' : X' ⟶ X`, `f' : X' ⟶ S'`, `f : X ⟶ S`, and `g : S' ⟶ S`, once the unbounded derived
pullbacks and pushforwards are chosen together with adjunctions
`Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, and once a comparison isomorphism
`L(f')^* \circ Lg^* \cong L(g')^* \circ Lf^*` is fixed, every object
`K ∈ D(\mathcal O_X)` admits a base-change morphism
`Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` whose adjoint is the composite
`L(f')^* Lg^* Rf_* K \to L(g')^* Lf^* Rf_* K \to L(g')^* K`
described in the remark. -/
theorem exists_unbounded_derived_baseChange_map
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(modulePullback g').Additive]
    [(modulePushforward f').Additive]
    [(modulePushforward f).Additive]
    [(modulePullback g).Additive]
    [(modulePullback f).Additive]
    [(modulePullback f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f')
      (HomologicalComplex.quasiIso (RingedSpace.Modules X') (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
    (adjf : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adjf' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (K : DerivedCategory (RingedSpace.Modules X)) :
    ∃ τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K,
      IsUnboundedDerivedBaseChangeMap g' f' f g hpull adjf adjf' K τ := sorry

end AlgebraicGeometry.RingedSpace
