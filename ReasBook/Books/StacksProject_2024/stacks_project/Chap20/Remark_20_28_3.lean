import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Lemma_20_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X X' S S' : RingedSpace.{u}}

/-- The source object `Lg^* Rf_* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeSource (f : X ⟶ S) (g : S' ⟶ S)
    [(f _*).Additive]
    [(g^*).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (L(g)^*).obj ((R(f)_*).obj K)

/-- The target object `R(f')_* L(g')^* K` of the unbounded base-change map. -/
abbrev derivedBaseChangeTarget (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(g'^*).Additive]
    [(f' _*).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    (K : DerivedCategory (RingedSpace.Modules X)) : DerivedCategory (RingedSpace.Modules S') :=
  (R(f')_*).obj ((L(g')^*).obj K)

section UnboundedBaseChange

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
variable [(g'^*).Additive]
variable [(f' _*).Additive]
variable [(f _*).Additive]
variable [(g^*).Additive]
variable [(f^*).Additive]
variable [(f'^*).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]

/-- The adjoint-side morphism whose transpose is the unbounded derived base-change map. -/
def unboundedDerivedBaseChangeMapAdjoint
    (adjf : L(f)^* ⊣ R(f)_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    (L(f')^*).obj (derivedBaseChangeSource f g K) ⟶
      (L(g')^*).obj K :=
  hpull.hom.app ((R(f)_*).obj K) ≫
    (L(g')^*).map (adjf.counit.app K)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if,
after transposing along `L(f')^* ⊣ R(f')_*`, it is the pullback along `L(g')^*` of the counit
`Lf^* Rf_* K ⟶ K`, transported across the chosen comparison isomorphism
`L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*`. -/
def IsUnboundedDerivedBaseChangeMap
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X))
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  ((adjf'.homEquiv (derivedBaseChangeSource f g K) ((L(g')^*).obj K)).symm τ) =
    unboundedDerivedBaseChangeMapAdjoint g' f' f g adjf hpull K

-- Proof sketch: use the derived adjunction for `f'` to identify morphisms
-- `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` with morphisms
-- `L(f')^* Lg^* Rf_* K ⟶ L(g')^* K`. The latter is obtained by first transporting along the
-- chosen comparison isomorphism `hpull`, then applying `L(g')^*` to the counit
-- `Lf^* Rf_* K ⟶ K`.
/-- Remark 20.28.3: for morphisms of ringed spaces
`g' : X' ⟶ X`, `f' : X' ⟶ S'`, `f : X ⟶ S`, and `g : S' ⟶ S`, once the unbounded derived
pullbacks and pushforwards are chosen together with adjunctions
`Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, and once a comparison isomorphism
`L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*` is fixed, every object
`K : DerivedCategory (RingedSpace.Modules X)` has a canonical base-change morphism
`Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` whose mate is the composite
`L(f')^* Lg^* Rf_* K ⟶ L(g')^* Lf^* Rf_* K ⟶ L(g')^* K`
described in the remark. -/
@[stacks 08HY]
def unboundedDerivedBaseChangeMap
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K :=
  adjf'.homEquiv (derivedBaseChangeSource f g K) ((L(g')^*).obj K)
    (unboundedDerivedBaseChangeMapAdjoint g' f' f g adjf hpull K)

/-- The mate of `unboundedDerivedBaseChangeMap` is the pullback of the counit prescribed in
Remark 20.28.3. -/
@[simp] theorem unboundedDerivedBaseChangeMap_mate
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    ((adjf'.homEquiv (derivedBaseChangeSource f g K) ((L(g')^*).obj K)).symm
        (unboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K)) =
      unboundedDerivedBaseChangeMapAdjoint g' f' f g adjf hpull K := by
  simp [unboundedDerivedBaseChangeMap]

/-- Transposing `unboundedDerivedBaseChangeMap` across `L(f')^* ⊣ R(f')_*` recovers the pullback
of the counit prescribed in Remark 20.28.3. -/
theorem unboundedDerivedBaseChangeMap_spec
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsUnboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K
      (unboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K) := by
  simpa [IsUnboundedDerivedBaseChangeMap] using
    unboundedDerivedBaseChangeMap_mate g' f' f g adjf adjf' hpull K

/-- A morphism satisfying the defining mate formula of Remark 20.28.3 is the canonical
`unboundedDerivedBaseChangeMap`. -/
theorem eq_unboundedDerivedBaseChangeMap
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory (RingedSpace.Modules X))
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K)
    (hτ : IsUnboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K τ) :
    τ = unboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K := by
  rw [← (adjf'.homEquiv (derivedBaseChangeSource f g K) ((L(g')^*).obj K)).apply_symm_apply τ, hτ]
  rfl

end UnboundedBaseChange

end AlgebraicGeometry.RingedSpace
