import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Tor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ModuleCat MonoidalCategory
open Functor.OplaxMonoidal

universe u

instance extendScalars_additive
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Additive where
  map_add := by
    intro X Y g h
    letI := f.toAlgebra
    change ModuleCat.ofHom ((g.hom + h.hom).baseChange S) =
      ModuleCat.ofHom (g.hom.baseChange S + h.hom.baseChange S)
    rw [LinearMap.baseChange_add]

/-
Domain triage:
- `source-facing`: `torBaseChangeHom` is the textbook flat base-change morphism
  `Tor_i^R(M, N) ⊗[R] S → Tor_i^S(M ⊗[R] S, N ⊗[R] S)`.
- `core/canonical`: the owner abstraction is the bifunctor `Tor (ModuleCat R) i`.
- `bridge/view`: the chain-level comparison is the oplax monoidal morphism
  `δ (ModuleCat.extendScalars f) M N`.

Primitive data are only the ring map, the flatness hypothesis, and the two modules. The
comparison map is derived from `Tor` and `extendScalars`; no public wrapper functors are kept.
-/

namespace ModuleCat

/-- The canonical comparison between extending scalars after tensoring with `M` and tensoring with
the extended module `M ⊗[R] S` after extending scalars. -/
noncomputable def extendScalarsTensorLeftNatIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat R) :
    tensorLeft M ⋙ extendScalars f ≅
      extendScalars f ⋙ tensorLeft ((extendScalars f).obj M) :=
  NatIso.ofComponents
    (fun X ↦ (Functor.Monoidal.μIso (extendScalars f) M X).symm)
    (by
      intro X Y g
      exact (Functor.OplaxMonoidal.δ_natural_right (extendScalars f) M g).symm)

end ModuleCat

private noncomputable def torBaseChangeSourceIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
        (((tensorLeft M ⋙ ModuleCat.extendScalars f).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  (ModuleCat.extendScalars f).mapIso ((projectiveResolution N).isoLeftDerivedObj (tensorLeft M) i) ≪≫
    (((((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (projectiveResolution N).complex).sc i).mapHomologyIso
      (ModuleCat.extendScalars f)).symm

private noncomputable def torBaseChangeTargetIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      (((ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
      ((ModuleCat.extendScalars f).obj N)) :=
  letI : (ModuleCat.extendScalars f).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj f)
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  ((ModuleCat.extendScalars f).mapProjectiveResolution (projectiveResolution N)).isoLeftDerivedObj
    (tensorLeft ((ModuleCat.extendScalars f).obj M)) i |>.symm

/-- The canonical flat base-change morphism
`Tor_i^R(M, N) ⊗[R] S → Tor_i^S(M ⊗[R] S, N ⊗[R] S)`. -/
noncomputable def torBaseChangeHom
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ⟶
      (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
      ((ModuleCat.extendScalars f).obj N)) :=
  (torBaseChangeSourceIso f hf M N i).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).map
      ((NatTrans.mapHomologicalComplex
        (ModuleCat.extendScalarsTensorLeftNatIso f M).hom (ComplexShape.down ℕ)).app
          (projectiveResolution N).complex) ≫
    (torBaseChangeTargetIso f hf M N i).hom

/-- Helper for Lemma 10.76.1: applying homology to the chain-level tensor/base-change comparison
produces the middle isomorphism in the `Tor` base-change map. -/
private noncomputable def torBaseChangeMiddleIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M N : ModuleCat R) (i : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      ((Functor.mapHomologicalComplex (tensorLeft M ⋙ ModuleCat.extendScalars f)
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M))
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  -- Apply homology to the chain-level natural isomorphism commuting tensor and scalar extension.
  (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).mapIso
    ((NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsTensorLeftNatIso f M) (ComplexShape.down ℕ)).app
        (projectiveResolution N).complex)

/-- Helper for Lemma 10.76.1: the flat base-change morphism on `Tor` is the hom of a composite
of the source, middle, and target comparison isomorphisms. -/
private noncomputable def torBaseChangeIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ≅
      (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N)) :=
  -- Compose the two resolution identifications with the homology comparison in the middle.
  torBaseChangeSourceIso f hf M N i ≪≫
    torBaseChangeMiddleIso f M N i ≪≫
      torBaseChangeTargetIso f hf M N i

/-- Lemma 10.76.1: for a flat ring map `f : R →+* S` and `R`-modules `M` and `N`, the canonical
base-change map on `Tor_i` is an isomorphism for every `i`. -/
-- Proof sketch: compute `Tor` from a projective resolution, apply extension of scalars termwise,
-- and use flatness of `f` to preserve the exactness of that resolution after tensoring with `S`.
theorem flat_tor_base_change_map_isIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) :
    IsIso (torBaseChangeHom f hf (ModuleCat.of R M) (ModuleCat.of R N) i) := by
  -- Package the source proof's three comparison steps into a single isomorphism.
  have hcomp :
      torBaseChangeHom f hf (ModuleCat.of R M) (ModuleCat.of R N) i =
        (torBaseChangeIso f hf (ModuleCat.of R M) (ModuleCat.of R N) i).hom := by
    -- Unfold both constructions to identify the textbook map with the composite iso morphism.
    dsimp [torBaseChangeHom, torBaseChangeIso, torBaseChangeMiddleIso, NatIso.mapHomologicalComplex]
  -- After rewriting, the goal is the standard fact that the hom of an isomorphism is invertible.
  rw [hcomp]
  exact (torBaseChangeIso f hf (ModuleCat.of R M) (ModuleCat.of R N) i).isIso_hom
