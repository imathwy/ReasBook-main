import Mathlib.Algebra.Group.TypeTags.Hom
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3

open CategoryTheory Limits
open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u v

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for `π_ n`,
-- Chapter 14 now exposes the named comparison owner `hurewiczComparison`, and Construction 14.1.3
-- supplies `basedReducedHomology H` with induced maps `basedHomologyReducedMap H`. This file
-- keeps the sphere-class formula as a bridge and exposes Definition 15.1.1 directly as the
-- canonical Hurewicz homomorphism on `π_ n(X)`.

/-- A reduced homology theory on based spaces supplies the canonical induced map on reduced
homology for every based map, invariant under based homotopy. -/
private class HasBasedReducedHomologyMaps
    (E : ℤ → (X : TopCat) → Set X → Type v) where
  /-- The map on reduced homology induced by a based map. -/
  reducedMap :
    ∀ {q : ℤ} {X Y : BasedSpace}, (X ⟶ Y) →
      reducedHomology E q X → reducedHomology E q Y
  /-- Based-homotopic maps induce the same value on each reduced-homology class. -/
  reducedMap_eq_of_basedHomotopy :
    ∀ {q : ℤ} {X Y : BasedSpace} {f g : X ⟶ Y},
      (basedHomotopySetoid X Y).r f g →
        ∀ x : reducedHomology E q X,
          reducedMap f x = reducedMap g x

/-- The canonical reduced-homology map induced by a based map. -/
private abbrev reducedHomologyMap [HasBasedReducedHomologyMaps E]
    {q : ℤ} {X Y : BasedSpace} (f : X ⟶ Y) :
    reducedHomology E q X → reducedHomology E q Y :=
  HasBasedReducedHomologyMaps.reducedMap f

/-- Based-homotopic maps induce the same value on each reduced-homology class. -/
private theorem reducedHomologyMap_eq_of_basedHomotopy
    (E : ℤ → (X : TopCat) → Set X → Type v)
    [HasBasedReducedHomologyMaps E]
    {q : ℤ} {X Y : BasedSpace} {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g)
    (x : reducedHomology E q X) :
    reducedHomologyMap f x = reducedHomologyMap g x := sorry

section

variable {π : Type u} [AddCommGroup π]

/-- A pair homology theory supplies the canonical induced map on based reduced homology; the
homotopy-invariance field is deferred to the proof stage. -/
private noncomputable instance pairHomologyTheoryHasBasedReducedHomologyMaps
    (H : PairHomologyTheory π) :
    HasBasedReducedHomologyMaps (pairHomologyGroup H) where
  reducedMap := fun {q} {X Y} f ↦ basedHomologyReducedMap H q f
  reducedMap_eq_of_basedHomotopy := sorry

/-- A chosen generator `i_n` of `H̃_n(S^n)`, packaged at the fixed degree `n`. -/
structure SphereHomologyGenerator
    (H : PairHomologyTheory π) (n : ℕ) where
  /-- The chosen class `i_n ∈ H̃_n(S^n)`. -/
  toReducedHomology : basedReducedHomology H (n : ℤ) (basedSphere n)
  /-- The chosen class generates `H̃_n(S^n)` additively. -/
  isGenerator :
    ∀ x : basedReducedHomology H (n : ℤ) (basedSphere n),
      ∃ m : ℤ, m • toReducedHomology = x

/-- A fixed-degree sphere generator can be used as its underlying reduced-homology class. -/
instance sphereHomologyGeneratorCoe
    (H : PairHomologyTheory π) (n : ℕ) :
    Coe (SphereHomologyGenerator H n)
      (basedReducedHomology H (n : ℤ) (basedSphere n)) where
  coe := SphereHomologyGenerator.toReducedHomology

/-- The packaged generator condition says every class in `H̃_n(S^n)` is an integer multiple of
the chosen class. -/
theorem SphereHomologyGenerator.exists_zsmul_eq
    {H : PairHomologyTheory π} {n : ℕ}
    (i_n : SphereHomologyGenerator H n)
    (x : basedReducedHomology H (n : ℤ) (basedSphere n)) :
    ∃ m : ℤ, m • i_n.toReducedHomology = x :=
  i_n.isGenerator x

variable (H : PairHomologyTheory π)

variable (n : ℕ) (X : BasedSpace)

/-- A chosen generator `i_n ∈ H̃_n(S^n)` yields the auxiliary sphere-class map
`basedHomotopyClasses (basedSphere n) X → basedReducedHomology H (n : ℤ) X`,
sending the class `[f]` of a based map `f : basedSphere n ⟶ X` to `f_*(i_n)`. -/
noncomputable def sphereClassHurewiczMap
    (n : ℕ) (i_n : SphereHomologyGenerator H n) (X : BasedSpace) :
    basedHomotopyClasses (basedSphere n) X → basedReducedHomology H (n : ℤ) X :=
  Quotient.lift
    (fun f : basedSphere n ⟶ X ↦ reducedHomologyMap f i_n.toReducedHomology)
    (fun _ _ hfg ↦
      reducedHomologyMap_eq_of_basedHomotopy (pairHomologyGroup H) hfg i_n.toReducedHomology)

/-- The helper `sphereClassHurewiczMap` is characterized by
`h([f]) = (basedHomologyReducedMap H (n : ℤ) f) i_n`, where `[f]` is the based homotopy class of
`f : basedSphere n ⟶ X`. -/
theorem sphereClassHurewiczMap_spec
    (n : ℕ) (i_n : SphereHomologyGenerator H n) (X : BasedSpace) (f : basedSphere n ⟶ X) :
    sphereClassHurewiczMap H n i_n X
      ((Quotient.mk (basedHomotopySetoid (basedSphere n) X) f) :
        basedHomotopyClasses (basedSphere n) X) =
      basedHomologyReducedMap H (n : ℤ) f i_n := sorry

/-- Definition 15.1.1. Relative to the named Chapter 14.3.3 comparison on `X`, the Hurewicz map
`π_ n(X) → H̃_n(X)` sends the homotopy class of `f : S^n ⟶ X` to `f_*(i_n)` for a chosen
generator `i_n ∈ H̃_n(S^n)`. -/
noncomputable def hurewiczMap
    (n : ℕ) (X : BasedSpace) [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n) :
    π_ n X.right (underTopBasepoint X) → basedReducedHomology H (n : ℤ) X :=
  fun a ↦ sphereClassHurewiczMap H n i_n X ((hurewiczComparison n X).toSphereClass a)

/-- The Hurewicz map carries the `π_ n(X)`-class represented by
`f : basedSphere n ⟶ X` to `f_*(i_n)`. -/
theorem hurewiczMap_spec
    (n : ℕ) (X : BasedSpace) [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n) (f : basedSphere n ⟶ X) :
    hurewiczMap H n X i_n
        ((hurewiczComparison n X).ofSphereClass
          ((Quotient.mk (basedHomotopySetoid (basedSphere n) X) f) :
            basedHomotopyClasses (basedSphere n) X)) =
      basedHomologyReducedMap H (n : ℤ) f i_n := sorry

/-- In positive degree, the Hurewicz map is viewed as an additive homomorphism on `π_ n(X)`. -/
noncomputable def hurewiczHomomorphism
    (n : ℕ) (X : BasedSpace) [Nonempty (Fin n)] [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n) :
    Additive (π_ n X.right (underTopBasepoint X)) →+ basedReducedHomology H (n : ℤ) X where
  toFun := fun a ↦ hurewiczMap H n X i_n a
  map_zero' := sorry
  map_add' := sorry

/-- The additive Hurewicz homomorphism has underlying function `hurewiczMap`. -/
theorem hurewiczHomomorphism_apply
    (n : ℕ) (X : BasedSpace) [Nonempty (Fin n)] [HasHurewiczComparison n X]
    (i_n : SphereHomologyGenerator H n)
    (a : Additive (π_ n X.right (underTopBasepoint X))) :
    hurewiczHomomorphism H n X i_n a = hurewiczMap H n X i_n a := sorry

end
