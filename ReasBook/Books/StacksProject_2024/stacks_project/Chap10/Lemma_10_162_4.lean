import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_162_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_161_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: write the essentially finite type `R`-algebra `S` as a localization of a finite
-- type `R`-algebra `A`. The finite type case is immediate from the definition of
-- `UniversallyJapaneseRing`, since any finite type domain over `A` is also finite type over `R`.
-- Then apply the localization stability of the `N-2` property from Lemma `10.161.3` to conclude
-- that finite type domain algebras over `S` are Japanese.
/-- Lemma 10.162.4: if `R` is universally Japanese, then any `R`-algebra essentially of finite
type is universally Japanese. -/
theorem universallyJapaneseRing_of_essFiniteType [UniversallyJapaneseRing.{u, v} R]
    [Algebra.EssFiniteType R S] : UniversallyJapaneseRing.{v, v} S := by
  let A := Algebra.EssFiniteType.subalgebra R S
  letI : Algebra R A := A.algebra
  refine
    { finiteType_algebra_isN2Ring := fun {T} [CommRing T] [Algebra S T] [Algebra.FiniteType S T]
        [IsDomain T] ↦ ?_ }
  letI : Algebra A S := inferInstance
  letI : Algebra.EssFiniteType A S :=
    Algebra.EssFiniteType.of_isLocalization S (Algebra.EssFiniteType.submonoid R S)
  letI : Algebra A T := inferInstance
  letI : IsScalarTower A S T := inferInstance
  letI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.comp A S T
  let T₀ := Algebra.EssFiniteType.subalgebra A T
  letI : Algebra A T₀ := T₀.algebra
  letI : Algebra R T₀ := (RingHom.comp (algebraMap A T₀) (algebraMap R A)).toAlgebra
  have hRT₀ : (algebraMap R T₀).FiniteType := by
    change (RingHom.comp (algebraMap A T₀) (algebraMap R A)).FiniteType
    exact RingHom.FiniteType.comp
      (RingHom.finiteType_algebraMap.mpr inferInstance)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType R T₀ := RingHom.finiteType_algebraMap.mp hRT₀
  let hR : UniversallyJapaneseRing.{u, v} R := inferInstance
  have hN2 : IsN2Ring T₀ := hR.finiteType_algebra_isN2Ring
  letI : IsN2Ring T₀ := hN2
  letI : Algebra T₀ T := inferInstance
  simpa [T₀] using isN2Ring_of_isLocalization (Algebra.EssFiniteType.submonoid A T)

end
