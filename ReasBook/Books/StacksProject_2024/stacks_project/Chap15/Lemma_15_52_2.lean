import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_105_5
import StacksProject_2024.Chap15.Definition_15_52_1
import StacksProject_2024.Chap15.Proposition_15_48_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable (R : Type u) [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

private theorem finiteType_isJ2Ring [IsJ2Ring R] :
    IsJ2Ring S :=
  (isJ2Ring_of_finiteType R : IsJ2Ring S)

/-- Helper for Lemma 15.52.2: essentially finite type algebras over a `G`-ring are `G`-rings. -/
private theorem essFiniteType_isGRing {T : Type w} [CommRing T] [Algebra R T]
    [Algebra.EssFiniteType R T] [IsGRing R] :
    IsGRing T := by
  sorry

private theorem essFiniteType_universallyCatenaryRing {T : Type w} [CommRing T] [Algebra R T]
    [UniversallyCatenaryRing R] [Algebra.EssFiniteType R T] :
    UniversallyCatenaryRing T :=
  (universallyCatenaryRing_of_essFiniteType R : UniversallyCatenaryRing T)

/- Domain-style sampling:
- primary domain: commutative algebra of quasi-excellent and excellent rings under localization of
  finite type algebras;
- sampled owner declarations:
  `IsQuasiExcellentRing`,
  `IsExcellentRing`,
  `IsGRing`,
  `IsJ2Ring`,
  `isJ2Ring_of_finiteType`,
  `universallyCatenaryRing_of_essFiniteType`;
- best owner abstraction: the source-facing statements here should remain about quasi-excellent and
  excellent rings for an arbitrary localization target `T` with `[IsLocalization M T]`, while
  their proof data is derived from the upstream owner chain
  `IsGRing`/`IsJ2Ring`/`UniversallyCatenaryRing` together with the canonical essential-finite-type
  localization bridge `Algebra.EssFiniteType.of_isLocalization`;
- primitive data: the finite type `R`-algebra `S`, the localization submonoid `M`, and the source
  owner assumptions `[IsQuasiExcellentRing R]` or `[IsExcellentRing R]`, plus the owner witness
  `[IsLocalization M T]`;
- derived API: the localized owners `IsQuasiExcellentRing T` and `IsExcellentRing T`; the
  concrete ring `Localization M` is only the canonical specialization.

Source/core/bridge triage:
- `source-facing`: the two localization permanence statements below;
- `core/canonical`: `IsQuasiExcellentRing`, `IsExcellentRing`, and their component owners;
- `bridge/view`: `Algebra.EssFiniteType.of_isLocalization` and
  `universallyCatenaryRing_of_essFiniteType`.
-/

-- Proof sketch: an arbitrary localization target `T` of `S` is essentially of finite type over
-- `R`, so Proposition `15.50.10` gives the `G`-ring condition. The finite type `R`-algebra `S`
-- is `J-2` by Proposition `15.48.7`, and `J-2` is preserved by localization. Combining these
-- two stability statements yields quasi-excellence of `T`.
/-- Lemma 15.52.2 (1): if `R` is quasi-excellent and `S` is a finite type `R`-algebra, then any
localization `T` of `S` is quasi-excellent. The textbook ring `Localization M` is the canonical
special case. -/
theorem isQuasiExcellentRing_localization_of_finiteType
    (M : Submonoid S) {T : Type w} [CommRing T] [Algebra S T] [IsLocalization M T]
    [IsQuasiExcellentRing R] :
    IsQuasiExcellentRing T := by
  -- Build the canonical algebra tower so the localization target is essentially of finite type over
  -- the original base ring `R`.
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType S T := .of_isLocalization T M
  letI : Algebra.EssFiniteType R T := .comp R S T
  -- Route correction: use Proposition `15.50.10` exactly as in the source to transfer the
  -- `G`-ring condition along the essentially finite type map `R → T`.
  letI : IsGRing T := essFiniteType_isGRing R
  -- The finite type algebra `S` is `J-2`, and localization preserves the `J-2` property.
  letI : IsJ2Ring S := finiteType_isJ2Ring R
  letI : IsJ2Ring T := inferInstance
  exact IsQuasiExcellentRing.mk

-- Proof sketch: apply part `(1)` to get that the localization target `T` is quasi-excellent.
-- Since `T` is essentially of finite type over `R`, Lemma `10.105.5` gives that it is
-- universally catenary. These two facts are exactly the data of excellence.
/-- Lemma 15.52.2 (2): if `R` is excellent and `S` is a finite type `R`-algebra, then any
localization `T` of `S` is excellent. The textbook ring `Localization M` is the canonical
special case. -/
theorem isExcellentRing_localization_of_finiteType
    (M : Submonoid S) {T : Type w} [CommRing T] [Algebra S T] [IsLocalization M T]
    [IsExcellentRing R] :
    IsExcellentRing T := by
  -- As above, view the localization target as essentially of finite type over `R`.
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType S T := .of_isLocalization T M
  letI : Algebra.EssFiniteType R T := .comp R S T
  -- Part `(1)` gives quasi-excellence, while universal catenarity comes from essential finite type.
  letI : IsQuasiExcellentRing T :=
    (isQuasiExcellentRing_localization_of_finiteType R M : IsQuasiExcellentRing T)
  let hUC : UniversallyCatenaryRing T := essFiniteType_universallyCatenaryRing R
  letI : UniversallyCatenaryRing T := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end
