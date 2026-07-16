import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w

section

/- Domain-style sampling for Situation 16.4.1:
- primary domain: extensions of discrete valuation rings and the ramification condition `e = 1`;
- sampled owner declarations:
  `Ideal.ramificationIdx`,
  `IsExtensionOfDiscreteValuationRings`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`;
- best owner abstraction: the extension data are owned by
  `IsExtensionOfDiscreteValuationRings`, while the `e = 1` hypothesis is the derived predicate
  `WeaklyUnramified`, itself defined through `Ideal.ramificationIdx` on the maximal ideals;
- primitive-vs-derived split:
  primitive data: the DVR structures on `R` and `L`, the algebra structure `R → L`, and the owner
  instance `IsExtensionOfDiscreteValuationRings R L`;
  derived API: the equality
  `Ideal.map (algebraMap R L) (maximalIdeal R) = maximalIdeal L`, the inclusion of the image of
  `maximalIdeal R` into the center ideal `𝔭 ⊆ A`, and the corresponding prime-spectrum points
  `qPoint`, `pPoint`, all obtained canonically from the owner declarations.

Source/core/bridge triage:
- `source-facing`: the packaged factorization situation with the hypothesis that the DVR extension
  has ramification index `1`;
- `core/canonical`: `Ideal.ramificationIdx`, `IsExtensionOfDiscreteValuationRings`, and
  `WeaklyUnramified`;
- `bridge/view`: the derived maximal-ideal equality used in the local factorization geometry.
-/

/-- Situation 16.4.1: discrete valuation rings `R` and `Λ` with ramification index `1`, an
`R`-algebra `A` that is flat and of finite type, and an `R`-algebra map `φ : A → Λ`; the
associated ideals are `𝔮 = ker(φ)` and `𝔭 = φ⁻¹(\mathfrak m_Λ)`. -/
structure RamificationOneDvrFactorizationSituation where
  /-- The source discrete valuation ring `R`. -/
  R : Type u
  /-- The target discrete valuation ring `Λ`. -/
  L : Type v
  /-- The intermediate `R`-algebra `A`. -/
  A : Type w
  /-- The commutative ring structure on `R`. -/
  instCommRingR : CommRing R
  /-- The source ring `R` is an integral domain. -/
  instIsDomainR : IsDomain R
  /-- The source ring `R` is a discrete valuation ring. -/
  instIsDiscreteValuationRingR : IsDiscreteValuationRing R
  /-- The commutative ring structure on `Λ`. -/
  instCommRingL : CommRing L
  /-- The target ring `Λ` is an integral domain. -/
  instIsDomainL : IsDomain L
  /-- The target ring `Λ` is a discrete valuation ring. -/
  instIsDiscreteValuationRingL : IsDiscreteValuationRing L
  /-- The commutative ring structure on `A`. -/
  instCommRingA : CommRing A
  /-- The given ring map `R → Λ`, viewed as an `R`-algebra structure on `Λ`. -/
  instAlgebraRL : Algebra R L
  /-- The map `R → Λ` is an extension of discrete valuation rings. -/
  dvrExtension : IsExtensionOfDiscreteValuationRings R L
  /-- The extension `R ⊂ Λ` has ramification index `1`. -/
  weaklyUnramified : WeaklyUnramified R L
  /-- The given ring map `R → A`, viewed as an `R`-algebra structure on `A`. -/
  instAlgebraRA : Algebra R A
  /-- The factorization map `φ : A → Λ` over `R`. -/
  phi : A →ₐ[R] L
  /-- The `R`-algebra `A` is flat. -/
  flat_toA : Module.Flat R A
  /-- The `R`-algebra `A` is of finite type. -/
  finiteType_toA : Algebra.FiniteType R A

attribute [instance] RamificationOneDvrFactorizationSituation.instCommRingR
attribute [instance] RamificationOneDvrFactorizationSituation.instIsDomainR
attribute [instance] RamificationOneDvrFactorizationSituation.instIsDiscreteValuationRingR
attribute [instance] RamificationOneDvrFactorizationSituation.instCommRingL
attribute [instance] RamificationOneDvrFactorizationSituation.instIsDomainL
attribute [instance] RamificationOneDvrFactorizationSituation.instIsDiscreteValuationRingL
attribute [instance] RamificationOneDvrFactorizationSituation.instCommRingA
attribute [instance] RamificationOneDvrFactorizationSituation.instAlgebraRL
attribute [instance] RamificationOneDvrFactorizationSituation.dvrExtension
attribute [instance] RamificationOneDvrFactorizationSituation.weaklyUnramified
attribute [instance] RamificationOneDvrFactorizationSituation.instAlgebraRA
attribute [instance] RamificationOneDvrFactorizationSituation.flat_toA
attribute [instance] RamificationOneDvrFactorizationSituation.finiteType_toA

namespace RamificationOneDvrFactorizationSituation

/-- The factorization map `φ : A → Λ` endows `Λ` with its induced `A`-algebra structure. -/
noncomputable instance (S : RamificationOneDvrFactorizationSituation) : Algebra S.A S.L :=
  S.phi.toAlgebra

/-- The structure maps `R → A → Λ` in Situation `16.4.1` form a scalar tower. -/
instance (S : RamificationOneDvrFactorizationSituation) : IsScalarTower S.R S.A S.L :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (S.phi.commutes x).symm

/-- The ideal `𝔮 = ker(φ)` attached to the factorization situation. -/
def q (S : RamificationOneDvrFactorizationSituation) : Ideal S.A :=
  RingHom.ker S.phi

/-- The ideal `𝔭 = φ⁻¹(\mathfrak m_Λ)` attached to the factorization situation. -/
def p (S : RamificationOneDvrFactorizationSituation) : Ideal S.A :=
  Ideal.comap S.phi (maximalIdeal S.L)

/-- In Situation `16.4.1`, the weakly unramified hypothesis identifies the image of the maximal
ideal of `R` with the maximal ideal of `Λ`. -/
theorem map_maximalIdeal_eq (S : RamificationOneDvrFactorizationSituation) :
    Ideal.map (algebraMap S.R S.L) (maximalIdeal S.R) = maximalIdeal S.L := by
  have hmap :
      WeaklyUnramified S.R S.L ↔
        Ideal.map (algebraMap S.R S.L) (maximalIdeal S.R) = maximalIdeal S.L :=
    weaklyUnramified_iff_map_maximalIdeal S.R S.L
  exact hmap.mp inferInstance

/-- Membership in `S.q` is equivalent to vanishing under `φ`. -/
@[simp]
theorem mem_q_iff (S : RamificationOneDvrFactorizationSituation) {x : S.A} :
    x ∈ S.q ↔ S.phi x = 0 := by
  simp [q]

/-- Membership in `S.p` is equivalent to the image under `φ` lying in the maximal ideal of `Λ`. -/
@[simp]
theorem mem_p_iff (S : RamificationOneDvrFactorizationSituation) {x : S.A} :
    x ∈ S.p ↔ S.phi x ∈ maximalIdeal S.L := by
  simp [p]

/-- The image of `maximalIdeal R` in `A` is contained in the center ideal `𝔭`. -/
theorem map_maximalIdeal_le_p (S : RamificationOneDvrFactorizationSituation) :
    Ideal.map (algebraMap S.R S.A) (maximalIdeal S.R) ≤ S.p := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_p_iff]
  have hx' : algebraMap S.R S.L x ∈ Ideal.map (algebraMap S.R S.L) (maximalIdeal S.R) :=
    Ideal.mem_map_of_mem _ hx
  simpa [S.map_maximalIdeal_eq] using hx'

/-- The ideal `𝔮 = ker(φ)` is prime because `Λ` is a domain. -/
instance (S : RamificationOneDvrFactorizationSituation) : S.q.IsPrime := by
  simpa [q] using RingHom.ker_isPrime S.phi.toRingHom

/-- The ideal `𝔭 = φ⁻¹(\mathfrak m_Λ)` is prime as the inverse image of the maximal ideal of the
local ring `Λ`. -/
instance (S : RamificationOneDvrFactorizationSituation) : S.p.IsPrime := by
  dsimp [p]
  infer_instance

/-- The prime-spectrum point corresponding to `𝔮 = ker(φ)`. -/
abbrev qPoint (S : RamificationOneDvrFactorizationSituation) : PrimeSpectrum S.A :=
  ⟨S.q, inferInstance⟩

/-- The prime-spectrum point corresponding to `𝔭 = φ⁻¹(\mathfrak m_Λ)`. -/
abbrev pPoint (S : RamificationOneDvrFactorizationSituation) : PrimeSpectrum S.A :=
  ⟨S.p, inferInstance⟩

end RamificationOneDvrFactorizationSituation

end
