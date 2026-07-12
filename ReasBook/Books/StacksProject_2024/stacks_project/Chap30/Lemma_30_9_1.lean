import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Definition_17_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the sheaf owners
-- `SheafOfModules.IsFinitePresentation`, `SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`,
-- and `SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`. Local Chapter 28 precedent
-- records affine-local module conditions on a quasi-coherent sheaf through finiteness of affine
-- section modules on all affine opens or on an affine open cover, rather than by introducing a
-- separate presentation wrapper.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/-- Lemma 30.9.1 (1): on a locally Noetherian scheme `X`, an `\mathcal O_X`-module `ℱ` is
coherent if and only if it is quasi-coherent and of finite type. -/
@[stacks 01XZ]
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔ ℱ.IsQuasicoherent ∧ ℱ.IsFiniteType := sorry

/-- Lemma 30.9.1 (2): on a locally Noetherian scheme `X`, an `\mathcal O_X`-module `ℱ` is
coherent if and only if it is of finite presentation. -/
@[stacks 01XZ]
theorem isCoherent_iff_isFinitePresentation
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation := sorry

/-- A coherent module on a locally Noetherian scheme is finite presentation. -/
instance instIsFinitePresentationOfIsCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ℱ.IsFinitePresentation :=
  (isCoherent_iff_isFinitePresentation ℱ).mp inferInstance

/-- A coherent module on a locally Noetherian scheme is quasi-coherent. -/
instance instIsQuasicoherentOfIsCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ℱ.IsQuasicoherent := by
  let _ : ℱ.IsFinitePresentation := instIsFinitePresentationOfIsCoherent ℱ
  infer_instance

/-- Lemma 30.9.1 (3): on a locally Noetherian scheme `X`, an `\mathcal O_X`-module `ℱ` is
coherent if and only if it is quasi-coherent and its affine-open section module `Γ(U, ℱ)` is
finite over `Γ(X, U)` for every affine open `U ⊆ X`. This is the project-level encoding of the
textbook clause that on every affine open `U = Spec(A)` the restriction `ℱ|_U` is `\widetilde M`
for a finite `A`-module `M`. -/
@[stacks 01XZ]
theorem isCoherent_iff_isQuasicoherent_and_forall_affineOpen_finite_sections
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(ℱ, U) := sorry

/-- Lemma 30.9.1 (4): on a locally Noetherian scheme `X`, an `\mathcal O_X`-module `ℱ` is
coherent if and only if it is quasi-coherent and there exists an affine open covering of `X` on
which every section module is finite over the corresponding affine coordinate ring. This is the
project-level encoding of the textbook affine-cover presentation criterion. -/
@[stacks 01XZ]
theorem isCoherent_iff_isQuasicoherent_and_exists_affineOpenCover_finite_sections
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            Module.Finite
              Γ(X, ((𝒰.openCover.f i).opensRange))
              Γ(ℱ, ((𝒰.openCover.f i).opensRange)) := sorry

/-- Lemma 30.9.1 (5): the structure sheaf of a locally Noetherian scheme is coherent. -/
@[stacks 01XZ]
theorem structureSheaf_isCoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent := sorry

/-- Lemma 30.9.1 (6): any invertible `\mathcal O_X`-module on a locally Noetherian scheme is
coherent. -/
@[stacks 01XZ]
theorem isCoherent_of_isInvertible
    [MonoidalCategory X.Modules] (ℒ : X.Modules) [IsInvertibleX ℒ] :
    ℒ.IsCoherent := sorry

/-- Lemma 30.9.1 (7): any finite locally free `\mathcal O_X`-module on a locally Noetherian
scheme is coherent. -/
@[stacks 01XZ]
theorem isCoherent_of_isFiniteLocallyFree
    (ℱ : X.Modules) [SheafOfModules.IsFiniteLocallyFree ℱ] :
    ℱ.IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
