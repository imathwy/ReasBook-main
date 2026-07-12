import Mathlib
import StacksProject_2024.Chap29.Lemma_29_5_3
import StacksProject_2024.Chap30.Lemma_30_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.Scheme.Modules`,
-- `Module.support_of_exact`, and `CategoryTheory.ObjectProperty.IsSerreClass`; local Chapter
-- 29/30 precedent fixes the scheme-module support owner as `moduleSupport` and properness over a
-- base via the reduced closed subscheme `vanishingIdeal` attached to that support.

/-- The support of a scheme module is proper over a base morphism `f : X ⟶ S`, represented by the
properness of the reduced closed subscheme attached to `moduleSupport`. -/
class HasProperSupportOver {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) : Prop where
  /-- The module support is closed. -/
  isClosed_moduleSupport : IsClosed (moduleSupport ℱ)
  /-- The reduced closed subscheme supported on `moduleSupport ℱ` is proper over the base. -/
  isProper_moduleSupport :
    IsProper ((vanishingIdeal
      (⟨moduleSupport ℱ, isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X)).subschemeι ≫ f)

/-- A finite type quasi-coherent module whose canonical closed support is proper has proper
support over the base. -/
instance instHasProperSupportOverOfIsProper
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [IsProper ((vanishingIdeal
      (⟨moduleSupport ℱ, Scheme.Modules.isClosed_moduleSupport ℱ⟩ :
        TopologicalSpace.Closeds X)).subschemeι ≫ f)] :
    HasProperSupportOver f ℱ := sorry

/-- The defining properness statement carried by `HasProperSupportOver`. -/
theorem hasProperSupportOver_isProper
    {X S : Scheme.{u}} {f : X ⟶ S} {ℱ : X.Modules} [h : HasProperSupportOver f ℱ] :
    IsProper ((vanishingIdeal
      (⟨moduleSupport ℱ, h.isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X)).subschemeι ≫ f) := sorry

/-- Lemma 30.26.9 (1): if `f : X ⟶ S` is locally of finite type and two finite type
quasi-coherent `\mathcal O_X`-modules have support proper over `S`, then their direct sum has
support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_biprod_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢] :
    HasProperSupportOver f (ℱ ⊞ 𝒢) := sorry

/-- Lemma 30.26.9 (2): if `f : X ⟶ S` is locally of finite type and `\mathcal F`,
`\mathcal G` are finite type quasi-coherent modules with support proper over `S`, then every
extension of `\mathcal G` by `\mathcal F` has support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_extension_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 ℰ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (ι : ℱ ⟶ ℰ) (π : ℰ ⟶ 𝒢) (w : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π w).ShortExact) :
    HasProperSupportOver f ℰ := sorry

/-- Lemma 30.26.9 (3): if `f : X ⟶ S` is locally of finite type and `\mathcal F`,
`\mathcal G` are finite type quasi-coherent modules with support proper over `S`, then the image
of any map `u : \mathcal F ⟶ \mathcal G` has support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_image_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (Abelian.image u) := sorry

/-- Lemma 30.26.9 (4): if `f : X ⟶ S` is locally of finite type and `\mathcal F`,
`\mathcal G` are finite type quasi-coherent modules with support proper over `S`, then the
cokernel of any map `u : \mathcal F ⟶ \mathcal G` has support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_cokernel_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (cokernel u) := sorry

/-- Lemma 30.26.9 (5): if `f : X ⟶ S` is locally of finite type and `\mathcal F`,
`\mathcal G` are finite type quasi-coherent modules with support proper over `S`, then every
quasi-coherent quotient of `\mathcal F` has support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_quotient_left_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 Q : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent] [Q.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (q : ℱ ⟶ Q) [Epi q] :
    HasProperSupportOver f Q := sorry

/-- Lemma 30.26.9 (6): if `f : X ⟶ S` is locally of finite type and `\mathcal F`,
`\mathcal G` are finite type quasi-coherent modules with support proper over `S`, then every
quasi-coherent quotient of `\mathcal G` has support proper over `S`. -/
@[stacks 0CYU]
theorem moduleSupport_quotient_right_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 Q : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent] [Q.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (q : 𝒢 ⟶ Q) [Epi q] :
    HasProperSupportOver f Q := sorry

/-- Lemma 30.26.9 (7): if `S` is locally Noetherian, then the coherent
`\mathcal O_X`-modules whose support is proper over `S` form a Serre subcategory of the abelian
category of coherent `\mathcal O_X`-modules. -/
@[stacks 0CYU]
theorem coherent_hasProperSupportOver_isSerreClass
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
        ObjectProperty (RingedSpace.Coh X.toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme.Modules
