import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization

universe uA vA uB vB

namespace CategoryTheory.Functor

open Abelian Limits

/-- An exact functor between abelian categories is faithful if its kernel consists only of zero
objects. -/
theorem faithful_of_exact_of_kernel_le_isZero
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : F.kernel ≤ IsZero) :
    F.Faithful := by
  let hExact : ∀ S : ShortComplex C, S.Exact → (S.map F).Exact := fun _ hS ↦ hS.map F
  letI : F.PreservesMonomorphisms := preservesMonomorphisms_of_map_exact F hExact
  letI : F.PreservesEpimorphisms := preservesEpimorphisms_of_map_exact F hExact
  letI : F.Additive := additive_of_preserves_binary_products F
  refine ⟨fun {X Y} f g hfg ↦ ?_⟩
  apply sub_eq_zero.mp
  have hmap : F.map (f - g) = 0 := by
    simp [map_sub, hfg]
  have hι :
      F.map (Abelian.image.ι (f - g)) = 0 := by
    apply zero_of_epi_comp (F.map (Abelian.factorThruImage (f - g)))
    rw [← F.map_comp, Abelian.image.fac]
    exact hmap
  have himageF : IsZero (F.obj (Abelian.image (f - g))) :=
    IsZero.of_mono_eq_zero (F.map (Abelian.image.ι (f - g))) hι
  have himage : IsZero (Abelian.image (f - g)) := hF _ himageF
  have hzero : Abelian.image.ι (f - g) = 0 := himage.eq_of_src _ _
  calc
    f - g = Abelian.factorThruImage (f - g) ≫ Abelian.image.ι (f - g) := by
      symm
      exact Abelian.image.fac (f - g)
    _ = 0 := by simp [hzero]

end CategoryTheory.Functor

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

noncomputable section

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

-- Proof sketch: if the induced functor is faithful, then any object annihilated by `G` has zero
-- identity in the Serre quotient, hence belongs to `P`. Conversely, if `P = G.obj.kernel`, then
-- a morphism in the quotient mapped to zero has image object in the kernel of `G`, hence in `P`,
-- so the morphism itself is zero.
/-- Lemma 12.10.7: let `G : A ⥤ₑ B` be an exact functor between abelian categories, and let `P`
be a Serre subcategory of `A` contained in the kernel of `G`. Then `P` equals the kernel of `G`
if and only if the induced functor from the Serre quotient `A/P` to `B` is faithful. -/
@[stacks 06XK]
theorem kernel_eq_iff_inducedFunctorToSerreQuotient_faithful
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    P = G.obj.kernel ↔
      (lift G.obj ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker) Q).Faithful := by
  let hG : P.isoModSerre.IsInvertedBy G.obj := (P.isoModSerre_isInvertedBy_iff G.obj).2 hPker
  let H := lift G.obj hG Q
  change P = G.obj.kernel ↔ H.Faithful
  have hHexact : exactFunctor _ _ H := by
    rw [← exactFunctor_comp_iff Q P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac G.obj hG Q).symm G.property
  letI : PreservesFiniteLimits H := (exactFunctor_iff H).1 hHexact |>.1
  letI : PreservesFiniteColimits H := (exactFunctor_iff H).1 hHexact |>.2
  constructor
  · intro hker
    have := Localization.essSurj (P.isoModSerre.Q) P.isoModSerre
    exact Functor.faithful_of_exact_of_kernel_le_isZero H <| show H.kernel ≤ IsZero from
      fun Y hY ↦ by
        have hpre :
            IsZero (H.obj ((P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage Y))) := by
          simpa using ((H.mapIso ((P.isoModSerre.Q).objObjPreimageIso Y)).isZero_iff).2 hY
        have hkernel :
            G.obj.kernel ((P.isoModSerre.Q).objPreimage Y) := by
          simpa using
            ((Localization.fac G.obj hG Q).app ((P.isoModSerre.Q).objPreimage Y)).isZero_iff.1 hpre
        have hPpre : P ((P.isoModSerre.Q).objPreimage Y) := by
          simpa [hker] using hkernel
        have hQpre : IsZero ((P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage Y)) :=
          (isZero_obj_iff Q P _).2 hPpre
        exact (((P.isoModSerre.Q).objObjPreimageIso Y).isZero_iff).1 hQpre
  · intro hfaithful
    ext X
    constructor
    · exact hPker X
    · intro hkernel
      have hQX :
          IsZero (H.obj ((P.isoModSerre.Q).obj X)) := by
        simpa using ((Localization.fac G.obj hG Q).app X).isZero_iff.2 hkernel
      have hQid : 𝟙 ((P.isoModSerre.Q).obj X) = 0 := by
        apply H.zero_of_map_zero
        simpa [IsZero.iff_id_eq_zero] using hQX
      exact (isZero_obj_iff Q P X).1 <| (IsZero.iff_id_eq_zero _).2 hQid

end

end _root_.CategoryTheory.ObjectProperty
