import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Types.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/- Domain-style sampling for 18.40.2.1:
- primary domain: sheafification and equalizers in the category of set-valued sheaves on a site,
  together with the underlying set-valued sheaf of a sheaf of commutative rings;
- sampled owner declarations:
  `Sheaf.terminal`,
  `presheafToSheaf`,
  `sheafCompose`,
  `sheafificationAdjunction`;
- best owner abstraction: the sheafification adjunction
  `sheafificationAdjunction J (Type (max u v))`, with the terminal sheaf and equalizer in
  `Sheaf J (Type (max u v))`;
- primitive data: the zero and one sections
  `* ⟶ (sheafCompose J (forget CommRingCat)).obj 𝒪`;
- derived API: the equalizer of those two sections and the canonical map from the sheafification
  of the empty presheaf into that equalizer.

Source/core/bridge triage:
- `source-facing`: the sections `0, 1 : * ⟶ 𝒪` and the canonical map
  `∅^# ⟶ equalizer (0, 1)`;
- `core/canonical`: `Sheaf.terminal`, `presheafToSheaf`, `sheafCompose`,
  `sheafificationAdjunction`, and `equalizer`;
- `bridge/view`: the forgetful passage from `CommRingCat`-valued sheaves to `Type`-valued sheaves.

The previous local abbreviations for the terminal sheaf, empty sheafification, underlying
set-valued sheaf, and the universal map out of `∅^#` were exact-interface wrappers around these
owners, so they should not survive as parallel public API.
-/

/-- The zero section `0 : * ⟶ \mathcal O` of the underlying set-valued sheaf of a sheaf of
commutative rings. -/
def zeroSection :
    Sheaf.terminal J Types.isTerminalPUnit ⟶
      (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪 where
  hom :=
    { app := fun U _ ↦ (0 : 𝒪.obj.obj U)
      naturality := by
        intro X Y f
        funext x
        simpa using (RingHom.map_zero ((𝒪.obj.map f).hom)).symm }

/-- The unit section `1 : * ⟶ \mathcal O` of the underlying set-valued sheaf of a sheaf of
commutative rings. -/
def oneSection :
    Sheaf.terminal J Types.isTerminalPUnit ⟶
      (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪 where
  hom :=
    { app := fun U _ ↦ (1 : 𝒪.obj.obj U)
      naturality := by
        intro X Y f
        funext x
        simpa using (RingHom.map_one ((𝒪.obj.map f).hom)).symm }

local instance typeSheafHasFiniteLimits : HasFiniteLimits (Sheaf J (Type (max u v))) := by
  infer_instance

/-- 18.40.2.1: the canonical morphism `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to
\mathcal O)` obtained from the sheafification adjunction. -/
def oneNeverZeroEqualizerMap :
    (presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))) ⟶
      equalizer (zeroSection 𝒪) (oneSection 𝒪) :=
  (((sheafificationAdjunction J (Type (max u v))).homEquiv
      (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
      (equalizer (zeroSection 𝒪) (oneSection 𝒪))).symm <|
    initial.to ((sheafToPresheaf J (Type (max u v))).obj
      (equalizer (zeroSection 𝒪) (oneSection 𝒪))))

end CategoryTheory
