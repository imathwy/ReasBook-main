import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

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
abbrev zeroSection (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶ (sheafCompose J (forget CommRingCat)).obj 𝒪 where
  hom :=
    { app := fun U _ ↦ (0 : 𝒪.obj.obj U)
      naturality := by
        intro X Y f
        funext x
        simp }

/-- The unit section `1 : * ⟶ \mathcal O` of the underlying set-valued sheaf of a sheaf of
commutative rings. -/
abbrev oneSection (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶ (sheafCompose J (forget CommRingCat)).obj 𝒪 where
  hom :=
    { app := fun U _ ↦ (1 : 𝒪.obj.obj U)
      naturality := by
        intro X Y f
        funext x
        simp }

/-- 18.40.2.1: the canonical morphism `\emptyset^\# \to \operatorname{Equalizer}(0,1 : * \to
\mathcal O)` obtained from the sheafification adjunction. -/
abbrev oneNeverZeroEqualizerMap (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))) ⟶
      equalizer (zeroSection 𝒪) (oneSection 𝒪) :=
  ((sheafificationAdjunction J (Type (max u v))).homEquiv _ _).symm (initial.to _)

/-- The labeled map is, by definition, the universal morphism from `\emptyset^\#` to the
equalizer of the zero and one sections. -/
theorem oneNeverZeroEqualizerMap_def (𝒪 : Sheaf J CommRingCat.{max u v}) :
    oneNeverZeroEqualizerMap 𝒪 =
      ((sheafificationAdjunction J (Type (max u v))).homEquiv _ _).symm (initial.to _) :=
  rfl

end CategoryTheory
