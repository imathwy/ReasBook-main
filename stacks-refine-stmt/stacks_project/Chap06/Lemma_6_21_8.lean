import Mathlib
import stacks_project.Chap06.Definition_6_21_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf
open scoped AlgebraicGeometry

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u v

/-
Domain-style sampling for Lemma 6.21.8:
- primary domain: sheaf pushforward along a continuous map and the pullback-pushforward adjunction
  on `TopCat.Sheaf`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.pushforward`,
  `CategoryTheory.CommSq`;
- owner abstraction: the canonical owner for an `f`-map is the Hom type
  `𝒢 ⟶ (pushforward (Type v) f).obj ℱ`, already fixed in `Definition_6_21_7`;
- primitive data: only the two-open-set family `η U V h`;
- derived API: the source/target `CommSq` naturality predicates, conversion to and from the
  canonical Hom type, the precomposition/postcomposition actions on compatible families, and the
  resulting equivalence with its naturality in both sheaf variables.

Source/core/bridge triage:
- `source-facing`: the Stacks-compatible family of maps `ξ_{U,V} : 𝒢(V) → ℱ(U)` for
  `U ⊆ f⁻¹(V)`;
- `core/canonical`: the sheaf pushforward owner `pushforward (Type v) f`;
- `bridge/view`: the equivalence between the compatible-family presentation and the canonical Hom
  type.

No upstream owner packages this two-open-set compatibility datum, so the bridge layer should remain
as a thin family type together with its compatibility predicates, not as a second bundled root API.
-/

/-- The explicit two-open-set family `ξ_{U,V} : 𝒢(V) → ℱ(U)` appearing in the fourth presentation
of Lemma 6.21.8, for opens `U ⊆ f⁻¹(V)`. Compatibility is recorded separately below. -/
abbrev ContinuousMapSheafMapFamily {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒢 : Y.Sheaf (Type v)) (ℱ : X.Sheaf (Type v)) : Type (max u v) :=
  ∀ (U : Opens X) (V : Opens Y) (_ : U ≤ (Opens.map f).obj V),
    (𝒢.presheaf.obj (op V) ⟶ ℱ.presheaf.obj (op U))

section

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
variable {𝒢 : Y.Sheaf (Type v)} {ℱ : X.Sheaf (Type v)}
variable {𝒢' : Y.Sheaf (Type v)} {ℱ' : X.Sheaf (Type v)}

namespace ContinuousMapSheafMapFamily

/-- Compatibility with restriction in the `X`-variable. -/
def SourceNatural (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  ∀ {U U' : Opens X} {V : Opens Y} (i : U' ⟶ U) (h : U ≤ (Opens.map f).obj V),
    CommSq (η U V h) (𝟙 _) (ℱ.presheaf.map i.op) (η U' V (i.le.trans h))

/-- Compatibility with restriction in the `Y`-variable. -/
def TargetNatural (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  ∀ {U : Opens X} {V V' : Opens Y} (j : V ⟶ V') (h : U ≤ (Opens.map f).obj V),
    CommSq (𝒢.presheaf.map j.op) (η U V' (h.trans ((Opens.map f).map j).le)) (η U V h) (𝟙 _)

/-- The full compatibility condition for the fourth Stacks-style presentation. -/
def Compatible (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  η.SourceNatural ∧ η.TargetNatural

/-- Precompose a two-open-set family with a sheaf morphism in the `Y`-variable. -/
def precomp (α : 𝒢' ⟶ 𝒢) (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    ContinuousMapSheafMapFamily f 𝒢' ℱ :=
  fun U V h ↦ α.1.app (op V) ≫ η U V h

/-- Postcompose a two-open-set family with a sheaf morphism in the `X`-variable. -/
def postcomp (β : ℱ ⟶ ℱ') (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    ContinuousMapSheafMapFamily f 𝒢 ℱ' :=
  fun U V h ↦ η U V h ≫ β.1.app (op U)

/-- Source-side naturality is preserved by precomposition in the `Y`-variable. -/
theorem SourceNatural.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.SourceNatural) (α : 𝒢' ⟶ 𝒢) : (precomp α η).SourceNatural :=
  sorry

/-- Target-side naturality is preserved by precomposition in the `Y`-variable. -/
theorem TargetNatural.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.TargetNatural) (α : 𝒢' ⟶ 𝒢) : (precomp α η).TargetNatural :=
  sorry

/-- Source-side naturality is preserved by postcomposition in the `X`-variable. -/
theorem SourceNatural.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.SourceNatural) (β : ℱ ⟶ ℱ') : (postcomp β η).SourceNatural :=
  sorry

/-- Target-side naturality is preserved by postcomposition in the `X`-variable. -/
theorem TargetNatural.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.TargetNatural) (β : ℱ ⟶ ℱ') : (postcomp β η).TargetNatural :=
  sorry

/-- Compatibility is preserved by precomposition in the `Y`-variable. -/
theorem Compatible.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.Compatible) (α : 𝒢' ⟶ 𝒢) : (precomp α η).Compatible :=
  ⟨SourceNatural.precomp hη.1 α, TargetNatural.precomp hη.2 α⟩

/-- Compatibility is preserved by postcomposition in the `X`-variable. -/
theorem Compatible.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.Compatible) (β : ℱ ⟶ ℱ') : (postcomp β η).Compatible :=
  ⟨SourceNatural.postcomp hη.1 β, TargetNatural.postcomp hη.2 β⟩

/-- Precomposition on compatible families in the source sheaf variable. -/
def precompCompatible (α : 𝒢' ⟶ 𝒢) :
    { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } →
      { η : ContinuousMapSheafMapFamily f 𝒢' ℱ // η.Compatible }
  | ⟨η, hη⟩ => ⟨precomp α η, hη.precomp α⟩

/-- Postcomposition on compatible families in the target sheaf variable. -/
def postcompCompatible (β : ℱ ⟶ ℱ') :
    { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } →
      { η : ContinuousMapSheafMapFamily f 𝒢 ℱ' // η.Compatible }
  | ⟨η, hη⟩ => ⟨postcomp β η, hη.postcomp β⟩

/-- The two-open-set family determined by an `f`-map of sheaves. -/
def ofHom (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) : ContinuousMapSheafMapFamily f 𝒢 ℱ :=
  fun _ V h ↦ ξ.1.app (op V) ≫ ℱ.presheaf.map (homOfLE h).op

/-- Converting a precomposition of sheaf maps to families matches family-level precomposition. -/
private theorem ofHom_precomp (α : 𝒢' ⟶ 𝒢) (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    ofHom (α ≫ ξ) = precomp α (ofHom ξ) :=
  sorry

/-- Converting a postcomposition of sheaf maps to families matches family-level postcomposition. -/
private theorem ofHom_postcomp (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) (β : ℱ ⟶ ℱ') :
    ofHom (ξ ≫ (pushforward (Type v) f).map β) = postcomp β (ofHom ξ) :=
  sorry

-- Proof sketch: expand both sides as iterated restriction maps in the presheaf `ℱ`; functoriality
-- of restrictions along inclusions of opens identifies the two composites.
/-- Restricting the collection attached to an `f`-map in the `X`-variable is compatible with the
restriction maps of `ℱ`. -/
private theorem ofHom_sourceNatural (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).SourceNatural :=
  sorry

-- Proof sketch: use the naturality of the underlying morphism `ξ : 𝒢 ⟶ f_* ℱ`; after evaluating
-- the naturality square on a section `s`, postcompose with the restriction map from `f⁻¹(V)` to
-- `U`.
/-- The collection attached to an `f`-map is compatible with restriction in the `Y`-variable. -/
private theorem ofHom_targetNatural (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).TargetNatural :=
  sorry

/-- The family attached to an `f`-map satisfies the Stacks compatibility conditions. -/
theorem ofHom_compatible (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).Compatible :=
  ⟨ofHom_sourceNatural ξ, ofHom_targetNatural ξ⟩

-- Proof sketch: the target-side naturality of `η` with `U = f⁻¹(V)` and `U' = f⁻¹(V')` yields
-- the naturality square of the corresponding natural transformation `𝒢 ⟶ f_* ℱ`.
/-- The family `η_{U,V}` defines a natural transformation `𝒢 ⟶ f_* ℱ` by evaluating at
`U = f⁻¹(V)`. -/
private theorem toHom_naturality'
    (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) (hη : η.TargetNatural) :
    ∀ ⦃V V' : (Opens Y)ᵒᵖ⦄ (j : V ⟶ V'),
      𝒢.presheaf.map j ≫ η ((Opens.map f).obj (unop V')) (unop V') le_rfl =
        η ((Opens.map f).obj (unop V)) (unop V) le_rfl ≫
          ((pushforward (Type v) f).obj ℱ).presheaf.map j :=
  sorry

/-- Recover an `f`-map from a family that is natural in the `Y`-variable by evaluating it on
`U = f⁻¹(V)`. -/
def toHom (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) (hη : η.TargetNatural) :
    𝒢 ⟶ (pushforward (Type v) f).obj ℱ :=
  ObjectProperty.homMk
    { app := fun V ↦ η ((Opens.map f).obj V.unop) V.unop le_rfl
      naturality := toHom_naturality' η hη }

-- Proof sketch: starting from `ξ`, evaluating on `U = f⁻¹(V)` and then restricting back along the
-- identity inclusion leaves each component unchanged; extensionality of sheaf morphisms finishes.
/-- Passing from an `f`-map to its compatible family and back recovers the original `f`-map. -/
private theorem hom_left_inv (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    toHom (ofHom ξ) (ofHom_targetNatural ξ) = ξ :=
  sorry

-- Proof sketch: starting from `η`, evaluating at `U = f⁻¹(V)` and then restricting to a smaller
-- open `U ⊆ f⁻¹(V)` recovers `η_{U,V}` by the source-side naturality of `η`; extensionality of
-- collections gives equality.
/-- Passing from a compatible family to an `f`-map and back recovers the original family. -/
private theorem hom_right_inv (η : ContinuousMapSheafMapFamily f 𝒢 ℱ)
    (hηS : η.SourceNatural) (hηT : η.TargetNatural) :
    ofHom (toHom η hηT) = η :=
  sorry

/-- Lemma 6.21.8: for a continuous map `f : X ⟶ Y`, the set of `f`-maps
`ξ : 𝒢 ⟶ f_* ℱ` is canonically equivalent to the set of compatible collections of maps
`ξ_{U,V} : 𝒢(V) → ℱ(U)` for opens `U ⊆ f⁻¹(V)`. Together with Definition 6.21.7 and the
canonical adjunction equivalence
`((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv 𝒢 ℱ).symm`, this yields the
four bijective descriptions in the Stacks statement; the companion theorems
`equiv_naturality_left` and `equiv_naturality_right` record functoriality in `𝒢` and `ℱ`. -/
noncomputable def equiv :
    (𝒢 ⟶ (pushforward (Type v) f).obj ℱ) ≃
      { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } where
  toFun := fun ξ ↦ ⟨ofHom ξ, ofHom_compatible ξ⟩
  invFun := fun η ↦ toHom η.1 η.2.2
  left_inv := hom_left_inv
  right_inv η := Subtype.ext (hom_right_inv η.1 η.2.1 η.2.2)

/-- The compatible-family equivalence is natural under precomposition on the source sheaf `𝒢`. -/
theorem equiv_naturality_left (α : 𝒢' ⟶ 𝒢) (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    equiv (α ≫ ξ) = precompCompatible α (equiv ξ) := by
  apply Subtype.ext
  exact ofHom_precomp α ξ

/-- The compatible-family equivalence is natural under postcomposition on the target sheaf `ℱ`. -/
theorem equiv_naturality_right (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) (β : ℱ ⟶ ℱ') :
    equiv (ξ ≫ (pushforward (Type v) f).map β) = postcompCompatible β (equiv ξ) := by
  apply Subtype.ext
  exact ofHom_postcomp ξ β

end ContinuousMapSheafMapFamily

end
