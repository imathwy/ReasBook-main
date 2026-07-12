import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical module restriction API
  `AlgebraicGeometry.Scheme.Modules.restrict` and the base-open restriction notation `f ∣_ U`;
- nearby Chapter 29 files use affine-base-local morphism properties through `S.affineOpens`;
- the checked-in Chapter 28 owner for ample invertible `\mathcal O_X`-modules is
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.

The source-facing owner below therefore records relative ampleness as a property of a morphism
`f : X ⟶ S` and an invertible module `L : X.Modules`, extending quasi-compactness of `f` and
requiring ampleness after restricting `L` to the inverse image of each affine open of `S`. -/

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- An `\mathcal O_X`-module is invertible for some chosen monoidal structure on `X.Modules`.
This wrapper keeps relative ampleness usable at sites where the monoidal structure is not a
canonical global typeclass instance. -/
def HasInvertibleModuleStructure {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∃ hmon : CategoryTheory.MonoidalCategory X.Modules,
    @Scheme.Modules.Invertible X hmon L

/-- An `\mathcal O_X`-module is ample for some chosen monoidal and invertible-module structure.
This is the explicit-instance form of `Scheme.Modules.IsAmple`. -/
def HasAmpleModuleStructure {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∃ hmon : CategoryTheory.MonoidalCategory X.Modules,
    ∃ hL : @Scheme.Modules.Invertible X hmon L,
      @Scheme.Modules.IsAmple X hmon L hL

/-- Restrict `L` to the preimage of an open subscheme `V ⊆ S`. -/
abbrev restrictToBasePreimage
    (f : X ⟶ S) (L : X.Modules) (V : S.Opens) :
    (f ⁻¹ᵁ V).toScheme.Modules :=
  L.restrict ((f ⁻¹ᵁ V).ι)

/-- The restriction of `L` to the preimage of a base open is ample, with the required monoidal
and invertible-module structures carried explicitly. -/
def IsAmpleOnBasePreimage (f : X ⟶ S) (L : X.Modules) (V : S.Opens) : Prop :=
  HasAmpleModuleStructure (restrictToBasePreimage f L V)

/-- Definition 29.37.1: an invertible `\mathcal{O}_X`-module `\mathcal L` is relatively ample on
`X/S` if `f : X ⟶ S` is quasi-compact and, for every affine open `U ⊆ S`, the restriction of
`\mathcal L` to the open subscheme `f^{-1}(U)` is ample. -/
@[stacks 01VH]
class RelativelyAmple (f : X ⟶ S) (L : X.Modules) : Prop where
  /-- The module is invertible on `X`, with the necessary monoidal structure recorded
  explicitly. -/
  invertible : HasInvertibleModuleStructure L
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- On every affine open of the base, the restricted module is ample. -/
  isAmpleOnAffinePreimage :
    ∀ U : S.affineOpens, IsAmpleOnBasePreimage f L (U : S.Opens)


/-- A relatively ample module is invertible on the source. -/
theorem RelativelyAmple.hasInvertibleModuleStructure
    (h : RelativelyAmple f L) :
    HasInvertibleModuleStructure L :=
  h.invertible

/-- For an affine open subscheme of the base, the restricted module is ample. -/
theorem RelativelyAmple.isAmpleOnPreimage
    (h : RelativelyAmple f L) (U : S.Opens) (hU : IsAffineOpen U) :
    IsAmpleOnBasePreimage f L U :=
  h.isAmpleOnAffinePreimage ⟨U, hU⟩

end

end AlgebraicGeometry
