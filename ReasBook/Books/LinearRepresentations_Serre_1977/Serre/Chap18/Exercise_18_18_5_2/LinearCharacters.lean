import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_1
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

-- The Fong–Swan import chain (via `Serre.Chap18.Exercise_18_18_5_1`) brings the global instance
-- `Field.henselian` (every field is a Henselian local ring) into scope.  That instance makes
-- type-class search diverge — even the trivial goal `Module F F` for a field `F` loops.  The
-- upstream file `Exercise_18_18_5_1` already disables it locally, but `attribute [-instance]`
-- removals do not propagate to importers, so we must repeat it here.  We never use the instance:
-- the modular system carries an explicit `[HenselianLocalRing A]` on the DVR `A`.
attribute [-instance] Field.henselian

noncomputable section

universe u w

namespace Representation

section

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)
local notation "V4InS4" => Subgroup.map (Subgroup.subtype A4) V4

local instance : (V4InS4).Normal := _root_.s4DoubleTranspositionKleinFour_normal

variable {k : Type u} [Field k]

/-- Helper for Exercise 18-18.5-2: scalar multiplication by the unit value of a linear character
is the identity endomorphism at the group identity. -/
lemma unitCharacterRepresentation_map_one
    {F : Type w} [Field F] {G : Type*} [Group G] (β : G →* Fˣ) :
    LinearMap.lsmul F F ((β 1 : Fˣ) : F) = 1 := by
  -- At the identity, the scalar is `1`, so the resulting linear map is the identity.
  apply LinearMap.ext
  intro x
  simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 18-18.5-2: scalar multiplication by a unit-valued character is
multiplicative in the group variable. -/
lemma unitCharacterRepresentation_map_mul
    {F : Type w} [Field F] {G : Type*} [Group G] (β : G →* Fˣ) (x y : G) :
    LinearMap.lsmul F F ((β (x * y) : Fˣ) : F) =
      LinearMap.lsmul F F ((β x : Fˣ) : F) *
        LinearMap.lsmul F F ((β y : Fˣ) : F) := by
  -- Both sides act by the same scalar `(β x : F) * (β y : F)` on every vector.
  apply LinearMap.ext
  intro z
  simp [LinearMap.lsmul_apply, mul_assoc]

/-- Helper for Exercise 18-18.5-2: a unit-valued character gives a one-dimensional
representation over an arbitrary field. -/
abbrev unitCharacterRepresentation
    {F : Type w} [Field F] {G : Type*} [Group G] (β : G →* Fˣ) : Representation F G F where
  toFun g := LinearMap.lsmul F F ((β g : Fˣ) : F)
  map_one' := unitCharacterRepresentation_map_one β
  map_mul' x y := unitCharacterRepresentation_map_mul β x y

/-- Helper for Exercise 18-18.5-2: the character of a one-dimensional unit-valued representation
is the underlying scalar character. -/
@[simp] lemma unitCharacterRepresentation_character_apply
    {F : Type*} [Field F] {G : Type*} [Group G] (β : G →* Fˣ) (g : G) :
    (unitCharacterRepresentation β).character g = (β g : F) := by
  -- The action map is scalar multiplication on a one-dimensional vector space.
  rw [Representation.character]
  have hβg :
      unitCharacterRepresentation β g =
        (LinearMap.id : F →ₗ[F] F).smulRight ((β g : Fˣ) : F) := by
    apply LinearMap.ext
    intro z
    simp [unitCharacterRepresentation, LinearMap.lsmul_apply, mul_comm]
  rw [hβg]
  exact LinearMap.trace_smulRight (LinearMap.id : F →ₗ[F] F) ((β g : Fˣ) : F)

/-- Helper for Exercise 18-18.5-2: a one-dimensional unit-valued representation is irreducible
over any field. -/
lemma unitCharacterRepresentation_isIrreducible
    {F : Type*} [Field F] {G : Type*} [Group G] (β : G →* Fˣ) :
    (unitCharacterRepresentation β).IsIrreducible := by
  -- A one-dimensional vector space over a field is already a simple module.
  have hfinrank : Module.finrank F F = 1 := by simp
  letI : Nontrivial (Subrepresentation (unitCharacterRepresentation β)) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule F F) :=
    (isSimpleModule_iff F F).1 ((isSimpleModule_iff_finrank_eq_one).2 hfinrank)
  -- Every stable subspace is therefore either `⊥` or `⊤`.
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <|
        Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Exercise 18-18.5-2: the constant unit character affords the trivial
representation. -/
noncomputable def unitCharacterRepresentation_one_equiv_trivial
    {F : Type*} [Field F] {G : Type*} [Group G] :
    (unitCharacterRepresentation (1 : G →* Fˣ)).Equiv (Representation.trivial F G F) := by
  refine Representation.Equiv.mk (LinearEquiv.refl F F) ?_
  intro g
  -- Both actions are the identity map on the one-dimensional carrier.
  apply LinearMap.ext
  intro x
  simp [unitCharacterRepresentation, Representation.trivial, LinearMap.lsmul_apply]

/-- Helper for Exercise 18-18.5-2: the canonical Klein-four subgroup of double transpositions in
`S₄` has quotient isomorphic to `S₃`. This is the structural bridge used in the modular
characteristic branches. -/
def s4_quotient_by_klein_four_equiv_s3 : S4 ⧸ V4InS4 ≃* Equiv.Perm (Fin 3) := by
  -- Reuse the chapter-level semidirect decomposition `S₄ = V₄ ⋊ S₃`.
  classical
  have hV4Normal : (V4InS4).Normal := _root_.s4DoubleTranspositionKleinFour_normal
  letI : (V4InS4).Normal := hV4Normal
  let H : Subgroup S4 := Classical.choose _root_.s4_hasSemidirectDecomposition
  have hH : ∃ e : H ≃* Equiv.Perm (Fin 3), (V4InS4).IsComplement' H :=
    Classical.choose_spec _root_.s4_hasSemidirectDecomposition
  let e : H ≃* Equiv.Perm (Fin 3) := Classical.choose hH
  have hcomp : (V4InS4).IsComplement' H := Classical.choose_spec hH
  let hHV : H.IsComplement' V4InS4 := hcomp.symm
  -- The complement identifies the quotient with the chosen `S₃` copy.
  exact hHV.QuotientMulEquiv.trans e

/-- Helper for Exercise 18-18.5-2: the quotient map followed by the canonical
`S₄ / V₄ ≃ S₃` identification gives the natural `S₄`-action on three letters used for the
degree-`2` constituent. -/
abbrev s4_quotient_hom_s3 : S4 →* Equiv.Perm (Fin 3) :=
  s4_quotient_by_klein_four_equiv_s3.toMonoidHom.comp (QuotientGroup.mk' V4InS4)

/-- Helper for Exercise 18-18.5-2: transport the natural `S₃`-action on `Fin 3` along the
quotient homomorphism from `S₄`. -/
local instance s4_action_on_three_via_quotient : MulAction S4 (Fin 3) :=
  MulAction.compHom (Fin 3) s4_quotient_hom_s3

/-- Helper for Exercise 18-18.5-2: the sign character of `S₄` with values in an arbitrary field. -/
abbrev s4_sign_character (F : Type w) [Field F] : S4 →* Fˣ :=
  (Units.map (Int.castRingHom F).toMonoidHom).comp Equiv.Perm.sign

/-- Helper for Exercise 18-18.5-2: the canonical sign representation of `S₄`. -/
abbrev s4_sign_representation (F : Type w) [Field F] : Representation F S4 F :=
  unitCharacterRepresentation (s4_sign_character F)

/-- Helper for Exercise 18-18.5-2: the sign character of `S₃` with values in an arbitrary field. -/
abbrev s3_sign_character (F : Type w) [Field F] : S3 →* Fˣ :=
  (Units.map (Int.castRingHom F).toMonoidHom).comp Equiv.Perm.sign

/-- Helper for Exercise 18-18.5-2: the canonical sign representation of `S₃`. -/
abbrev s3_sign_representation (F : Type w) [Field F] : Representation F S3 F :=
  unitCharacterRepresentation (s3_sign_character F)

/-- Helper for Exercise 18-18.5-2: the degree-`2` model is the augmentation representation of
the quotient action of `S₄` on `Fin 3`. -/
abbrev s4_quotient_augmentation_representation
    (F : Type w) [Field F] :
    Representation F S4 (permutationAugmentationSubrepresentation F S4 (Fin 3)).toSubmodule :=
  permutationAugmentationRepresentation F S4 (Fin 3)

/-- Helper for Exercise 18-18.5-2: the degree-`3` standard model is the augmentation
representation of the natural action of `S₄` on `Fin 4`. -/
abbrev s4_standard_augmentation_representation
    (F : Type w) [Field F] :
    Representation F S4 (permutationAugmentationSubrepresentation F S4 (Fin 4)).toSubmodule :=
  permutationAugmentationRepresentation F S4 (Fin 4)

end

end Representation
