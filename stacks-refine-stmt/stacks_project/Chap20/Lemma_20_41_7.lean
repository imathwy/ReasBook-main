import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The `RingCat`-valued structure sheaf underlying a ringed space. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose (Opens.grothendieckTopology X.carrier) (forget₂ CommRingCat RingCat.{u})).obj
    X.sheaf

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
private abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable {X : RingedSpace.{u}}
variable [Abelian (ambientModuleCategory X)]
variable [CategoryWithHomology (ambientModuleCategory X)]

/-- Use the preadditive structure induced by the ambient abelian category so the standard
Hom-complex API applies to complexes of `\mathcal O_X`-modules. -/
local instance : Preadditive (ambientModuleCategory X) :=
  Abelian.toPreadditive

local notation "CpxOX" => CochainComplex (ambientModuleCategory X) ℤ

/-- The degree-`n` cochains in the Hom complex of two complexes of `\mathcal O_X`-modules. -/
private abbrev homComplexCochain (K L : CpxOX) (n : ℤ) :=
  Cochain K L n

/-- The degreewise comparison on Hom-complex cochains induced by precomposition with `a` and
postcomposition with `b`. -/
private def homComplexPrecompPostcompComponentToFun
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    homComplexCochain L I' n → homComplexCochain L' I n :=
  fun z ↦ (Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)

-- Proof sketch: postcomposition by `b` and precomposition by `a` are additive on cochains, so
-- their composite preserves addition degreewise.
/-- The degreewise Hom-complex comparison map is additive on cochains. -/
private theorem homComplexPrecompPostcompComponentToFun_map_add
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    ∀ z z' : homComplexCochain L I' n,
      homComplexPrecompPostcompComponentToFun a b n (z + z') =
        homComplexPrecompPostcompComponentToFun a b n z +
          homComplexPrecompPostcompComponentToFun a b n z' := sorry

/-- The degree-`n` component of the comparison morphism
`Hom^\bullet(L^\bullet, (I')^\bullet) ⟶ Hom^\bullet((L')^\bullet, I^\bullet)`. -/
private def homComplexPrecompPostcompComponent
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) (n : ℤ) :
    (CochainComplex.HomComplex L I').X n ⟶ (CochainComplex.HomComplex L' I).X n :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (homComplexPrecompPostcompComponentToFun a b n)
      (homComplexPrecompPostcompComponentToFun_map_add a b n))

-- Proof sketch: the Hom-complex differential is the cochain differential `δ`. Functoriality of
-- `δ` with respect to precomposition and postcomposition is exactly the pair of identities
-- `δ_zero_cocycle_comp` and `δ_comp_zero_cocycle`, specialized to the `0`-cocycles attached to
-- `a` and `b`.
/-- Precomposition and postcomposition assemble into a morphism of Hom complexes. -/
private theorem homComplexPrecompPostcomp_comm
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) :
    ∀ n m : ℤ, (up ℤ).Rel n m →
      homComplexPrecompPostcompComponent a b n ≫ (CochainComplex.HomComplex L' I).d n m =
        (CochainComplex.HomComplex L I').d n m ≫ homComplexPrecompPostcompComponent a b m := sorry

/-- The comparison morphism on Hom complexes induced by precomposition with `a` and
postcomposition with `b`. -/
private def homComplexPrecompPostcomp
    {L' L I' I : CpxOX} (a : L' ⟶ L) (b : I' ⟶ I) :
    CochainComplex.HomComplex L I' ⟶ CochainComplex.HomComplex L' I where
  f := homComplexPrecompPostcompComponent a b
  comm' := homComplexPrecompPostcomp_comm a b

-- Proof sketch: by Lemma `20.41.6`, after restricting to any open subset `U`, the degree-zero
-- homology sheaf of each Hom complex identifies with the sheaf associated to the presheaf
-- `U ↦ \mathrm{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. Under these identifications the map induced
-- by `a` and `b` is the identity, so the comparison morphism is a quasi-isomorphism.
/-- Lemma 20.41.7: if `a : (\mathcal L')^\bullet ⟶ \mathcal L^\bullet` and
`b : (\mathcal I')^\bullet ⟶ \mathcal I^\bullet` are quasi-isomorphisms of complexes of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, with both
`\mathcal I^\bullet` and `(\mathcal I')^\bullet` K-injective, then the induced map
`\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, (\mathcal I')^\bullet) ⟶
\mathcal H\!\mathit{om}^\bullet((\mathcal L')^\bullet, \mathcal I^\bullet)` is a
quasi-isomorphism. -/
theorem quasiIso_homComplex_precomp_postcomp_of_quasiIso_of_isKInjective
    {L' L I' I : CpxOX}
    (a : L' ⟶ L) (ha : QuasiIso a)
    (b : I' ⟶ I) (hb : QuasiIso b)
    [I'.IsKInjective] [I.IsKInjective] :
    QuasiIso (homComplexPrecompPostcomp a b) := sorry

end AlgebraicGeometry.RingedSpace
