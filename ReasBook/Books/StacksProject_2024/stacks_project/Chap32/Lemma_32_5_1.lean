import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IsQuasiAffine`, the canonical open
-- immersion `Scheme.toSpecΓ`, and the scheme-morphism owners `QuasiCompact` and
-- `LocallyOfFiniteType`; the
-- source-facing statement here is an explicit descent/exhaustion theorem for affine ambient
-- rings.

variable {W : Scheme.{u}} {R : Type u} [CommRing R]

/-- An open immersion `W ⟶ Spec(R)` descends along the inclusion of a `ℤ`-subalgebra `A ⊆ R`. -/
def DescendsToZSubalgebra
    (f : W ⟶ Spec (CommRingCat.of R)) (A : Subalgebra ℤ R) : Prop :=
  ∃ (W₀ : Scheme) (g : W₀ ⟶ Spec (CommRingCat.of A)) (_ : IsOpenImmersion g)
    (e : W ≅ pullback (Spec.map (CommRingCat.ofHom A.val.toRingHom)) g),
      e.hom ≫ pullback.fst _ _ = f

/-- Unfold `DescendsToZSubalgebra` into the descended open immersion and pullback identification.
-/
theorem descendsToZSubalgebra_iff
    (f : W ⟶ Spec (CommRingCat.of R)) (A : Subalgebra ℤ R) :
    DescendsToZSubalgebra f A ↔
      ∃ (W₀ : Scheme) (g : W₀ ⟶ Spec (CommRingCat.of A)) (_ : IsOpenImmersion g)
        (e : W ≅ pullback (Spec.map (CommRingCat.ofHom A.val.toRingHom)) g),
          e.hom ≫ pullback.fst _ _ = f :=
  Iff.rfl

namespace DescendsToZSubalgebra

/-- The finite type `ℤ`-subalgebras of `R` along which `f` descends as an open immersion. -/
def finiteTypeStages (f : W ⟶ Spec (CommRingCat.of R)) : Set (Subalgebra ℤ R) :=
  {A | Algebra.FiniteType ℤ A ∧ DescendsToZSubalgebra f A}

theorem mem_finiteTypeStages
    (f : W ⟶ Spec (CommRingCat.of R)) (A : Subalgebra ℤ R) :
    A ∈ finiteTypeStages f ↔ Algebra.FiniteType ℤ A ∧ DescendsToZSubalgebra f A :=
  Iff.rfl

end DescendsToZSubalgebra

variable (s : W ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) (f : W ⟶ Spec (CommRingCat.of R))
variable [QuasiCompact s] [LocallyOfFiniteType s] [IsOpenImmersion f]
variable
  (hcomp :
    f ≫
        Spec.map
          (CommRingCat.ofHom
            ((algebraMap ℤ R).comp
              ((ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))) =
      s)

/-- If `W` is quasi-compact over `Spec(ℤ)`, then any open immersion `W ⟶ Spec(R)` is quasi-affine.
-/
theorem isQuasiAffine_of_quasiCompact_overSpecZ_of_isOpenImmersion
    (s : W ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) (f : W ⟶ Spec (CommRingCat.of R))
    [QuasiCompact s] [IsOpenImmersion f] : W.IsQuasiAffine := by
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace s
  exact Scheme.IsQuasiAffine.of_isImmersion f

/-- Lemma 32.5.1 (1): if `W` is of finite type over `Spec(ℤ)` and admits an open immersion
`W ⟶ Spec(R)`, then that open immersion descends from an open immersion into `Spec(A)` for some
finite type `ℤ`-subalgebra `A ⊆ R`. -/
@[stacks 01Z7]
theorem exists_finiteType_zSubalgebra
    :
    ∃ A : Subalgebra ℤ R, A ∈ DescendsToZSubalgebra.finiteTypeStages f := sorry

/-- Lemma 32.5.1 (2): under the same hypotheses, the ambient ring `R` is the directed colimit of
finite type `ℤ`-subalgebras `A ⊆ R` admitting such a descended open immersion. Equivalently, the
set of finite type descent stages is directed and has supremum `⊤`. -/
@[stacks 01Z7]
theorem exists_directed_finiteType_zSubalgebra_family
    :
    DirectedOn (· ≤ ·) (DescendsToZSubalgebra.finiteTypeStages f) ∧
      sSup (DescendsToZSubalgebra.finiteTypeStages f) = ⊤ := sorry

end AlgebraicGeometry
