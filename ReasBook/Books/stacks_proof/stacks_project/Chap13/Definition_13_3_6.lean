import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Limits
open CategoryTheory.Pretriangulated

universe vA uA vD uD

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Abelian A]
  [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section

/- Domain-style sampling for Definition 13.3.6:
- primary domain: short exact sequences in an abelian category mapped to distinguished triangles in
  a pretriangulated category;
- inspected nearby canonical declarations in this domain:
  `ShortComplex.ShortExact`,
  `Triangle.mk`,
  `distTriang`,
  `Functor.IsHomological`;
- best owner abstraction: there is no upstream owner for this source-facing notion, so the file
  itself must own `DeltaFunctor`;
- primitive data: the inherited functor, the connecting morphism for each short exact sequence,
  additivity of that functor, the connecting morphism for each short exact sequence,
  distinguishedness of the induced triangle, and naturality for morphisms of short exact
  sequences;
- derived API: the inherited functor projections `obj` and `map`, and the associated triangle
  attached to a short exact sequence;
- source/core/bridge triage:
  `source-facing`: `DeltaFunctor`;
  `core/canonical`: the canonical triangle and short-exact-sequence owners `Triangle.mk`,
    `distTriang`, and `ShortComplex.ShortExact`;
  `bridge/view`: `Functor.IsHomological` on the target side, used later to extract long exact
    sequences from the distinguished triangles carried by a `DeltaFunctor`.

The owner only needs the pretriangulated distinguished-triangle structure on `D`; the stronger
`IsTriangulated D` hypothesis is not primitive data for this definition. The associated triangle
is derived API from the owner, not a second packaged notion. -/

/-- Definition 13.3.6: A `δ`-functor from an abelian category `A` to a pretriangulated category
`D` consists of an additive functor `A ⥤ D` together with a connecting morphism for every short
exact sequence in `A`, such that the associated triangle is distinguished and these connecting
morphisms are natural in morphisms of short exact sequences. -/
@[stacks 0150]
structure DeltaFunctor (A : Type uA) [Category.{vA} A] [Abelian A]
    (D : Type uD) [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] extends A ⥤ D where
  /-- The underlying functor of a `δ`-functor is additive. -/
  additive : toFunctor.Additive
  /-- The connecting morphism attached to a short exact sequence in `A`. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    obj S.X₃ ⟶ (obj S.X₁)⟦(1 : ℤ)⟧
  /-- The triangle obtained from a short exact sequence by the `δ`-functor is distinguished. -/
  map_distinguished ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    Triangle.mk (map S.f) (map S.g) (δ hS) ∈ distTriang D
  /-- The connecting morphisms commute with morphisms of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) :
    CommSq (map φ.τ₃) (δ hS) (δ hT) ((map φ.τ₁)⟦(1 : ℤ)⟧')

namespace DeltaFunctor

variable (F : DeltaFunctor A D)

instance : F.toFunctor.Additive := F.additive

/-- The triangle attached by a `δ`-functor to a short exact sequence. -/
def triangle {S : ShortComplex A} (hS : S.ShortExact) : Triangle D :=
  Triangle.mk (F.map S.f) (F.map S.g) (F.δ hS)

/-- A morphism of short exact sequences induces a morphism between the attached triangles. -/
@[simps]
def triangleMap {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    F.triangle hS ⟶ F.triangle hT :=
  Triangle.homMk _ _ (F.map φ.τ₁) (F.map φ.τ₂) (F.map φ.τ₃)
    (by
      simpa only [Functor.map_comp] using
        congrArg (fun f ↦ F.map f) φ.comm₁₂.symm)
    (by
      simpa only [Functor.map_comp] using
        congrArg (fun g ↦ F.map g) φ.comm₂₃.symm)
    (by
      simpa [triangle] using (F.δ_naturality hS hT φ).w.symm)

/-- The triangle attached to a short exact sequence by a `δ`-functor is distinguished. -/
theorem triangle_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    F.triangle hS ∈ distTriang D :=
  F.map_distinguished hS

end DeltaFunctor

end

end CategoryTheory
