import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: mathlib provides the canonical open-cover owner `Scheme.OpenCover` together
-- with basic-open infrastructure for affine schemes. The source item here is more specific: a
-- finite family of distinguished opens of an affine scheme whose union is the whole scheme. We
-- therefore keep that finite generator family as the source-facing owner and derive the
-- `Scheme.OpenCover` view as companion API.

variable (T : Scheme.{u})

/-- Definition 34.3.4: a standard Zariski covering of an affine scheme `T` is a finite Zariski
covering of `T` by distinguished opens is a finite family of global sections whose associated
basic opens cover `T`. The canonical open-cover presentation is derived below. -/
@[stacks 020R]
structure StandardZariskiCover where
  /-- The number of distinguished opens in the chosen standard cover. -/
  n : ℕ
  /-- The global sections defining the distinguished opens of the cover. -/
  generator : Fin n → Γ(T, ⊤)
  /-- The distinguished opens associated to the generators cover `T`. -/
  cover : (⊤ : T.Opens) = ⨆ i, T.basicOpen (generator i)

namespace StandardZariskiCover

variable {T : Scheme.{u}}

/-- The index type of a standard Zariski cover is the chosen finite set of generators. -/
abbrev I₀ (𝒰 : T.StandardZariskiCover) : Type := Fin 𝒰.n

/-- The `i`-th distinguished open in a standard Zariski cover, viewed as an open subscheme of
`T`. -/
abbrev X (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) : Scheme.{u} :=
  T.basicOpen (𝒰.generator i)

/-- The inclusion of the `i`-th distinguished open into `T`. -/
abbrev f (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) : 𝒰.X i ⟶ T :=
  (T.basicOpen (𝒰.generator i)).ι

/-- The distinguished opens in a standard Zariski covering have supremum `⊤`. -/
theorem iSup_eq_top (𝒰 : T.StandardZariskiCover) :
    (⨆ i : 𝒰.I₀, T.basicOpen (𝒰.generator i)) = (⊤ : T.Opens) :=
  𝒰.cover.symm

/-- The underlying standard-open family, viewed as an ordinary open cover of `T`. -/
abbrev toOpenCover (𝒰 : T.StandardZariskiCover) : T.OpenCover :=
  Scheme.openCoverOfIsOpenCover T
    (fun i : 𝒰.I₀ ↦ T.basicOpen (𝒰.generator i))
    ((show TopologicalSpace.IsOpenCover (fun i : 𝒰.I₀ ↦ T.basicOpen (𝒰.generator i)) by
      simpa [TopologicalSpace.IsOpenCover] using 𝒰.iSup_eq_top))

/-- A standard Zariski covering has finitely many members. -/
instance (𝒰 : T.StandardZariskiCover) : Finite 𝒰.I₀ :=
  inferInstance

@[simp] theorem toOpenCover_X (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) :
    𝒰.toOpenCover.X i = 𝒰.X i := rfl

@[simp] theorem toOpenCover_f (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) :
    𝒰.toOpenCover.f i = 𝒰.f i := rfl

/-- Each component map in a standard Zariski covering is an open immersion. -/
instance isOpenImmersion_f (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) :
    IsOpenImmersion (𝒰.f i) :=
  inferInstance

/-- In a standard Zariski covering, the range of the `i`-th component is the basic open cut out
by the chosen generator `𝒰.generator i`. -/
theorem opensRange_eq_basicOpen (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) :
    (𝒰.f i).opensRange = T.basicOpen (𝒰.generator i) := by
  simpa [StandardZariskiCover.f] using
    Scheme.Opens.opensRange_ι (T.basicOpen (𝒰.generator i))

/-- Every component of a standard Zariski covering of an affine scheme is affine. -/
theorem isAffine_obj [IsAffine T] (𝒰 : T.StandardZariskiCover) (i : 𝒰.I₀) :
    IsAffine (𝒰.X i) :=
  inferInstance

end StandardZariskiCover

end Scheme
end AlgebraicGeometry
