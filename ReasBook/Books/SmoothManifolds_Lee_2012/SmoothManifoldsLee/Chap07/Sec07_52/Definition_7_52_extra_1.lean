import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_52.Proposition_7_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uH uE uG uV

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local
-- repository/mathlib inspection was used instead. The canonical owner reused here is the existing
-- `LieGroupRepresentation`, i.e. a smooth homomorphism into the smooth general linear group.

section

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]

local notation "Rep" => LieGroupRepresentation I G V

namespace LieGroupRepresentation

/-- Definition 7.52-extra-1: for a real or complex Lie-group representation `ρ` on `V`, `ρ` is
faithful if the underlying Lie-group homomorphism into `GL(V)` is
injective. -/
class IsFaithful (ρ : Rep) : Prop where
  injective : Function.Injective ρ

/-- Faithfulness of a Lie-group representation is a proposition. -/
instance instSubsingletonIsFaithful (ρ : Rep) : Subsingleton (IsFaithful ρ) :=
  inferInstance

/-- A Lie-group representation is faithful exactly when it is injective as a map into `GL(V)`. -/
theorem isFaithful_iff_injective (ρ : Rep) :
    IsFaithful ρ ↔ Function.Injective ρ := sorry

end LieGroupRepresentation

end
