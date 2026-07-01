import Mathlib.Analysis.Convex.Extreme

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

/-!
Source/core/bridge triage:
- `source-facing`: Defn 18.1 introduces faces of a convex set.
- `core/canonical`: mathlib's owner abstraction for the extreme-subset part of the definition is
  `IsExtreme R C F`.
- `bridge/view`: the textbook face notion is the source-facing predicate `Set.IsFace`, built from
  the convexity of `F` together with the canonical extremeness predicate.

Domain-style sampling used here:
- `Convex`;
- `IsExtreme`;
- `IsExtreme.subset`;
- `isExtreme_singleton`;
- `IsExtreme.mono`.

Primitive data vs derived API:
- primitive source-facing data: convexity of the candidate face `F` and the canonical extreme-set
  condition `IsExtreme R C F`;
- derived API: subset inclusion, reflexivity, transitivity, monotonicity through intermediate
  ambient sets, the nonempty-intersection theorem, and the singleton/extreme-point bridge.
- ambient minimization: both primitive ingredients `Convex` and `IsExtreme` live on the
  ordered-semiring scalar-action layer, so the owner uses `[SMul R E]`; the singleton bridge keeps
  this layer by taking singleton convexity as explicit primitive data in `_of_convex` lemmas,
  while module-level wrappers provide the ordinary no-noise singleton surface.

Layer target: `source-facing`.

Notation check: the face predicate itself stays on the short owner name `Set.IsFace`; for the
family of faces of `C`, the textbook surface notation `𝓕[R](C)` is provided and used.
-/

namespace Set

/-- Defn 18.1: `F` is a face of `C` if `F` is convex and is an extreme subset of `C`. -/
@[mk_iff]
structure IsFace (R : Type v) [Semiring R] [PartialOrder R] [SMul R E] (F C : Set E) : Prop where
  convex : Convex R F
  isExtreme : IsExtreme R C F

namespace IsFace

variable (R) in
/-- The family of faces of `C`. -/
def faces (C : Set E) : Set (Set E) :=
  {F : Set E | F.IsFace R C}

variable {C D F G : Set E}

/- Rockafellar notation for the family of faces of `C`. -/
scoped[Rockafellar] notation "𝓕[" K "](" C ")" => Set.IsFace.faces K C

open scoped Rockafellar

@[simp] theorem mem_faces_iff {C F : Set E} :
    F ∈ 𝓕[R](C) ↔ F.IsFace R C :=
  Iff.rfl

/-- Face-family notation bridge: membership in `𝓕[R](·)` is transitive. -/
theorem mem_faces_trans {C F G : Set E}
    (hF : F ∈ 𝓕[R](C)) (hG : G ∈ 𝓕[R](F)) :
    G ∈ 𝓕[R](C) := by
  have hFaceF : F.IsFace R C := mem_faces_iff.mp hF
  have hFaceG : G.IsFace R F := mem_faces_iff.mp hG
  exact mem_faces_iff.mpr ⟨hFaceG.convex, hFaceF.isExtreme.trans hFaceG.isExtreme⟩

theorem empty (C : Set E) : (∅ : Set E).IsFace R C := by
  refine ⟨convex_empty, ?_⟩
  refine ⟨empty_subset C, ?_⟩
  intro _ _ _ _ _ hz
  exact False.elim hz

/-- Face-family notation bridge: the empty set belongs to every face family. -/
theorem empty_mem_faces (C : Set E) :
    (∅ : Set E) ∈ 𝓕[R](C) :=
  mem_faces_iff.2 (empty C)

theorem subset (hF : F.IsFace R C) : F ⊆ C :=
  hF.isExtreme.subset

theorem refl (hC : Convex R C) : C.IsFace R C :=
  ⟨hC, .rfl⟩

/-- Face-family notation bridge: a convex set belongs to its own face family. -/
theorem mem_faces_self {C : Set E} (hC : Convex R C) :
    C ∈ 𝓕[R](C) :=
  mem_faces_iff.2 (refl hC)

/-- Primitive constructor: convexity plus extremality yields facehood. -/
theorem of_convex_isExtreme (hF_convex : Convex R F) (hF_extreme : IsExtreme R C F) :
    F.IsFace R C :=
  ⟨hF_convex, hF_extreme⟩

theorem trans (hF : F.IsFace R C) (hG : G.IsFace R F) : G.IsFace R C :=
  ⟨hG.convex, hF.isExtreme.trans hG.isExtreme⟩

theorem mono (hF : F.IsFace R C) (hFD : F ⊆ D) (hDC : D ⊆ C) : F.IsFace R D :=
  ⟨hF.convex, hF.isExtreme.mono hDC hFD⟩

/-- Face-family notation bridge: membership in `𝓕[R](·)` is monotone through intermediate
ambient sets. -/
theorem mem_faces_mono {C D F : Set E}
    (hF : F ∈ 𝓕[R](C)) (hFD : F ⊆ D) (hDC : D ⊆ C) :
    F ∈ 𝓕[R](D) := by
  exact mem_faces_iff.2 ((mem_faces_iff.1 hF).mono hFD hDC)

theorem extremePoints_subset (hF : F.IsFace R C) :
    F.extremePoints R ⊆ C.extremePoints R :=
  hF.isExtreme.extremePoints_subset_extremePoints

/-- Face-family notation bridge: extreme points are monotone along face membership in `𝓕[R](·)`.
-/
theorem extremePoints_subset_of_mem_faces {C F : Set E}
    (hF : F ∈ 𝓕[R](C)) :
    F.extremePoints R ⊆ C.extremePoints R := by
  exact (mem_faces_iff.mp hF).isExtreme.extremePoints_subset_extremePoints

/-- A nonempty intersection of faces of `C` is again a face of `C`. -/
theorem sInter {S : Set (Set E)} (hS : S.Nonempty) (hSC : ∀ F ∈ S, F.IsFace R C) :
    (⋂₀ S).IsFace R C :=
  ⟨convex_sInter fun F hF ↦ (hSC F hF).convex,
    isExtreme_sInter hS fun F hF ↦ (hSC F hF).isExtreme⟩

end IsFace
end Set

end

section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

namespace IsFace

theorem singleton_mem_extremePoints {C : Set E} {x : E}
    (h : ({x} : Set E).IsFace R C) :
    x ∈ C.extremePoints R := by
  simpa using h.isExtreme

theorem singleton_iff_mem_extremePoints_of_convex {C : Set E} {x : E}
    (hxs : Convex R ({x} : Set E)) :
    ({x} : Set E).IsFace R C ↔ x ∈ C.extremePoints R := by
  constructor
  · intro h
    simpa using h.isExtreme
  · intro hx
    exact ⟨hxs, (isExtreme_singleton).2 hx⟩

theorem singleton_of_mem_extremePoints_of_convex {C : Set E} {x : E}
    (hxs : Convex R ({x} : Set E)) (hx : x ∈ C.extremePoints R) :
    ({x} : Set E).IsFace R C :=
  ⟨hxs, (isExtreme_singleton).2 hx⟩

end IsFace

end Set

end

section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set

namespace IsFace

theorem singleton_iff_mem_extremePoints {C : Set E} {x : E} :
    ({x} : Set E).IsFace R C ↔ x ∈ C.extremePoints R :=
  singleton_iff_mem_extremePoints_of_convex (convex_singleton x)

theorem singleton_of_mem_extremePoints {C : Set E} {x : E}
    (hx : x ∈ C.extremePoints R) :
    ({x} : Set E).IsFace R C :=
  ⟨convex_singleton x, (isExtreme_singleton).2 hx⟩

end IsFace

end Set

end
