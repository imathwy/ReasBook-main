import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

universe uM uHM uEM uN uHN uEN

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {I : ModelWithCorners ℝ EM HM} [IsManifold I ⊤ M]

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {K : ModelWithCorners ℝ EN HN} [IsManifold K ⊤ N]

namespace ContMDiffMap

/-- Definition 6.43-extra-1 (1). A smooth homotopy between smooth maps `f` and `g` is a smooth
map `N × I → M`, with `I = [0,1]`, whose values at the interval endpoints are `f` and `g`. The
smoothness on `N × I` is encoded by the manifold-with-boundary model `K.prod (𝓡∂ 1)`. -/
structure SmoothHomotopy (f g : C^∞⟮K, N; I, M⟯) where
  toContMDiffMap : C^∞⟮K.prod (𝓡∂ 1), N × Set.Icc (0 : ℝ) 1; I, M⟯
  map_zero_right : ∀ x : N, toContMDiffMap (x, (0 : Set.Icc (0 : ℝ) 1)) = f x
  map_one_right : ∀ x : N, toContMDiffMap (x, (1 : Set.Icc (0 : ℝ) 1)) = g x

/-- A smooth homotopy can be used as its underlying function on `N × I`. -/
instance {f g : C^∞⟮K, N; I, M⟯} :
    CoeFun (SmoothHomotopy f g) (fun _ ↦ N × Set.Icc (0 : ℝ) 1 → M) where
  coe H := H.toContMDiffMap

section

omit [IsManifold I ⊤ M] [IsManifold K ⊤ N]

/-- Evaluating a smooth homotopy at `t = 0` recovers its initial map. -/
@[simp] theorem SmoothHomotopy.apply_zero {f g : C^∞⟮K, N; I, M⟯}
    (H : SmoothHomotopy f g) (x : N) :
    H (x, (0 : Set.Icc (0 : ℝ) 1)) = f x :=
  H.map_zero_right x

/-- Evaluating a smooth homotopy at `t = 1` recovers its terminal map. -/
@[simp] theorem SmoothHomotopy.apply_one {f g : C^∞⟮K, N; I, M⟯}
    (H : SmoothHomotopy f g) (x : N) :
    H (x, (1 : Set.Icc (0 : ℝ) 1)) = g x :=
  H.map_one_right x

end

/-- A smooth homotopy forgets to a continuous homotopy of the underlying continuous maps. -/
def SmoothHomotopy.toContinuousMapHomotopy {f g : C^∞⟮K, N; I, M⟯}
    (H : SmoothHomotopy f g) :
    ContinuousMap.Homotopy (f : C(N, M)) (g : C(N, M)) where
  toFun p := H (p.2, p.1)
  continuous_toFun :=
    (map_continuous H.toContMDiffMap).comp (continuous_snd.prodMk continuous_fst)
  map_zero_left x := H.map_zero_right x
  map_one_left x := H.map_one_right x

section

omit [IsManifold I ⊤ M] [IsManifold K ⊤ N]

/-- A smooth homotopy yields a continuous homotopy of the underlying continuous maps. -/
theorem SmoothHomotopy.continuousMapHomotopic {f g : C^∞⟮K, N; I, M⟯}
    (H : SmoothHomotopy f g) :
    (f : C(N, M)).Homotopic (g : C(N, M)) :=
  ⟨H.toContinuousMapHomotopy⟩

/-- A smooth homotopy relative to `A` is a smooth homotopy that stays fixed on `A` throughout the
interval. -/
abbrev SmoothHomotopyRel (f g : C^∞⟮K, N; I, M⟯) (A : Set N) :=
  { H : SmoothHomotopy f g // ∀ x ∈ A, ∀ t : Set.Icc (0 : ℝ) 1, H (x, t) = f x }

namespace SmoothHomotopyRel

section

variable {f g : C^∞⟮K, N; I, M⟯} {A : Set N}

/-- A smooth homotopy relative to `A` is pointwise equal to the initial map on `A`. -/
theorem eq_fst (H : SmoothHomotopyRel f g A) {x : N} (hx : x ∈ A)
    (t : Set.Icc (0 : ℝ) 1) :
    H.1 (x, t) = f x :=
  H.2 x hx t

/-- A smooth homotopy relative to `A` is pointwise equal to the terminal map on `A`. -/
theorem eq_snd (H : SmoothHomotopyRel f g A) {x : N} (hx : x ∈ A)
    (t : Set.Icc (0 : ℝ) 1) :
    H.1 (x, t) = g x := by
  rw [H.eq_fst hx t, ← H.eq_fst hx 1, H.1.apply_one]

/-- Maps joined by a smooth homotopy relative to `A` agree on `A`. -/
theorem fst_eq_snd (H : SmoothHomotopyRel f g A) {x : N} (hx : x ∈ A) :
    f x = g x :=
  H.eq_fst hx 0 ▸ H.eq_snd hx 0

/-- Forget a smooth homotopy relative to `A` to a continuous homotopy relative to `A`. -/
def toContinuousMapHomotopyRel (H : SmoothHomotopyRel f g A) :
    (f : C(N, M)).HomotopyRel (g : C(N, M)) A where
  toHomotopy := H.1.toContinuousMapHomotopy
  prop' := fun t _ hx ↦ H.eq_fst hx t

end

end SmoothHomotopyRel

/-- Definition 6.43-extra-1 (2). Two smooth maps are smoothly homotopic if there exists a smooth
homotopy between them. -/
def SmoothlyHomotopic (f g : C^∞⟮K, N; I, M⟯) : Prop :=
  Nonempty (SmoothHomotopy f g)

/-- Two smooth maps are smoothly homotopic relative to `A` if there exists a smooth homotopy
between them that is fixed on `A`. -/
def SmoothlyHomotopicRel (f g : C^∞⟮K, N; I, M⟯) (A : Set N) : Prop :=
  Nonempty (SmoothHomotopyRel f g A)

/-- A smooth homotopy yields a continuous homotopy between the underlying continuous maps. -/
theorem SmoothlyHomotopic.continuousMapHomotopic {f g : C^∞⟮K, N; I, M⟯}
    (h : SmoothlyHomotopic f g) :
    (f : C(N, M)).Homotopic (g : C(N, M)) :=
  h.some.continuousMapHomotopic

namespace SmoothlyHomotopicRel

section

variable {f g : C^∞⟮K, N; I, M⟯} {A : Set N}

/-- A smooth homotopy relative to `A` forgets to an ordinary smooth homotopy. -/
protected theorem smoothlyHomotopic (h : SmoothlyHomotopicRel f g A) :
    SmoothlyHomotopic f g :=
  h.map Subtype.val

/-- A smooth homotopy relative to `A` forgets to a continuous homotopy relative to `A`. -/
theorem continuousMapHomotopicRel (h : SmoothlyHomotopicRel f g A) :
    (f : C(N, M)).HomotopicRel (g : C(N, M)) A :=
  h.map SmoothHomotopyRel.toContinuousMapHomotopyRel

/-- Maps that are smoothly homotopic relative to `A` agree on `A`. -/
theorem fst_eq_snd (h : SmoothlyHomotopicRel f g A) {x : N} (hx : x ∈ A) :
    f x = g x :=
  Nonempty.elim h (SmoothHomotopyRel.fst_eq_snd · hx)

@[simp] theorem empty_iff :
    SmoothlyHomotopicRel f g (∅ : Set N) ↔ SmoothlyHomotopic f g := by
  constructor
  · exact SmoothlyHomotopicRel.smoothlyHomotopic
  · intro h
    exact h.map fun H ↦ ⟨H, by simp⟩

end

end SmoothlyHomotopicRel

end

end ContMDiffMap
