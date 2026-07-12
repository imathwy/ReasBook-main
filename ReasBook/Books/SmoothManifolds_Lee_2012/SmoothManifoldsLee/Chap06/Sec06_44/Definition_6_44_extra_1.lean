import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Proposition_4_28
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Notation_5_35_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1

open scoped ContDiff Manifold
open Manifold Set

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` did not surface a ready-made transversality owner for
-- this chapter-local API, so the statement surface below follows the local Chapter 4 and Chapter 5
-- APIs `Manifold.IsSmoothSubmersion`, `IsEmbeddedSubmanifold`, and `T[J; p]`.
-- Domain sampling pass: in this embedded-submanifold / tangent-space / transversality domain, the
-- owner abstraction is the Chapter 5 class `IsEmbeddedSubmanifold I J S`; the relevant derived API
-- is `Manifold.submanifoldTangentSpace` (`T[J; p]`) together with `mfderiv` and
-- `Manifold.IsSmoothSubmersion`. Primitive data is the embedded-submanifold instance on each
-- subset, while the tangent-space spanning conditions are the derived transversality predicates.

section TransversalityDefinitions

universe u𝕜 uE uF uE' uE'' uH uG uH' uH'' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]
variable {JS : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable {JS' : ModelWithCorners 𝕜 E'' H''} {S' : Set M}
variable [ChartedSpace H' S] [IsManifold JS ∞ S]
variable [ChartedSpace H'' S'] [IsManifold JS' ∞ S']
variable [IsEmbeddedSubmanifold I JS S] [IsEmbeddedSubmanifold I JS' S']

/-- Definition 6.44-extra-1 (1): two embedded submanifolds `S, S' ⊆ M` intersect transversely
when, at each point of `S ∩ S'`, their tangent spaces together span the ambient tangent space of
`M`. -/
def SubmanifoldsIntersectTransversely
    (I : ModelWithCorners 𝕜 E H)
    (JS : ModelWithCorners 𝕜 E' H') (S : Set M)
    [ChartedSpace H' S] [IsManifold JS ∞ S]
    (JS' : ModelWithCorners 𝕜 E'' H'') (S' : Set M)
    [ChartedSpace H'' S'] [IsManifold JS' ∞ S']
    [IsEmbeddedSubmanifold I JS S] [IsEmbeddedSubmanifold I JS' S'] : Prop :=
  ∀ p : (S ∩ S' : Set M),
    let pS : S := ⟨(p : M), p.2.1⟩
    let pS' : S' := ⟨(p : M), p.2.2⟩
    (T[JS; pS] : Submodule 𝕜 (TangentSpace I (p : M))) ⊔
      (T[JS'; pS'] : Submodule 𝕜 (TangentSpace I (p : M))) = ⊤

end TransversalityDefinitions

section TransverseMapsToSubmanifolds

universe u𝕜 uE uF uE' uH uG uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]
variable {JX : ModelWithCorners 𝕜 E' H'} {X : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X]
variable [IsEmbeddedSubmanifold I JX X]

/-- Definition 6.44-extra-1 (2): a map `F : N → M` is transverse to the embedded submanifold
`X ⊆ M` when, at each point of the set-theoretic preimage `F ⁻¹' X`, the image of `dF` together
with the tangent space of `X` spans the ambient tangent space of `M`. -/
class IsTransverseToSubmanifold
    (I : ModelWithCorners 𝕜 E H) (K : ModelWithCorners 𝕜 F G)
    (JX : ModelWithCorners 𝕜 E' H') (X : Set M)
    [ChartedSpace H' X] [IsManifold JX ∞ X]
    [IsEmbeddedSubmanifold I JX X] (F : N → M) : Prop where
  /-- A transverse map is smooth. -/
  contMDiff : ContMDiff K I ∞ F
  /-- At each point of the preimage, the image of `dF` together with the tangent space of `X`
  spans the ambient tangent space of `M`. -/
  tangent_sup_eq_top :
    ∀ p : F ⁻¹' X,
      let x : X := ⟨F p, p.2⟩
      let TX : Submodule 𝕜 (TangentSpace I (F p)) := T[JX; x]
      (mfderiv K I F (p : N)).range ⊔ TX = ⊤

/-- A proof that `F` is transverse to the chosen embedded submanifold structure canonically
coerces to the corresponding smoothness proof. -/
instance instCoeContMDiffIsTransverseToSubmanifold
    (F : N → M) :
    CoeTC (IsTransverseToSubmanifold I K JX X F) (ContMDiff K I ∞ F) where
  coe hF := hF.contMDiff

/-- A map is transverse to the chosen embedded submanifold structure exactly when it is smooth and,
at each point of the preimage, the derivative image together with the tangent space of the
submanifold spans the ambient tangent space. -/
theorem isTransverseToSubmanifold_iff (F : N → M) :
    IsTransverseToSubmanifold I K JX X F ↔
      ContMDiff K I ∞ F ∧
        ∀ p : F ⁻¹' X,
          let x : X := ⟨F p, p.2⟩
          let TX : Submodule 𝕜 (TangentSpace I (F p)) := T[JX; x]
          (mfderiv K I F (p : N)).range ⊔ TX = ⊤ := by
  constructor
  · intro hF
    -- Unpack the class fields into the advertised smoothness and spanning data.
    refine ⟨hF.contMDiff, ?_⟩
    intro p
    simpa using hF.tangent_sup_eq_top p
  · rintro ⟨hFcont, hFtrans⟩
    -- Repackage the smoothness and tangent-space condition into the class structure.
    refine ⟨hFcont, ?_⟩
    intro p
    simpa using hFtrans p

end TransverseMapsToSubmanifolds

section SmoothSubmersionsAreTransverse

universe u𝕜 uE uF uE' uH uG uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {K : ModelWithCorners 𝕜 F G}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N] [IsManifold K ∞ N]
variable {JX : ModelWithCorners 𝕜 E' H'} {X : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold I JX X]

namespace Manifold.IsSmoothSubmersion

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [IsManifold I ∞ M] [IsManifold K ∞ N] in
/-- Definition 6.44-extra-1 (3): every smooth submersion is transverse to every chosen embedded
submanifold structure on a target subset. -/
theorem isTransverseToSubmanifold {f : N → M} (hF : Manifold.IsSmoothSubmersion K I f)
    : IsTransverseToSubmanifold I K JX X f := by
  refine ⟨hF.contMDiff, ?_⟩
  intro p
  -- A submersion has full derivative range at every point.
  have hrange : (mfderiv K I f (p : N)).range = ⊤ :=
    LinearMap.range_eq_top.2 (hF.surjective_mfderiv (p : N))
  -- Once the derivative already fills the ambient tangent space, the sup is automatically `⊤`.
  simpa [hrange]

end Manifold.IsSmoothSubmersion

end SmoothSubmersionsAreTransverse

section SubmanifoldIntersectionInclusionCriteria

universe u𝕜 uE uE' uE'' uH uH' uH'' uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {JS : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable {JS' : ModelWithCorners 𝕜 E'' H''} {S' : Set M}
variable [ChartedSpace H' S] [IsManifold JS ∞ S]
variable [ChartedSpace H'' S'] [IsManifold JS' ∞ S']
variable [IsEmbeddedSubmanifold I JS S] [IsEmbeddedSubmanifold I JS' S']

omit [TopologicalSpace M] in
/-- Helper for Definition 6.44-extra-1: a point of the preimage of `S'` under the inclusion
`S ↪ M` canonically determines a point of `S ∩ S'`. -/
def leftInclusionPreimageToIntersection
    (p : (Subtype.val : S → M) ⁻¹' S') : (S ∩ S' : Set M) :=
  ⟨p.1, p.1.2, p.2⟩

omit [TopologicalSpace M] in
/-- Helper for Definition 6.44-extra-1: a point of `S ∩ S'` canonically determines a point of the
preimage of `S'` under the inclusion `S ↪ M`. -/
def intersectionToLeftInclusionPreimage
    (p : (S ∩ S' : Set M)) : (Subtype.val : S → M) ⁻¹' S' :=
  ⟨⟨p.1, p.2.1⟩, p.2.2⟩

omit [IsManifold I ∞ M] in
/-- Helper for Definition 6.44-extra-1: transversality of two embedded submanifolds is symmetric
in the two submanifold arguments. -/
theorem submanifoldsIntersectTransversely_symm :
    SubmanifoldsIntersectTransversely I JS S JS' S' ↔
      SubmanifoldsIntersectTransversely I JS' S' JS S := by
  constructor
  · intro h p
    -- Reinterpret a point of `S' ∩ S` as a point of `S ∩ S'` and swap the summands.
    have hp := h ⟨(p : M), p.2.2, p.2.1⟩
    simpa only [sup_comm] using hp
  · intro h p
    -- Apply the same argument after exchanging the two submanifolds.
    have hp := h ⟨(p : M), p.2.2, p.2.1⟩
    simpa only [sup_comm] using hp

/-- Definition 6.44-extra-1 (4): two embedded submanifolds with chosen smooth structures intersect
transversely exactly when the inclusion of `S` into `M` is transverse to `S'`. -/
theorem submanifoldsIntersectTransversely_iff_left_inclusion_transverse
    : SubmanifoldsIntersectTransversely I JS S JS' S' ↔
      IsTransverseToSubmanifold I JS JS' S' (Subtype.val : S → M) := by
  constructor
  · intro hSS'
    have hSubtypeContMDiff : ContMDiff JS I ∞ (Subtype.val : S → M) := by
      -- The embedded-submanifold inclusion is an immersion, hence smooth.
      let hEmbedded : IsEmbeddedSubmanifold I JS S := inferInstance
      have hSubtypeContMDiffTop : ContMDiff JS I ω (Subtype.val : S → M) := by
        simpa using hEmbedded.isSmoothEmbedding_subtype_val.isImmersion.contMDiff
      exact hSubtypeContMDiffTop.of_le (by simp)
    refine ⟨hSubtypeContMDiff, ?_⟩
    intro p
    -- Transport the inclusion-preimage point to the corresponding intersection point.
    have hp := hSS' (leftInclusionPreimageToIntersection p)
    simpa using hp
  · intro hIncl p
    -- Read the transverse-inclusion condition back at the matching preimage point.
    have hp := hIncl.tangent_sup_eq_top (intersectionToLeftInclusionPreimage p)
    simpa using hp

/-- Definition 6.44-extra-1 (5): two embedded submanifolds with chosen smooth structures intersect
transversely exactly when the inclusion of `S'` into `M` is transverse to `S`. -/
theorem submanifoldsIntersectTransversely_iff_right_inclusion_transverse
    : SubmanifoldsIntersectTransversely I JS S JS' S' ↔
      IsTransverseToSubmanifold I JS' JS S (Subtype.val : S' → M) := by
  -- Route correction: derive the right-inclusion criterion from symmetry and the left criterion.
  calc
    SubmanifoldsIntersectTransversely I JS S JS' S' ↔
        SubmanifoldsIntersectTransversely I JS' S' JS S :=
      submanifoldsIntersectTransversely_symm
    _ ↔ IsTransverseToSubmanifold I JS' JS S (Subtype.val : S' → M) :=
      submanifoldsIntersectTransversely_iff_left_inclusion_transverse

end SubmanifoldIntersectionInclusionCriteria
