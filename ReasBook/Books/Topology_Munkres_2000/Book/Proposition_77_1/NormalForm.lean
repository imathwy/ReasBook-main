module

public import Topology_Munkres_2000.Book.Definition_77_2.OrientationType
import all Topology_Munkres_2000.Book.Definition_77_2

public section

universe u

namespace PolygonWord

/-- A residual signed word has torus type when each of its labels occurs once with each
sign. Unlike a `PolygonWord`, a residual may have fewer than three letters. -/
def TorusResidual {α : Type u} (tail : List (α × Bool)) : Prop :=
  ∀ c ∈ tail.map Prod.fst,
    ∃ rest : Multiset (α × Bool),
      (tail : Multiset (α × Bool)) = (c, true) ::ₘ (c, false) ::ₘ rest ∧
        ∀ sign : Bool, (c, sign) ∉ rest

/-- The signed-pair characterization of a torus residual. -/
theorem torusResidual_iff {α : Type u} {tail : List (α × Bool)} :
    TorusResidual tail ↔
      ∀ c ∈ tail.map Prod.fst,
        ∃ rest : Multiset (α × Bool),
          (tail : Multiset (α × Bool)) = (c, true) ::ₘ (c, false) ::ₘ rest ∧
            ∀ sign : Bool, (c, sign) ∉ rest := by
  rfl

/-- A sufficiently long residual has torus type exactly when the corresponding polygon word
does. -/
theorem torusResidual_iff_torusType {α : Type u} {tail : List (α × Bool)}
    (htail : 3 ≤ tail.length) :
    TorusResidual tail ↔
      PolygonWord.TorusType (⟨tail, htail⟩ : PolygonWord α) := by
  -- A singleton scheme's label multiset is the unsigned image of its word.
  simp only [TorusResidual, TorusType, LabellingScheme.labels,
    Multiset.singleton_bind, Multiset.mem_coe]

/-- A polygon word is obtained from a list of distinct duplicated signed letters followed
by a residual using none of their labels. -/
def IsDuplicatedPrefix {α : Type u} (normalized : PolygonWord α)
    (pairs tail : List (α × Bool)) : Prop :=
  normalized.1 = pairs.flatMap (fun letter ↦ [letter, letter]) ++ tail ∧
    (pairs.map Prod.fst).Pairwise (· ≠ ·) ∧
      ∀ letter ∈ pairs, ∀ tailLetter ∈ tail, letter.1 ≠ tailLetter.1

/-- The decomposition characterization of a duplicated prefix. -/
theorem isDuplicatedPrefix_iff {α : Type u} {normalized : PolygonWord α}
    {pairs tail : List (α × Bool)} :
    IsDuplicatedPrefix normalized pairs tail ↔
      normalized.1 = pairs.flatMap (fun letter ↦ [letter, letter]) ++ tail ∧
        (pairs.map Prod.fst).Pairwise (· ≠ ·) ∧
          ∀ letter ∈ pairs, ∀ tailLetter ∈ tail, letter.1 ≠ tailLetter.1 := by
  rfl

/-- A projective normal form consists of a nonempty initial list of distinct equally signed
duplicate pairs, followed by an empty tail or a tail of torus type using none of those labels. -/
def ProjectiveNormalForm {α : Type u} (normalized : PolygonWord α) : Prop :=
  ∃ pairs : List (α × Bool), pairs ≠ [] ∧
    ∃ tail : List (α × Bool),
      IsDuplicatedPrefix normalized pairs tail ∧
        (tail = [] ∨ TorusResidual tail)

/-- The explicit duplicated-prefix and empty-or-torus-tail specification of projective normal
form. -/
theorem projectiveNormalForm_iff {α : Type u} {normalized : PolygonWord α} :
    normalized.ProjectiveNormalForm ↔
      ∃ pairs : List (α × Bool), pairs ≠ [] ∧
        ∃ tail : List (α × Bool),
          IsDuplicatedPrefix normalized pairs tail ∧
            (tail = [] ∨ TorusResidual tail) := by
  rfl

end PolygonWord
