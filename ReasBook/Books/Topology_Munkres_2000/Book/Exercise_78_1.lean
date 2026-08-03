module

public import Topology_Munkres_2000.Book.Example_74_3
public import Topology_Munkres_2000.Book.Exercise_74_3.Quotient
public import Topology_Munkres_2000.Book.Exercise_78_1.TriangleSquare
public import Topology_Munkres_2000.Book.Exercise_78_1.TriangularRegions
public import Topology_Munkres_2000.Book.Exercise_78_1.OccurrenceNormalization
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization
import all Topology_Munkres_2000.Book.Exercise_74_3.Quotient
import all Topology_Munkres_2000.Book.Example_22_5.Torus
import all Topology_Munkres_2000.Book.Exercise_78_1.TriangleSquare

public section

open scoped SignedLetter

namespace FourTrianglePasting

/-- The signed word `a b c`, using `0 = a`, ..., `5 = f`. -/
def wordABC : List (Fin 6 × Bool) :=
  [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)]

/-- The polygon word `a b c`. -/
def polygonABC : PolygonWord (Fin 6) :=
  ⟨wordABC, by decide⟩

/-- The signed word `d a e`, using `0 = a`, ..., `5 = f`. -/
def wordDAE : List (Fin 6 × Bool) :=
  [(3 : Fin 6), (0 : Fin 6), (4 : Fin 6)]

/-- The polygon word `d a e`. -/
def polygonDAE : PolygonWord (Fin 6) :=
  ⟨wordDAE, by decide⟩

/-- The signed word `b e f`, using `0 = a`, ..., `5 = f`. -/
def wordBEF : List (Fin 6 × Bool) :=
  [(1 : Fin 6), (4 : Fin 6), (5 : Fin 6)]

/-- The polygon word `b e f`. -/
def polygonBEF : PolygonWord (Fin 6) :=
  ⟨wordBEF, by decide⟩

/-- The signed word `c d f`, using `0 = a`, ..., `5 = f`. -/
def wordCDF : List (Fin 6 × Bool) :=
  [(2 : Fin 6), (3 : Fin 6), (5 : Fin 6)]

/-- The polygon word `c d f`. -/
def polygonCDF : PolygonWord (Fin 6) :=
  ⟨wordCDF, by decide⟩

/-- The signed word `c b a`, using `0 = a`, ..., `5 = f`. -/
def wordCBA : List (Fin 6 × Bool) :=
  [(2 : Fin 6), (1 : Fin 6), (0 : Fin 6)]

/-- The polygon word `c b a`. -/
def polygonCBA : PolygonWord (Fin 6) :=
  ⟨wordCBA, by decide⟩

/-- The signed word `d e f`, using `0 = a`, ..., `5 = f`. -/
def wordDEF : List (Fin 6 × Bool) :=
  [(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)]

/-- The polygon word `d e f`. -/
def polygonDEF : PolygonWord (Fin 6) :=
  ⟨wordDEF, by decide⟩

/-- The signed word `d f e⁻¹`; only the final occurrence of `e` is reversed. -/
def wordDFEInv : List (Fin 6 × Bool) :=
  [(3 : Fin 6), (5 : Fin 6), (4 : Fin 6)⁻¹]

/-- The polygon word `d f e⁻¹`. -/
def polygonDFEInv : PolygonWord (Fin 6) :=
  ⟨wordDFEInv, by decide⟩

/-- The four-word labelling scheme `abc`, `dae`, `bef`, `cdf`. -/
def schemeA : LabellingScheme (Fin 6) :=
  polygonABC ::ₘ polygonDAE ::ₘ polygonBEF ::ₘ polygonCDF ::ₘ 0

/-- The underlying words of `schemeA` are exactly `abc`, `dae`, `bef`, and `cdf`. -/
theorem schemeA_words :
    schemeA.words = wordABC ::ₘ wordDAE ::ₘ wordBEF ::ₘ wordCDF ::ₘ 0 := by
  -- Route correction: the imported `words` body is opaque, so local unfolding is unavailable.
  -- Compute the four mapped words through the public cons and empty-scheme equations.
  simp only [schemeA, LabellingScheme.words_cons, LabellingScheme.words_zero, polygonABC,
    polygonDAE, polygonBEF, polygonCDF]

/-- The four-word labelling scheme `abc`, `cba`, `def`, `d f e⁻¹`. -/
def schemeB : LabellingScheme (Fin 6) :=
  polygonABC ::ₘ polygonCBA ::ₘ polygonDEF ::ₘ polygonDFEInv ::ₘ 0

/-- The underlying words of `schemeB` are exactly `abc`, `cba`, `def`, and `d f e⁻¹`. -/
theorem schemeB_words :
    schemeB.words = wordABC ::ₘ wordCBA ::ₘ wordDEF ::ₘ wordDFEInv ::ₘ 0 := by
  -- Route correction: the imported `words` body is opaque, so local unfolding is unavailable.
  -- Compute the four mapped words through the public cons and empty-scheme equations.
  simp only [schemeB, LabellingScheme.words_cons, LabellingScheme.words_zero, polygonABC,
    polygonCBA, polygonDEF, polygonDFEInv]

/-- Every word in `schemeA` has three edges. -/
theorem schemeA_isTriangular : schemeA.IsTriangular := by
  -- Route correction: the imported predicate body is opaque, so occurrences cannot be introduced.
  -- Reduce triangularity to the lengths of the four explicit polygon words.
  refine LabellingScheme.isTriangular_of_forall_mem ?_
  intro word hword
  simp only [schemeA, Multiset.mem_cons] at hword
  rcases hword with rfl | rfl | rfl | rfl | hword
  · decide
  · decide
  · decide
  · decide
  · simp at hword

/-- Every word in `schemeB` has three edges. -/
theorem schemeB_isTriangular : schemeB.IsTriangular := by
  -- Route correction: the imported predicate body is opaque, so occurrences cannot be introduced.
  -- Reduce triangularity to the lengths of the four explicit polygon words.
  refine LabellingScheme.isTriangular_of_forall_mem ?_
  intro word hword
  simp only [schemeB, Multiset.mem_cons] at hword
  rcases hword with rfl | rfl | rfl | rfl | hword
  · decide
  · decide
  · decide
  · decide
  · simp at hword

/-- Helper for Exercise 78.1: the four occurrences of scheme A in displayed order. -/
noncomputable def schemeAOccurrence : Fin 4 → LabellingScheme.Occurrence schemeA
  | ⟨0, _⟩ => fourConsOccurrenceZero polygonABC polygonDAE polygonBEF polygonCDF
  | ⟨1, _⟩ => fourConsOccurrenceOne polygonABC polygonDAE polygonBEF polygonCDF
  | ⟨2, _⟩ => fourConsOccurrenceTwo polygonABC polygonDAE polygonBEF polygonCDF
  | ⟨3, _⟩ => fourConsOccurrenceThree polygonABC polygonDAE polygonBEF polygonCDF
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: the four occurrences of scheme B in displayed order. -/
noncomputable def schemeBOccurrence : Fin 4 → LabellingScheme.Occurrence schemeB
  | ⟨0, _⟩ => fourConsOccurrenceZero polygonABC polygonCBA polygonDEF polygonDFEInv
  | ⟨1, _⟩ => fourConsOccurrenceOne polygonABC polygonCBA polygonDEF polygonDFEInv
  | ⟨2, _⟩ => fourConsOccurrenceTwo polygonABC polygonCBA polygonDEF polygonDFEInv
  | ⟨3, _⟩ => fourConsOccurrenceThree polygonABC polygonCBA polygonDEF polygonDFEInv
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: the displayed occurrences exhaust scheme A. -/
theorem schemeAOccurrence_surjective : Function.Surjective schemeAOccurrence := by
  -- Rewrite the scheme to its four cons cells and use the generic occurrence classification.
  intro region
  rcases fourConsOccurrence_cases polygonABC polygonDAE polygonBEF polygonCDF region with
    h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩

/-- Helper for Exercise 78.1: the displayed occurrences exhaust scheme B. -/
theorem schemeBOccurrence_surjective : Function.Surjective schemeBOccurrence := by
  -- The same generic four-cons classification enumerates the second scheme.
  intro region
  rcases fourConsOccurrence_cases polygonABC polygonCBA polygonDEF polygonDFEInv region with
    h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩

/-- Helper for Exercise 78.1: the polygon word carried by each normalized scheme-A occurrence. -/
def schemeAWordTable : Fin 4 → PolygonWord (Fin 6)
  | ⟨0, _⟩ => polygonABC
  | ⟨1, _⟩ => polygonDAE
  | ⟨2, _⟩ => polygonBEF
  | ⟨3, _⟩ => polygonCDF
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: the polygon word carried by each normalized scheme-B occurrence. -/
def schemeBWordTable : Fin 4 → PolygonWord (Fin 6)
  | ⟨0, _⟩ => polygonABC
  | ⟨1, _⟩ => polygonCBA
  | ⟨2, _⟩ => polygonDEF
  | ⟨3, _⟩ => polygonDFEInv
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: normalized scheme-A occurrences project to their word table. -/
theorem schemeAOccurrence_fst (i : Fin 4) : (schemeAOccurrence i).1 = schemeAWordTable i := by
  -- Each finite index selects one of the four generic occurrence projection equations.
  fin_cases i
  · exact fourConsOccurrenceZero_fst polygonABC polygonDAE polygonBEF polygonCDF
  · exact fourConsOccurrenceOne_fst polygonABC polygonDAE polygonBEF polygonCDF
  · exact fourConsOccurrenceTwo_fst polygonABC polygonDAE polygonBEF polygonCDF
  · exact fourConsOccurrenceThree_fst polygonABC polygonDAE polygonBEF polygonCDF

/-- Helper for Exercise 78.1: normalized scheme-B occurrences project to their word table. -/
theorem schemeBOccurrence_fst (i : Fin 4) : (schemeBOccurrence i).1 = schemeBWordTable i := by
  -- Each finite index selects one of the four generic occurrence projection equations.
  fin_cases i
  · exact fourConsOccurrenceZero_fst polygonABC polygonCBA polygonDEF polygonDFEInv
  · exact fourConsOccurrenceOne_fst polygonABC polygonCBA polygonDEF polygonDFEInv
  · exact fourConsOccurrenceTwo_fst polygonABC polygonCBA polygonDEF polygonDFEInv
  · exact fourConsOccurrenceThree_fst polygonABC polygonCBA polygonDEF polygonDFEInv

/-- Helper for Exercise 78.1: the signed edge letters of scheme A in normalized coordinates. -/
def schemeAEdgeTable : Fin 4 → Fin 3 → Fin 6 × Bool
  | ⟨0, _⟩, ⟨0, _⟩ => (0, true)
  | ⟨0, _⟩, ⟨1, _⟩ => (1, true)
  | ⟨0, _⟩, ⟨2, _⟩ => (2, true)
  | ⟨1, _⟩, ⟨0, _⟩ => (3, true)
  | ⟨1, _⟩, ⟨1, _⟩ => (0, true)
  | ⟨1, _⟩, ⟨2, _⟩ => (4, true)
  | ⟨2, _⟩, ⟨0, _⟩ => (1, true)
  | ⟨2, _⟩, ⟨1, _⟩ => (4, true)
  | ⟨2, _⟩, ⟨2, _⟩ => (5, true)
  | ⟨3, _⟩, ⟨0, _⟩ => (2, true)
  | ⟨3, _⟩, ⟨1, _⟩ => (3, true)
  | ⟨3, _⟩, ⟨2, _⟩ => (5, true)
  | ⟨n + 4, h⟩, _ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim
  | _, ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim

/-- Helper for Exercise 78.1: the signed edge letters of scheme B in normalized coordinates. -/
def schemeBEdgeTable : Fin 4 → Fin 3 → Fin 6 × Bool
  | ⟨0, _⟩, ⟨0, _⟩ => (0, true)
  | ⟨0, _⟩, ⟨1, _⟩ => (1, true)
  | ⟨0, _⟩, ⟨2, _⟩ => (2, true)
  | ⟨1, _⟩, ⟨0, _⟩ => (2, true)
  | ⟨1, _⟩, ⟨1, _⟩ => (1, true)
  | ⟨1, _⟩, ⟨2, _⟩ => (0, true)
  | ⟨2, _⟩, ⟨0, _⟩ => (3, true)
  | ⟨2, _⟩, ⟨1, _⟩ => (4, true)
  | ⟨2, _⟩, ⟨2, _⟩ => (5, true)
  | ⟨3, _⟩, ⟨0, _⟩ => (3, true)
  | ⟨3, _⟩, ⟨1, _⟩ => (5, true)
  | ⟨3, _⟩, ⟨2, _⟩ => (4, false)
  | ⟨n + 4, h⟩, _ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim
  | _, ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim

/-- Helper for Exercise 78.1: actual scheme-A edge labels compute by the finite table. -/
theorem schemeA_edgeLetter (i : Fin 4) (j : Fin 3) :
    (schemeAOccurrence i).1.1.get
        (Fin.cast (schemeA_isTriangular.region_length (schemeAOccurrence i)).symm j) =
      schemeAEdgeTable i j := by
  -- Normalize the occurrence and edge indices, then evaluate the explicit polygon words.
  fin_cases i <;> fin_cases j <;>
    simp [schemeAOccurrence_fst, schemeAWordTable, schemeAEdgeTable, polygonABC, polygonDAE,
      polygonBEF, polygonCDF, wordABC, wordDAE, wordBEF, wordCDF, SignedLetter.positive]

/-- Helper for Exercise 78.1: actual scheme-B edge labels compute by the finite table. -/
theorem schemeB_edgeLetter (i : Fin 4) (j : Fin 3) :
    (schemeBOccurrence i).1.1.get
        (Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j) =
      schemeBEdgeTable i j := by
  -- Normalize the occurrence and edge indices, including the one reversed final edge.
  fin_cases i <;> fin_cases j <;>
    simp [schemeBOccurrence_fst, schemeBWordTable, schemeBEdgeTable, polygonABC, polygonCBA,
      polygonDEF, polygonDFEInv, wordABC, wordCBA, wordDEF, wordDFEInv,
      SignedLetter.positive, SignedLetter.inverse]

/-- Helper for Exercise 78.1: distinct finite indices give distinct scheme-A occurrences. -/
theorem schemeAOccurrence_injective : Function.Injective schemeAOccurrence := by
  -- Equality of occurrences forces equality of their explicit polygon-word projections.
  intro i j hij
  have hword := congrArg Sigma.fst hij
  rw [schemeAOccurrence_fst, schemeAOccurrence_fst] at hword
  fin_cases i <;> fin_cases j <;>
    simp [schemeAWordTable, polygonABC, polygonDAE, polygonBEF, polygonCDF,
      wordABC, wordDAE, wordBEF, wordCDF, SignedLetter.positive] at hword ⊢

/-- Helper for Exercise 78.1: distinct finite indices give distinct scheme-B occurrences. -/
theorem schemeBOccurrence_injective : Function.Injective schemeBOccurrence := by
  -- Equality of occurrences forces equality of their explicit polygon-word projections.
  intro i j hij
  have hword := congrArg Sigma.fst hij
  rw [schemeBOccurrence_fst, schemeBOccurrence_fst] at hword
  fin_cases i <;> fin_cases j <;>
    simp [schemeBWordTable, polygonABC, polygonCBA, polygonDEF, polygonDFEInv,
      wordABC, wordCBA, wordDEF, wordDFEInv, SignedLetter.positive,
      SignedLetter.inverse] at hword ⊢

/-- Helper for Exercise 78.1: scheme-A occurrences are canonically indexed by `Fin 4`. -/
noncomputable def schemeAOccurrenceEquiv : LabellingScheme.Occurrence schemeA ≃ Fin 4 :=
  Equiv.ofBijective schemeAOccurrence ⟨schemeAOccurrence_injective, schemeAOccurrence_surjective⟩
    |>.symm

/-- Helper for Exercise 78.1: scheme-B occurrences are canonically indexed by `Fin 4`. -/
noncomputable def schemeBOccurrenceEquiv : LabellingScheme.Occurrence schemeB ≃ Fin 4 :=
  Equiv.ofBijective schemeBOccurrence ⟨schemeBOccurrence_injective, schemeBOccurrence_surjective⟩
    |>.symm

/-- Helper for Exercise 78.1: the first two scheme-B triangles form one block and the last two
form the other. -/
def schemeBIndexBlock : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => true
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: equal labels in the scheme-B edge table stay in one block. -/
theorem schemeBEdgeTable_label_preservesBlock (i k : Fin 4) (j l : Fin 3)
    (hlabel : (schemeBEdgeTable i j).1 = (schemeBEdgeTable k l).1) :
    schemeBIndexBlock i = schemeBIndexBlock k := by
  -- Exhaust the finite table; every cross-block case has unequal labels.
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [schemeBEdgeTable, schemeBIndexBlock] at hlabel ⊢

/-- Helper for Exercise 78.1: the block of a scheme-B occurrence. -/
noncomputable def schemeBRegionBlock (region : LabellingScheme.Occurrence schemeB) : Bool :=
  schemeBIndexBlock (schemeBOccurrenceEquiv region)

/-- Helper for Exercise 78.1: an arbitrary scheme-B edge label computes in normalized
occurrence and edge coordinates. -/
theorem schemeB_edgeLetter_normalized (region : LabellingScheme.Occurrence schemeB)
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      schemeBEdgeTable (schemeBOccurrenceEquiv region)
        (Fin.cast (schemeB_isTriangular.region_length region) edge) := by
  -- Enumerate the occurrence, normalize the dependent edge index, and use the table theorem.
  obtain ⟨i, rfl⟩ := schemeBOccurrence_surjective region
  let j : Fin 3 := Fin.cast
    (schemeB_isTriangular.region_length (schemeBOccurrence i)) edge
  have hedge : edge = Fin.cast
      (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j := by
    simp [j]
  rw [hedge, schemeB_edgeLetter]
  congr
  simp [schemeBOccurrenceEquiv]

/-- Helper for Exercise 78.1: an arbitrary scheme-A edge label computes in normalized
occurrence and edge coordinates. -/
theorem schemeA_edgeLetter_normalized (region : LabellingScheme.Occurrence schemeA)
    (edge : Fin region.1.1.length) :
    region.1.1.get edge =
      schemeAEdgeTable (schemeAOccurrenceEquiv region)
        (Fin.cast (schemeA_isTriangular.region_length region) edge) := by
  -- Enumerate the occurrence, normalize the dependent edge index, and use the table theorem.
  obtain ⟨i, rfl⟩ := schemeAOccurrence_surjective region
  let j : Fin 3 := Fin.cast
    (schemeA_isTriangular.region_length (schemeAOccurrence i)) edge
  have hedge : edge = Fin.cast
      (schemeA_isTriangular.region_length (schemeAOccurrence i)).symm j := by
    simp [j]
  rw [hedge, schemeA_edgeLetter]
  congr
  simp [schemeAOccurrenceEquiv]

/-- Helper for Exercise 78.1: the block function computes directly on normalized scheme-B
occurrences. -/
theorem schemeBRegionBlock_schemeBOccurrence (i : Fin 4) :
    schemeBRegionBlock (schemeBOccurrence i) = schemeBIndexBlock i := by
  -- Cancel the occurrence equivalence against its explicit inverse enumeration.
  simp [schemeBRegionBlock, schemeBOccurrenceEquiv]

/-- Helper for Exercise 78.1: the labelled-edge setoid is the equivalence closure of direct
edge pairings. -/
theorem identified_iff_eqvGen {α : Type u} {scheme : LabellingScheme α}
    (regions : LabellingScheme.PolygonalRegions scheme) (x y : regions.Source) :
    regions.Identified.r x y ↔ Relation.EqvGen regions.EdgeRelated x y := by
  -- Expose the defining generated relation once, so later invariant proofs avoid unfolding it.
  rfl

/-- Helper for Exercise 78.1: equal normalized scheme-A edge labels give the corresponding
labelled identification, with the second parameter reversed exactly when the signs differ. -/
theorem schemeANormalizedEdgePair_identified (i k : Fin 4) (j l : Fin 3)
    (t : unitInterval) (hlabel : (schemeAEdgeTable i j).1 = (schemeAEdgeTable k l).1) :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence i, TriangleDisk.edgePoint j t⟩
      ⟨schemeAOccurrence k, TriangleDisk.edgePoint l
        (if (schemeAEdgeTable i j).2 = (schemeAEdgeTable k l).2 then t
          else unitInterval.symm t)⟩ := by
  -- Insert the normalized pair as one generator of the equivalence closure.
  rw [identified_iff_eqvGen]
  apply Relation.EqvGen.rel
  refine ⟨schemeAOccurrence i, schemeAOccurrence k,
    Fin.cast (schemeA_isTriangular.region_length (schemeAOccurrence i)).symm j,
    Fin.cast (schemeA_isTriangular.region_length (schemeAOccurrence k)).symm l,
    t, ?_, ?_, ?_⟩
  · simpa only [schemeA_edgeLetter] using hlabel
  · simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast, Fin.cast_eq_self]
  · rw [schemeA_edgeLetter, schemeA_edgeLetter]
    simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast, Fin.cast_eq_self]

/-- Helper for Exercise 78.1: equal normalized scheme-B edge labels give the corresponding
labelled identification, including the reversed final `e` occurrence. -/
theorem schemeBNormalizedEdgePair_identified (i k : Fin 4) (j l : Fin 3)
    (t : unitInterval) (hlabel : (schemeBEdgeTable i j).1 = (schemeBEdgeTable k l).1) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r
      ⟨schemeBOccurrence i, TriangleDisk.edgePoint j t⟩
      ⟨schemeBOccurrence k, TriangleDisk.edgePoint l
        (if (schemeBEdgeTable i j).2 = (schemeBEdgeTable k l).2 then t
          else unitInterval.symm t)⟩ := by
  -- The same direct generator construction records the unique negative sign in scheme B.
  rw [identified_iff_eqvGen]
  apply Relation.EqvGen.rel
  refine ⟨schemeBOccurrence i, schemeBOccurrence k,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence k)).symm l,
    t, ?_, ?_, ?_⟩
  · simpa only [schemeB_edgeLetter] using hlabel
  · simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast, Fin.cast_eq_self]
  · rw [schemeB_edgeLetter, schemeB_edgeLetter]
    simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast, Fin.cast_eq_self]

/-- Helper for Exercise 78.1: every direct scheme-B edge pairing stays within one of the two
triangle blocks. -/
theorem schemeBEdgeRelated_preservesRegionBlock
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : (schemeB.triangularRegions schemeB_isTriangular).EdgeRelated x y) :
    schemeBRegionBlock x.1 = schemeBRegionBlock y.1 := by
  -- Extract the paired edge occurrences and discard the point-coordinate equations.
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, _, hlabel, hx, hy⟩
  subst x
  subst y
  -- Normalize both dependent edge labels to the finite table, where equality separates blocks.
  rw [schemeB_edgeLetter_normalized, schemeB_edgeLetter_normalized] at hlabel
  unfold schemeBRegionBlock
  exact schemeBEdgeTable_label_preservesBlock _ _ _ _ hlabel

/-- Helper for Exercise 78.1: every generated scheme-B identification stays within one of the
two triangle blocks. -/
theorem schemeBIdentified_preservesRegionBlock
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y) :
    schemeBRegionBlock x.1 = schemeBRegionBlock y.1 := by
  -- Replace the opaque setoid relation by its generated-relation interface.
  rw [identified_iff_eqvGen] at hxy
  -- The block equality is stable under every constructor of the equivalence closure.
  induction hxy with
  | rel _ _ h => exact schemeBEdgeRelated_preservesRegionBlock _ _ h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Helper for Exercise 78.1: the closed unit interval parametrizes a chosen half-circle. -/
noncomputable def halfCircleCoordinate (x : unitInterval) : Circle :=
  AddCircle.homeomorphCircle one_ne_zero (((x : ℝ) / 2 : ℝ) : UnitAddCircle)

/-- Helper for Exercise 78.1: the closed unit interval parametrizes a full circle. -/
noncomputable def fullCircleCoordinate (x : unitInterval) : Circle :=
  AddCircle.homeomorphCircle one_ne_zero ((x : ℝ) : UnitAddCircle)

/-- Helper for Exercise 78.1: the half-circle coordinate is continuous. -/
theorem continuous_halfCircleCoordinate : Continuous halfCircleCoordinate := by
  -- Compose division by two, the additive-circle quotient, and the circle homeomorphism.
  unfold halfCircleCoordinate
  fun_prop

/-- Helper for Exercise 78.1: the full-circle coordinate is continuous. -/
theorem continuous_fullCircleCoordinate : Continuous fullCircleCoordinate := by
  -- Compose the interval inclusion with the additive-circle quotient and homeomorphism.
  unfold fullCircleCoordinate
  fun_prop

/-- Helper for Exercise 78.1: the half-circle coordinate has no repeated values. -/
theorem halfCircleCoordinate_injective : Function.Injective halfCircleCoordinate := by
  -- Equality in one half-period lifts uniquely to equality of real representatives.
  intro x y hxy
  unfold halfCircleCoordinate at hxy
  apply (AddCircle.homeomorphCircle one_ne_zero).injective at hxy
  have hxmem : (x : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    exact ⟨by linarith [x.property.1], by linarith [x.property.2]⟩
  have hymem : (y : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    exact ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  have hreal : (x : ℝ) / 2 = (y : ℝ) / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxmem hymem).mp hxy
  apply Subtype.ext
  linarith

/-- Helper for Exercise 78.1: adding a half-turn to a circle argument gives its antipode. -/
theorem circleExp_add_pi (theta : ℝ) :
    Circle.exp (theta + Real.pi) = -Circle.exp theta := by
  -- Compare complex representatives and use `exp (π I) = -1`.
  apply Circle.ext
  rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_exp]
  have hexponent : (((theta + Real.pi : ℝ) : ℂ) * Complex.I) =
      (theta : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Helper for Exercise 78.1: antipodal half-circle values occur only at opposite endpoints. -/
theorem halfCircleCoordinate_eq_neg_iff (x y : unitInterval) :
    halfCircleCoordinate y = -halfCircleCoordinate x ↔
      (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  -- Convert the equality to real circle arguments modulo `2π` and bound the integer period.
  unfold halfCircleCoordinate
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk, ← circleExp_add_pi]
  constructor
  · intro hxy
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hxy
    norm_num at hm
    have hnormalized : (y : ℝ) = (x : ℝ) + 1 + 2 * (m : ℝ) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      apply mul_left_cancel₀ hpi
      linear_combination hm
    have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by
      linarith [x.property.2, y.property.1]
    have hmUpper : (m : ℝ) ≤ 0 := by
      linarith [x.property.1, y.property.2]
    have hmLowerInt : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
    have hmUpperInt : m ≤ (0 : ℤ) := by exact_mod_cast hmUpper
    have hmCases : m = -1 ∨ m = 0 := by omega
    rcases hmCases with rfl | rfl
    · right
      norm_num at hnormalized
      have hx : (x : ℝ) = 1 := by linarith [x.property.2, y.property.1]
      have hy : (y : ℝ) = 0 := by linarith [x.property.2, y.property.1]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · left
      norm_num at hnormalized
      have hx : (x : ℝ) = 0 := by linarith [x.property.1, y.property.2]
      have hy : (y : ℝ) = 1 := by linarith [x.property.1, y.property.2]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have harg : 2 * Real.pi / 1 * (((1 : unitInterval) : ℝ) / 2) =
          Real.pi := by
        norm_num
        ring
      rw [harg]
      simp
    · have harg : 2 * Real.pi / 1 * (((1 : unitInterval) : ℝ) / 2) =
          Real.pi := by
        norm_num
        ring
      rw [harg]
      have htwo : Real.pi + Real.pi = 2 * Real.pi := by ring
      rw [htwo, Circle.exp_two_pi]
      norm_num

/-- Helper for Exercise 78.1: full-circle equality is exactly interval endpoint equality. -/
theorem fullCircleCoordinate_eq_iff (x y : unitInterval) :
    fullCircleCoordinate x = fullCircleCoordinate y ↔
      unitInterval.endpointSetoid x y := by
  -- Transport the additive-circle endpoint relation through its circle homeomorphism.
  unfold fullCircleCoordinate
  simp only [AddCircle.homeomorphCircle_apply]
  change AddCircle.toCircle (x : UnitAddCircle) = AddCircle.toCircle (y : UnitAddCircle) ↔
    (x : UnitAddCircle) = (y : UnitAddCircle)
  exact (AddCircle.injective_toCircle one_ne_zero).eq_iff

/-- Helper for Exercise 78.1: reflecting the interval inverts the full-circle coordinate. -/
theorem fullCircleCoordinate_symm (x : unitInterval) :
    fullCircleCoordinate (unitInterval.symm x) = Inv.inv (fullCircleCoordinate x) := by
  -- The reflected argument differs from the negative argument by one period.
  unfold fullCircleCoordinate
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk, ← Circle.exp_neg]
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  rw [unitInterval.coe_symm_eq]
  norm_num
  ring

/-- Helper for Exercise 78.1: inversion within the chosen half-circle fixes only its endpoints. -/
theorem halfCircleCoordinate_eq_inv_iff (x y : unitInterval) :
    halfCircleCoordinate y = Inv.inv (halfCircleCoordinate x) ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
  -- Circle-exponential equality bounds the possible period by the interval endpoints.
  unfold halfCircleCoordinate
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk, ← Circle.exp_neg]
  constructor
  · intro hxy
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hxy
    norm_num at hm
    have hnormalized : (y : ℝ) = -(x : ℝ) + 2 * (m : ℝ) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      apply mul_left_cancel₀ hpi
      linear_combination hm
    have hmLower : (0 : ℝ) ≤ (m : ℝ) := by
      linarith [x.property.1, y.property.1]
    have hmUpper : (m : ℝ) ≤ 1 := by
      linarith [x.property.2, y.property.2]
    have hmLowerInt : (0 : ℤ) ≤ m := by exact_mod_cast hmLower
    have hmUpperInt : m ≤ (1 : ℤ) := by exact_mod_cast hmUpper
    have hmCases : m = 0 ∨ m = 1 := by omega
    rcases hmCases with rfl | rfl
    · left
      norm_num at hnormalized
      have hx : (x : ℝ) = 0 := by linarith [x.property.1, y.property.1]
      have hy : (y : ℝ) = 0 := by linarith [x.property.1, y.property.1]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    · right
      norm_num at hnormalized
      have hx : (x : ℝ) = 1 := by linarith [x.property.2, y.property.2]
      have hy : (y : ℝ) = 1 := by linarith [x.property.2, y.property.2]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · rw [Circle.exp_eq_exp]
      refine ⟨1, ?_⟩
      norm_num
      ring

/-- Helper for Exercise 78.1: the half-circle by full-circle rectangle maps to the Klein
bottle. -/
noncomputable def kleinHalfFullMap (point : unitInterval × unitInterval) : KleinBottle :=
  KleinBottle.quotientMap (halfCircleCoordinate point.1, fullCircleCoordinate point.2)

/-- Helper for Exercise 78.1: the full-circle by half-circle cylinder maps to the Klein
bottle. -/
noncomputable def kleinFullHalfMap (point : unitInterval × unitInterval) : KleinBottle :=
  KleinBottle.quotientMap (fullCircleCoordinate point.1, halfCircleCoordinate point.2)

/-- Helper for Exercise 78.1: equality under the half-full rectangle is its ordinary or
reflected boundary relation. -/
theorem kleinHalfFullMap_eq_iff (p q : unitInterval × unitInterval) :
    kleinHalfFullMap p = kleinHalfFullMap q ↔
      (p.1 = q.1 ∧ unitInterval.endpointSetoid p.2 q.2) ∨
        (((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ q.1 = 0)) ∧
          unitInterval.endpointSetoid q.2 (unitInterval.symm p.2)) := by
  -- Normalize the two orbit branches coordinatewise.
  unfold kleinHalfFullMap
  rw [KleinBottle.quotientMap_eq_iff]
  simp only [KleinBottle.involution, Prod.mk.injEq]
  constructor
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · left
      exact ⟨(halfCircleCoordinate_injective hfirst).symm,
        (fullCircleCoordinate_eq_iff _ _).mp hsecond.symm⟩
    · right
      refine ⟨(halfCircleCoordinate_eq_neg_iff _ _).mp hfirst, ?_⟩
      rw [← fullCircleCoordinate_symm] at hsecond
      exact (fullCircleCoordinate_eq_iff _ _).mp hsecond
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · left
      exact ⟨congrArg halfCircleCoordinate hfirst.symm,
        ((fullCircleCoordinate_eq_iff p.2 q.2).mpr hsecond).symm⟩
    · right
      refine ⟨(halfCircleCoordinate_eq_neg_iff _ _).mpr hfirst, ?_⟩
      rw [← fullCircleCoordinate_symm]
      exact (fullCircleCoordinate_eq_iff _ _).mpr hsecond

/-- Helper for Exercise 78.1: equality under the full-half cylinder is its circular or
half-turn boundary relation. -/
theorem kleinFullHalfMap_eq_iff (p q : unitInterval × unitInterval) :
    kleinFullHalfMap p = kleinFullHalfMap q ↔
      (unitInterval.endpointSetoid p.1 q.1 ∧ p.2 = q.2) ∨
        (((p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)) ∧
          ((q.1 : ℝ) = p.1 + 1 / 2 ∨ (q.1 : ℝ) = p.1 - 1 / 2)) := by
  -- The ordinary orbit branch preserves height; the involution branch fixes an endpoint
  -- height and shifts the circular coordinate by a half-turn.
  unfold kleinFullHalfMap
  rw [KleinBottle.quotientMap_eq_iff]
  simp only [KleinBottle.involution, Prod.mk.injEq]
  constructor
  · rintro (⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩)
    · left
      exact ⟨(fullCircleCoordinate_eq_iff _ _).mp hfirst.symm,
        (halfCircleCoordinate_injective hsecond).symm⟩
    · right
      refine ⟨(halfCircleCoordinate_eq_inv_iff _ _).mp hsecond, ?_⟩
      unfold fullCircleCoordinate at hfirst
      rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk] at hfirst
      rw [← circleExp_add_pi] at hfirst
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hfirst
      norm_num at hm
      have hnormalized : (q.1 : ℝ) = (p.1 : ℝ) + 1 / 2 + (m : ℝ) := by
        nlinarith [hm, Real.pi_pos]
      have hmLower : (-2 : ℝ) < (m : ℝ) := by
        linarith [p.1.property.2, q.1.property.1]
      have hmUpper : (m : ℝ) < 1 := by
        linarith [p.1.property.1, q.1.property.2]
      have hmLowerInt : (-2 : ℤ) < m := by exact_mod_cast hmLower
      have hmUpperInt : m < (1 : ℤ) := by exact_mod_cast hmUpper
      have hmCases : m = -1 ∨ m = 0 := by omega
      rcases hmCases with rfl | rfl
      · right
        norm_num at hnormalized ⊢
        linarith
      · left
        norm_num at hnormalized ⊢
        linarith
  · rintro (⟨hfirst, hsecond⟩ | ⟨hheight, hshift⟩)
    · left
      exact ⟨((fullCircleCoordinate_eq_iff p.1 q.1).mpr hfirst).symm,
        congrArg halfCircleCoordinate hsecond.symm⟩
    · right
      refine ⟨?_, (halfCircleCoordinate_eq_inv_iff _ _).mpr hheight⟩
      unfold fullCircleCoordinate
      rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
      rw [← circleExp_add_pi]
      apply Circle.exp_eq_exp.mpr
      rcases hshift with hshift | hshift
      · refine ⟨0, ?_⟩
        norm_num
        nlinarith [hshift, Real.pi_pos]
      · refine ⟨-1, ?_⟩
        norm_num
        nlinarith [hshift, Real.pi_pos]

/-- Helper for Exercise 78.1: the Klein-bottle orbit projection is open and quotient. -/
theorem kleinBottle_isOpenQuotientMap : IsOpenQuotientMap KleinBottle.quotientMap := by
  -- The saturation of an open set is its union with the inverse image under the involution.
  have hinvolution : Continuous KleinBottle.involution := by
    unfold KleinBottle.involution
    fun_prop
  have hquot : Topology.IsQuotientMap
      (@Quotient.mk' (Circle × Circle) KleinBottle.identified) :=
    isQuotientMap_quotient_mk'
  refine IsOpenQuotientMap.of_isOpenMap_isQuotientMap ?_ hquot
  intro U hU
  rw [← hquot.isOpen_preimage]
  have hsaturation : KleinBottle.quotientMap ⁻¹' (KleinBottle.quotientMap '' U) =
      U ∪ KleinBottle.involution ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [KleinBottle.quotientMap_eq_iff] at hyx
      rcases hyx with rfl | hxy
      · exact Or.inl hy
      · apply Or.inr
        change KleinBottle.involution x ∈ U
        rw [hxy, KleinBottle.involution_involutive]
        exact hy
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · refine ⟨KleinBottle.involution x, hx, ?_⟩
        rw [KleinBottle.quotientMap_eq_iff]
        exact Or.inr (KleinBottle.involution_involutive x).symm
  have hopen : IsOpen
      (KleinBottle.quotientMap ⁻¹' (KleinBottle.quotientMap '' U)) := by
    rw [hsaturation]
    exact hU.union (hU.preimage hinvolution)
  have hmk : (@Quotient.mk' (Circle × Circle) KleinBottle.identified) =
      (@Quotient.mk'' (Circle × Circle) KleinBottle.identified) := rfl
  rw [hmk]
  simpa only [KleinBottle.quotientMap, ContinuousMap.coe_mk] using hopen

/-- Helper for Exercise 78.1: the standard quotient model of the Klein bottle is Hausdorff. -/
local instance kleinBottleT2Space : T2Space KleinBottle := by
  -- Its fiber relation is the closed union of the diagonal and the involution graph.
  apply (t2Space_iff_of_isOpenQuotientMap kleinBottle_isOpenQuotientMap).2
  have hfiber : {q : (Circle × Circle) × (Circle × Circle) |
      KleinBottle.quotientMap q.1 = KleinBottle.quotientMap q.2} =
      {q | q.2 = q.1} ∪ {q | q.2 = KleinBottle.involution q.1} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, KleinBottle.quotientMap_eq_iff]
  rw [hfiber]
  have hinvolution : Continuous KleinBottle.involution := by
    unfold KleinBottle.involution
    fun_prop
  exact (isClosed_eq continuous_snd continuous_fst).union
    (isClosed_eq continuous_snd (hinvolution.comp continuous_fst))

/-- Helper for Exercise 78.1: every circle point or its antipode occurs on the chosen
half-circle. -/
theorem halfCircleCoordinate_eq_or_eq_neg (z : Circle) :
    ∃ x : unitInterval, halfCircleCoordinate x = z ∨ halfCircleCoordinate x = -z := by
  -- Choose a representative in one period and split it at the midpoint.
  let angle : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm z
  obtain ⟨r, hr, hrangle⟩ := AddCircle.eq_coe_Ico angle
  by_cases hlower : r ≤ 1 / 2
  · have hxmem : 2 * r ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr.1], by linarith⟩
    let x : unitInterval := ⟨2 * r, hxmem⟩
    refine ⟨x, Or.inl ?_⟩
    rw [halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z]
    congr 1
    calc
      (((((x : unitInterval) : ℝ) / 2 : ℝ)) : UnitAddCircle) =
          (r : UnitAddCircle) := by
        have hreal : ((x : ℝ) / 2) = r := by
          simp only [x]
          ring
        exact congrArg (fun u : ℝ ↦ (u : UnitAddCircle)) hreal
      _ = angle := hrangle
      _ = (AddCircle.homeomorphCircle one_ne_zero).symm z := rfl
  · have hrhalf : 1 / 2 < r := lt_of_not_ge hlower
    have hxmem : 2 * r - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith, by linarith [hr.2]⟩
    let x : unitInterval := ⟨2 * r - 1, hxmem⟩
    refine ⟨x, Or.inr ?_⟩
    rw [halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z,
      AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
    change AddCircle.toCircle _ = -AddCircle.toCircle angle
    rw [AddCircle.toCircle_apply_mk, ← hrangle, AddCircle.toCircle_apply_mk]
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_neg, Circle.coe_exp]
    have hexponent :
        ((2 * Real.pi / 1 * (((x : unitInterval) : ℝ) / 2) : ℝ) : ℂ) * Complex.I =
          ((2 * Real.pi / 1 * r : ℝ) : ℂ) * Complex.I -
            (Real.pi : ℂ) * Complex.I := by
      simp only [x]
      push_cast
      ring
    rw [hexponent, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring

/-- Helper for Exercise 78.1: every circle point or its inverse occurs on the chosen
half-circle. -/
theorem halfCircleCoordinate_eq_or_eq_inv (z : Circle) :
    ∃ x : unitInterval,
      halfCircleCoordinate x = z ∨ halfCircleCoordinate x = Inv.inv z := by
  -- Choose a representative in one period; reflect representatives in the upper half.
  let angle : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm z
  obtain ⟨r, hr, hrangle⟩ := AddCircle.eq_coe_Ico angle
  by_cases hlower : r ≤ 1 / 2
  · have hxmem : 2 * r ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr.1], by linarith⟩
    let x : unitInterval := ⟨2 * r, hxmem⟩
    refine ⟨x, Or.inl ?_⟩
    rw [halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z]
    congr 1
    calc
      (((((x : unitInterval) : ℝ) / 2 : ℝ)) : UnitAddCircle) =
          (r : UnitAddCircle) := by
        have hreal : ((x : ℝ) / 2) = r := by
          simp only [x]
          ring
        exact congrArg (fun u : ℝ ↦ (u : UnitAddCircle)) hreal
      _ = angle := hrangle
      _ = (AddCircle.homeomorphCircle one_ne_zero).symm z := rfl
  · have hrhalf : 1 / 2 < r := lt_of_not_ge hlower
    have hxmem : 2 - 2 * r ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr.2], by linarith⟩
    let x : unitInterval := ⟨2 - 2 * r, hxmem⟩
    refine ⟨x, Or.inr ?_⟩
    rw [halfCircleCoordinate, ←
      (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z,
      AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply]
    change AddCircle.toCircle _ = Inv.inv (AddCircle.toCircle angle)
    rw [AddCircle.toCircle_apply_mk, ← hrangle, AddCircle.toCircle_apply_mk,
      ← Circle.exp_neg]
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, ?_⟩
    simp only [x]
    norm_num
    ring

/-- Helper for Exercise 78.1: the full-circle coordinate is surjective. -/
theorem fullCircleCoordinate_surjective : Function.Surjective fullCircleCoordinate := by
  -- Choose the standard representative of the inverse image in one period.
  intro z
  let angle : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm z
  obtain ⟨r, hr, hrangle⟩ := AddCircle.eq_coe_Ico angle
  let y : unitInterval := ⟨r, hr.1, hr.2.le⟩
  refine ⟨y, ?_⟩
  rw [fullCircleCoordinate, ←
    (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z]
  congr 1

/-- Helper for Exercise 78.1: the half-full Klein rectangle covers every orbit. -/
theorem kleinHalfFullMap_surjective : Function.Surjective kleinHalfFullMap := by
  -- Put a torus representative or its involute into the selected half-circle.
  intro z
  refine Quotient.inductionOn z ?_
  intro point
  obtain ⟨x, hx | hx⟩ := halfCircleCoordinate_eq_or_eq_neg point.1
  · obtain ⟨y, hy⟩ := fullCircleCoordinate_surjective point.2
    refine ⟨(x, y), ?_⟩
    unfold kleinHalfFullMap
    rw [hx, hy]
    change KleinBottle.quotientMap point = KleinBottle.quotientMap point
    rfl
  · obtain ⟨y, hy⟩ := fullCircleCoordinate_surjective point.2⁻¹
    refine ⟨(x, y), ?_⟩
    unfold kleinHalfFullMap
    rw [hx, hy]
    change KleinBottle.quotientMap (-point.1, point.2⁻¹) =
      KleinBottle.quotientMap point
    rw [KleinBottle.quotientMap_eq_iff]
    have horbit : point = KleinBottle.involution (-point.1, (point.2⁻¹ : Circle)) := by
      simp [KleinBottle.involution]
    exact Or.inr horbit

/-- Helper for Exercise 78.1: the half-full Klein rectangle map is continuous. -/
theorem continuous_kleinHalfFullMap : Continuous kleinHalfFullMap := by
  -- Compose the coordinate product with the continuous orbit projection.
  unfold kleinHalfFullMap
  exact KleinBottle.quotientMap.continuous.comp
    ((continuous_halfCircleCoordinate.comp continuous_fst).prodMk
      (continuous_fullCircleCoordinate.comp continuous_snd))

/-- Helper for Exercise 78.1: the half-full Klein rectangle is a quotient presentation. -/
theorem kleinHalfFullMap_isQuotientMap : Topology.IsQuotientMap kleinHalfFullMap := by
  -- Compactness and the Hausdorff target upgrade the continuous surjection.
  exact Topology.IsQuotientMap.of_surjective_continuous
    kleinHalfFullMap_surjective continuous_kleinHalfFullMap

/-- Helper for Exercise 78.1: the full-half Klein cylinder covers every orbit. -/
theorem kleinFullHalfMap_surjective : Function.Surjective kleinFullHalfMap := by
  -- Put the second circle coordinate, or its inverse, into the chosen half-circle.
  intro z
  refine Quotient.inductionOn z ?_
  intro point
  obtain ⟨y, hy | hy⟩ := halfCircleCoordinate_eq_or_eq_inv point.2
  · obtain ⟨x, hx⟩ := fullCircleCoordinate_surjective point.1
    refine ⟨(x, y), ?_⟩
    unfold kleinFullHalfMap
    rw [hx, hy]
    change KleinBottle.quotientMap point = KleinBottle.quotientMap point
    rfl
  · obtain ⟨x, hx⟩ := fullCircleCoordinate_surjective (-point.1)
    refine ⟨(x, y), ?_⟩
    unfold kleinFullHalfMap
    rw [hx, hy]
    change KleinBottle.quotientMap (-point.1, point.2⁻¹) =
      KleinBottle.quotientMap point
    rw [KleinBottle.quotientMap_eq_iff]
    have horbit : point = KleinBottle.involution (-point.1, (point.2⁻¹ : Circle)) := by
      simp [KleinBottle.involution]
    exact Or.inr horbit

/-- Helper for Exercise 78.1: the full-half Klein cylinder map is continuous. -/
theorem continuous_kleinFullHalfMap : Continuous kleinFullHalfMap := by
  -- Compose the coordinate product with the continuous orbit projection.
  unfold kleinFullHalfMap
  exact KleinBottle.quotientMap.continuous.comp
    ((continuous_fullCircleCoordinate.comp continuous_fst).prodMk
      (continuous_halfCircleCoordinate.comp continuous_snd))

/-- Helper for Exercise 78.1: the full-half Klein cylinder is a quotient presentation. -/
theorem kleinFullHalfMap_isQuotientMap : Topology.IsQuotientMap kleinFullHalfMap := by
  -- Compactness and the Hausdorff target upgrade the continuous surjection.
  exact Topology.IsQuotientMap.of_surjective_continuous
    kleinFullHalfMap_surjective continuous_kleinFullHalfMap

/-- Helper for Exercise 78.1: the first scheme-A affine formula lies in the unit square. -/
theorem schemeAFirstChart_mem (point : standardTriangle) :
    1 - point.1 0 / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      1 - point.1 0 - point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The triangle inequalities bound both affine coordinates.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  exact ⟨⟨by linarith [hpoint.1], by linarith [hpoint.1]⟩,
    ⟨by linarith [hpoint.2.2], by linarith [hpoint.1, hpoint.2.1]⟩⟩

/-- Helper for Exercise 78.1: the second scheme-A affine formula lies in the unit square. -/
theorem schemeASecondChart_mem (point : standardTriangle) :
    (1 + point.1 0) / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      1 - point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- Coordinate nonnegativity and the triangle upper bound give the two interval bounds.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  exact ⟨⟨by linarith [hpoint.1], by linarith [hpoint.2.2, hpoint.2.1]⟩,
    ⟨by linarith [hpoint.2.2, hpoint.1], by linarith [hpoint.2.1]⟩⟩

/-- Helper for Exercise 78.1: the third scheme-A affine formula lies in the unit square. -/
theorem schemeAThirdChart_mem (point : standardTriangle) :
    (point.1 0 + point.1 1) / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- Both coordinates are bounded by the defining triangle inequalities.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  exact ⟨⟨by linarith [hpoint.1, hpoint.2.1], by linarith [hpoint.2.2]⟩,
    ⟨hpoint.2.1, by linarith [hpoint.2.2, hpoint.1]⟩⟩

/-- Helper for Exercise 78.1: the fourth scheme-A affine formula lies in the unit square. -/
theorem schemeAFourthChart_mem (point : standardTriangle) :
    point.1 1 / 2 ∈ Set.Icc (0 : ℝ) 1 ∧
      point.1 0 + point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The same triangle inequalities bound the reflected left-hand chart.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  exact ⟨⟨by linarith [hpoint.2.1], by linarith [hpoint.2.2, hpoint.1]⟩,
    ⟨by linarith [hpoint.1, hpoint.2.1], hpoint.2.2⟩⟩

/-- Helper for Exercise 78.1: the first scheme-A triangle develops into the right-hand
square. -/
noncomputable def schemeAFirstChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨1 - point.1 0 / 2, (schemeAFirstChart_mem point).1⟩,
    ⟨1 - point.1 0 - point.1 1, (schemeAFirstChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the second scheme-A triangle develops into the right-hand
square. -/
noncomputable def schemeASecondChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨(1 + point.1 0) / 2, (schemeASecondChart_mem point).1⟩,
    ⟨1 - point.1 1, (schemeASecondChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the third scheme-A triangle develops into the left-hand
square. -/
noncomputable def schemeAThirdChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨(point.1 0 + point.1 1) / 2, (schemeAThirdChart_mem point).1⟩,
    ⟨point.1 1, (schemeAThirdChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the fourth scheme-A triangle develops into the left-hand
square. -/
noncomputable def schemeAFourthChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨point.1 1 / 2, (schemeAFourthChart_mem point).1⟩,
    ⟨point.1 0 + point.1 1, (schemeAFourthChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the normalized index selects its scheme-A affine chart. -/
noncomputable def schemeAChart : Fin 4 → standardTriangle → unitInterval × unitInterval
  | ⟨0, _⟩ => schemeAFirstChart
  | ⟨1, _⟩ => schemeASecondChart
  | ⟨2, _⟩ => schemeAThirdChart
  | ⟨3, _⟩ => schemeAFourthChart
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: every scheme-A affine chart is continuous. -/
theorem continuous_schemeAChart (i : Fin 4) : Continuous (schemeAChart i) := by
  -- Each branch is a pair of affine real-coordinate formulas with subtype witnesses.
  fin_cases i
  all_goals
    apply Continuous.prodMk
    · exact Continuous.subtype_mk (by fun_prop) _
    · exact Continuous.subtype_mk (by fun_prop) _

/-- Helper for Exercise 78.1: the scheme-A charts have the finite boundary table prescribed
by the displayed labels. -/
theorem schemeAChart_edge (region : Fin 4) (edge : Fin 3) (t : unitInterval) :
    (((schemeAChart region (TriangleDisk.edgePoint edge t)).1 : ℝ),
        ((schemeAChart region (TriangleDisk.edgePoint edge t)).2 : ℝ)) =
      match region, edge with
      | ⟨0, _⟩, ⟨0, _⟩ => (1 - (t : ℝ) / 2, 1 - t)
      | ⟨0, _⟩, ⟨1, _⟩ => ((1 + (t : ℝ)) / 2, 0)
      | ⟨0, _⟩, ⟨2, _⟩ => (1, (t : ℝ))
      | ⟨1, _⟩, ⟨0, _⟩ => ((1 + (t : ℝ)) / 2, 1)
      | ⟨1, _⟩, ⟨1, _⟩ => (1 - (t : ℝ) / 2, 1 - t)
      | ⟨1, _⟩, ⟨2, _⟩ => ((1 / 2 : ℝ), t)
      | ⟨2, _⟩, ⟨0, _⟩ => ((t : ℝ) / 2, 0)
      | ⟨2, _⟩, ⟨1, _⟩ => ((1 / 2 : ℝ), t)
      | ⟨2, _⟩, ⟨2, _⟩ => ((1 - (t : ℝ)) / 2, 1 - t)
      | ⟨3, _⟩, ⟨0, _⟩ => (0, (t : ℝ))
      | ⟨3, _⟩, ⟨1, _⟩ => ((t : ℝ) / 2, 1)
      | ⟨3, _⟩, ⟨2, _⟩ => ((1 - (t : ℝ)) / 2, 1 - t)
      | ⟨n + 4, h⟩, _ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim
      | _, ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim := by
  -- Evaluate the four affine formulas on the three standard boundary parametrizations.
  fin_cases region <;> fin_cases edge <;> apply Prod.ext <;>
    simp [schemeAChart, schemeAFirstChart, schemeASecondChart, schemeAThirdChart,
      schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
      unitInterval.coe_symm_eq] <;> ring

/-- Helper for Exercise 78.1: the four normalized scheme-A triangles develop into one square. -/
noncomputable def schemeADevelopment :
    (schemeA.triangularRegions schemeA_isTriangular).Source →
      unitInterval × unitInterval :=
  fun point ↦ schemeAChart (schemeAOccurrenceEquiv point.1) point.2

/-- Helper for Exercise 78.1: the scheme-A development computes on each normalized
occurrence. -/
theorem schemeADevelopment_schemeAOccurrence (i : Fin 4) (point : standardTriangle) :
    schemeADevelopment ⟨schemeAOccurrence i, point⟩ = schemeAChart i point := by
  -- Cancel the occurrence equivalence and evaluate the selected affine chart.
  fin_cases i <;> simp [schemeADevelopment, schemeAOccurrenceEquiv]

/-- Helper for Exercise 78.1: each affine chart in the scheme-A development is injective. -/
theorem schemeAChart_injective (i : Fin 4) : Function.Injective (schemeAChart i) := by
  -- In each of the four finite cases, recover the two triangle coordinates from the two
  -- affine square coordinates.
  fin_cases i
  all_goals
    intro point point' hpoints
    have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
    have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
    simp only [schemeAChart, schemeAFirstChart, schemeASecondChart,
      schemeAThirdChart, schemeAFourthChart] at hfirst hsecond
    have hzero : point.1 0 = point'.1 0 := by
      linarith
    have hone : point.1 1 = point'.1 1 := by
      linarith
    apply Subtype.ext
    ext coordinate
    fin_cases coordinate
    · exact hzero
    · exact hone

/-- Helper for Exercise 78.1: the first and second scheme-A charts meet along their two
occurrences of the edge labelled `a`. -/
theorem schemeAFirstSecond_eq_identified (point point' : standardTriangle)
    (hpoints : schemeAChart 0 point = schemeAChart 1 point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 0, point⟩ ⟨schemeAOccurrence 1, point'⟩ := by
  -- The affine equations force both points onto the common edge with parameter `point 0`.
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeAFirstChart, schemeASecondChart] at hfirst hsecond
  have htmem : point.1 0 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hpoint.1, (le_add_of_nonneg_right hpoint.2.1).trans hpoint.2.2⟩
  let t : unitInterval := ⟨point.1 0, htmem⟩
  have hpointEdge : point = TriangleDisk.edgePoint 0 t := by
    apply Subtype.ext
    ext coordinate
    fin_cases coordinate
    · simp [t, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
    · simp [t, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
  have hpoint'Edge : point' = TriangleDisk.edgePoint 1 t := by
    apply Subtype.ext
    ext coordinate
    fin_cases coordinate
    · simp [t, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
        unitInterval.coe_symm_eq]
      linarith
    · simp [t, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
  rw [hpointEdge, hpoint'Edge]
  have hlabel : (schemeAEdgeTable 0 0).1 = (schemeAEdgeTable 1 1).1 := by
    simp [schemeAEdgeTable]
  simpa [schemeAEdgeTable] using
    schemeANormalizedEdgePair_identified 0 1 0 1 t hlabel

/-- Helper for Exercise 78.1: the second and third scheme-A charts meet along their two
occurrences of the edge labelled `e`. -/
theorem schemeASecondThird_eq_identified (point point' : standardTriangle)
    (hpoints : schemeAChart 1 point = schemeAChart 2 point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 1, point⟩ ⟨schemeAOccurrence 2, point'⟩ := by
  -- Equality forces the first point onto edge two and the second onto edge one with the same
  -- reflected second-coordinate parameter.
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeASecondChart, schemeAThirdChart] at hfirst hsecond
  have hcoordMem : point.1 1 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hpoint.2.1, (le_add_of_nonneg_left hpoint.1).trans hpoint.2.2⟩
  let coordinate : unitInterval := ⟨point.1 1, hcoordMem⟩
  let t : unitInterval := unitInterval.symm coordinate
  have hpointEdge : point = TriangleDisk.edgePoint 2 t := by
    apply Subtype.ext
    ext index
    fin_cases index
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
  have hpoint'Edge : point' = TriangleDisk.edgePoint 1 t := by
    apply Subtype.ext
    ext index
    fin_cases index
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
  rw [hpointEdge, hpoint'Edge]
  have hlabel : (schemeAEdgeTable 1 2).1 = (schemeAEdgeTable 2 1).1 := by
    simp [schemeAEdgeTable]
  simpa [schemeAEdgeTable] using
    schemeANormalizedEdgePair_identified 1 2 2 1 t hlabel

/-- Helper for Exercise 78.1: the third and fourth scheme-A charts meet along their two
occurrences of the edge labelled `f`. -/
theorem schemeAThirdFourth_eq_identified (point point' : standardTriangle)
    (hpoints : schemeAChart 2 point = schemeAChart 3 point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 2, point⟩ ⟨schemeAOccurrence 3, point'⟩ := by
  -- The common affine image forces both triangle points onto edge two with one parameter.
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeAThirdChart, schemeAFourthChart] at hfirst hsecond
  have hcoordMem : point.1 1 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hpoint.2.1, (le_add_of_nonneg_left hpoint.1).trans hpoint.2.2⟩
  let coordinate : unitInterval := ⟨point.1 1, hcoordMem⟩
  let t : unitInterval := unitInterval.symm coordinate
  have hpointEdge : point = TriangleDisk.edgePoint 2 t := by
    apply Subtype.ext
    ext index
    fin_cases index
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
  have hpoint'Edge : point' = TriangleDisk.edgePoint 2 t := by
    apply Subtype.ext
    ext index
    fin_cases index
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
    · simp [t, coordinate, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      linarith
  rw [hpointEdge, hpoint'Edge]
  have hlabel : (schemeAEdgeTable 2 2).1 = (schemeAEdgeTable 3 2).1 := by
    simp [schemeAEdgeTable]
  simpa [schemeAEdgeTable] using
    schemeANormalizedEdgePair_identified 2 3 2 2 t hlabel

/-- Helper for Exercise 78.1: an equality between the first and third scheme-A charts occurs
at their shared developed vertex and is connected by the `a` and `e` seams. -/
theorem schemeAFirstThird_eq_identified (point point' : standardTriangle)
    (hpoints : schemeAChart 0 point = schemeAChart 2 point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 0, point⟩ ⟨schemeAOccurrence 2, point'⟩ := by
  -- The first coordinate lies in opposite half-squares, so equality pins both points to the
  -- unique intervening vertex.
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeAFirstChart, schemeAThirdChart] at hfirst hsecond
  have hpointEdge : point = TriangleDisk.edgePoint 0 1 := by
    apply Subtype.ext
    ext index
    fin_cases index <;>
      simp [TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] <;> linarith
  have hpoint'Edge : point' = TriangleDisk.edgePoint 1 0 := by
    apply Subtype.ext
    ext index
    fin_cases index <;>
      simp [TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] <;> linarith
  rw [hpointEdge, hpoint'Edge]
  have haLabel : (schemeAEdgeTable 0 0).1 = (schemeAEdgeTable 1 1).1 := by
    simp [schemeAEdgeTable]
  have heLabel : (schemeAEdgeTable 1 2).1 = (schemeAEdgeTable 2 1).1 := by
    simp [schemeAEdgeTable]
  have ha := schemeANormalizedEdgePair_identified 0 1 0 1 1 haLabel
  have he := schemeANormalizedEdgePair_identified 1 2 2 1 0 heLabel
  have haAtVertex : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 0, TriangleDisk.edgePoint 0 1⟩
      ⟨schemeAOccurrence 1, TriangleDisk.edgePoint 2 0⟩ := by
    simpa [schemeAEdgeTable, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using ha
  have heAtVertex : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 1, TriangleDisk.edgePoint 2 0⟩
      ⟨schemeAOccurrence 2, TriangleDisk.edgePoint 1 0⟩ := by
    simpa [schemeAEdgeTable, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using he
  exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
    haAtVertex heAtVertex

/-- Helper for Exercise 78.1: an equality between the second and fourth scheme-A charts
occurs at their shared developed vertex and is connected by the `e` and `f` seams. -/
theorem schemeASecondFourth_eq_identified (point point' : standardTriangle)
    (hpoints : schemeAChart 1 point = schemeAChart 3 point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 1, point⟩ ⟨schemeAOccurrence 3, point'⟩ := by
  -- Opposite half-square bounds again reduce the overlap to one vertex, now chained through
  -- the middle two triangles.
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeASecondChart, schemeAFourthChart] at hfirst hsecond
  have hpointEdge : point = TriangleDisk.edgePoint 2 1 := by
    apply Subtype.ext
    ext index
    fin_cases index <;>
      simp [TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] <;> linarith
  have hpoint'Edge : point' = TriangleDisk.edgePoint 2 0 := by
    apply Subtype.ext
    ext index
    fin_cases index <;>
      simp [TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] <;> linarith
  rw [hpointEdge, hpoint'Edge]
  have heLabel : (schemeAEdgeTable 1 2).1 = (schemeAEdgeTable 2 1).1 := by
    simp [schemeAEdgeTable]
  have hfLabel : (schemeAEdgeTable 2 2).1 = (schemeAEdgeTable 3 2).1 := by
    simp [schemeAEdgeTable]
  have he := schemeANormalizedEdgePair_identified 1 2 2 1 1 heLabel
  have hf := schemeANormalizedEdgePair_identified 2 3 2 2 0 hfLabel
  have heAtVertex : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 1, TriangleDisk.edgePoint 2 1⟩
      ⟨schemeAOccurrence 2, TriangleDisk.edgePoint 2 0⟩ := by
    simpa [schemeAEdgeTable, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using he
  have hfAtVertex : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence 2, TriangleDisk.edgePoint 2 0⟩
      ⟨schemeAOccurrence 3, TriangleDisk.edgePoint 2 0⟩ := by
    simpa [schemeAEdgeTable, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using hf
  exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
    heAtVertex hfAtVertex

/-- Helper for Exercise 78.1: the first and fourth scheme-A chart images are disjoint. -/
theorem schemeAFirstFourth_ne (point point' : standardTriangle) :
    schemeAChart 0 point ≠ schemeAChart 3 point' := by
  -- Their horizontal half-square bounds could meet only at one half, but their vertical
  -- coordinates would then be zero and one respectively.
  intro hpoints
  have hpoint := point.property
  have hpoint' := point'.property
  rw [mem_standardTriangle] at hpoint hpoint'
  have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
  simp only [schemeAChart, schemeAFirstChart, schemeAFourthChart] at hfirst hsecond
  linarith

/-- Helper for Exercise 78.1: equality of scheme-A chart images implies the corresponding
labelled identification. -/
theorem schemeAChart_eq_identified (i k : Fin 4) (point point' : standardTriangle)
    (hpoints : schemeAChart i point = schemeAChart k point') :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r
      ⟨schemeAOccurrence i, point⟩ ⟨schemeAOccurrence k, point'⟩ := by
  -- Dispatch the finite chart pair to injectivity, one seam, or one of the two vertex chains;
  -- reverse-order cases use symmetry of the generated setoid.
  fin_cases i <;> fin_cases k
  · have hpoint : point = point' := schemeAChart_injective 0 hpoints
    subst point'
    exact (schemeA.triangularRegions schemeA_isTriangular).Identified.refl' _
  · exact schemeAFirstSecond_eq_identified point point' hpoints
  · exact schemeAFirstThird_eq_identified point point' hpoints
  · exact (schemeAFirstFourth_ne point point' hpoints).elim
  · exact (schemeA.triangularRegions schemeA_isTriangular).Identified.symm'
      (schemeAFirstSecond_eq_identified point' point hpoints.symm)
  · have hpoint : point = point' := schemeAChart_injective 1 hpoints
    subst point'
    exact (schemeA.triangularRegions schemeA_isTriangular).Identified.refl' _
  · exact schemeASecondThird_eq_identified point point' hpoints
  · exact schemeASecondFourth_eq_identified point point' hpoints
  · exact (schemeA.triangularRegions schemeA_isTriangular).Identified.symm'
      (schemeAFirstThird_eq_identified point' point hpoints.symm)
  · exact (schemeA.triangularRegions schemeA_isTriangular).Identified.symm'
      (schemeASecondThird_eq_identified point' point hpoints.symm)
  · have hpoint : point = point' := schemeAChart_injective 2 hpoints
    subst point'
    exact (schemeA.triangularRegions schemeA_isTriangular).Identified.refl' _
  · exact schemeAThirdFourth_eq_identified point point' hpoints
  · exact (schemeAFirstFourth_ne point' point hpoints.symm).elim
  · exact (schemeA.triangularRegions schemeA_isTriangular).Identified.symm'
      (schemeASecondFourth_eq_identified point' point hpoints.symm)
  · exact (schemeA.triangularRegions schemeA_isTriangular).Identified.symm'
      (schemeAThirdFourth_eq_identified point' point hpoints.symm)
  · have hpoint : point = point' := schemeAChart_injective 3 hpoints
    subst point'
    exact (schemeA.triangularRegions schemeA_isTriangular).Identified.refl' _

/-- Helper for Exercise 78.1: equality in the scheme-A square development already gives a
labelled identification. -/
theorem schemeADevelopment_eq_identified
    (x y : (schemeA.triangularRegions schemeA_isTriangular).Source)
    (hxy : schemeADevelopment x = schemeADevelopment y) :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r x y := by
  -- Normalize both source occurrences to the finite chart table and apply its complete kernel
  -- classification.
  rcases x with ⟨region, point⟩
  rcases y with ⟨region', point'⟩
  obtain ⟨i, rfl⟩ := schemeAOccurrence_surjective region
  obtain ⟨k, rfl⟩ := schemeAOccurrence_surjective region'
  rw [schemeADevelopment_schemeAOccurrence,
    schemeADevelopment_schemeAOccurrence] at hxy
  exact schemeAChart_eq_identified i k point point' hxy

/-- Helper for Exercise 78.1: the scheme-A square development is continuous. -/
theorem continuous_schemeADevelopment : Continuous schemeADevelopment := by
  -- Continuity on the disjoint union is continuity on each normalized occurrence summand.
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  letI : TopologicalSpace
      ((schemeA.triangularRegions schemeA_isTriangular).Point region) :=
    (schemeA.triangularRegions schemeA_isTriangular).topology region
  change Continuous (schemeAChart (schemeAOccurrenceEquiv region))
  exact continuous_schemeAChart (schemeAOccurrenceEquiv region)

/-- Helper for Exercise 78.1: the four scheme-A charts cover the unit square. -/
theorem schemeADevelopment_surjective : Function.Surjective schemeADevelopment := by
  intro point
  by_cases hleft : (point.1 : ℝ) ≤ 1 / 2
  · by_cases hlower : (point.2 : ℝ) ≤ 2 * point.1
    · let coordinates : EuclideanSpace ℝ (Fin 2) :=
        !₂[2 * (point.1 : ℝ) - point.2, point.2]
      have coordinates_mem : coordinates ∈ standardTriangle := by
        rw [mem_standardTriangle]
        simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact ⟨by linarith, point.2.property.1, by linarith⟩
      refine ⟨⟨schemeAOccurrence 2, ⟨coordinates, coordinates_mem⟩⟩, ?_⟩
      -- In the lower-left half, invert the third affine chart.
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [schemeADevelopment, schemeAChart, schemeAThirdChart, coordinates,
          schemeAOccurrenceEquiv]
    · have hupper : 2 * (point.1 : ℝ) ≤ point.2 := le_of_not_ge hlower
      let coordinates : EuclideanSpace ℝ (Fin 2) :=
        !₂[(point.2 : ℝ) - 2 * point.1, 2 * point.1]
      have coordinates_mem : coordinates ∈ standardTriangle := by
        rw [mem_standardTriangle]
        simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact ⟨by linarith, by linarith [point.1.property.1],
          by linarith [point.2.property.2]⟩
      refine ⟨⟨schemeAOccurrence 3, ⟨coordinates, coordinates_mem⟩⟩, ?_⟩
      -- In the upper-left half, invert the fourth affine chart.
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [schemeADevelopment, schemeAChart, schemeAFourthChart, coordinates,
          schemeAOccurrenceEquiv]
  · have hright : 1 / 2 ≤ (point.1 : ℝ) := le_of_not_ge hleft
    by_cases hlower : (point.2 : ℝ) ≤ 2 * point.1 - 1
    · let coordinates : EuclideanSpace ℝ (Fin 2) :=
        !₂[2 - 2 * (point.1 : ℝ), 2 * point.1 - point.2 - 1]
      have coordinates_mem : coordinates ∈ standardTriangle := by
        rw [mem_standardTriangle]
        simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact ⟨by linarith [point.1.property.2], by linarith,
          by linarith [point.2.property.1]⟩
      refine ⟨⟨schemeAOccurrence 0, ⟨coordinates, coordinates_mem⟩⟩, ?_⟩
      -- In the lower-right half, invert the first affine chart.
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [schemeADevelopment, schemeAChart, schemeAFirstChart, coordinates,
          schemeAOccurrenceEquiv] <;> ring
    · have hupper : 2 * (point.1 : ℝ) - 1 ≤ point.2 := le_of_not_ge hlower
      let coordinates : EuclideanSpace ℝ (Fin 2) :=
        !₂[2 * (point.1 : ℝ) - 1, 1 - point.2]
      have coordinates_mem : coordinates ∈ standardTriangle := by
        rw [mem_standardTriangle]
        simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact ⟨by linarith, by linarith [point.2.property.2], by linarith⟩
      refine ⟨⟨schemeAOccurrence 1, ⟨coordinates, coordinates_mem⟩⟩, ?_⟩
      -- In the upper-right half, invert the second affine chart.
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [schemeADevelopment, schemeAChart, schemeASecondChart, coordinates,
          schemeAOccurrenceEquiv]

/-- Helper for Exercise 78.1: the second torus triangle is reflected across the square's
anti-diagonal. -/
def schemeBTorusSecondChart (point : standardTriangle) : unitInterval × unitInterval :=
  (unitInterval.symm (upperTriangleChart point).2,
    unitInterval.symm (upperTriangleChart point).1)

/-- Helper for Exercise 78.1: the first Klein triangle is rotated into the half-square below
the anti-diagonal. -/
def schemeBKleinFirstChart (point : standardTriangle) : unitInterval × unitInterval :=
  (unitInterval.symm (upperTriangleChart point).2, (upperTriangleChart point).1)

/-- Helper for Exercise 78.1: the second Klein triangle is reflected into the half-square above
the anti-diagonal. -/
def schemeBKleinSecondChart (point : standardTriangle) : unitInterval × unitInterval :=
  (unitInterval.symm (upperTriangleChart point).1, (upperTriangleChart point).2)

/-- Helper for Exercise 78.1: the reflected second torus chart is continuous. -/
theorem continuous_schemeBTorusSecondChart : Continuous schemeBTorusSecondChart := by
  -- Compose the two upper-chart projections with the interval reflection.
  exact (unitInterval.continuous_symm.comp
      (continuous_snd.comp continuous_upperTriangleChart)).prodMk
    (unitInterval.continuous_symm.comp
      (continuous_fst.comp continuous_upperTriangleChart))

/-- Helper for Exercise 78.1: the rotated first Klein chart is continuous. -/
theorem continuous_schemeBKleinFirstChart : Continuous schemeBKleinFirstChart := by
  -- Only the second upper-chart coordinate is reflected.
  exact (unitInterval.continuous_symm.comp
      (continuous_snd.comp continuous_upperTriangleChart)).prodMk
    (continuous_fst.comp continuous_upperTriangleChart)

/-- Helper for Exercise 78.1: the reflected second Klein chart is continuous. -/
theorem continuous_schemeBKleinSecondChart : Continuous schemeBKleinSecondChart := by
  -- Only the first upper-chart coordinate is reflected.
  exact (unitInterval.continuous_symm.comp
      (continuous_fst.comp continuous_upperTriangleChart)).prodMk
    (continuous_snd.comp continuous_upperTriangleChart)

/-- Helper for Exercise 78.1: the reflected torus chart has the normalized formulas on all
three triangle edges. -/
theorem schemeBTorusSecondChart_edge (edge : Fin 3) (t : unitInterval) :
    schemeBTorusSecondChart (TriangleDisk.edgePoint edge t) =
      match edge with
      | ⟨0, _⟩ => (unitInterval.symm t, unitInterval.symm t)
      | ⟨1, _⟩ => (0, t)
      | ⟨2, _⟩ => (t, 1)
      | ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim := by
  -- Evaluate the affine chart and interval reflections edge by edge.
  fin_cases edge <;> apply Prod.ext <;> apply Subtype.ext <;>
    simp [schemeBTorusSecondChart, upperTriangleChart, TriangleDisk.edgePoint,
      TriangleDisk.edgeCoordinates, unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the first Klein chart has the normalized formulas on all three
triangle edges. -/
theorem schemeBKleinFirstChart_edge (edge : Fin 3) (t : unitInterval) :
    schemeBKleinFirstChart (TriangleDisk.edgePoint edge t) =
      match edge with
      | ⟨0, _⟩ => (unitInterval.symm t, t)
      | ⟨1, _⟩ => (0, unitInterval.symm t)
      | ⟨2, _⟩ => (t, 0)
      | ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim := by
  -- Evaluate the quarter-turn of the upper chart on each boundary edge.
  fin_cases edge <;> apply Prod.ext <;> apply Subtype.ext <;>
    simp [schemeBKleinFirstChart, upperTriangleChart, TriangleDisk.edgePoint,
      TriangleDisk.edgeCoordinates, unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the second Klein chart has the normalized formulas on all three
triangle edges. -/
theorem schemeBKleinSecondChart_edge (edge : Fin 3) (t : unitInterval) :
    schemeBKleinSecondChart (TriangleDisk.edgePoint edge t) =
      match edge with
      | ⟨0, _⟩ => (unitInterval.symm t, t)
      | ⟨1, _⟩ => (t, 1)
      | ⟨2, _⟩ => (1, unitInterval.symm t)
      | ⟨n + 3, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 3 n) h).elim := by
  -- Evaluate the horizontal reflection of the upper chart on each boundary edge.
  fin_cases edge <;> apply Prod.ext <;> apply Subtype.ext <;>
    simp [schemeBKleinSecondChart, upperTriangleChart, TriangleDisk.edgePoint,
      TriangleDisk.edgeCoordinates, unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the first two scheme-B triangles cover the torus fundamental
square through their affine charts. -/
def schemeBTorusPairToSquare : standardTriangle ⊕ standardTriangle →
    unitInterval × unitInterval :=
  Sum.elim lowerTriangleChart schemeBTorusSecondChart

/-- Helper for Exercise 78.1: the last two scheme-B triangles cover the Klein fundamental
square through their affine charts. -/
def schemeBKleinPairToSquare : standardTriangle ⊕ standardTriangle →
    unitInterval × unitInterval :=
  Sum.elim schemeBKleinFirstChart schemeBKleinSecondChart

/-- Helper for Exercise 78.1: the torus chart-pair map is continuous. -/
theorem continuous_schemeBTorusPairToSquare : Continuous schemeBTorusPairToSquare := by
  -- Continuity out of the tagged pair is continuity of its two branches.
  exact continuous_lowerTriangleChart.sumElim continuous_schemeBTorusSecondChart

/-- Helper for Exercise 78.1: the Klein chart-pair map is continuous. -/
theorem continuous_schemeBKleinPairToSquare : Continuous schemeBKleinPairToSquare := by
  -- Continuity out of the tagged pair is continuity of its two branches.
  exact continuous_schemeBKleinFirstChart.sumElim continuous_schemeBKleinSecondChart

/-- Helper for Exercise 78.1: the torus chart pair covers the entire unit square. -/
theorem schemeBTorusPairToSquare_surjective :
    Function.Surjective schemeBTorusPairToSquare := by
  intro point
  by_cases hlower : point.2 ≤ point.1
  · let coordinates : EuclideanSpace ℝ (Fin 2) :=
      !₂[(point.1 : ℝ) - point.2, point.2]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨sub_nonneg.mpr hlower, point.2.property.1, by linarith [point.1.property.2]⟩
    refine ⟨Sum.inl ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- In the lower half, subtract the second coordinate to invert the lower chart.
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [schemeBTorusPairToSquare, lowerTriangleChart, coordinates]
  · have hupper : point.1 ≤ point.2 := le_of_not_ge hlower
    let coordinates : EuclideanSpace ℝ (Fin 2) :=
      !₂[1 - (point.2 : ℝ), (point.2 : ℝ) - point.1]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨by linarith [point.2.property.2], sub_nonneg.mpr hupper,
        by linarith [point.1.property.1]⟩
    refine ⟨Sum.inr ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- In the upper half, invert the reflected upper chart explicitly.
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [schemeBTorusPairToSquare, schemeBTorusSecondChart, upperTriangleChart,
        coordinates, unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the Klein chart pair covers the entire unit square. -/
theorem schemeBKleinPairToSquare_surjective :
    Function.Surjective schemeBKleinPairToSquare := by
  intro point
  by_cases hlower : (point.1 : ℝ) + point.2 ≤ 1
  · let coordinates : EuclideanSpace ℝ (Fin 2) :=
      !₂[(point.2 : ℝ), 1 - point.1 - point.2]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨point.2.property.1, by linarith, by linarith [point.1.property.1]⟩
    refine ⟨Sum.inl ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- Below the anti-diagonal, invert the quarter-turned upper chart.
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [schemeBKleinPairToSquare, schemeBKleinFirstChart, upperTriangleChart,
        coordinates, unitInterval.coe_symm_eq]
  · have hupper : 1 ≤ (point.1 : ℝ) + point.2 := le_of_not_ge hlower
    let coordinates : EuclideanSpace ℝ (Fin 2) :=
      !₂[1 - (point.1 : ℝ), (point.1 : ℝ) + point.2 - 1]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨by linarith [point.1.property.2], by linarith,
        by linarith [point.2.property.2]⟩
    refine ⟨Sum.inr ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- Above the anti-diagonal, invert the horizontally reflected upper chart.
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [schemeBKleinPairToSquare, schemeBKleinSecondChart, upperTriangleChart,
        coordinates, unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the reflected second torus chart is injective. -/
theorem schemeBTorusSecondChart_injective : Function.Injective schemeBTorusSecondChart := by
  -- Undo the two interval reflections and then use upper-chart injectivity.
  intro point point' hpoints
  apply upperTriangleChart_injective
  apply Prod.ext
  · have hsecond := congrArg (fun square ↦ unitInterval.symm square.2) hpoints
    simpa [schemeBTorusSecondChart] using hsecond
  · have hfirst := congrArg (fun square ↦ unitInterval.symm square.1) hpoints
    simpa [schemeBTorusSecondChart] using hfirst

/-- Helper for Exercise 78.1: the two torus charts overlap exactly on their common `c` edge. -/
theorem lowerTriangleChart_eq_schemeBTorusSecondChart_iff
    (point point' : standardTriangle) :
    lowerTriangleChart point = schemeBTorusSecondChart point' ↔
      ∃ t : unitInterval,
        point = TriangleDisk.edgePoint 2 t ∧ point' = TriangleDisk.edgePoint 0 t := by
  constructor
  · intro hpoints
    have hpoint := point.property
    have hpoint' := point'.property
    rw [mem_standardTriangle] at hpoint hpoint'
    let t : unitInterval := (upperTriangleChart point').1
    refine ⟨t, ?_, ?_⟩
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [lowerTriangleChart, schemeBTorusSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] at hfirst hsecond ⊢
        linarith [hpoint.1, hpoint'.2.1]
      · have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simpa [lowerTriangleChart, schemeBTorusSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] using hsecond
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · simp [t, upperTriangleChart, TriangleDisk.edgePoint,
          TriangleDisk.edgeCoordinates]
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [lowerTriangleChart, schemeBTorusSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] at hfirst hsecond ⊢
        linarith [hpoint.1, hpoint'.2.1]
  · rintro ⟨t, rfl, rfl⟩
    -- The two explicit edge formulas coincide pointwise.
    rw [lowerTriangleChart_edge_two, schemeBTorusSecondChart_edge]

/-- Helper for Exercise 78.1: the first Klein chart is injective. -/
theorem schemeBKleinFirstChart_injective : Function.Injective schemeBKleinFirstChart := by
  -- Undo the reflected coordinate and use upper-chart injectivity.
  intro point point' hpoints
  apply upperTriangleChart_injective
  apply Prod.ext
  · exact congrArg Prod.snd hpoints
  · have hfirst := congrArg (fun square ↦ unitInterval.symm square.1) hpoints
    simpa [schemeBKleinFirstChart] using hfirst

/-- Helper for Exercise 78.1: the second Klein chart is injective. -/
theorem schemeBKleinSecondChart_injective : Function.Injective schemeBKleinSecondChart := by
  -- Undo the reflected coordinate and use upper-chart injectivity.
  intro point point' hpoints
  apply upperTriangleChart_injective
  apply Prod.ext
  · have hfirst := congrArg (fun square ↦ unitInterval.symm square.1) hpoints
    simpa [schemeBKleinSecondChart] using hfirst
  · simpa [schemeBKleinSecondChart] using congrArg Prod.snd hpoints

/-- Helper for Exercise 78.1: the two Klein charts overlap exactly on their common `d` edge. -/
theorem schemeBKleinFirstChart_eq_second_iff (point point' : standardTriangle) :
    schemeBKleinFirstChart point = schemeBKleinSecondChart point' ↔
      ∃ t : unitInterval,
        point = TriangleDisk.edgePoint 0 t ∧ point' = TriangleDisk.edgePoint 0 t := by
  constructor
  · intro hpoints
    have hpoint := point.property
    have hpoint' := point'.property
    rw [mem_standardTriangle] at hpoint hpoint'
    let t : unitInterval := (upperTriangleChart point).1
    refine ⟨t, ?_, ?_⟩
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · simp [t, upperTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [schemeBKleinFirstChart, schemeBKleinSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] at hfirst hsecond ⊢
        linarith [hpoint.2.1, hpoint'.2.1]
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [schemeBKleinFirstChart, schemeBKleinSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] at hfirst hsecond ⊢
        linarith [hpoint.2.1, hpoint'.2.1]
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [schemeBKleinFirstChart, schemeBKleinSecondChart, upperTriangleChart, t,
          TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates,
          unitInterval.coe_symm_eq] at hfirst hsecond ⊢
        linarith [hpoint.2.1, hpoint'.2.1]
  · rintro ⟨t, rfl, rfl⟩
    -- Both charts have the same normalized formula on edge zero.
    rw [schemeBKleinFirstChart_edge, schemeBKleinSecondChart_edge]

/-- Helper for Exercise 78.1: a normalized scheme-B occurrence selects its component square
chart. -/
def schemeBChart : Fin 4 → standardTriangle →
    (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval)
  | ⟨0, _⟩ => fun point ↦ Sum.inl (lowerTriangleChart point)
  | ⟨1, _⟩ => fun point ↦ Sum.inl (schemeBTorusSecondChart point)
  | ⟨2, _⟩ => fun point ↦ Sum.inr (schemeBKleinFirstChart point)
  | ⟨3, _⟩ => fun point ↦ Sum.inr (schemeBKleinSecondChart point)
  | ⟨n + 4, h⟩ => (Nat.not_lt_of_ge (Nat.le_add_left 4 n) h).elim

/-- Helper for Exercise 78.1: every normalized scheme-B component chart is continuous. -/
theorem continuous_schemeBChart (i : Fin 4) : Continuous (schemeBChart i) := by
  -- The four cases are continuous affine charts followed by a sum inclusion.
  fin_cases i
  · exact continuous_inl.comp continuous_lowerTriangleChart
  · exact continuous_inl.comp continuous_schemeBTorusSecondChart
  · exact continuous_inr.comp continuous_schemeBKleinFirstChart
  · exact continuous_inr.comp continuous_schemeBKleinSecondChart

/-- Helper for Exercise 78.1: scheme B develops its first pair of triangles to the torus
square and its second pair to the Klein square. -/
noncomputable def schemeBDevelopment :
    (schemeB.triangularRegions schemeB_isTriangular).Source →
      (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval) :=
  fun point ↦ schemeBChart (schemeBOccurrenceEquiv point.1) point.2

/-- Helper for Exercise 78.1: the scheme-B development computes by its four normalized
occurrences. -/
theorem schemeBDevelopment_schemeBOccurrence (i : Fin 4) (point : standardTriangle) :
    schemeBDevelopment ⟨schemeBOccurrence i, point⟩ = schemeBChart i point := by
  -- Cancel the occurrence equivalence and evaluate the selected branch.
  fin_cases i <;> simp [schemeBDevelopment, schemeBOccurrenceEquiv]

/-- Helper for Exercise 78.1: the internal scheme-B seams are precisely the `c` and `d`
edge pairings. -/
def schemeBInternalRelated
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source) : Prop :=
  (schemeB.triangularRegions schemeB_isTriangular).EdgeRelatedAt 2 x y ∨
    (schemeB.triangularRegions schemeB_isTriangular).EdgeRelatedAt 3 x y

/-- Helper for Exercise 78.1: the two normalized `c` edges form a direct internal seam. -/
theorem schemeBCSeamRelated (t : unitInterval) :
    schemeBInternalRelated
      ⟨schemeBOccurrence 0, TriangleDisk.edgePoint 2 t⟩
      ⟨schemeBOccurrence 1, TriangleDisk.edgePoint 0 t⟩ := by
  -- Choose the two positive occurrences of label `c` in the finite edge table.
  left
  refine ⟨schemeBOccurrence 0, schemeBOccurrence 1,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence 0)).symm 2,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence 1)).symm 0,
    t, ?_, ?_, ?_, ?_⟩
  · simpa [schemeBEdgeTable] using congrArg Prod.fst (schemeB_edgeLetter 0 2)
  · simpa [schemeBEdgeTable] using congrArg Prod.fst (schemeB_edgeLetter 1 0)
  · simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast,
      Fin.cast_eq_self]
  · have hsign0 := congrArg Prod.snd (schemeB_edgeLetter 0 2)
    have hsign1 := congrArg Prod.snd (schemeB_edgeLetter 1 0)
    simp only [schemeBEdgeTable] at hsign0 hsign1
    rw [if_pos (hsign0.trans hsign1.symm)]
    simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast,
      Fin.cast_eq_self]

/-- Helper for Exercise 78.1: the two normalized `d` edges form a direct internal seam. -/
theorem schemeBDSeamRelated (t : unitInterval) :
    schemeBInternalRelated
      ⟨schemeBOccurrence 2, TriangleDisk.edgePoint 0 t⟩
      ⟨schemeBOccurrence 3, TriangleDisk.edgePoint 0 t⟩ := by
  -- Choose the two positive occurrences of label `d` in the finite edge table.
  right
  refine ⟨schemeBOccurrence 2, schemeBOccurrence 3,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence 2)).symm 0,
    Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence 3)).symm 0,
    t, ?_, ?_, ?_, ?_⟩
  · simpa [schemeBEdgeTable] using congrArg Prod.fst (schemeB_edgeLetter 2 0)
  · simpa [schemeBEdgeTable] using congrArg Prod.fst (schemeB_edgeLetter 3 0)
  · simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast,
      Fin.cast_eq_self]
  · have hsign2 := congrArg Prod.snd (schemeB_edgeLetter 2 0)
    have hsign3 := congrArg Prod.snd (schemeB_edgeLetter 3 0)
    simp only [schemeBEdgeTable] at hsign2 hsign3
    rw [if_pos (hsign2.trans hsign3.symm)]
    simp only [LabellingScheme.triangularRegions_edge, Fin.cast_cast,
      Fin.cast_eq_self]

/-- Helper for Exercise 78.1: every occurrence of an internal scheme-B label has positive
orientation. -/
theorem schemeBInternalLabel_positive (i : Fin 4) (j : Fin 3)
    (hlabel : (schemeBEdgeTable i j).1 = 2 ∨
      (schemeBEdgeTable i j).1 = 3) :
    (schemeBEdgeTable i j).2 = true := by
  -- The finite table shows that the two internal labels `c` and `d` are never reversed.
  fin_cases i <;> fin_cases j <;> simp [schemeBEdgeTable] at hlabel ⊢

/-- Helper for Exercise 78.1: each direct internal scheme-B seam has equal development
image. -/
theorem schemeBInternalRelated_mapsEqual
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : schemeBInternalRelated x y) :
    schemeBDevelopment x = schemeBDevelopment y := by
  -- Normalize the two occurrences and dependent edge indices to the finite edge table.
  rcases hxy with hxy | hxy
  all_goals
    rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel₁, hlabel₂, rfl, rfl⟩
    obtain ⟨i, rfl⟩ := schemeBOccurrence_surjective region₁
    obtain ⟨k, rfl⟩ := schemeBOccurrence_surjective region₂
    let j : Fin 3 := Fin.cast
      (schemeB_isTriangular.region_length (schemeBOccurrence i)) edge₁
    let l : Fin 3 := Fin.cast
      (schemeB_isTriangular.region_length (schemeBOccurrence k)) edge₂
    have hedge₁ : edge₁ = Fin.cast
        (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j := by
      simp [j]
    have hedge₂ : edge₂ = Fin.cast
        (schemeB_isTriangular.region_length (schemeBOccurrence k)).symm l := by
      simp [l]
    rw [hedge₁] at hlabel₁ ⊢
    rw [hedge₂] at hlabel₂ ⊢
    rw [schemeB_edgeLetter] at hlabel₁ hlabel₂
    have hinternal₁ : (schemeBEdgeTable i j).1 = 2 ∨
        (schemeBEdgeTable i j).1 = 3 := by
      simp_all
    have hinternal₂ : (schemeBEdgeTable k l).1 = 2 ∨
        (schemeBEdgeTable k l).1 = 3 := by
      simp_all
    have hsign₁ :
        ((schemeBOccurrence i).1.1.get
          (Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j)).2 =
          true := by
      rw [schemeB_edgeLetter]
      exact schemeBInternalLabel_positive i j hinternal₁
    have hsign₂ :
        ((schemeBOccurrence k).1.1.get
          (Fin.cast (schemeB_isTriangular.region_length (schemeBOccurrence k)).symm l)).2 =
          true := by
      rw [schemeB_edgeLetter]
      exact schemeBInternalLabel_positive k l hinternal₂
    rw [hsign₁, hsign₂, if_pos rfl]
    clear_value j
    clear_value l
    clear edge₁ hedge₁ edge₂ hedge₂
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l
    all_goals
      simp [schemeBEdgeTable] at hlabel₁ hlabel₂ ⊢
      try simp [schemeBDevelopment_schemeBOccurrence, schemeBChart,
        lowerTriangleChart_edge_two, schemeBTorusSecondChart_edge,
        schemeBKleinFirstChart_edge, schemeBKleinSecondChart_edge]

/-- Helper for Exercise 78.1: the equivalence closure of the internal scheme-B seams is
contained in the development kernel. -/
theorem schemeBInternal_eqvGen_mapsEqual
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : Relation.EqvGen schemeBInternalRelated x y) :
    schemeBDevelopment x = schemeBDevelopment y := by
  -- Equality of development images is reflexive, symmetric, and transitive, so induct on the
  -- generated relation after proving its direct generators.
  induction hxy with
  | rel x y h => exact schemeBInternalRelated_mapsEqual x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

/-- Helper for Exercise 78.1: equal scheme-B development points are generated by the two
internal seams. -/
theorem schemeBDevelopment_eq_imp_internal
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : schemeBDevelopment x = schemeBDevelopment y) :
    Relation.EqvGen schemeBInternalRelated x y := by
  -- Normalize both occurrences, then use injectivity or the corresponding overlap theorem.
  rcases x with ⟨region, point⟩
  rcases y with ⟨region', point'⟩
  obtain ⟨i, rfl⟩ := schemeBOccurrence_surjective region
  obtain ⟨j, rfl⟩ := schemeBOccurrence_surjective region'
  rw [schemeBDevelopment_schemeBOccurrence,
    schemeBDevelopment_schemeBOccurrence] at hxy
  fin_cases i
  · fin_cases j
    · have hpoint : point = point' :=
        lowerTriangleChart_injective (Sum.inl.inj hxy)
      subst point'
      exact Relation.EqvGen.refl _
    · obtain ⟨t, hpoint, hpoint'⟩ :=
        (lowerTriangleChart_eq_schemeBTorusSecondChart_iff point point').mp
          (Sum.inl.inj hxy)
      subst point
      subst point'
      exact Relation.EqvGen.rel _ _ (schemeBCSeamRelated t)
    · simp [schemeBChart] at hxy
    · simp [schemeBChart] at hxy
  · fin_cases j
    · obtain ⟨t, hpoint', hpoint⟩ :=
        (lowerTriangleChart_eq_schemeBTorusSecondChart_iff point' point).mp
          (Sum.inl.inj hxy.symm)
      subst point
      subst point'
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (schemeBCSeamRelated t))
    · have hpoint : point = point' :=
        schemeBTorusSecondChart_injective (Sum.inl.inj hxy)
      subst point'
      exact Relation.EqvGen.refl _
    · simp [schemeBChart] at hxy
    · simp [schemeBChart] at hxy
  · fin_cases j
    · simp [schemeBChart] at hxy
    · simp [schemeBChart] at hxy
    · have hpoint : point = point' :=
        schemeBKleinFirstChart_injective (Sum.inr.inj hxy)
      subst point'
      exact Relation.EqvGen.refl _
    · obtain ⟨t, hpoint, hpoint'⟩ :=
        (schemeBKleinFirstChart_eq_second_iff point point').mp
          (Sum.inr.inj hxy)
      subst point
      subst point'
      exact Relation.EqvGen.rel _ _ (schemeBDSeamRelated t)
  · fin_cases j
    · simp [schemeBChart] at hxy
    · simp [schemeBChart] at hxy
    · obtain ⟨t, hpoint', hpoint⟩ :=
        (schemeBKleinFirstChart_eq_second_iff point' point).mp
          (Sum.inr.inj hxy.symm)
      subst point
      subst point'
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (schemeBDSeamRelated t))
    · have hpoint : point = point' :=
        schemeBKleinSecondChart_injective (Sum.inr.inj hxy)
      subst point'
      exact Relation.EqvGen.refl _

/-- Helper for Exercise 78.1: the fibers of the scheme-B development are exactly the
equivalence closure of its two internal seams. -/
theorem schemeBDevelopment_fibers
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source) :
    schemeBDevelopment x = schemeBDevelopment y ↔
      Relation.EqvGen schemeBInternalRelated x y := by
  -- Combine the finite chart-overlap classification with stability under generated seams.
  exact ⟨schemeBDevelopment_eq_imp_internal x y,
    schemeBInternal_eqvGen_mapsEqual x y⟩

/-- Helper for Exercise 78.1: the scheme-B development is continuous. -/
theorem continuous_schemeBDevelopment : Continuous schemeBDevelopment := by
  -- Continuity on the disjoint union reduces to the appropriate affine branch.
  rw [continuous_iSup_dom]
  intro region
  rw [continuous_coinduced_dom]
  letI : TopologicalSpace
      ((schemeB.triangularRegions schemeB_isTriangular).Point region) :=
    (schemeB.triangularRegions schemeB_isTriangular).topology region
  change Continuous (schemeBChart (schemeBOccurrenceEquiv region))
  exact continuous_schemeBChart (schemeBOccurrenceEquiv region)

/-- Helper for Exercise 78.1: the scheme-B development covers both component squares. -/
theorem schemeBDevelopment_surjective : Function.Surjective schemeBDevelopment := by
  intro point
  cases point with
  | inl square =>
      obtain ⟨preimage, hpreimage⟩ := schemeBTorusPairToSquare_surjective square
      cases preimage with
      | inl triangle =>
          refine ⟨⟨schemeBOccurrence 0, triangle⟩, ?_⟩
          simpa [schemeBDevelopment, schemeBChart, schemeBOccurrenceEquiv,
            schemeBTorusPairToSquare] using congrArg
              (Sum.inl : unitInterval × unitInterval →
                (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval)) hpreimage
      | inr triangle =>
          refine ⟨⟨schemeBOccurrence 1, triangle⟩, ?_⟩
          simpa [schemeBDevelopment, schemeBChart, schemeBOccurrenceEquiv,
            schemeBTorusPairToSquare] using congrArg
              (Sum.inl : unitInterval × unitInterval →
                (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval)) hpreimage
  | inr square =>
      obtain ⟨preimage, hpreimage⟩ := schemeBKleinPairToSquare_surjective square
      cases preimage with
      | inl triangle =>
          refine ⟨⟨schemeBOccurrence 2, triangle⟩, ?_⟩
          simpa [schemeBDevelopment, schemeBChart, schemeBOccurrenceEquiv,
            schemeBKleinPairToSquare] using congrArg
              (Sum.inr : unitInterval × unitInterval →
                (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval)) hpreimage
      | inr triangle =>
          refine ⟨⟨schemeBOccurrence 3, triangle⟩, ?_⟩
          simpa [schemeBDevelopment, schemeBChart, schemeBOccurrenceEquiv,
            schemeBKleinPairToSquare] using congrArg
              (Sum.inr : unitInterval × unitInterval →
                (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval)) hpreimage

/-- Helper for Exercise 78.1: the standard triangle is compact. -/
theorem isCompact_standardTriangle : IsCompact standardTriangle := by
  -- Realize the triangle as a closed bounded subset of the Euclidean plane.
  have hclosed : IsClosed standardTriangle := by
    have htriangle : standardTriangle =
        {point | 0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1} := by
      ext point
      exact mem_standardTriangle point
    rw [htriangle]
    have hcoord0 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 0) := by
      fun_prop
    have hcoord1 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 1) := by
      fun_prop
    exact (isClosed_le continuous_const hcoord0).inter
      ((isClosed_le continuous_const hcoord1).inter
        (isClosed_le (hcoord0.add hcoord1) continuous_const))
  exact Metric.isCompact_of_isClosed_isBounded hclosed isBounded_standardTriangle

/-- Helper for Exercise 78.1: a finite family of standard triangular regions has compact
source. -/
theorem isCompact_triangularRegionsSource {α : Type u} {scheme : LabellingScheme α}
    (h : scheme.IsTriangular) [Finite (LabellingScheme.Occurrence scheme)] :
    IsCompact (Set.univ : Set (scheme.triangularRegions h).Source) := by
  -- The source is the finite union of the compact images of its triangle summands.
  let regions := scheme.triangularRegions h
  letI : CompactSpace standardTriangle :=
    isCompact_iff_compactSpace.mp isCompact_standardTriangle
  have hinclusion : ∀ region : LabellingScheme.Occurrence scheme,
      @Continuous (regions.Point region) regions.Source
        (regions.topology region) regions.sourceTopology
        (Sigma.mk region : regions.Point region → regions.Source) := by
    intro region
    exact continuous_iSup_rng (i := region) (f := Sigma.mk region)
      (continuous_coinduced_rng (f := Sigma.mk region))
  have sourceUniv : (Set.univ : Set regions.Source) =
      ⋃ region, Set.range (Sigma.mk region) := by
    ext source
    constructor
    · intro _
      exact Set.mem_iUnion.mpr ⟨source.1, ⟨source.2, rfl⟩⟩
    · intro _
      exact Set.mem_univ source
  rw [sourceUniv]
  apply isCompact_iUnion
  intro region
  letI : TopologicalSpace (regions.Point region) := regions.topology region
  letI : CompactSpace (regions.Point region) := by
    change CompactSpace standardTriangle
    infer_instance
  simpa only [Set.image_univ] using
    (isCompact_univ : IsCompact
      (Set.univ : Set (regions.Point region))).image
      (hinclusion region)

/-- Helper for Exercise 78.1: the scheme-A development is a quotient map onto the square. -/
theorem schemeADevelopment_isQuotientMap :
    Topology.IsQuotientMap schemeADevelopment := by
  -- The finite disjoint union of compact triangles is compact, so the continuous surjection
  -- to the Hausdorff square is quotient.
  letI : Fintype (LabellingScheme.Occurrence schemeA) :=
    Fintype.ofEquiv (Fin 4) schemeAOccurrenceEquiv.symm
  letI : CompactSpace (schemeA.triangularRegions schemeA_isTriangular).Source :=
    ⟨isCompact_triangularRegionsSource schemeA_isTriangular⟩
  exact Topology.IsQuotientMap.of_surjective_continuous
    schemeADevelopment_surjective continuous_schemeADevelopment

/-- Helper for Exercise 78.1: the scheme-B development is a quotient map onto the sum of
squares. -/
theorem schemeBDevelopment_isQuotientMap :
    Topology.IsQuotientMap schemeBDevelopment := by
  -- Again the source is a finite disjoint union of compact triangles and the target is
  -- Hausdorff, so the continuous surjection is quotient.
  letI : Fintype (LabellingScheme.Occurrence schemeB) :=
    Fintype.ofEquiv (Fin 4) schemeBOccurrenceEquiv.symm
  letI : CompactSpace (schemeB.triangularRegions schemeB_isTriangular).Source :=
    ⟨isCompact_triangularRegionsSource schemeB_isTriangular⟩
  exact Topology.IsQuotientMap.of_surjective_continuous
    schemeBDevelopment_surjective continuous_schemeBDevelopment

/-- Helper for Exercise 78.1: the torus chart-pair map is a quotient map onto the square. -/
theorem schemeBTorusPairToSquare_isQuotientMap :
    Topology.IsQuotientMap schemeBTorusPairToSquare := by
  -- Compactness and the verified continuous surjection give quotientness.
  letI : CompactSpace standardTriangle := isCompact_iff_compactSpace.mp
    isCompact_standardTriangle
  exact Topology.IsQuotientMap.of_surjective_continuous
    schemeBTorusPairToSquare_surjective continuous_schemeBTorusPairToSquare

/-- Helper for Exercise 78.1: the Klein chart-pair map is a quotient map onto the square. -/
theorem schemeBKleinPairToSquare_isQuotientMap :
    Topology.IsQuotientMap schemeBKleinPairToSquare := by
  -- The same compact-domain criterion applies to the anti-diagonal decomposition.
  letI : CompactSpace standardTriangle := isCompact_iff_compactSpace.mp
    isCompact_standardTriangle
  exact Topology.IsQuotientMap.of_surjective_continuous
    schemeBKleinPairToSquare_surjective continuous_schemeBKleinPairToSquare

/-- Helper for Exercise 78.1: the first scheme-B triangle pair maps through its square to the
standard torus. -/
def schemeBTorusPairToTorus : standardTriangle ⊕ standardTriangle →
    UnitAddCircle × UnitAddCircle :=
  TorusSquare.toTorus ∘ schemeBTorusPairToSquare

/-- Helper for Exercise 78.1: the torus component map is a quotient map. -/
theorem schemeBTorusPairToTorus_isQuotientMap :
    Topology.IsQuotientMap schemeBTorusPairToTorus := by
  -- Compose the chart-pair quotient with the standard square-to-torus quotient.
  exact TorusSquare.toTorus_isQuotientMap.comp
    schemeBTorusPairToSquare_isQuotientMap

/-- Helper for Exercise 78.1: the scheme-A square development followed by the full-half
rectangle quotient is its Klein-bottle comparison map. -/
noncomputable def schemeAComparison :
    (schemeA.triangularRegions schemeA_isTriangular).Source → KleinBottle :=
  kleinFullHalfMap ∘ schemeADevelopment

/-- Helper for Exercise 78.1: the two scheme-B rectangles map respectively to the torus and
the Klein bottle. -/
noncomputable def schemeBRectangleComparison :
    (unitInterval × unitInterval) ⊕ (unitInterval × unitInterval) →
      (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle :=
  Sum.map TorusSquare.toTorus kleinHalfFullMap

/-- Helper for Exercise 78.1: the scheme-B development followed by its component rectangle
quotients is the final comparison map. -/
noncomputable def schemeBComparison :
    (schemeB.triangularRegions schemeB_isTriangular).Source →
      (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle :=
  schemeBRectangleComparison ∘ schemeBDevelopment

/-- Helper for Exercise 78.1: the componentwise scheme-B rectangle comparison is continuous. -/
theorem continuous_schemeBRectangleComparison :
    Continuous schemeBRectangleComparison := by
  -- Each sum component is one of the two verified continuous fundamental-domain maps.
  unfold schemeBRectangleComparison
  apply Continuous.sumMap
  · unfold TorusSquare.toTorus
    fun_prop
  · exact continuous_kleinHalfFullMap

/-- Helper for Exercise 78.1: the componentwise scheme-B rectangle comparison is surjective. -/
theorem schemeBRectangleComparison_surjective :
    Function.Surjective schemeBRectangleComparison := by
  -- Lift a target point through the quotient map in its tagged component.
  intro point
  cases point with
  | inl torusPoint =>
      obtain ⟨square, hsquare⟩ := TorusSquare.toTorus_isQuotientMap.surjective torusPoint
      refine ⟨Sum.inl square, ?_⟩
      simpa [schemeBRectangleComparison] using congrArg
        (Sum.inl : UnitAddCircle × UnitAddCircle →
          (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle) hsquare
  | inr kleinPoint =>
      obtain ⟨square, hsquare⟩ := kleinHalfFullMap_surjective kleinPoint
      refine ⟨Sum.inr square, ?_⟩
      simpa [schemeBRectangleComparison] using congrArg
        (Sum.inr : KleinBottle →
          (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle) hsquare

/-- Helper for Exercise 78.1: the componentwise scheme-B rectangle comparison is a quotient
map. -/
theorem schemeBRectangleComparison_isQuotientMap :
    Topology.IsQuotientMap schemeBRectangleComparison := by
  -- Compactness of the two squares and Hausdorffness of the tagged target upgrade the verified
  -- continuous surjection to a quotient map.
  exact Topology.IsQuotientMap.of_surjective_continuous
    schemeBRectangleComparison_surjective continuous_schemeBRectangleComparison

/-- Helper for Exercise 78.1: the scheme-A comparison map is quotient. -/
theorem schemeAComparison_isQuotientMap :
    Topology.IsQuotientMap schemeAComparison := by
  -- Quotientness is stable under the two-stage development and rectangle quotient.
  exact kleinFullHalfMap_isQuotientMap.comp schemeADevelopment_isQuotientMap

/-- Helper for Exercise 78.1: the scheme-B comparison map is quotient. -/
theorem schemeBComparison_isQuotientMap :
    Topology.IsQuotientMap schemeBComparison := by
  -- Compose the internal-seam development with the componentwise boundary quotient.
  exact schemeBRectangleComparison_isQuotientMap.comp schemeBDevelopment_isQuotientMap

/-- Helper for Exercise 78.1: equality under the square-to-torus map is coordinatewise
endpoint identification. -/
theorem torusSquareToTorus_eq_iff (p q : unitInterval × unitInterval) :
    TorusSquare.toTorus p = TorusSquare.toTorus q ↔
      unitInterval.endpointSetoid p.1 q.1 ∧
        unitInterval.endpointSetoid p.2 q.2 := by
  -- This is the public square relation with its kernel definition exposed.
  exact TorusSquare.identified_iff p q

/-- Helper for Exercise 78.1: reflecting an interval point represented by `1 - t` returns
`t`. -/
theorem unitIntervalSymm_oneSub (t : unitInterval)
    (h : 1 - (t : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    unitInterval.symm ⟨1 - (t : ℝ), h⟩ = t := by
  -- Compare real coordinates, where interval reflection is exactly subtraction from one.
  apply Subtype.ext
  simp [unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: the interval point represented by `1 - t` is the reflection of
`t`. -/
theorem unitIntervalOneSub_eq_symm (t : unitInterval)
    (h : 1 - (t : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (⟨1 - (t : ℝ), h⟩ : unitInterval) = unitInterval.symm t := by
  -- The same real-coordinate calculation gives the reverse normal form.
  apply Subtype.ext
  simp [unitInterval.coe_symm_eq]

/-- Helper for Exercise 78.1: every direct labelled edge pairing of scheme A has equal
Klein-bottle comparison image. -/
theorem schemeAComparison_edgeRelated
    (x y : (schemeA.triangularRegions schemeA_isTriangular).Source)
    (hxy : (schemeA.triangularRegions schemeA_isTriangular).EdgeRelated x y) :
    schemeAComparison x = schemeAComparison y := by
  -- Normalize the edge pairing to the finite affine chart table and then apply the exact
  -- full-half rectangle fiber description.
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  obtain ⟨i, rfl⟩ := schemeAOccurrence_surjective region₁
  obtain ⟨k, rfl⟩ := schemeAOccurrence_surjective region₂
  let j : Fin 3 := Fin.cast
    (schemeA_isTriangular.region_length (schemeAOccurrence i)) edge₁
  let l : Fin 3 := Fin.cast
    (schemeA_isTriangular.region_length (schemeAOccurrence k)) edge₂
  have hedge₁ : edge₁ = Fin.cast
      (schemeA_isTriangular.region_length (schemeAOccurrence i)).symm j := by
    simp [j]
  have hedge₂ : edge₂ = Fin.cast
      (schemeA_isTriangular.region_length (schemeAOccurrence k)).symm l := by
    simp [l]
  rw [hedge₁] at hlabel ⊢
  rw [hedge₂] at hlabel ⊢
  rw [schemeA_edgeLetter, schemeA_edgeLetter] at hlabel
  have hsign₁ := congrArg Prod.snd (schemeA_edgeLetter i j)
  have hsign₂ := congrArg Prod.snd (schemeA_edgeLetter k l)
  rw [hsign₁, hsign₂]
  clear_value j
  clear_value l
  clear edge₁ hedge₁ edge₂ hedge₂
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l
  all_goals
    simp [schemeAEdgeTable] at hlabel ⊢
    try simp [schemeAComparison, schemeADevelopment_schemeAOccurrence, schemeAChart,
      schemeAFirstChart, schemeASecondChart, schemeAThirdChart, schemeAFourthChart,
      kleinFullHalfMap_eq_iff, unitInterval.endpointSetoid_iff,
      TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates, unitInterval.coe_symm_eq]
  all_goals try norm_num at *
  all_goals try ring_nf at *
  all_goals simp_all

/-- Helper for Exercise 78.1: every generated scheme-A identification has equal comparison
image. -/
theorem schemeAIdentified_mapsEqual
    (x y : (schemeA.triangularRegions schemeA_isTriangular).Source)
    (hxy : (schemeA.triangularRegions schemeA_isTriangular).Identified.r x y) :
    schemeAComparison x = schemeAComparison y := by
  -- Close the generated relation under the direct edge compatibility just proved.
  rw [identified_iff_eqvGen] at hxy
  induction hxy with
  | rel x y h => exact schemeAComparison_edgeRelated x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

/-- Helper for Exercise 78.1: every direct labelled edge pairing of scheme B has equal
comparison image. -/
theorem schemeBComparison_edgeRelated
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : (schemeB.triangularRegions schemeB_isTriangular).EdgeRelated x y) :
    schemeBComparison x = schemeBComparison y := by
  -- Normalize the paired occurrences and edges to the finite table before evaluating the two
  -- rectangle quotient maps.
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  obtain ⟨i, rfl⟩ := schemeBOccurrence_surjective region₁
  obtain ⟨k, rfl⟩ := schemeBOccurrence_surjective region₂
  let j : Fin 3 := Fin.cast
    (schemeB_isTriangular.region_length (schemeBOccurrence i)) edge₁
  let l : Fin 3 := Fin.cast
    (schemeB_isTriangular.region_length (schemeBOccurrence k)) edge₂
  have hedge₁ : edge₁ = Fin.cast
      (schemeB_isTriangular.region_length (schemeBOccurrence i)).symm j := by
    simp [j]
  have hedge₂ : edge₂ = Fin.cast
      (schemeB_isTriangular.region_length (schemeBOccurrence k)).symm l := by
    simp [l]
  rw [hedge₁] at hlabel ⊢
  rw [hedge₂] at hlabel ⊢
  rw [schemeB_edgeLetter, schemeB_edgeLetter] at hlabel
  have hsign₁ := congrArg Prod.snd (schemeB_edgeLetter i j)
  have hsign₂ := congrArg Prod.snd (schemeB_edgeLetter k l)
  rw [hsign₁, hsign₂]
  clear_value j
  clear_value l
  clear edge₁ hedge₁ edge₂ hedge₂
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l
  all_goals
    simp [schemeBEdgeTable] at hlabel ⊢
    try simp [schemeBComparison, schemeBRectangleComparison,
      schemeBDevelopment_schemeBOccurrence, schemeBChart,
      torusSquareToTorus_eq_iff, kleinHalfFullMap_eq_iff,
      unitInterval.endpointSetoid_iff, lowerTriangleChart, schemeBTorusSecondChart,
      schemeBKleinFirstChart, schemeBKleinSecondChart, upperTriangleChart,
      TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates, unitInterval.coe_symm_eq,
      unitIntervalOneSub_eq_symm]

/-- Helper for Exercise 78.1: every generated scheme-B identification has equal comparison
image. -/
theorem schemeBIdentified_mapsEqual
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y) :
    schemeBComparison x = schemeBComparison y := by
  -- Equality of comparison images contains every direct edge generator and is an equivalence
  -- relation, so it contains their generated closure.
  rw [identified_iff_eqvGen] at hxy
  induction hxy with
  | rel x y h => exact schemeBComparison_edgeRelated x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

/-- Helper for Exercise 78.1: equality in the scheme-B development already gives a labelled
identification. -/
theorem schemeBDevelopment_eq_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : schemeBDevelopment x = schemeBDevelopment y) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- The development kernel is generated by the `c` and `d` seams, each of which is a labelled
  -- edge generator in the full relation.
  rw [identified_iff_eqvGen]
  have hinternal := (schemeBDevelopment_fibers x y).mp hxy
  apply Relation.EqvGen.mono _ _ _ hinternal
  intro a b hab
  rcases hab with hab | hab
  · exact (schemeB.triangularRegions schemeB_isTriangular).edgeRelatedAt_le_edgeRelated 2
      a b hab
  · exact (schemeB.triangularRegions schemeB_isTriangular).edgeRelatedAt_le_edgeRelated 3
      a b hab

/-- Helper for Exercise 78.1: an endpoint identification in the first torus-square coordinate
lifts through the two scheme-B edges labelled `b`. -/
theorem schemeBTorusFirstEndpoint_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (p q : unitInterval × unitInterval)
    (hx : schemeBDevelopment x = Sum.inl p)
    (hy : schemeBDevelopment y = Sum.inl q)
    (hfirst : unitInterval.endpointSetoid p.1 q.1) (hsecond : p.2 = q.2) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- Equal coordinates are already in one development fiber; the two endpoint cases use the
  -- normalized vertical `b` edges in the appropriate direction.
  rcases (unitInterval.endpointSetoid_iff _ _).mp hfirst with
      hcoordinate | ⟨hpzero, hqone⟩ | ⟨hpone, hqzero⟩
  · apply schemeBDevelopment_eq_identified x y
    rw [hx, hy]
    exact congrArg Sum.inl (Prod.ext hcoordinate hsecond)
  · let left : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 1, TriangleDisk.edgePoint 1 p.2⟩
    let right : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 0, TriangleDisk.edgePoint 1 p.2⟩
    have hxleft : schemeBDevelopment x = schemeBDevelopment left := by
      rw [hx]
      unfold left
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [left, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hpzero
      · simp [schemeBTorusSecondChart_edge]
    have hrighty : schemeBDevelopment right = schemeBDevelopment y := by
      rw [hy]
      unfold right
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
          hqone.symm
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
          hsecond
    have hbLabel : (schemeBEdgeTable 1 1).1 = (schemeBEdgeTable 0 1).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        left right := by
      simpa [left, right, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 1 0 1 1 p.2 hbLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x left hxleft)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hedge
        (schemeBDevelopment_eq_identified right y hrighty))
  · let left : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 1, TriangleDisk.edgePoint 1 q.2⟩
    let right : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 0, TriangleDisk.edgePoint 1 q.2⟩
    have hxright : schemeBDevelopment x = schemeBDevelopment right := by
      rw [hx]
      unfold right
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using hpone
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
          hsecond
    have hlefty : schemeBDevelopment left = schemeBDevelopment y := by
      rw [hy]
      unfold left
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [left, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hqzero.symm
      · simp [schemeBTorusSecondChart_edge]
    have hbLabel : (schemeBEdgeTable 1 1).1 = (schemeBEdgeTable 0 1).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        left right := by
      simpa [left, right, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 1 0 1 1 q.2 hbLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x right hxright)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
        ((schemeB.triangularRegions schemeB_isTriangular).Identified.symm' hedge)
        (schemeBDevelopment_eq_identified left y hlefty))

/-- Helper for Exercise 78.1: an endpoint identification in the second torus-square
coordinate lifts through the two scheme-B edges labelled `a`. -/
theorem schemeBTorusSecondEndpoint_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (p q : unitInterval × unitInterval)
    (hx : schemeBDevelopment x = Sum.inl p)
    (hy : schemeBDevelopment y = Sum.inl q)
    (hfirst : p.1 = q.1) (hsecond : unitInterval.endpointSetoid p.2 q.2) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- The horizontal `a` pair handles the two nontrivial endpoint directions.
  rcases (unitInterval.endpointSetoid_iff _ _).mp hsecond with
      hcoordinate | ⟨hpzero, hqone⟩ | ⟨hpone, hqzero⟩
  · apply schemeBDevelopment_eq_identified x y
    rw [hx, hy]
    exact congrArg Sum.inl (Prod.ext hfirst hcoordinate)
  · let bottom : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 0, TriangleDisk.edgePoint 0 p.1⟩
    let top : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 1, TriangleDisk.edgePoint 2 p.1⟩
    have hxbottom : schemeBDevelopment x = schemeBDevelopment bottom := by
      rw [hx]
      unfold bottom
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simp [lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      · simpa [bottom, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using hpzero
    have htopy : schemeBDevelopment top = schemeBDevelopment y := by
      rw [hy]
      unfold top
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hfirst
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hqone.symm
    have haLabel : (schemeBEdgeTable 0 0).1 = (schemeBEdgeTable 1 2).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        bottom top := by
      simpa [bottom, top, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 0 1 0 2 p.1 haLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x bottom hxbottom)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hedge
        (schemeBDevelopment_eq_identified top y htopy))
  · let bottom : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 0, TriangleDisk.edgePoint 0 q.1⟩
    let top : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 1, TriangleDisk.edgePoint 2 q.1⟩
    have hxtop : schemeBDevelopment x = schemeBDevelopment top := by
      rw [hx]
      unfold top
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hfirst
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBTorusSecondChart_edge] using hpone
    have hbottomy : schemeBDevelopment bottom = schemeBDevelopment y := by
      rw [hy]
      unfold bottom
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inl
      apply Prod.ext
      · simp [lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      · simpa [bottom, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
          hqzero.symm
    have haLabel : (schemeBEdgeTable 0 0).1 = (schemeBEdgeTable 1 2).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        bottom top := by
      simpa [bottom, top, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 0 1 0 2 q.1 haLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x top hxtop)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
        ((schemeB.triangularRegions schemeB_isTriangular).Identified.symm' hedge)
        (schemeBDevelopment_eq_identified bottom y hbottomy))

/-- Helper for Exercise 78.1: an endpoint identification in the Klein-square vertical
coordinate lifts through the two positive scheme-B edges labelled `f`. -/
theorem schemeBKleinSecondEndpoint_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (p q : unitInterval × unitInterval)
    (hx : schemeBDevelopment x = Sum.inr p)
    (hy : schemeBDevelopment y = Sum.inr q)
    (hfirst : p.1 = q.1) (hsecond : unitInterval.endpointSetoid p.2 q.2) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- Equal heights stay in one development fiber; bottom/top crossings use the two `f` edges.
  rcases (unitInterval.endpointSetoid_iff _ _).mp hsecond with
      hcoordinate | ⟨hpzero, hqone⟩ | ⟨hpone, hqzero⟩
  · apply schemeBDevelopment_eq_identified x y
    rw [hx, hy]
    exact congrArg Sum.inr (Prod.ext hfirst hcoordinate)
  · let bottom : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 2, TriangleDisk.edgePoint 2 p.1⟩
    let top : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 3, TriangleDisk.edgePoint 1 p.1⟩
    have hxbottom : schemeBDevelopment x = schemeBDevelopment bottom := by
      rw [hx]
      unfold bottom
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simp [schemeBKleinFirstChart_edge]
      · simpa [bottom, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinFirstChart_edge] using hpzero
    have htopy : schemeBDevelopment top = schemeBDevelopment y := by
      rw [hy]
      unfold top
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hfirst
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hqone.symm
    have hfLabel : (schemeBEdgeTable 2 2).1 = (schemeBEdgeTable 3 1).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        bottom top := by
      simpa [bottom, top, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 2 3 2 1 p.1 hfLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x bottom hxbottom)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hedge
        (schemeBDevelopment_eq_identified top y htopy))
  · let bottom : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 2, TriangleDisk.edgePoint 2 q.1⟩
    let top : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 3, TriangleDisk.edgePoint 1 q.1⟩
    have hxtop : schemeBDevelopment x = schemeBDevelopment top := by
      rw [hx]
      unfold top
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hfirst
      · simpa [top, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hpone
    have hbottomy : schemeBDevelopment bottom = schemeBDevelopment y := by
      rw [hy]
      unfold bottom
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simp [schemeBKleinFirstChart_edge]
      · simpa [bottom, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinFirstChart_edge] using hqzero.symm
    have hfLabel : (schemeBEdgeTable 2 2).1 = (schemeBEdgeTable 3 1).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        bottom top := by
      simpa [bottom, top, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 2 3 2 1 q.1 hfLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x top hxtop)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
        ((schemeB.triangularRegions schemeB_isTriangular).Identified.symm' hedge)
        (schemeBDevelopment_eq_identified bottom y hbottomy))

/-- Helper for Exercise 78.1: the reflected horizontal Klein-square boundary relation lifts
through the positive and negative scheme-B occurrences of `e`. -/
theorem schemeBKleinReflection_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (p q : unitInterval × unitInterval)
    (hx : schemeBDevelopment x = Sum.inr p)
    (hy : schemeBDevelopment y = Sum.inr q)
    (hfirst : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ q.1 = 0))
    (hsecond : q.2 = unitInterval.symm p.2) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- Orient the `e` generator from the left edge to the right edge; in the reverse endpoint
  -- case use setoid symmetry after choosing the reflected parameter from `q`.
  rcases hfirst with ⟨hpzero, hqone⟩ | ⟨hpone, hqzero⟩
  · let left : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 2,
        TriangleDisk.edgePoint 1 (unitInterval.symm p.2)⟩
    let right : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 3, TriangleDisk.edgePoint 2 p.2⟩
    have hxleft : schemeBDevelopment x = schemeBDevelopment left := by
      rw [hx]
      unfold left
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [left, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinFirstChart_edge] using hpzero
      · simp [schemeBKleinFirstChart_edge]
    have hrighty : schemeBDevelopment right = schemeBDevelopment y := by
      rw [hy]
      unfold right
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hqone.symm
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hsecond.symm
    have heLabel : (schemeBEdgeTable 2 1).1 = (schemeBEdgeTable 3 2).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        left right := by
      simpa [left, right, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 2 3 1 2
          (unitInterval.symm p.2) heLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x left hxleft)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hedge
        (schemeBDevelopment_eq_identified right y hrighty))
  · let left : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 2,
        TriangleDisk.edgePoint 1 (unitInterval.symm q.2)⟩
    let right : (schemeB.triangularRegions schemeB_isTriangular).Source :=
      ⟨schemeBOccurrence 3, TriangleDisk.edgePoint 2 q.2⟩
    have hxright : schemeBDevelopment x = schemeBDevelopment right := by
      rw [hx]
      unfold right
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [right, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinSecondChart_edge] using hpone
      · simp [schemeBKleinSecondChart_edge, hsecond]
    have hlefty : schemeBDevelopment left = schemeBDevelopment y := by
      rw [hy]
      unfold left
      rw [schemeBDevelopment_schemeBOccurrence]
      apply congrArg Sum.inr
      apply Prod.ext
      · simpa [left, schemeBDevelopment_schemeBOccurrence, schemeBChart,
          schemeBKleinFirstChart_edge] using hqzero.symm
      · simp [schemeBKleinFirstChart_edge]
    have heLabel : (schemeBEdgeTable 2 1).1 = (schemeBEdgeTable 3 2).1 := by
      simp [schemeBEdgeTable]
    have hedge : (schemeB.triangularRegions schemeB_isTriangular).Identified.r
        left right := by
      simpa [left, right, schemeBEdgeTable] using
        schemeBNormalizedEdgePair_identified 2 3 1 2
          (unitInterval.symm q.2) heLabel
    exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
      (schemeBDevelopment_eq_identified x right hxright)
      ((schemeB.triangularRegions schemeB_isTriangular).Identified.trans'
        ((schemeB.triangularRegions schemeB_isTriangular).Identified.symm' hedge)
        (schemeBDevelopment_eq_identified left y hlefty))

/-- Helper for Exercise 78.1: equal scheme-A Klein comparison images arise from the labelled
edge relation. -/
theorem schemeAComparison_eq_imp_identified
    (x y : (schemeA.triangularRegions schemeA_isTriangular).Source)
    (hxy : schemeAComparison x = schemeAComparison y) :
    (schemeA.triangularRegions schemeA_isTriangular).Identified.r x y := by
  -- Classify the outer rectangle kernel, then connect each point through the development
  -- kernel to canonical representatives on the appropriate `b`, `c`, or `d` edges.
  have hcomparison : kleinFullHalfMap (schemeADevelopment x) =
      kleinFullHalfMap (schemeADevelopment y) := by
    simpa [schemeAComparison] using hxy
  have hkernel := (kleinFullHalfMap_eq_iff (schemeADevelopment x)
    (schemeADevelopment y)).mp hcomparison
  rcases hkernel with ⟨hfirst, hsecond⟩ | ⟨hheight, hshift⟩
  · rcases (unitInterval.endpointSetoid_iff _ _).mp hfirst with
      hcoordinate | ⟨hxzero, hyone⟩ | ⟨hxone, hyzero⟩
    · apply schemeADevelopment_eq_identified x y
      exact Prod.ext hcoordinate hsecond
    · let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
        ⟨schemeAOccurrence 3,
          TriangleDisk.edgePoint 0 (schemeADevelopment x).2⟩
      let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
        ⟨schemeAOccurrence 0,
          TriangleDisk.edgePoint 2 (schemeADevelopment x).2⟩
      have hxleft : schemeADevelopment x = schemeADevelopment left := by
        apply Prod.ext <;> apply Subtype.ext
        · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hxzero
        · simp [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      have hrighty : schemeADevelopment right = schemeADevelopment y := by
        apply Prod.ext <;> apply Subtype.ext
        · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hyone.symm
        · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hsecond
      have hcLabel : (schemeAEdgeTable 3 0).1 = (schemeAEdgeTable 0 2).1 := by
        simp [schemeAEdgeTable]
      have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
          left right := by
        simpa [left, right, schemeAEdgeTable] using
          schemeANormalizedEdgePair_identified 3 0 0 2
            (schemeADevelopment x).2 hcLabel
      exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
        (schemeADevelopment_eq_identified x left hxleft)
        ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans' hedge
          (schemeADevelopment_eq_identified right y hrighty))
    · let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
        ⟨schemeAOccurrence 0,
          TriangleDisk.edgePoint 2 (schemeADevelopment y).2⟩
      let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
        ⟨schemeAOccurrence 3,
          TriangleDisk.edgePoint 0 (schemeADevelopment y).2⟩
      have hxright : schemeADevelopment x = schemeADevelopment right := by
        apply Prod.ext <;> apply Subtype.ext
        · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hxone
        · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hsecond
      have hlefty : schemeADevelopment left = schemeADevelopment y := by
        apply Prod.ext <;> apply Subtype.ext
        · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
            congrArg (fun t : unitInterval ↦ (t : ℝ)) hyzero.symm
        · simp [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
            schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      have hcLabel : (schemeAEdgeTable 3 0).1 = (schemeAEdgeTable 0 2).1 := by
        simp [schemeAEdgeTable]
      have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
          left right := by
        simpa [left, right, schemeAEdgeTable] using
          schemeANormalizedEdgePair_identified 3 0 0 2
            (schemeADevelopment y).2 hcLabel
      exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
        (schemeADevelopment_eq_identified x right hxright)
        ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
          ((schemeA.triangularRegions schemeA_isTriangular).Identified.symm' hedge)
          (schemeADevelopment_eq_identified left y hlefty))
  · rcases hheight with ⟨hxheight, hyheight⟩ | ⟨hxheight, hyheight⟩
    · rcases hshift with hforward | hbackward
      · have htmem : 2 * ((schemeADevelopment x).1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          have hlower : 0 ≤ 2 * ((schemeADevelopment x).1 : ℝ) := by
            linarith [(schemeADevelopment x).1.property.1]
          have hupper : 2 * ((schemeADevelopment x).1 : ℝ) ≤ 1 := by
            linarith [(schemeADevelopment y).1.property.2]
          exact ⟨hlower, hupper⟩
        let t : unitInterval := ⟨2 * ((schemeADevelopment x).1 : ℝ), htmem⟩
        let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 2, TriangleDisk.edgePoint 0 t⟩
        let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 0, TriangleDisk.edgePoint 1 t⟩
        have hxleft : schemeADevelopment x = schemeADevelopment left := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [left, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAThirdChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
          · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAThirdChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hxheight
        have hrighty : schemeADevelopment right = schemeADevelopment y := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [right, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
            linarith
          · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hyheight.symm
        have hbLabel : (schemeAEdgeTable 2 0).1 = (schemeAEdgeTable 0 1).1 := by
          simp [schemeAEdgeTable]
        have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
            left right := by
          simpa [left, right, schemeAEdgeTable] using
            schemeANormalizedEdgePair_identified 2 0 0 1 t hbLabel
        exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
          (schemeADevelopment_eq_identified x left hxleft)
          ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans' hedge
            (schemeADevelopment_eq_identified right y hrighty))
      · have htmem : 2 * ((schemeADevelopment y).1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          have hlower : 0 ≤ 2 * ((schemeADevelopment y).1 : ℝ) := by
            linarith [(schemeADevelopment y).1.property.1]
          have hupper : 2 * ((schemeADevelopment y).1 : ℝ) ≤ 1 := by
            linarith [(schemeADevelopment x).1.property.2]
          exact ⟨hlower, hupper⟩
        let t : unitInterval := ⟨2 * ((schemeADevelopment y).1 : ℝ), htmem⟩
        let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 2, TriangleDisk.edgePoint 0 t⟩
        let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 0, TriangleDisk.edgePoint 1 t⟩
        have hxright : schemeADevelopment x = schemeADevelopment right := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [right, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
            linarith
          · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFirstChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hxheight
        have hlefty : schemeADevelopment left = schemeADevelopment y := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [left, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAThirdChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
          · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAThirdChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hyheight.symm
        have hbLabel : (schemeAEdgeTable 2 0).1 = (schemeAEdgeTable 0 1).1 := by
          simp [schemeAEdgeTable]
        have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
            left right := by
          simpa [left, right, schemeAEdgeTable] using
            schemeANormalizedEdgePair_identified 2 0 0 1 t hbLabel
        exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
          (schemeADevelopment_eq_identified x right hxright)
          ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
            ((schemeA.triangularRegions schemeA_isTriangular).Identified.symm' hedge)
            (schemeADevelopment_eq_identified left y hlefty))
    · rcases hshift with hforward | hbackward
      · have htmem : 2 * ((schemeADevelopment x).1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          have hlower : 0 ≤ 2 * ((schemeADevelopment x).1 : ℝ) := by
            linarith [(schemeADevelopment x).1.property.1]
          have hupper : 2 * ((schemeADevelopment x).1 : ℝ) ≤ 1 := by
            linarith [(schemeADevelopment y).1.property.2]
          exact ⟨hlower, hupper⟩
        let t : unitInterval := ⟨2 * ((schemeADevelopment x).1 : ℝ), htmem⟩
        let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 3, TriangleDisk.edgePoint 1 t⟩
        let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 1, TriangleDisk.edgePoint 0 t⟩
        have hxleft : schemeADevelopment x = schemeADevelopment left := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [left, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
          · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hxheight
        have hrighty : schemeADevelopment right = schemeADevelopment y := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [right, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeASecondChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
            linarith
          · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeASecondChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hyheight.symm
        have hdLabel : (schemeAEdgeTable 3 1).1 = (schemeAEdgeTable 1 0).1 := by
          simp [schemeAEdgeTable]
        have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
            left right := by
          simpa [left, right, schemeAEdgeTable] using
            schemeANormalizedEdgePair_identified 3 1 1 0 t hdLabel
        exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
          (schemeADevelopment_eq_identified x left hxleft)
          ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans' hedge
            (schemeADevelopment_eq_identified right y hrighty))
      · have htmem : 2 * ((schemeADevelopment y).1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          have hlower : 0 ≤ 2 * ((schemeADevelopment y).1 : ℝ) := by
            linarith [(schemeADevelopment y).1.property.1]
          have hupper : 2 * ((schemeADevelopment y).1 : ℝ) ≤ 1 := by
            linarith [(schemeADevelopment x).1.property.2]
          exact ⟨hlower, hupper⟩
        let t : unitInterval := ⟨2 * ((schemeADevelopment y).1 : ℝ), htmem⟩
        let left : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 3, TriangleDisk.edgePoint 1 t⟩
        let right : (schemeA.triangularRegions schemeA_isTriangular).Source :=
          ⟨schemeAOccurrence 1, TriangleDisk.edgePoint 0 t⟩
        have hxright : schemeADevelopment x = schemeADevelopment right := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [right, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeASecondChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
            linarith
          · simpa [right, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeASecondChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hxheight
        have hlefty : schemeADevelopment left = schemeADevelopment y := by
          apply Prod.ext <;> apply Subtype.ext
          · simp [left, t, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
          · simpa [left, schemeADevelopment_schemeAOccurrence, schemeAChart,
              schemeAFourthChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates] using
              congrArg (fun z : unitInterval ↦ (z : ℝ)) hyheight.symm
        have hdLabel : (schemeAEdgeTable 3 1).1 = (schemeAEdgeTable 1 0).1 := by
          simp [schemeAEdgeTable]
        have hedge : (schemeA.triangularRegions schemeA_isTriangular).Identified.r
            left right := by
          simpa [left, right, schemeAEdgeTable] using
            schemeANormalizedEdgePair_identified 3 1 1 0 t hdLabel
        exact (schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
          (schemeADevelopment_eq_identified x right hxright)
          ((schemeA.triangularRegions schemeA_isTriangular).Identified.trans'
            ((schemeA.triangularRegions schemeA_isTriangular).Identified.symm' hedge)
            (schemeADevelopment_eq_identified left y hlefty))

/-- Helper for Exercise 78.1: the scheme-A comparison fibers are exactly its labelled-edge
identifications. -/
theorem schemeAComparison_fibers
    (x y : (schemeA.triangularRegions schemeA_isTriangular).Source) :
    schemeAComparison x = schemeAComparison y ↔
      (schemeA.triangularRegions schemeA_isTriangular).Identified.r x y := by
  -- The two implications are the canonical-boundary lift theorem and generator compatibility.
  exact ⟨schemeAComparison_eq_imp_identified x y,
    schemeAIdentified_mapsEqual x y⟩

/-- Helper for Exercise 78.1: equal scheme-B torus-or-Klein comparison images arise from the
labelled edge relation. -/
theorem schemeBComparison_eq_imp_identified
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source)
    (hxy : schemeBComparison x = schemeBComparison y) :
    (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- Separate the two rectangle components. In each matching component, insert one intermediate
  -- developed point so the two coordinate identifications can be lifted one at a time.
  have hcomparison :
      schemeBRectangleComparison (schemeBDevelopment x) =
        schemeBRectangleComparison (schemeBDevelopment y) := by
    simpa [schemeBComparison] using hxy
  cases hxdev : schemeBDevelopment x with
  | inl p =>
      cases hydev : schemeBDevelopment y with
      | inl q =>
          have htorus : TorusSquare.toTorus p = TorusSquare.toTorus q := by
            simpa [schemeBRectangleComparison, hxdev, hydev] using hcomparison
          obtain ⟨hfirst, hsecond⟩ := (torusSquareToTorus_eq_iff p q).mp htorus
          obtain ⟨middle, hmiddle⟩ :=
            schemeBDevelopment_surjective (Sum.inl (q.1, p.2))
          have hxm := schemeBTorusFirstEndpoint_identified x middle p (q.1, p.2)
            hxdev hmiddle hfirst rfl
          have hmy := schemeBTorusSecondEndpoint_identified middle y (q.1, p.2) q
            hmiddle hydev rfl hsecond
          exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hxm hmy
      | inr q =>
          simp [schemeBRectangleComparison, hxdev, hydev] at hcomparison
  | inr p =>
      cases hydev : schemeBDevelopment y with
      | inl q =>
          simp [schemeBRectangleComparison, hxdev, hydev] at hcomparison
      | inr q =>
          have hklein : kleinHalfFullMap p = kleinHalfFullMap q := by
            simpa [schemeBRectangleComparison, hxdev, hydev] using hcomparison
          rcases (kleinHalfFullMap_eq_iff p q).mp hklein with
              ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
          · exact schemeBKleinSecondEndpoint_identified x y p q
              hxdev hydev hfirst hsecond
          · obtain ⟨middle, hmiddle⟩ :=
              schemeBDevelopment_surjective
                (Sum.inr (q.1, unitInterval.symm p.2))
            have hxm := schemeBKleinReflection_identified x middle p
              (q.1, unitInterval.symm p.2) hxdev hmiddle hfirst rfl
            have hendpoint :
                unitInterval.endpointSetoid (unitInterval.symm p.2) q.2 :=
              unitInterval.endpointSetoid.symm' hsecond
            have hmy := schemeBKleinSecondEndpoint_identified middle y
              (q.1, unitInterval.symm p.2) q hmiddle hydev rfl hendpoint
            exact (schemeB.triangularRegions schemeB_isTriangular).Identified.trans' hxm hmy

/-- Helper for Exercise 78.1: the scheme-B comparison fibers are exactly its labelled-edge
identifications. -/
theorem schemeBComparison_fibers
    (x y : (schemeB.triangularRegions schemeB_isTriangular).Source) :
    schemeBComparison x = schemeBComparison y ↔
      (schemeB.triangularRegions schemeB_isTriangular).Identified.r x y := by
  -- Combine canonical-boundary lifting with the already verified generator compatibility.
  exact ⟨schemeBComparison_eq_imp_identified x y,
    schemeBIdentified_mapsEqual x y⟩



/-- Helper for Exercise 78.1: a quotient map with exactly the labelled-edge fibers identifies the
explicit relation quotient with its target. -/
theorem quotientHomeomorphOfRealizes {α : Type u} {scheme : LabellingScheme α}
    (regions : LabellingScheme.PolygonalRegions scheme)
    {X : Type w} [TopologicalSpace X] (q : regions.Source → X)
    (hq : regions.Realizes q) : Nonempty (Quotient regions.Identified ≃ₜ X) := by
  -- Replace the realization relation by the kernel relation of the quotient map.
  let qContinuous : C(regions.Source, X) := ⟨q, hq.isQuotientMap.continuous⟩
  let relationEquiv : Quotient regions.Identified ≃ₜ Quotient (Setoid.ker q) :=
    Homeomorph.Quotient.congrRight (r := regions.Identified) (r' := Setoid.ker q)
      (fun x y ↦ (hq.fibers x y).symm)
  -- The standard quotient-kernel homeomorphism identifies that kernel quotient with `X`.
  exact ⟨relationEquiv.trans
    (Topology.IsQuotientMap.homeomorph (f := qContinuous) hq.isQuotientMap)⟩

/-- Helper for Exercise 78.1: any two maps realizing the same labelled-edge relation have
homeomorphic targets. -/
theorem homeomorphOfRealizes {α : Type u} {scheme : LabellingScheme α}
    (regions : LabellingScheme.PolygonalRegions scheme)
    {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (qX : regions.Source → X) (qY : regions.Source → Y)
    (hX : regions.Realizes qX) (hY : regions.Realizes qY) : Nonempty (X ≃ₜ Y) := by
  -- Compare both targets through the quotients by their kernel relations.
  let qXContinuous : C(regions.Source, X) := ⟨qX, hX.isQuotientMap.continuous⟩
  let qYContinuous : C(regions.Source, Y) := ⟨qY, hY.isQuotientMap.continuous⟩
  let kernelEquiv : Quotient (Setoid.ker qX) ≃ₜ Quotient (Setoid.ker qY) :=
    Homeomorph.Quotient.congrRight (r := Setoid.ker qX) (r' := Setoid.ker qY)
      (fun x y ↦ (hX.fibers x y).trans (hY.fibers x y).symm)
  -- Compose the two quotient-kernel homeomorphisms with this relation comparison.
  exact ⟨(Topology.IsQuotientMap.homeomorph (f := qXContinuous) hX.isQuotientMap).symm |>.trans
    (kernelEquiv.trans
      (Topology.IsQuotientMap.homeomorph (f := qYContinuous) hY.isQuotientMap))⟩

/-- Helper for Exercise 78.1: scheme A has a quotient map to the Klein bottle whose fibers
are exactly the labelled-edge identifications. -/
theorem existsSchemeARealizesKleinBottle :
    ∃ comparison : (schemeA.triangularRegions schemeA_isTriangular).Source → KleinBottle,
      (schemeA.triangularRegions schemeA_isTriangular).Realizes comparison := by
  -- Package the verified two-stage quotient map and its exact fiber theorem.
  refine ⟨schemeAComparison, ?_⟩
  constructor
  · exact schemeAComparison_isQuotientMap
  · intro x y
    exact schemeAComparison_fibers x y

/-- Helper for Exercise 78.1: scheme B has a quotient map to the sum of a torus and a Klein
bottle whose fibers are exactly the labelled-edge identifications. -/
theorem existsSchemeBRealizesTorusSumKleinBottle :
    ∃ comparison : (schemeB.triangularRegions schemeB_isTriangular).Source →
        (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle,
      (schemeB.triangularRegions schemeB_isTriangular).Realizes comparison := by
  -- Package the sum-of-rectangles quotient map and its exact fiber theorem.
  refine ⟨schemeBComparison, ?_⟩
  constructor
  · exact schemeBComparison_isQuotientMap
  · intro x y
    exact schemeBComparison_fibers x y

/-- Helper for Exercise 78.1: the realization of the four triangular regions labelled `abc`,
`dae`, `bef`, and `cdf` is homeomorphic to the Klein bottle. -/
theorem schemeA_homeomorphicKleinBottle :
    Nonempty ((schemeA.triangularRegions schemeA_isTriangular).Realization ≃ₜ KleinBottle) := by
  -- Compare the canonical relation quotient with the scheme-specific Klein-bottle realization.
  obtain ⟨comparison, hcomparison⟩ := existsSchemeARealizesKleinBottle
  exact homeomorphOfRealizes (schemeA.triangularRegions schemeA_isTriangular)
    (schemeA.triangularRegions schemeA_isTriangular).quotientMap comparison
    (schemeA.triangularRegions schemeA_isTriangular).quotientMap_realizes hcomparison

/-- Helper for Exercise 78.1: the realization of the four triangular regions labelled `abc`,
`cba`, `def`, and `d f e⁻¹` is homeomorphic to the disjoint sum of a torus and a Klein bottle. -/
theorem schemeB_homeomorphicTorusSumKleinBottle :
    Nonempty
      ((schemeB.triangularRegions schemeB_isTriangular).Realization ≃ₜ
        (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle) := by
  -- Compare the canonical relation quotient with the componentwise torus/Klein realization.
  obtain ⟨comparison, hcomparison⟩ := existsSchemeBRealizesTorusSumKleinBottle
  exact homeomorphOfRealizes (schemeB.triangularRegions schemeB_isTriangular)
    (schemeB.triangularRegions schemeB_isTriangular).quotientMap comparison
    (schemeB.triangularRegions schemeB_isTriangular).quotientMap_realizes hcomparison

/-- Exercise 78.1: the first four-triangle scheme yields the Klein bottle, while the second
yields the disjoint sum of a torus and a Klein bottle. -/
theorem fourTriangleSchemes_homeomorphismTypes :
    Nonempty ((schemeA.triangularRegions schemeA_isTriangular).Realization ≃ₜ KleinBottle) ∧
      Nonempty
        ((schemeB.triangularRegions schemeB_isTriangular).Realization ≃ₜ
          (UnitAddCircle × UnitAddCircle) ⊕ KleinBottle) := by
  -- Assemble the two independently established identifications into the exercise's answer.
  exact ⟨schemeA_homeomorphicKleinBottle, schemeB_homeomorphicTorusSumKleinBottle⟩

end FourTrianglePasting
