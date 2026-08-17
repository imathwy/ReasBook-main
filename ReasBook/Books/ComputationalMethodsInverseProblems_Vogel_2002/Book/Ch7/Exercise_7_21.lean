module

public import Book.Ch7.Theorem_7_25

public section

/- Exercise 7.21. The source asks the reader to prove Theorem 7.25. In this
repository, that theorem is recorded directly by the TSVD discrepancy-choice
comparison below, so the exercise is formalized by direct reuse of the
theorem-level Chapter 7 surface rather than by repeating its statement. -/
#check TsvdDiscrepancy.isEquivalent_indexBenchmark
#check TsvdDiscrepancy.isTheta_indexBenchmark

end
