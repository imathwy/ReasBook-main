import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_9_33 (from Items/Chap09) -/
/- Remark 9.33: The submartingale analogues singled out in the text already belong to the
canonical mathlib owner API. Negating a submartingale produces a supermartingale. -/
recall MeasureTheory.Submartingale.neg

/- Negating a supermartingale produces a submartingale, giving the converse sign-change duality. -/
recall MeasureTheory.Supermartingale.neg

/- The pointwise maximum of two submartingales is again a submartingale. -/
recall MeasureTheory.Submartingale.sup
