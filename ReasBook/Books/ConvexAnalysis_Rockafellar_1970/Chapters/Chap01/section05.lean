/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part13

/-!
Overview page for `Section 1.5`.

This aggregation module imports all currently available part files for this section.

Verso links:
- [Section overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05/)
- [Chapter overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/)
- [Book overview](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/book/)

Directory:

- [Part 1 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part1.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part1/))
- [Part 2 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part2.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part2/))
- [Part 3 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part3.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part3/))
- [Part 4 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part4.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part4/))
- [Part 5 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part5.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part5/))
- [Part 6 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part6.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part6/))
- [Part 7 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part7.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part7/))
- [Part 8 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part8.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part8/))
- [Part 9 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part9.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part9/))
- [Part 10 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part10.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part10/))
- [Part 11 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part11.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part11/))
- [Part 12 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part12.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part12/))
- [Part 13 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section05_part13.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/convexanalysis_rockafellar_1970/chapters/chap01/section05_part13/))

-/
