import Mathlib

import AchimKlenkeLean.Chapters.Chap01
import AchimKlenkeLean.Chapters.Chap02
import AchimKlenkeLean.Chapters.Chap03
import AchimKlenkeLean.Chapters.Chap04
import AchimKlenkeLean.Chapters.Chap05
import AchimKlenkeLean.Chapters.Chap06
import AchimKlenkeLean.Chapters.Chap07
import AchimKlenkeLean.Chapters.Chap08
import AchimKlenkeLean.Chapters.Chap09
import AchimKlenkeLean.Chapters.Chap10
import AchimKlenkeLean.Chapters.Chap11
import AchimKlenkeLean.Chapters.Chap12
import AchimKlenkeLean.Chapters.Chap13
import AchimKlenkeLean.Chapters.Chap14
import AchimKlenkeLean.Chapters.Chap15
import AchimKlenkeLean.Chapters.Chap16
import AchimKlenkeLean.Chapters.Chap17
import AchimKlenkeLean.Chapters.Chap18
import AchimKlenkeLean.Chapters.Chap19
import AchimKlenkeLean.Chapters.Chap20
import AchimKlenkeLean.Chapters.Chap21
import AchimKlenkeLean.Chapters.Chap22
import AchimKlenkeLean.Chapters.Chap23
import AchimKlenkeLean.Chapters.Chap24
import AchimKlenkeLean.Chapters.Chap25
import AchimKlenkeLean.Chapters.Chap26

/-!
Overview page for Achimklenkelean.

This aggregation module imports the currently formalized sections in this book.
Use the links below to jump directly into chapter and section overview pages.

Verso links:
- [Book home](/ReasBook-private/books/achimklenkelean/)
- [Book overview](/ReasBook-private/books/achimklenkelean/book/)

Directory:

Chapter 01

- Section 1.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap01/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap01/section01/))

Chapter 02

- Section 2.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap02/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap02/section01/))

Chapter 03

- Section 3.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap03/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap03/section01/))

Chapter 04

- Section 4.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap04/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap04/section01/))

Chapter 05

- Section 5.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap05/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap05/section01/))

Chapter 06

- Section 6.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap06/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap06/section01/))

Chapter 07

- Section 7.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap07/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap07/section01/))

Chapter 08

- Section 8.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap08/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap08/section01/))

Chapter 09

- Section 9.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap09/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap09/section01/))

Chapter 10

- Section 10.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap10/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap10/section01/))

Chapter 11

- Section 11.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap11/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap11/section01/))

Chapter 12

- Section 12.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap12/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap12/section01/))

Chapter 13

- Section 13.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap13/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap13/section01/))

Chapter 14

- Section 14.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap14/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap14/section01/))

Chapter 15

- Section 15.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap15/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap15/section01/))

Chapter 16

- Section 16.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap16/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap16/section01/))

Chapter 17

- Section 17.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap17/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap17/section01/))

Chapter 18

- Section 18.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap18/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap18/section01/))

Chapter 19

- Section 19.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap19/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap19/section01/))

Chapter 20

- Section 20.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap20/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap20/section01/))

Chapter 21

- Section 21.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap21/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap21/section01/))

Chapter 22

- Section 22.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap22/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap22/section01/))

Chapter 23

- Section 23.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap23/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap23/section01/))

Chapter 24

- Section 24.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap24/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap24/section01/))

Chapter 25

- Section 25.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap25/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap25/section01/))

Chapter 26

- Section 26.1 ([Documentation](/ReasBook-private/docs/Books/AchimKlenkeLean/Chapters/Chap26/section01.html)) ([Verso](/ReasBook-private/books/achimklenkelean/chapters/chap26/section01/))

-/

/-!
# AchimKlenkeLean

Auto-managed aggregation root for `AchimKlenkeLean`.
Keep project mathematics in `Chapters/` and let the orchestrator manage
the import block above.
-/
