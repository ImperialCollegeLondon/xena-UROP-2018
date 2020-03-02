# Geometry in Lean
An attempt to formalise geometry in Lean.

## Outline

During the summer of 2018, I was part of the Xena project run by Kevin Buzzard. I found this book: 

Schwabhäuser, W., Szmielew, W., and Alfred Tarski, 1983. Metamathematische Methoden in der Geometrie. Springer-Verlag.

Using google translate, I was able to work out most of what was going on. I mostly stuck to the progression in the book, following the chapters one by one. Of course, I was learning Lean during this period, so I made many revisions to my older code as I learned new things. I am by no means an expert at Lean, so I am sure there are many ways to improve my code. I'm going to make a more detailed explanation of my code in another file.

### Rough Summary

I chose to use Tarki's system of axioms, and it turns out the geocoq also used tarski. I went through the book above, chapter by chapter proving everything. Some cases where they prove general results, I only proved in two dimensions, since that was all I was interested about. I tried to stay computable where possible, but the 11th axiom (regarding continuity of a segment) is of course noncomputable. I know I did not do this in the most elegant way, and I hope it can be improved in the future.

I named my theorems the same as in the book, so theorem 13.1 is thirteen1 in my code. I went through most of the early chapters fairly quickly, but I struggled a lot when I got to chapter 13. After introducing the cosine function, the book uses it to prove theorems on similarity. I would have liked to have been able to identify my lengths with the positive reals, but that surpasses my lean knowledge.

**Message me on zulip (ali sever) if there's anything that needs further explanation.**
