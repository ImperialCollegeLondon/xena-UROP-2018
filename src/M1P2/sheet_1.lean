import linear_algebra.basic

-- obviously can't do any of this until matrix stuff and linear algebra has been developed
-- need to format matrices better

-- *1. The rank of an m × n matrix A is defined to be the dimension of its row space R−Span(A) and is denoted by rankA. Let A be an m×n matrix and B an n×p matrix.
-- (i) Let v be a row vector in Rn. Prove that vB is a linear combination of the rows of B.
-- (ii) Prove that the row space of AB is contained in the row space of B and rank AB ≤
-- rankB.
-- (iii) Prove that if m = n and A is invertible, then rank AB = rank B.
-- (iv) Prove that rank AB ≤ rank A.


-- 2.(i) Find the ranks of the matrices \mat{1,3,1,-2,-3 // 1,4,3,-1,-4 // 2,3,-4,-7,-3}

-- (ii) Find an equation for a and b such that the following matrix has rank 2:

-- (iii) Find an equation for b, c and d such that the matrices both have the same rank.

-- 3. Let V be a finite-dimensional vector space. For each of the following statements, say whether it is true or false. If it is true, give a justification; otherwise find a counterexample.
-- (i) If {v1,...,vn} is a basis for V and {w1,...,ws} is a spanning set for V,then n≤s.
-- (ii) If {v1,...,vn} is a basis, for V, and {x1,...,xr} is a linearly independent subset of V with r < n, and if vi ∈/ Span{x1,...,xr} for all i, then {x1,...,xr,vr+1,...,vn} is a basis for V .
-- (iii) If U is a subspace of V , then U + U = U.
-- (iv) If U and W are subspaces of V,and dimU + dimW = dimV,then U∩W ={0}.
-- (v) If dimV =n and v₁ ∈V,then there exist vectors v₂,...,vn ∈ V such that {v1,...,vn} spans V .
-- 4.
-- (i) Let U and W be the following subspaces of R4:
-- U ={(x₁,x₂,x₃,x₄)∈ R4 |x₁ +x₂ +x₄ =−x₁ +x₂ +x₃ =0},
-- W ={(x₁,x₂,x₃,x₄)∈ R4 |2x₁ +x₃ −x₄ =−x₁ +2x₂ +x₃ +x₄ =0}.
-- Find a basis of U ∩W.
-- Find bases of U and of W, both of which contain your basis of U ∩ W. Find a basis of U + W containing your basis of U ∩ W.
-- (ii) Let X and Y be the following subspaces of R4:
-- X = Span{(1, 1, 0, −1), (1, 2, 3, 0), (2, 3, 3, −1)},
-- Y =Span{(1,2,2,−2),(2,3,2,−3),(1,3,4,−3)}. Find bases of X ∩ Y and X + Y .
-- (iii) Let X and Y be as in part (ii). Find a subspace Z of R4 with the properties that R4 =X+Z=Y +Z,andX∩Z=Y ∩Z={0}.
-- 5.
-- (ii) Let U₁, U₂ and U₃ be 3-dimensional subspaces of R4. Give a proof that dim U₁∩U₂ ≥ 2. Deduce that U₁ ∩ U₂ ∩ U₃  ̸= {0}.
-- (iii) Now let V be the vector space of 2 × 3 matrices over R. Find subspaces X and Y of V such that dimX = dimY = 4,and dim X∩Y =2.
-- (iv) Let V be as in part (iii). Do there exist subspaces X and Y of V such that dim X = 3, dimY =5,and dimX∩Y =1?