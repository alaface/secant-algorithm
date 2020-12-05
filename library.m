// IsSeparating 
// INPUT: a set of points pts, a vector v
// OUTPUT: true if there exists 
// a simplex whose baricenter in the 
// direction m attains the maximum
// false otherwise

IsSeparating := function(pts,v)
 M := Parent(Random(pts));
 N := Dual(M);
 v := N!v;
 n := Dimension(M);
 lis := Sort([[v*p] cat Eltseq(p) : p in pts]);
 lis := [<u[1],M!u[2..#u]> : u in lis];
 mat := Matrix([[1] cat Eltseq(p[2]) : p in lis]);
 r := Rank(mat);
 if #{p[1] : p in lis} lt #pts or r le n 
  then return false,r;
 else
  simp := [lis[#lis][2]];
  ms := RowSubmatrix(mat,[#lis]);
  i := 0;
  repeat
   i := i + 1;
   C := RowSubmatrix(mat,[#lis-i]);
   mst := VerticalJoin(C,ms);
   if Rank(mst) gt Rank(ms) 
    then 
     ms := mst;
     Append(~simp,lis[#lis-i][2]);
    end if;
  until Rank(ms) eq n+1;
 end if;
 return true,simp;
end function;


// RemovePoints
// INPUT: two set/sequence of points A, S
// OUTPUT: the difference A diff S

RemovePoints := function(A,S)
 return Set(A) diff Set(S);
end function;


// Findv
// INPUT: a set of points pts
// OUTPUT: a direction v such that v separates 
// a simplex of pts

Findv := function(pts)
 M := Parent(Random(pts));
 N := Dual(M);
 n := Dimension(M);
 repeat
  v := N![Random([-50..50])+1/10^(i-1) : i in [1..n]];
 until IsSeparating(pts,v);
 return v;
end function;


// FindTriangulation
// INPUT: a set of points pts
// OUTPUT: a partial triangulation of pts, the residual coplanar points

FindTriangulation := function(pts)
 M := Parent(Random(pts));
 N := Dual(M);
 n := Dimension(M);
 simp := <>;
 repeat
  v := Findv(pts);
  _,S := IsSeparating(pts,v);
  Append(~simp,S);
  pts := RemovePoints(pts,S);
  mat := Matrix([[1] cat Eltseq(p) : p in pts]);
 until Rank(mat) le n or #pts eq n+1;
  if Rank(mat) le n then
   return simp,pts;
  else
   Append(~simp,Setseq(pts));
   return simp,{};
  end if;
end function;


// TestDef
// INPUT: a set of points pts, a positive integer k
// OUTPUT: a boolean, a partial triangulation of pts, the residual coplanar points
// the best of k attempts

TestDef := function(pts,k)
 M := Parent(Random(pts));
 N := Dual(M);
 n := Dimension(M);
 lis := <>;
 for i in [1..k] do
  tri,pp := FindTriangulation(pts);
  Append(~lis,<tri,pp>);
  if #pp le n then break; end if;
 end for;
 _,i := Min([#p[2] : p in lis]);
 pp := lis[i][2];
 if #pp eq 0 then return false,lis[i]; end if;
 mat := Matrix([[1] cat Eltseq(p) : p in pp]);
 if Rank(mat) eq #pp then 
  return false,lis[i];
 else
  return true,lis[i];
 end if;
end function;



// CoplanarPoints
// INPUT: a polytope pol
// OUTPUT: all the subsets of > dim(pol) points 
// which lie on a hyperplane

CoplanarPoints := function(pol)
 d := Dimension(pol);
 pts := Points(pol);
 cl := {};
 for S in Subsets(pts,d) do
  p := Random(S);
  L := [q-p : q in S];
  N := {q : q in pts | Rank(Matrix(L)) eq Rank(Matrix(L cat [q-p]))};
  if #N gt d then Include(~cl,N); end if;
 end for;
 return [C : C in cl | not &or{C subset Q : Q in cl diff {C}}];
end function;


// IsSpecial
// INPUT: a polytope pol
// OUTPUT: true if the toric variety defined by pol
// admits a defective k-secant variety for some k
// false otherwise

IsSpecial := function(pol)
 N := Ambient(pol);
 P := pol-N![Min(Eltseq(R)) : R in Rows(Transpose(Matrix(Vertices(pol))))];
 d := Dimension(P);
 Q := GF(32003);
 A<[x]> := AffineSpace(Q,d);
 R := CoordinateRing(A);
 mon := [Monomial(R,Eltseq(p)) : p in Points(P)];
 L := LinearSystem(A,mon);
 r := Floor(#mon/(d+1));
 pts := [A![Random(Q) : i in [1..d]] : j in [1..r+1]];
 ls1 := LinearSystem(L,pts[1..r],[2 : i in [1..r]]);
 ls2 := LinearSystem(ls1,[pts[r+1]],[2]);
 if #mon - r*(d+1) lt Dimension(ls1) 
  then return true;
 elif Dimension(ls2) gt 0
  then return true;
 end if;
 return false;
end function;


// ProjSpace
// INPUT: positive integers m,d
// OUTPUT: the polytope of P^m embedded with degree d

ProjSpace := function(m,d)
 return Polytope([[0: i in [1..m]]] cat [[0: i in [1..j-1]] cat [d] cat [0: i in [j+1..m]]:  j in [1..m]]);
end function;


// ProjSpaces
// INPUT: two lists of positive integers n,d
// OUTPUT: the polytope of P^n_1 x ... x P^n_k 
// embedded with multidegree [d_1,...,d_k]

ProjSpaces := function(n,d)
 return &*[ProjSpace(n[i],d[i]) : i in [1..#n]];
end function;
