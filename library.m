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
 lis := Sort([<v*p,p> : p in pts]);
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
   Append(~simp,pts);
   return simp,{};
  end if;
end function;


// Test
// INPUT: a set of points pts, a positive integer k
// OUTPUT: a partial triangulation of pts, the residual coplanar points
// the best of k attempts

Test := function(pts,k)
 lis := <>;
 for i in [1..k] do
  tri,pp := FindTriangulation(pts);
  Append(~lis,<tri,pp>);
 end for;
 _,i := Min([#p[2] : p in lis]);
 return lis[i];
end function;
