
------------------------
---- Primitive data ----
------------------------

data Point a = Pt a 

data Line a = Ln a

data LiesOn : Point a -> Line a -> Type where

data Between : Point a -> Point a -> Point a -> Type where

data LineCong: Line a -> Line a -> Type where

record Angle a where
  constructor MkAngle
  l1 : Line a
  l2 : Line a

record Segment a where
  constructor MkSegment
  p1 : Point a
  p2 : Point a

data SegCong : Segment a -> Segment a -> Type where

newSegment : (p1 : Point a) -> (p2 : Point a) -> (l : Line a) -> 
                 {auto prf1 : LiesOn p1 l} -> {auto prf2 : LiesOn p2 l} -> Segment a
newSegment p1 p2 l = MkSegment p2 p2

data AngleCongruence : Angle a -> Angle a -> Type where
  AngleCong : (a1 : Angle a) -> (a2 : Angle a) -> AngleCongruence a1 a2

Seg : (p1 : Point a) -> (p2 :  Point a) -> Type
Seg p1 p2 = (l : Line a ** (LiesOn p1 l, LiesOn p2 l))

--------------------------
---- Hilbert's Axioms ----
--------------------------

contains : (p1 : Point a) -> (p2 : Point a) -> (l : Line a) -> Type
contains p1 p2 l = (p1 `LiesOn` l, p2 `LiesOn` l)

Intersect : (l1 : Line x) -> (l2 : Line x) -> Type
Intersect l1 l2 = (p : Point x ** (p `LiesOn` l1, p `LiesOn` l2))

contains' : (p1 : Point a) -> (p2 : Point a) -> (p3 : Point a) -> (l : Line a) -> Type
contains' p1 p2 p3 l = (p1 `LiesOn` l, p2 `LiesOn` l, p3 `LiesOn` l)
syntax "[" [p1] [p2] "=" [l] "]" = contains p1 p2 l
syntax "[" [p1] [p2] [p3] "=" [l] "]" = contains' p1 p2 p3 l
syntax "[" [a] ">" [b] "<" [c] "]"= Between a b c

sym : [p1 p2 = l] -> [p2 p1 = l]
sym (a, b) = (b, a)

--Incidence
||| Given two points p1 and p2 there exist a line l such that l contains p1 and p2
postulate I1 : (p1 : Point a) -> (p2 : Point a) -> (l : Line a ** [ p1 p2 = l ])

||| given two points p1 and p2 there exist no more than one line that contains them both
postulate I2 : (p1 : Point a) -> (p2 : Point a) -> (l1 : Line a) -> (l2 : Line a) ->
               [ p1 p2 = l1 ] -> [ p1 p2 = l2 ] -> l1 = l2

||| There exist at least two points on a line
postulate I3 : (l : Line a) -> DPair (Point a, Point a) (\pair => 
               case pair of
                    (p1, p2) => [p1 p2 = l])
||| There exist at least three points that do not lie on the same line
postulate I3' : (l : Line a) -> DPair (Point a, Point a, Point a) (\triple =>
                case triple of
                     (p1, p2, p3) => ([p1 p2 = l], Not (p3 `LiesOn` l)))

--Order
||| If B is between A and C then B is between C and A, and there exist a line containing all three
postulate II1 : (a : Point x) -> (b : Point x) -> (c : Point x) -> [a > b < c] ->
                [c > b < a]
postulate II1': (a : Point x) -> (b : Point x) -> (c : Point x) -> [a > b < c] ->
                (l : Line x ** [a b c = l])

||| If A and C are two points on a line then there exist B between A and C which is on the line too
postulate II2 : (a : Point x) -> (c : Point x) -> [a c = l] -> (b : Point x ** ([a > b < c], b `LiesOn` l))

||| for any three points on a line there is at most one which is between the two others
postulate II3 : (a : Point x) -> (b : Point x) -> (c : Point x) -> [a b c = l] -> 
                (Either (Either (b = c) (b = a)) [a > b < c])
                
||| Given three points and a line that does not cross with any of them
||| if the line goes between a and b then it also either goes betwneen a and c or b and c
postulate II4 : (a : Point x) -> (b : Point x) -> (c : Point x) -> (l : Line x) -> 
                Not (a `LiesOn`l) -> Not (b `LiesOn` l) -> Not (c `LiesOn` l) ->
                (k : Point x) -> [a > k < b] -> k `LiesOn` l ->
                     (m : Point x ** (m `LiesOn` l, Either [a > m < c] [b > m < c]))


-- Congruence
postulate III1 : [a b = l] -> Not (a = b) -> (a' : Point x) -> a `LiesOn` d

postulate III2 : (s1 : Seg p1 p2) -> (s2 : Seg p3 p4) -> (s3 : Seg p5 p6) ->
                 SegCong s1 s2 -> SegCong s1 s3 -> SegCong s2 s3

-- Parallels
||| given a line `l` and a point `p` not on the line, there exist at most one line phat passes through `p` and
||| does not interesect `l`
postulate IV : (l : Line x) -> (p : Point x) -> (Not (p `LiesOn` l)) ->
               ((k : Line x ** (p `LiesOn` k, Not (Intersect l k))),
               (k' : Line x ** (p `LiesOn` k', Not (Intersect l k')))) ->
               k = k'
