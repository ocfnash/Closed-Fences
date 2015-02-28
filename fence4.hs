import Data.Tuple (swap)
import Control.Monad (foldM)

det (a, b)
    (c, d) = a*d - b*c

det3 :: Point -> Point -> Point -> Int
det3 (Point a b c)
     (Point d e f)
     (Point g h i) = a * det (e, f) (h, i) -
                     b * det (d, f) (g, i) +
                     c * det (d, e) (g, h)

data Point = Point Int Int Int deriving (Show)
instance Eq Point where
    Point x1 y1 z1 == Point x2 y2 z2 =
        det (y1, z1) (y2, z2) == 0 &&
        det (x1, z1) (x2, z2) == 0 &&
        det (x1, y1) (x2, y2) == 0

type Line = (Point, Point)
type LineSeg = Line
type ViewPort = (Point, LineSeg)

data Edge = EdgeA | EdgeB deriving (Eq)

intersectLineLine :: Line -> Line -> Point
intersectLineLine ((Point x1 y1 z1), (Point x2 y2 z2))
                  ((Point x3 y3 z3), (Point x4 y4 z4)) =
    let a = det (x1, y1) (x2, y2)
        b = det (x1, z1) (x2, z2)
        c = det (x3, y3) (x4, y4)
        d = det (x3, z3) (x4, z4)
        e = det (y1, z1) (y2, z2)
        f = det (y3, z3) (y4, z4)
    in Point (det (a, b) (c, d)) (det (a, e) (c, f)) (det (b, e) (d, f))

pointOnLine :: Point -> Line -> Bool
pointOnLine p (lp, lq) = (det3 p lp lq == 0)

-- Assumes point on line.
pointOnLineSeg :: Point -> LineSeg -> Bool
pointOnLineSeg (Point px py pz) ((Point x1 y1 z1), (Point x2 y2 z2))
    | pz == 0   = False
    | otherwise = (0 <= top) && (top <= bottom)
    where a = det (py, pz) (y1, z1)
          b = det (y2, z2) (y1, z1)
          c = det (px, pz) (x2, z2)
          d = det (x1, z1) (x2, z2)
          sb = signum(pz*b)
          sd = signum(pz*d)
          (top, bottom) = if d == 0 then (sb*z2*a, sb*pz*b)
                                    else (sd*z1*c, sd*pz*d)

-- Lazy evaluation saves trying to intersect line with itself.
lineSegMeetsLine :: LineSeg -> Line -> Bool
lineSegMeetsLine ls l = pointOnLine (fst ls) l ||
                        pointOnLineSeg (intersectLineLine l ls) ls

-- Again, lazy evaluation saves trying to intersect line with itself.
lineSegMeetsLineSeg :: LineSeg -> LineSeg -> Bool
lineSegMeetsLineSeg l m
    | sameLine  = (pointOnLineSeg lp m ||
                   pointOnLineSeg lq m ||
                   pointOnLineSeg mp l ||
                   pointOnLineSeg mq l)
    | otherwise = lineSegMeetsLine l m && lineSegMeetsLine m l
    where (lp, lq) = l
          (mp, mq) = m
          sameLine = pointOnLine lp m && pointOnLine lq m

reducePoint :: Point -> Point
reducePoint (Point x y z) = let d = (if z < 0 then -1 else 1) * gcd x (gcd y z)
                            in Point (x `div` d) (y `div` d) (z `div` d)

sameSidest :: LineSeg -> Line -> Point -> Point
sameSidest (i, j) (p, q) r = if sr > 0 then if si > sj then i else j
                             else if si < sj then i else j
                             where si = signum $ det3 i p q
                                   sj = signum $ det3 j p q
                                   sr = signum $ det3 r p q

clipEdge :: Edge -> LineSeg -> ViewPort -> ViewPort
clipEdge edge ls (e, (a, b)) = (e, fn (a'', b'))
    where fn = if edge == EdgeA then id else swap
          (a', b') = fn (a, b)
          a'' = reducePoint $ intersectLineLine (a, b) (e, sameSidest ls (e, a') b')

clipByOneSide :: ViewPort -> LineSeg -> Maybe ViewPort
clipByOneSide v ls
    | meetsEA && meetsEB       = Nothing
    | not (meetsEA || meetsEB) = Just v
    | i == a || j == a         = Just $ if lineSegMeetsLine (b, e) ls then clipEdge EdgeA ls v else v
    | i == b || j == b         = Just $ if lineSegMeetsLine (a, e) ls then clipEdge EdgeB ls v else v
    | meetsEA                  = Just $ clipEdge EdgeA ls v
    | meetsEB                  = Just $ clipEdge EdgeB ls v
    where (e, (a, b)) = v
          (i, j) = ls
          meetsEA = lineSegMeetsLineSeg (e, a) ls
          meetsEB = lineSegMeetsLineSeg (e, b) ls

rotate l k = take (length l) $ drop (k + length l) $ cycle l

clipByAllSides :: Point -> [Point] -> Int -> Maybe LineSeg
clipByAllSides e endPoints k
    | d == 0    = Nothing
    | otherwise = let v = if d > 0 then (e, (i, j)) else (e, (j, i))
                      edges = zip endPoints (rotate endPoints 1)
                      edges' = take (n-1) $ rotate edges (k+1)
                  in fmap snd $ foldM clipByOneSide v edges'
    where n = length endPoints
          i = endPoints !! k
          j = endPoints !! ((k+1) `mod` n)
          d = det3 e i j

readPoint :: String -> Point
readPoint s = Point (read x :: Int) (read y :: Int) 1 
    where (x:y:_) = words s

getInput :: String -> (Point, [Point])
getInput s = (readPoint leye, map readPoint leps)
    where (_:leye:leps) = lines s

getResult :: (Point, [Point]) -> [Bool]
getResult (eye, endPoints) = map ((/=) Nothing) clippedSides
    where clippedSides = map (clipByAllSides eye endPoints) [0..length endPoints-1]

main = interact $ show . getResult . getInput
