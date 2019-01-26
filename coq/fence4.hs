import ClipPolygon -- Import from clipPolygon.hs, generated via coq extraction.

instance Prelude.Show IsClipableResult where
    show (CR_FullyWithin v l) = "Unclipable (fully within): { v: " ++ (Prelude.show v) ++ ", l: " ++ (Prelude.show l) ++ " }"
    show (CR_ThroughEye v l) = "Unclipable (through eye): { v: " ++ (Prelude.show v) ++ ", l: " ++ (Prelude.show l) ++ " }"
    show (CR_ThroughBack v l) = "Unclipable (through back): { v: " ++ (Prelude.show v) ++ ", l: " ++ (Prelude.show l) ++ " }"
    show CR_Clipable = "Clipable"

instance Prelude.Show ClippingResult where
    show (Visible l) = "Visible: { l: " ++ (Prelude.show l) ++ " }"
    show Invisible = "Invisible"
    show (Unclipable cr) = Prelude.show cr
    show (CollinearViewPort e l) = "CollinearViewPort : { e: " ++ (Prelude.show e) ++ ", l: " ++ (Prelude.show l) ++ " }"

instance Prelude.Show Q where
  show (Qmake p q) = (Prelude.show p) ++ (if q == 1 then "" else "/" ++ (Prelude.show q))

instance Prelude.Show Triple0 where
  show (Triple a b c) = "[" ++ (Prelude.show a) ++ ", " ++ (Prelude.show b) ++ ", " ++ (Prelude.show c) ++ "]"

instance Prelude.Show LineSeg0 where
  show (LineSeg p q) = "{ p: " ++ (Prelude.show p) ++ ", q: " ++ (Prelude.show q) ++ " }"

instance Prelude.Show ViewPort0 where
  show (ViewPort e l) = "{ e: " ++ (Prelude.show e) ++ ", lv: " ++ (Prelude.show l) ++ " }"

readPoint :: String -> Prod Prelude.Integer Prelude.Integer
readPoint s = Pair (read x :: Prelude.Integer) (read y :: Prelude.Integer)
    where (x:y:_) = words s

getInput :: String -> Prod (Prod Prelude.Integer Prelude.Integer) ([Prod Prelude.Integer Prelude.Integer])
getInput s = Pair (readPoint leye) (Prelude.map readPoint leps)
    where (_:leye:leps) = lines s

main = interact $ unlines . (Prelude.map show) . clipPolygon . getInput
