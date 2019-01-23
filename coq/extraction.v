Require Coq.extraction.Extraction.
Extraction Language Haskell.
Require Import ExtrHaskellZNum.
Require Import ZArith.

From F4 Require Export clipping.

Open Scope Z_scope.

Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inductive positive => "Prelude.Integer" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))".

(* Annoyingly, when run inside CoqIde the below will try to write to the directory from which CoqIde
   is run, and I cannot find a way to alter this behaviour. Fortunately, this does not arise when
   compiling from the command line with coqc which is the typical flow so we can live with this.
   The alternative would be to use an absolute path below which I refuse to do. *)
Extraction "./clipPolygon.hs" clipPolygon.
