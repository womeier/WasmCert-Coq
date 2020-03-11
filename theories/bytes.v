From compcert Require Import Integers.
Require Import Coq.Arith.Le.
From parseque Require Import Char.

Instance: EqDec.EqDec Integers.byte := {
  eq_dec := Integers.Byte.eq_dec;
}.

Fixpoint encode (n : nat) :=
  match n with
  | 0 => Integers.Byte.zero
  | S n' => Integers.Byte.add Integers.Byte.one (encode n')
  end.

(* TODO: is there a better way to do this? With LTac? *)
Notation "#A" := 10.
Notation "#B" := 11.
Notation "#C" := 12.
Notation "#D" := 13.
Notation "#E" := 14.
Notation "#F" := 15.
Notation "#00" := Integers.Byte.zero.
Notation "#01" := Integers.Byte.one.
Notation "#02" := (encode 2).
Notation "#03" := (encode 3).
Notation "#04" := (encode 4).
Notation "#05" := (encode 5).
Notation "#06" := (encode 6).
Notation "#07" := (encode 7).
Notation "#08" := (encode 8).
Notation "#09" := (encode 9).
Notation "#0A" := (encode #A).
Notation "#0B" := (encode #B).
Notation "#0C" := (encode #C).
Notation "#0D" := (encode #D).
Notation "#0E" := (encode #E).
Notation "#0F" := (encode #F).
Notation "#10" := (encode (1 * 16)).
Notation "#11" := (encode (1 * 16 + 1)).
Notation "#1A" := (encode (1 * 16 + #A)).
Notation "#1B" := (encode (1 * 16 + #B)).
Notation "#20" := (encode (2 * 16)).
Notation "#21" := (encode (2 * 16 + 1)).
Notation "#22" := (encode (2 * 16 + 2)).
Notation "#23" := (encode (2 * 16 + 3)).
Notation "#24" := (encode (2 * 16 + 4)).
Notation "#25" := (encode (2 * 16 + 5)).
Notation "#26" := (encode (2 * 16 + 6)).
Notation "#27" := (encode (2 * 16 + 7)).
Notation "#28" := (encode (2 * 16 + 8)).
Notation "#29" := (encode (2 * 16 + 9)).
Notation "#2A" := (encode (2 * 16 + #A)).
Notation "#2B" := (encode (2 * 16 + #B)).
Notation "#2C" := (encode (2 * 16 + #C)).
Notation "#2D" := (encode (2 * 16 + #D)).
Notation "#2E" := (encode (2 * 16 + #E)).
Notation "#2F" := (encode (2 * 16 + #F)).
Notation "#30" := (encode (3 * 16)).
Notation "#31" := (encode (3 * 16 + 1)).
Notation "#32" := (encode (3 * 16 + 2)).
Notation "#33" := (encode (3 * 16 + 3)).
Notation "#34" := (encode (3 * 16 + 4)).
Notation "#35" := (encode (3 * 16 + 5)).
Notation "#36" := (encode (3 * 16 + 6)).
Notation "#37" := (encode (3 * 16 + 7)).
Notation "#38" := (encode (3 * 16 + 8)).
Notation "#39" := (encode (3 * 16 + 9)).
Notation "#3A" := (encode (3 * 16 + #A)).
Notation "#3B" := (encode (3 * 16 + #B)).
Notation "#3C" := (encode (3 * 16 + #C)).
Notation "#3D" := (encode (3 * 16 + #D)).
Notation "#3E" := (encode (3 * 16 + #E)).
Notation "#3F" := (encode (3 * 16 + #F)).

Notation "#40" := (encode (4 * 16 + 0)).
Notation "#41" := (encode (4 * 16 + 1)).
Notation "#42" := (encode (4 * 16 + 2)).
Notation "#43" := (encode (4 * 16 + 3)).
Notation "#44" := (encode (4 * 16 + 4)).
Notation "#45" := (encode (4 * 16 + 5)).
Notation "#46" := (encode (4 * 16 + 6)).
Notation "#47" := (encode (4 * 16 + 7)).
Notation "#48" := (encode (4 * 16 + 8)).
Notation "#49" := (encode (4 * 16 + 9)).
Notation "#4A" := (encode (4 * 16 + #A)).
Notation "#4B" := (encode (4 * 16 + #B)).
Notation "#4C" := (encode (4 * 16 + #C)).
Notation "#4D" := (encode (4 * 16 + #D)).
Notation "#4E" := (encode (4 * 16 + #E)).
Notation "#4F" := (encode (4 * 16 + #F)).

Notation "#50" := (encode (5 * 16 + 0)).
Notation "#51" := (encode (5 * 16 + 1)).
Notation "#52" := (encode (5 * 16 + 2)).
Notation "#53" := (encode (5 * 16 + 3)).
Notation "#54" := (encode (5 * 16 + 4)).
Notation "#55" := (encode (5 * 16 + 5)).
Notation "#56" := (encode (5 * 16 + 6)).
Notation "#57" := (encode (5 * 16 + 7)).
Notation "#58" := (encode (5 * 16 + 8)).
Notation "#59" := (encode (5 * 16 + 9)).
Notation "#5A" := (encode (5 * 16 + #A)).
Notation "#5B" := (encode (5 * 16 + #B)).
Notation "#5C" := (encode (5 * 16 + #C)).
Notation "#5D" := (encode (5 * 16 + #D)).
Notation "#5E" := (encode (5 * 16 + #E)).
Notation "#5F" := (encode (5 * 16 + #F)).

Notation "#60" := (encode (6 * 16 + 0)).
Notation "#61" := (encode (6 * 16 + 1)).
Notation "#62" := (encode (6 * 16 + 2)).
Notation "#63" := (encode (6 * 16 + 3)).
Notation "#64" := (encode (6 * 16 + 4)).
Notation "#65" := (encode (6 * 16 + 5)).
Notation "#66" := (encode (6 * 16 + 6)).
Notation "#67" := (encode (6 * 16 + 7)).
Notation "#68" := (encode (6 * 16 + 8)).
Notation "#69" := (encode (6 * 16 + 9)).
Notation "#6A" := (encode (6 * 16 + #A)).
Notation "#6B" := (encode (6 * 16 + #B)).
Notation "#6C" := (encode (6 * 16 + #C)).
Notation "#6D" := (encode (6 * 16 + #D)).
Notation "#6E" := (encode (6 * 16 + #E)).
Notation "#6F" := (encode (6 * 16 + #F)).

Notation "#70" := (encode (7 * 16 + 0)).
Notation "#71" := (encode (7 * 16 + 1)).
Notation "#72" := (encode (7 * 16 + 2)).
Notation "#73" := (encode (7 * 16 + 3)).
Notation "#74" := (encode (7 * 16 + 4)).
Notation "#75" := (encode (7 * 16 + 5)).
Notation "#76" := (encode (7 * 16 + 6)).
Notation "#77" := (encode (7 * 16 + 7)).
Notation "#78" := (encode (7 * 16 + 8)).
Notation "#79" := (encode (7 * 16 + 9)).
Notation "#7A" := (encode (7 * 16 + #A)).
Notation "#7B" := (encode (7 * 16 + #B)).
Notation "#7C" := (encode (7 * 16 + #C)).
Notation "#7D" := (encode (7 * 16 + #D)).
Notation "#7E" := (encode (7 * 16 + #E)).
Notation "#7F" := (encode (7 * 16 + #F)).

Notation "#80" := (encode (8 * 16 + 0)).
Notation "#81" := (encode (8 * 16 + 1)).
Notation "#82" := (encode (8 * 16 + 2)).
Notation "#83" := (encode (8 * 16 + 3)).
Notation "#84" := (encode (8 * 16 + 4)).
Notation "#85" := (encode (8 * 16 + 5)).
Notation "#86" := (encode (8 * 16 + 6)).
Notation "#87" := (encode (8 * 16 + 7)).
Notation "#88" := (encode (8 * 16 + 8)).
Notation "#89" := (encode (8 * 16 + 9)).
Notation "#8A" := (encode (8 * 16 + #A)).
Notation "#8B" := (encode (8 * 16 + #B)).
Notation "#8C" := (encode (8 * 16 + #C)).
Notation "#8D" := (encode (8 * 16 + #D)).
Notation "#8E" := (encode (8 * 16 + #E)).
Notation "#8F" := (encode (8 * 16 + #F)).

Notation "#90" := (encode (9 * 16 + 0)).
Notation "#91" := (encode (9 * 16 + 1)).
Notation "#92" := (encode (9 * 16 + 2)).
Notation "#93" := (encode (9 * 16 + 3)).
Notation "#94" := (encode (9 * 16 + 4)).
Notation "#95" := (encode (9 * 16 + 5)).
Notation "#96" := (encode (9 * 16 + 6)).
Notation "#97" := (encode (9 * 16 + 7)).
Notation "#98" := (encode (9 * 16 + 8)).
Notation "#99" := (encode (9 * 16 + 9)).
Notation "#9A" := (encode (9 * 16 + #A)).
Notation "#9B" := (encode (9 * 16 + #B)).
Notation "#9C" := (encode (9 * 16 + #C)).
Notation "#9D" := (encode (9 * 16 + #D)).
Notation "#9E" := (encode (9 * 16 + #E)).
Notation "#9F" := (encode (9 * 16 + #F)).

Notation "#A0" := (encode (#A * 16 + 0)).
Notation "#A1" := (encode (#A * 16 + 1)).
Notation "#A2" := (encode (#A * 16 + 2)).
Notation "#A3" := (encode (#A * 16 + 3)).
Notation "#A4" := (encode (#A * 16 + 4)).
Notation "#A5" := (encode (#A * 16 + 5)).
Notation "#A6" := (encode (#A * 16 + 6)).
Notation "#A7" := (encode (#A * 16 + 7)).
Notation "#A8" := (encode (#A * 16 + 8)).
Notation "#A9" := (encode (#A * 16 + 9)).
Notation "#AA" := (encode (#A * 16 + #A)).
Notation "#AB" := (encode (#A * 16 + #B)).
Notation "#AC" := (encode (#A * 16 + #C)).
Notation "#AD" := (encode (#A * 16 + #D)).
Notation "#AE" := (encode (#A * 16 + #E)).
Notation "#AF" := (encode (#A * 16 + #F)).

Notation "#B0" := (encode (#B * 16 + 0)).
Notation "#B1" := (encode (#B * 16 + 1)).
Notation "#B2" := (encode (#B * 16 + 2)).
Notation "#B3" := (encode (#B * 16 + 3)).
Notation "#B4" := (encode (#B * 16 + 4)).
Notation "#B5" := (encode (#B * 16 + 5)).
Notation "#B6" := (encode (#B * 16 + 6)).
Notation "#B7" := (encode (#B * 16 + 7)).
Notation "#B8" := (encode (#B * 16 + 8)).
Notation "#B9" := (encode (#B * 16 + 9)).
Notation "#BA" := (encode (#B * 16 + #A)).
Notation "#BB" := (encode (#B * 16 + #B)).
Notation "#BC" := (encode (#B * 16 + #C)).
Notation "#BD" := (encode (#B * 16 + #D)).
Notation "#BE" := (encode (#B * 16 + #E)).
Notation "#BF" := (encode (#B * 16 + #F)).

Notation "#C0" := (encode (#C * 16 + 0)).
Notation "#C1" := (encode (#C * 16 + 1)).
Notation "#C2" := (encode (#C * 16 + 2)).
Notation "#C3" := (encode (#C * 16 + 3)).
Notation "#C4" := (encode (#C * 16 + 4)).
Notation "#C5" := (encode (#C * 16 + 5)).
Notation "#C6" := (encode (#C * 16 + 6)).
Notation "#C7" := (encode (#C * 16 + 7)).
Notation "#C8" := (encode (#C * 16 + 8)).
Notation "#C9" := (encode (#C * 16 + 9)).
Notation "#CA" := (encode (#C * 16 + #A)).
Notation "#CB" := (encode (#C * 16 + #B)).
Notation "#CC" := (encode (#C * 16 + #C)).
Notation "#CD" := (encode (#C * 16 + #D)).
Notation "#CE" := (encode (#C * 16 + #E)).
Notation "#CF" := (encode (#C * 16 + #F)).

Notation "#D0" := (encode (#D * 16 + 0)).
Notation "#D1" := (encode (#D * 16 + 1)).
Notation "#D2" := (encode (#D * 16 + 2)).
Notation "#D3" := (encode (#D * 16 + 3)).
Notation "#D4" := (encode (#D * 16 + 4)).
Notation "#D5" := (encode (#D * 16 + 5)).
Notation "#D6" := (encode (#D * 16 + 6)).
Notation "#D7" := (encode (#D * 16 + 7)).
Notation "#D8" := (encode (#D * 16 + 8)).
Notation "#D9" := (encode (#D * 16 + 9)).
Notation "#DA" := (encode (#D * 16 + #A)).
Notation "#DB" := (encode (#D * 16 + #B)).
Notation "#DC" := (encode (#D * 16 + #C)).
Notation "#DD" := (encode (#D * 16 + #D)).
Notation "#DE" := (encode (#D * 16 + #E)).
Notation "#DF" := (encode (#D * 16 + #F)).

Notation "#E0" := (encode (#E * 16 + 0)).
Notation "#E1" := (encode (#E * 16 + 1)).
Notation "#E2" := (encode (#E * 16 + 2)).
Notation "#E3" := (encode (#E * 16 + 3)).
Notation "#E4" := (encode (#E * 16 + 4)).
Notation "#E5" := (encode (#E * 16 + 5)).
Notation "#E6" := (encode (#E * 16 + 6)).
Notation "#E7" := (encode (#E * 16 + 7)).
Notation "#E8" := (encode (#E * 16 + 8)).
Notation "#E9" := (encode (#E * 16 + 9)).
Notation "#EA" := (encode (#E * 16 + #A)).
Notation "#EB" := (encode (#E * 16 + #B)).
Notation "#EC" := (encode (#E * 16 + #C)).
Notation "#ED" := (encode (#E * 16 + #D)).
Notation "#EE" := (encode (#E * 16 + #E)).
Notation "#EF" := (encode (#E * 16 + #F)).

Notation "#F0" := (encode (#F * 16 + 0)).
Notation "#F1" := (encode (#F * 16 + 1)).
Notation "#F2" := (encode (#F * 16 + 2)).
Notation "#F3" := (encode (#F * 16 + 3)).
Notation "#F4" := (encode (#F * 16 + 4)).
Notation "#F5" := (encode (#F * 16 + 5)).
Notation "#F6" := (encode (#F * 16 + 6)).
Notation "#F7" := (encode (#F * 16 + 7)).
Notation "#F8" := (encode (#F * 16 + 8)).
Notation "#F9" := (encode (#F * 16 + 9)).
Notation "#FA" := (encode (#F * 16 + #A)).
Notation "#FB" := (encode (#F * 16 + #B)).
Notation "#FC" := (encode (#F * 16 + #C)).
Notation "#FD" := (encode (#F * 16 + #D)).
Notation "#FE" := (encode (#F * 16 + #E)).
Notation "#FF" := (encode (#F * 16 + #F)).
