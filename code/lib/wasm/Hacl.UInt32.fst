module Hacl.UInt32

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt32
module U = FStar.UInt32
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [Hacl.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

let n = U.n

assume type t

assume val v: (x:t) -> GTot (FStar.UInt.uint_t U.n)

assume val add: a:t -> b:t{UInt.size (v a + v b) n} -> Tot (c:t{v a + v b = v c})

assume val add_mod: a:t -> b:t -> Tot (c:t{(v a + v b) % pow2 n = v c})

(* Subtraction primitives *)
assume val sub: a:t -> b:t{UInt.size (v a - v b) n} -> Tot (c:t{UInt.size (v a - v b) n})

assume val sub_mod: a:t -> b:t -> Tot (c:t{(v a - v b) % pow2 n = v c})

(* Multiplication primitives *)
assume val mul: a:t -> b:t{UInt.size (v a * v b) n} -> Tot (c:t{v a * v b = v c})

assume val mul_mod: a:t -> b:t -> Tot (c:t{(v a * v b) % pow2 n = v c})

(* Bitwise operators *)
assume val logand: t -> t -> Tot t
assume val logxor: t -> t -> Tot t
assume val logor: t -> t -> Tot t
assume val lognot: t -> Tot t

(* Shift operators *)
assume val shift_right: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n}
  -> Tot (c:t{v c = (v a / (pow2 (FStar.UInt32.v s)))})

assume val shift_left: a:t -> s:FStar.UInt32.t{FStar.UInt32.v s < n}
  -> Tot (c:t{v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)})

assume val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
assume val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
assume val gt_mask: a:t -> b:t -> Tot (c:t{(v a > v b ==> v c = pow2 n - 1) /\ (v a <= v b ==> v c = 0)})
assume val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})
assume val lte_mask: a:t -> b:t -> Tot (c:t{(v a <= v b ==> v c = pow2 n - 1) /\ (v a > v b ==> v c = 0)})

(* Infix notations *)
let op_Plus_Hat a b = add a b
let op_Plus_Percent_Hat a b  = add_mod a b
let op_Subtraction_Hat a b = sub a b
let op_Subtraction_Percent_Hat a b = sub_mod a b
let op_Star_Hat a b = mul a b
let op_Star_Percent_Hat a b = mul_mod a b
let op_Hat_Hat a b = logxor a b
let op_Amp_Hat a b = logand a b
let op_Bar_Hat a b = logor a b
let op_Less_Less_Hat a b = shift_left a b
let op_Greater_Greater_Hat a b = shift_right a b

(* (\* To input / output constants *\) *)
(* assume val of_string: string -> Tot t *)
