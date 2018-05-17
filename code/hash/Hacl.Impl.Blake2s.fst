module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf.LoadStore

module ST = FStar.HyperStack.ST
module LSeq = Spec.Lib.IntSeq
module Spec = Spec.Blake2s


///
/// STATUS
/// ------
///
/// 0. The code is proven until `blake2s_internal`.
/// 1. Rewrite update_sub to be in the correct order.
/// 2. Lemmata need to be proven and moved back to the libraries.
///


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
let op_String_Access #a #len m b = as_lseq #a #len b m

///
/// Helper lemmata
///

val lemma_cast_to_u64: x:uint32 -> Lemma
  (requires (True))
  (ensures  (to_u64 #U32 x == u64 (uint_v #U32 x)))
  [SMTPat (to_u64 #U32 x)]

let lemma_cast_to_u64 x = admit()


val lemma_modifies0_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (h0 == h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies0_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_modifies1_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (modifies1 b0 h0 h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies1_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_repeati: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> i:size_nat{i < n} -> Lemma
  (requires True)
  (ensures  (f i (repeati #a i f init) == repeati #a (i + 1) f init))
  [SMTPat (repeati #a (i + 1) f init)]

let lemma_repeati #a n f init i = admit()


(* val lemma_repeati_zero: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> Lemma *)
(*   (requires True) *)
(*   (ensures  (init == repeati #a 0 f init)) *)
(*   [SMTPat (repeati #a 0 f init)] *)

(* let lemma_repeati_zero #a n f init = admit() *)


(* val lemma_size_to_uint32_equal_u32_of_v_of_size_t: x:size_t -> Lemma *)
(*   (requires True) *)
(*   (ensures (size_to_uint32 x == u32 (v x))) *)
(*   [SMTPat (u32 (v x))] *)
(* let lemma_size_to_uint32_equal_u32_of_v_of_size_t x = admit() *)


val lemma_value_mixed_size_addition: x:size_t -> y:size_nat -> Lemma
  (requires True)
  (ensures (v (x +. (size y)) == v x + y))
  [SMTPat (v (x +. (size y)) == v x + y)]
let lemma_value_mixed_size_addition x y = admit()


(* Functions to add to the libraries *)
val update_sub: #a:Type0 -> #len:size_nat -> #xlen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == xlen} -> x:lbuffer a xlen ->
  Stack unit
    (requires (fun h -> live h i /\ live h x))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == Spec.Lib.IntSeq.update_sub #a #len h0.[i] (v start) (v n) h0.[x]))

[@ Substitute]
let update_sub #a #len #olen i start n x =
  let i' = sub i start n in
  copy i' n x


///
/// Blake2s
///

(* Define algorithm parameters *)
type init_vector = lbuffer uint32 8
type working_vector = lbuffer uint32 16
type message_block = lbuffer uint32 16
type hash_state = lbuffer uint32 8
type idx = n:size_t{size_v n < 16}
type sigma_elt = n:size_t{size_v n < 16}
type sigma_t = lbuffer sigma_elt 160


(* Definition of constants *)
inline_for_extraction val create_const_iv: unit -> StackInline init_vector
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> live h1 r /\ h1.[r] == Spec.const_init))

inline_for_extraction let create_const_iv () =
  assert_norm(List.Tot.length Spec.list_init = 8);
  createL Spec.list_init


inline_for_extraction val create_const_sigma: unit -> StackInline sigma_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> live h1 r /\ h1.[r] == Spec.sigma))

inline_for_extraction let create_const_sigma () =
  assert_norm(List.Tot.length Spec.list_sigma = 160);
  createL Spec.list_sigma


(* Define algorithm functions *)
val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r))
let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x))
let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (add_mod #U32 wv_a wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4


#reset-options "--max_fuel 0 --z3rlimit 150"

val blake2_round1 : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_round1 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)))


val blake2_round2 : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))


val blake2_round : wv:working_vector -> m:message_block -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv
                   /\ h.[const_sigma] == Spec.sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round h0.[m] (v i) h0.[wv]))

// [@ (CConst "const_sigma")]
let blake2_round wv m i const_sigma =
  blake2_round1 wv m i const_sigma;
  blake2_round2 wv m i const_sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:init_vector ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv /\ live h const_iv
                     /\ h.[const_iv] == Spec.const_init
                     /\ disjoint wv s /\ disjoint wv m /\ disjoint wv const_iv
                     /\ disjoint s wv /\ disjoint m wv /\ disjoint const_iv wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

//[@ Substitute ]
let blake2_compress1 wv s m offset flag const_iv =
  update_sub wv (size 0) (size 8) s;
  update_sub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 Spec.word_size) in
  // BB. Note that using the ^. operator here would break extraction !
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


val blake2_compress2 :
  wv:working_vector -> m:message_block -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ h.[const_sigma] == Spec.sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 h0.[wv] h0.[m]))


//[@ Substitute ]
let blake2_compress2 wv m const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size Spec.rounds_in_f) wv
    (fun hi ->  Spec.blake2_round hi.[m])
    (fun i ->
      blake2_round wv m i const_sigma;
      lemma_repeati Spec.rounds_in_f (Spec.blake2_round h0.[m]) h0.[wv] (v i))


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner h0.[wv] (v i) h0.[s]))

//[@ Substitute ]
let blake2_compress3_inner wv i s const_sigma =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  // BB. Note that using the ^. operator here would break extraction !
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma
                     /\ h.[const_sigma] == Spec.sigma
                     /\ disjoint wv s /\ disjoint wv const_sigma
                     /\ disjoint s wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 h0.[wv] h0.[s]))

//[@ Substitute ]
let blake2_compress3 wv s const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size 8) s
    (fun hi -> Spec.blake2_compress3_inner hi.[wv])
    (fun i -> blake2_compress3_inner wv i s const_sigma;
           lemma_repeati 8 (Spec.blake2_compress3_inner h0.[wv]) h0.[s] (v i))


val blake2_compress :
  s:hash_state -> m:message_block ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:init_vector -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h const_iv /\ live h const_sigma
                         /\ h.[const_sigma] == Spec.sigma
                         /\ h.[const_iv] == Spec.const_init
                         /\ disjoint s m /\ disjoint s const_sigma /\ disjoint s const_iv
                         /\ disjoint m s /\ disjoint const_sigma s /\ disjoint const_iv s))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

// [@ (CConst "const_iv") (CConst "const_sigma")]
let blake2_compress s m offset flag const_iv const_sigma =
  (**) let hinit = ST.get () in
  salloc11 #hinit #_ #_ #_ #16 #_ (size 16) (u32 0) [BufItem m; BufItem const_iv; BufItem const_sigma] s
  (fun h0 _ sv -> sv == Spec.Blake2s.blake2_compress h0.[s] h0.[m] offset flag)
  (fun wv ->
    blake2_compress1 wv s m offset flag const_iv;
    blake2_compress2 wv m const_sigma;
    blake2_compress3 wv s const_sigma)


val blake2s_internal1: s:lbuffer uint32 8 ->
    kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
    Stack unit
     (requires (fun h -> live h s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                          /\ h1.[s] == Spec.Blake2s.blake2s_internal1 h0.[s] (v kk) (v nn)))

[@ Substitute]
let blake2s_internal1 s kk nn =
  let s0 = s.(size 0) in
  // BB. Note that using the <<. operator here would break extraction !
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  s.(size 0) <- s0'


val blake2s_internal2_inner: s:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   i:size_t{v i < v dd - 1} ->
   const_iv:init_vector -> const_sigma:sigma_t ->
   Stack unit
     (requires (fun h -> live h s /\ live h d /\ live h const_iv /\ live h const_sigma
                    /\ h.[const_sigma] == Spec.sigma
                    /\ h.[const_iv] == Spec.const_init
                    /\ disjoint s d /\ disjoint s const_iv /\ disjoint s const_sigma
                    /\ disjoint d s /\ disjoint const_iv s /\ disjoint const_sigma s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                          /\ h1.[s] == Spec.blake2s_internal2_inner (v dd) h0.[d] (v i) h0.[s]))

[@ Substitute]
let blake2s_internal2_inner s dd d i const_iv const_sigma =
  let h0 = ST.get () in
  salloc11 #h0 #uint32 #unit #_ #16 #_ (size 16) (u32 0) [BufItem d; BufItem const_iv; BufItem const_sigma] s
  (fun h0 _ sv -> sv == Spec.blake2s_internal2_inner (v dd) h0.[d] (v i) h0.[s])
  (fun to_compress ->
    let sub_d = sub d (i *. (size Spec.bytes_in_block)) (size Spec.bytes_in_block) in
    uint32s_from_bytes_le #16 to_compress sub_d;
    let offset32 = size_to_uint32 ((i +. (size 1)) *. (size Spec.block_bytes)) in
    let offset = to_u64 #U32 offset32 in
    (**) lemma_cast_to_u64 offset32;
    blake2_compress s to_compress offset false const_iv const_sigma
  )


val blake2s_internal2_loop: s:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   to_compress:lbuffer uint32 16 ->
   const_iv:init_vector -> const_sigma:sigma_t ->
   Stack unit
     (requires (fun h -> live h s /\ live h d /\ live h to_compress /\ live h const_iv /\ live h const_sigma
                    /\ h.[const_sigma] == Spec.sigma
                    /\ h.[const_iv] == Spec.const_init
                    // Disjointness for s
                    /\ disjoint s d /\ disjoint d s
                    /\ disjoint s const_iv /\ disjoint const_iv s
                    /\ disjoint s const_sigma /\ disjoint const_sigma s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                          /\ h1.[s] == Spec.blake2s_internal2_loop (v dd) h0.[d] h0.[s]))

[@ Substitute]
let blake2s_internal2_loop s dd d to_compress const_iv const_sigma =
  (**) let h0 = ST.get () in
  let idx = dd -. (size 1) in
  loop #h0 idx s
    (fun hi -> Spec.blake2s_internal2_inner (v dd) (hi.[d]))
    (fun i ->
      let h00 = ST.get () in
      blake2s_internal2_inner s dd d i const_iv const_sigma;
      lemma_repeati (v idx) (Spec.blake2s_internal2_inner (v dd) h0.[d]) h0.[s] (v i))


val blake2s_internal2: s:lbuffer uint32 8 ->
   dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
   d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
   to_compress:lbuffer uint32 16 ->
   const_iv:init_vector -> const_sigma:sigma_t ->
   Stack unit
     (requires (fun h -> live h s /\ live h d /\ live h to_compress /\ live h const_iv /\ live h const_sigma
                    /\ h.[const_sigma] == Spec.sigma
                    /\ h.[const_iv] == Spec.const_init
                    // Disjointness for s
                    /\ disjoint s d /\ disjoint d s
                    /\ disjoint s const_iv /\ disjoint const_iv s
                    /\ disjoint s const_sigma /\ disjoint const_sigma s
                    // Disjointness for to_compress
                    /\ disjoint to_compress d /\ disjoint d to_compress
                    /\ disjoint to_compress const_iv /\ disjoint const_iv to_compress
                    /\ disjoint to_compress const_sigma /\ disjoint const_sigma to_compress
                    // Disjointness for s and to_compress
                    /\ disjoint s to_compress /\ disjoint to_compress s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 s to_compress h0 h1
                          /\ h1.[s] == Spec.blake2s_internal2 (v dd) h0.[d] h0.[s]))

//[@ Substitute]
let blake2s_internal2 s dd d to_compress const_iv const_sigma =
  (**) let h0 = ST.get () in
  if (dd >. size 1) then
    blake2s_internal2_loop s dd d to_compress const_iv const_sigma
  else begin
    (**) let h1 = ST.get () in
    (**) lemma_modifies0_is_modifies2 s to_compress h0 h1
  end


val blake2s_internal3: s:lbuffer uint32 8 ->
  dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
  d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
  ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
  to_compress:lbuffer uint32 16 ->
  res:lbuffer uint8 (size_v nn) ->
  const_iv:init_vector -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h d /\ live h to_compress /\ live h res /\ live h const_iv /\ live h const_sigma
                   /\ h.[const_sigma] == Spec.sigma
                   /\ h.[const_iv] == Spec.const_init
                   // Disjointness for s
                   /\ disjoint s d /\ disjoint d s
                   /\ disjoint s const_sigma /\ disjoint const_sigma s
                   /\ disjoint s const_iv /\ disjoint const_iv s
                   // Disjointness for to_compress
                   /\ disjoint to_compress d /\ disjoint d to_compress
                   /\ disjoint to_compress res /\ disjoint res to_compress
                   /\ disjoint to_compress const_iv /\ disjoint const_iv to_compress
                   /\ disjoint to_compress const_sigma /\ disjoint const_sigma to_compress
                   // Disjointness of s and to_compress
                   /\ disjoint s to_compress /\ disjoint to_compress s
                   ))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 s to_compress h0 h1
                         /\ (let sub_d = Spec.Lib.IntSeq.sub h0.[d] ((v dd - 1) * 64) Spec.bytes_in_block in
                           h1.[to_compress] == Spec.Lib.IntSeq.uints_from_bytes_le #U32 #16 sub_d)
                         /\ h1.[s] == Spec.blake2s_internal3 h0.[s] (v dd) h0.[d] (v ll) (v kk) (v nn)))

//[@ Substitute]
let blake2s_internal3 s dd d ll kk nn to_compress res const_iv const_sigma =
  let offset:size_t = (dd -. (size 1)) *. (size 64) in
  let sub_d = sub d offset (size Spec.bytes_in_block) in
  uint32s_from_bytes_le #16 to_compress sub_d;
  let ll64 = to_u64 #U32 (size_to_uint32 ll) in
  let ll_plus_block_bytes64 = to_u64 #U32 (size_to_uint32 (ll +. (size Spec.block_bytes))) in
  (**) lemma_value_mixed_size_addition ll Spec.block_bytes;
  if kk =. size 0 then
    blake2_compress s to_compress ll64 true const_iv const_sigma
  else
    blake2_compress s to_compress ll_plus_block_bytes64 true const_iv const_sigma


#set-options "--max_fuel 0 --z3rlimit 25"

val blake2s_internal:
  dd:size_t{0 < size_v dd /\ size_v dd * Spec.bytes_in_block <= max_size_t}  ->
  d:lbuffer uint8 (size_v dd * Spec.bytes_in_block) ->
  ll:size_t -> kk:size_t{size_v kk <= 32} -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} ->
  res:lbuffer uint8 (size_v nn) ->
  const_iv:init_vector -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h d /\ live h res /\ live h const_iv /\ live h const_sigma
                   /\ h.[const_sigma] == Spec.sigma
                   /\ h.[const_iv] == Spec.const_init
                   // Disjointness for res
                   /\ disjoint res d
                   /\ disjoint res const_iv /\ disjoint res const_sigma
                   /\ disjoint d res
                   /\ disjoint const_iv res /\ disjoint const_sigma res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
//                         /\ h1.[res] == Spec.Blake2s.blake2s_internal (v dd) h0.[d] (v ll) (v kk) (v nn)))

// [@ (CConst "const_iv") (CConst "const_sigma")]
let blake2s_internal dd d ll kk nn res const_iv const_sigma =
  let h0 = ST.get () in
  salloc21 #h0 #unit #uint32 #uint8 #uint8 #32 #8 #(v nn) (size 32) (size 8) (u32 0) (u8 0) [BufItem d; BufItem const_iv; BufItem const_sigma] res
  (fun h0 _ h1 -> True)
  (fun st_u32 tmp ->
    let s = sub st_u32 (size 16) (size 8) in
    let to_compress = sub st_u32 (size 0) (size 16) in
    copy s (size 8) const_iv;
    blake2s_internal1 s kk nn;
    blake2s_internal2 s dd d to_compress const_iv const_sigma;
    blake2s_internal3 s dd d ll kk nn to_compress res const_iv const_sigma;
    uints_to_bytes_le #U32 tmp s;
    let tmp' = sub tmp (size 0) nn in
    copy res nn tmp'
  )


val blake2s :
  ll:size_t{0 < size_v ll /\ size_v ll <= max_size_t - 2 * Spec.bytes_in_block } ->
  d:lbuffer uint8 (size_v ll) -> kk:size_t{size_v kk <= 32} ->
  k:lbuffer uint8 (size_v kk) -> nn:size_t{1 <= size_v nn /\ size_v nn <= 32} -> res:lbuffer uint8 (size_v nn) ->
  Stack unit
    (requires (fun h -> live h d /\ live h k /\ live h res))
    (ensures  (fun h0 _ h1 -> modifies1 res h0 h1))

let blake2s ll d kk k nn res =
  push_frame ();
  let data_blocks : size_t = size 1 +. ((ll -. (size 1)) /. (size Spec.bytes_in_block)) in
  let padded_data_length : size_t = data_blocks *. (size Spec.bytes_in_block) in
  let data_length : size_t = (size Spec.bytes_in_block) +. padded_data_length in
  let len_st_u32 = size 32 +. size 8 in
  let len_st_u8 = (size 32) +. (padded_data_length +. ((size Spec.bytes_in_block) +. data_length)) in
  let const_iv : lbuffer uint32 8 = create_const_iv () in
  let const_sigma : lbuffer (n:size_t{size_v n < 16}) 160 = create_const_sigma () in

  let h0 = ST.get () in
  salloc #h0 #uint8 #unit #(v len_st_u8) len_st_u8 (u8 0) [BufItem d; BufItem k; BufItem const_iv; BufItem const_sigma] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st_u8 ->

      let padded_data = sub #uint8 #(v len_st_u8) #(v padded_data_length) st_u8 (size 32) padded_data_length in
      let padded_key = sub #uint8 #(v len_st_u8) #(Spec.bytes_in_block) st_u8 ((size 32) +. padded_data_length) (size Spec.bytes_in_block) in
      let data = sub #uint8 #(v len_st_u8) #(v data_length) st_u8 ((size 32) +. (padded_data_length +. (size Spec.bytes_in_block))) data_length in

      let padded_data' = sub padded_data (size 0) ll in
      copy padded_data' ll d;

      if (kk =. size 0) then
	     blake2s_internal data_blocks padded_data ll kk nn res const_iv const_sigma
      else begin
	     let padded_key' = sub padded_key (size 0) kk in
	     copy padded_key' kk k;

	     let data' = sub data (size 0) (size Spec.bytes_in_block) in
	     copy data' (size Spec.bytes_in_block) padded_key;

	     let data' = sub data (size Spec.bytes_in_block) padded_data_length in
        copy data' padded_data_length padded_data;

	     blake2s_internal (data_blocks +. (size 1)) data' ll kk nn res const_iv const_sigma
      end
  );
  pop_frame ()