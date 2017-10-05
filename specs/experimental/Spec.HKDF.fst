module Spec.HKDF

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8

module Hash = Spec.SHA2
module HMAC = Spec.HMAC


(* Extraction function *)
val hkdf_extract:
  a    :Hash.hash_alg ->
  salt :bytes{Seq.length salt < Hash.max_input8 a} ->
  ikm  :bytes{Seq.length ikm + Hash.size_block a < Hash.max_input8 a} ->
  Tot (prk:bytes{Seq.length prk = Hash.size_hash a})

let hkdf_extract a salt ikm = HMAC.hmac a salt ikm


(* Core Expansion function *)
val hkdf_expand_core :
  a    : Hash.hash_alg ->
  prk  : bytes{Hash.size_hash a <= Seq.length prk /\ Seq.length prk < Hash.max_input8 a} ->
  info : bytes{Hash.size_hash a + Seq.length info + 1 + Hash.size_block a < Hash.max_input8 a} ->
  t0   : bytes{length t0 = Hash.size_hash a} ->
  ni   : UInt8.t{UInt8.v ni + 1 <= UInt.max_int UInt8.n} ->
  t    : bytes{length t = UInt8.v ni * Hash.size_hash a} ->
  Tot (ti:bytes{length ti = length t + Hash.size_hash a}) // (N + 1) * size_hash

let hkdf_expand_core a prk info t0 ni t =
  let n = Seq.create 1 U8.(ni +^ 1uy) in
  let ti = HMAC.hmac a prk (t0 @| info @| n) in
  t @| t0


(* Expansion function *)
val hkdf_expand :
  a       :Hash.hash_alg ->
  prk     :bytes{Hash.size_hash a <= Seq.length prk /\ Seq.length prk < Hash.max_input8 a} ->
  info    :bytes{Hash.size_hash a + Seq.length info + 1 + Hash.size_block a < Hash.max_input8 a} ->
  len     :nat{len <= 255 * (Hash.size_hash a)} ->
  Tot (okm:bytes{Seq.length okm = len})

let hkdf_expand a prk info len =
  let c = if len % (Hash.size_hash a) = 0 then 0 else 1 in
  let n = len / (Hash.size_hash a) + c in
  let i = 0uy in
  let ti = Seq.createEmpty in
  let acc = hkdf_expand_core a prk info ti i (Seq.createEmpty) in
  let rec loop acc ti i =
    if UInt8.v i <> n then
      let acc = hkdf_expand_core a prk info ti U8.(i +^ 1uy) acc in
      let last = Seq.slice acc (length acc - Hash.size_hash a) (length acc) in
      loop acc last U8.(i +^ 1uy)
    else acc
  in
  loop acc ti i
