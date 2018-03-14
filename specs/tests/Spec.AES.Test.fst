module Spec.AES.Test

open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.AES

let test_key = List.map u8 [
  0x2b; 0x7e; 0x15; 0x16; 0x28; 0xae; 0xd2; 0xa6; 
  0xab; 0xf7; 0x15; 0x88; 0x09; 0xcf; 0x4f; 0x3c
]

let test_nonce = List.map u8 [
  0xf0; 0xf1; 0xf2 ; 0xf3; 0xf4; 0xf5; 0xf6; 0xf7; 0xf8; 0xf9; 0xfa; 0xfb
]

let test_counter = 0xfcfdfeff

let test_plaintext = List.map u8 [
  0x6b; 0xc1; 0xbe; 0xe2; 0x2e; 0x40; 0x9f; 0x96; 0xe9; 0x3d; 0x7e; 0x11; 0x73; 0x93; 0x17; 0x2a
]

let test_ciphertext = List.map u8 [
  0x87; 0x4d; 0x61; 0x91; 0xb6; 0x20; 0xe3; 0x26; 0x1b; 0xef; 0x68; 0x64; 0x99; 0x0d; 0xb6; 0xce
]
(* From RFC 3686 *)
let test_key1 = List.map u8 [
0xAE; 0x68; 0x52; 0xF8; 0x12; 0x10; 0x67; 0xCC; 0x4B; 0xF7; 0xA5; 0x76; 0x55; 0x77; 0xF3; 0x9E
]

let test_nonce1 = List.map u8 [
  0x00; 0x00; 0x00 ; 0x30;  0x00; 0x00; 0x00 ; 0x00;  0x00; 0x00; 0x00 ; 0x00;  0x00; 0x00; 0x00 ; 0x00
]

let test_counter1 = 1

let test_plaintext1 = List.map u8 [
 0x53; 0x69; 0x6E; 0x67; 0x6C; 0x65; 0x20; 0x62; 0x6C; 0x6F; 0x63; 0x6B; 0x20; 0x6D; 0x73; 0x67
]

let test_ciphertext1 = List.map u8 [
 0xE4; 0x09; 0x5D; 0x4F; 0xB7; 0xA7; 0xB3; 0x79; 0x2D; 0x61; 0x75; 0xA3; 0x26; 0x13; 0x11; 0xB8
]

let test_key2 = List.map u8 [
 0x7E; 0x24; 0x06; 0x78; 0x17; 0xFA; 0xE0; 0xD7; 0x43; 0xD6; 0xCE; 0x1F; 0x32; 0x53; 0x91; 0x63
]

let test_nonce2 = List.map u8 [
 0x00; 0x6C; 0xB6; 0xDB; 0xC0; 0x54; 0x3B; 0x59; 0xDA; 0x48; 0xD9; 0x0B
]

let test_counter2 = 1

let test_plaintext2 = List.map u8 [
 0x00; 0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07; 0x08; 0x09; 0x0A; 0x0B; 0x0C; 0x0D; 0x0E; 0x0F; 0x10; 0x11; 0x12; 0x13; 0x14; 0x15; 0x16; 0x17; 0x18; 0x19; 0x1A; 0x1B; 0x1C; 0x1D; 0x1E; 0x1F
]

let test_ciphertext2 = List.map u8 [
 0x51; 0x04; 0xA1; 0x06; 0x16; 0x8A; 0x72; 0xD9; 0x79; 0x0D; 0x41; 0xEE; 0x8E; 0xDA; 0xD3; 0x88; 0xEB; 0x2E; 0x1E; 0xFC; 0x46; 0xDA; 0x57; 0xC8; 0xFC; 0xE6; 0x30; 0xDF; 0x91; 0x41; 0xBE; 0x28
]


let test() : FStar.All.ML unit = 
  let seq = create 256 (u8 0) in
  let seqi = repeati #(lseq uint8 256) 256 (fun i s -> s.[i] <- u8 i) seq in
  (*
  let inv = map (fun s -> from_elem (finv (to_elem s))) seqi in
  IO.print_string "inv i:     \n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #256 inv);
  IO.print_string "\n";
  *)
  let seqsbox = map (fun s -> sbox s) seqi in
  IO.print_string "sbox i:     \n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #256 seqsbox);
  IO.print_string "\n";
(*
  let seqsbox_16 = map (fun s -> sbox_bp_16 s) seqi in
  IO.print_string "sbox bp_i i:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #256 seqsbox_16);
  IO.print_string "\n";
  *)
  let key = createL test_key in
  let nonce = createL test_nonce in
  let counter = test_counter in
  let plain = createL test_plaintext in
  let expected = createL test_ciphertext in
  let cip = aes128_encrypt_bytes key nonce counter 16 plain in
//  let cip = aes128_block key nonce counter in
//  let cip = map2 (logxor #U8) cip plain in
  IO.print_string "aes_cip computed:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #16 cip);
  IO.print_string "\n";
  IO.print_string "aes_cip expected:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #16 expected);
  IO.print_string "\n";
  let key = createL test_key1 in
  let nonce = createL test_nonce1 in
  let counter = test_counter1 in
  let plain = createL test_plaintext1 in
  let expected = createL test_ciphertext1 in
  let cip = aes128_encrypt_bytes key nonce counter 16 plain in
//  let cip = aes128_block key nonce counter in
//  let cip = map2 (logxor #U8) cip plain in
  IO.print_string "aes_cip computed:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #16 cip);
  IO.print_string "\n";
  IO.print_string "aes_cip expected:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #16 expected);
  IO.print_string "\n";
  let key = createL test_key2 in
  let nonce = createL test_nonce2 in
  let counter = test_counter2 in
  let plain = createL test_plaintext2 in
  let expected = createL test_ciphertext2 in
  let cip = aes128_encrypt_bytes key nonce counter 32 plain in
//  let cip = aes128_block key nonce counter in
//  let cip = map2 (logxor #U8) cip plain in
  IO.print_string "aes_cip computed:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #32 cip);
  IO.print_string "\n";
  IO.print_string "aes_cip expected:\n";
  FStar.List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 a)); IO.print_string " ; ") (as_list #uint8 #16 expected);
  IO.print_string "\n";
  ()