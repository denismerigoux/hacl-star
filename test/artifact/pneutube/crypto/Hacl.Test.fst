module Hacl.Test

open FStar.Buffer
open Hacl.Cast

val test_poly1305_64: unit -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))
let test_poly1305_64 () =
  push_frame();
  let len = 34ul in
  let len' = 34uL in
  let keysize = 32ul in
  let macsize = 16ul in
  let mac = create (0uy) macsize in
  let mac2 = create (0uy) macsize in
  let mac3 = create (0uy) macsize in
  let plaintext = createL [
    0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
    0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
    0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
    0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
    0x75uy; 0x70uy
    ] in
  let expected = createL [
    0xa8uy; 0x06uy; 0x1duy; 0xc1uy; 0x30uy; 0x51uy; 0x36uy; 0xc6uy;
    0xc2uy; 0x2buy; 0x8buy; 0xafuy; 0x0cuy; 0x01uy; 0x27uy; 0xa9uy
    ] in
  let key = createL [
    0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
    0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
    0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
    0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy
    ] in
  Hacl.Symmetric.Poly1305_64.crypto_onetimeauth mac plaintext len' key;
  let poly1305 = createL [
    0x50y; 0x6fy; 0x6cy; 0x79y; 0x31y; 0x33y; 0x30y; 0x35y; 0y
  ] (* Buffer literal for 'Poly1305' *) in
  TestLib.compare_and_print poly1305 expected mac macsize;
  pop_frame()

val test_xsalsa20: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_xsalsa20 () =
  push_frame();
  let len = 163ul in
  let len' = 163uL in
  let keysize = 32ul in
  let noncesize = 8ul in
  let ciphertext = create 0uy len in
  let plaintext = createL [
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
    0xbeuy; 0x07uy; 0x5fuy; 0xc5uy; 0x3cuy; 0x81uy; 0xf2uy; 0xd5uy;
    0xcfuy; 0x14uy; 0x13uy; 0x16uy; 0xebuy; 0xebuy; 0x0cuy; 0x7buy;
    0x52uy; 0x28uy; 0xc5uy; 0x2auy; 0x4cuy; 0x62uy; 0xcbuy; 0xd4uy;
    0x4buy; 0x66uy; 0x84uy; 0x9buy; 0x64uy; 0x24uy; 0x4fuy; 0xfcuy;
    0xe5uy; 0xecuy; 0xbauy; 0xafuy; 0x33uy; 0xbduy; 0x75uy; 0x1auy;
    0x1auy; 0xc7uy; 0x28uy; 0xd4uy; 0x5euy; 0x6cuy; 0x61uy; 0x29uy;
    0x6cuy; 0xdcuy; 0x3cuy; 0x01uy; 0x23uy; 0x35uy; 0x61uy; 0xf4uy;
    0x1duy; 0xb6uy; 0x6cuy; 0xceuy; 0x31uy; 0x4auy; 0xdbuy; 0x31uy;
    0x0euy; 0x3buy; 0xe8uy; 0x25uy; 0x0cuy; 0x46uy; 0xf0uy; 0x6duy;
    0xceuy; 0xeauy; 0x3auy; 0x7fuy; 0xa1uy; 0x34uy; 0x80uy; 0x57uy;
    0xe2uy; 0xf6uy; 0x55uy; 0x6auy; 0xd6uy; 0xb1uy; 0x31uy; 0x8auy;
    0x02uy; 0x4auy; 0x83uy; 0x8fuy; 0x21uy; 0xafuy; 0x1fuy; 0xdeuy;
    0x04uy; 0x89uy; 0x77uy; 0xebuy; 0x48uy; 0xf5uy; 0x9fuy; 0xfduy;
    0x49uy; 0x24uy; 0xcauy; 0x1cuy; 0x60uy; 0x90uy; 0x2euy; 0x52uy;
    0xf0uy; 0xa0uy; 0x89uy; 0xbcuy; 0x76uy; 0x89uy; 0x70uy; 0x40uy;
    0xe0uy; 0x82uy; 0xf9uy; 0x37uy; 0x76uy; 0x38uy; 0x48uy; 0x64uy;
    0x5euy; 0x07uy; 0x05uy
    ] in
  let expected = createL [
    0x8euy; 0x99uy; 0x3buy; 0x9fuy; 0x48uy; 0x68uy; 0x12uy; 0x73uy;
    0xc2uy; 0x96uy; 0x50uy; 0xbauy; 0x32uy; 0xfcuy; 0x76uy; 0xceuy;
    0x48uy; 0x33uy; 0x2euy; 0xa7uy; 0x16uy; 0x4duy; 0x96uy; 0xa4uy;
    0x47uy; 0x6fuy; 0xb8uy; 0xc5uy; 0x31uy; 0xa1uy; 0x18uy; 0x6auy;
    0xc0uy; 0xdfuy; 0xc1uy; 0x7cuy; 0x98uy; 0xdcuy; 0xe8uy; 0x7buy;
    0x4duy; 0xa7uy; 0xf0uy; 0x11uy; 0xecuy; 0x48uy; 0xc9uy; 0x72uy;
    0x71uy; 0xd2uy; 0xc2uy; 0x0fuy; 0x9buy; 0x92uy; 0x8fuy; 0xe2uy;
    0x27uy; 0x0duy; 0x6fuy; 0xb8uy; 0x63uy; 0xd5uy; 0x17uy; 0x38uy;
    0xb4uy; 0x8euy; 0xeeuy; 0xe3uy; 0x14uy; 0xa7uy; 0xccuy; 0x8auy;
    0xb9uy; 0x32uy; 0x16uy; 0x45uy; 0x48uy; 0xe5uy; 0x26uy; 0xaeuy;
    0x90uy; 0x22uy; 0x43uy; 0x68uy; 0x51uy; 0x7auy; 0xcfuy; 0xeauy;
    0xbduy; 0x6buy; 0xb3uy; 0x73uy; 0x2buy; 0xc0uy; 0xe9uy; 0xdauy;
    0x99uy; 0x83uy; 0x2buy; 0x61uy; 0xcauy; 0x01uy; 0xb6uy; 0xdeuy;
    0x56uy; 0x24uy; 0x4auy; 0x9euy; 0x88uy; 0xd5uy; 0xf9uy; 0xb3uy;
    0x79uy; 0x73uy; 0xf6uy; 0x22uy; 0xa4uy; 0x3duy; 0x14uy; 0xa6uy;
    0x59uy; 0x9buy; 0x1fuy; 0x65uy; 0x4cuy; 0xb4uy; 0x5auy; 0x74uy;
    0xe3uy; 0x55uy; 0xa5uy
    ] in
  let key = createL [
    0x1buy; 0x27uy; 0x55uy; 0x64uy; 0x73uy; 0xe9uy; 0x85uy; 0xd4uy;
    0x62uy; 0xcduy; 0x51uy; 0x19uy; 0x7auy; 0x9auy; 0x46uy; 0xc7uy;
    0x60uy; 0x09uy; 0x54uy; 0x9euy; 0xacuy; 0x64uy; 0x74uy; 0xf2uy;
    0x06uy; 0xc4uy; 0xeeuy; 0x08uy; 0x44uy; 0xf6uy; 0x83uy; 0x89uy
    ] in
  let nonce = createL [
    0x69uy; 0x69uy; 0x6euy; 0xe9uy; 0x55uy; 0xb6uy; 0x2buy; 0x73uy;
    0xcduy; 0x62uy; 0xbduy; 0xa8uy; 0x75uy; 0xfcuy; 0x73uy; 0xd6uy;
    0x82uy; 0x19uy; 0xe0uy; 0x03uy; 0x6buy; 0x7auy; 0x0buy; 0x37uy
    ] in
  let xsalsa20 = createL [
    0x58y; 0x53y; 0x61y; 0x6cy; 0x73y; 0x61y; 0x32y; 0x30y; 0y
  ] (* Buffer literal for 'XSalsa20' *) in
  Hacl.Symmetric.XSalsa20.crypto_stream_xsalsa20_xor ciphertext plaintext len' nonce key;
  TestLib.compare_and_print xsalsa20 expected (offset ciphertext 32ul) (FStar.UInt32 (len -^ 32ul));
  pop_frame()

val test_curve25519: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let test_curve25519 () =
  push_frame();
  let keysize = 32ul in
  let result = create 0uy keysize in
  let scalar1 = createL [
    0xa5uy; 0x46uy; 0xe3uy; 0x6buy; 0xf0uy; 0x52uy; 0x7cuy; 0x9duy;
    0x3buy; 0x16uy; 0x15uy; 0x4buy; 0x82uy; 0x46uy; 0x5euy; 0xdduy;
    0x62uy; 0x14uy; 0x4cuy; 0x0auy; 0xc1uy; 0xfcuy; 0x5auy; 0x18uy;
    0x50uy; 0x6auy; 0x22uy; 0x44uy; 0xbauy; 0x44uy; 0x9auy; 0xc4uy
    ] in
  let scalar2 = createL [
    0x4buy; 0x66uy; 0xe9uy; 0xd4uy; 0xd1uy; 0xb4uy; 0x67uy; 0x3cuy;
    0x5auy; 0xd2uy; 0x26uy; 0x91uy; 0x95uy; 0x7duy; 0x6auy; 0xf5uy;
    0xc1uy; 0x1buy; 0x64uy; 0x21uy; 0xe0uy; 0xeauy; 0x01uy; 0xd4uy;
    0x2cuy; 0xa4uy; 0x16uy; 0x9euy; 0x79uy; 0x18uy; 0xbauy; 0x0duy
    ] in
  let input1 = createL [
    0xe6uy; 0xdbuy; 0x68uy; 0x67uy; 0x58uy; 0x30uy; 0x30uy; 0xdbuy;
    0x35uy; 0x94uy; 0xc1uy; 0xa4uy; 0x24uy; 0xb1uy; 0x5fuy; 0x7cuy;
    0x72uy; 0x66uy; 0x24uy; 0xecuy; 0x26uy; 0xb3uy; 0x35uy; 0x3buy;
    0x10uy; 0xa9uy; 0x03uy; 0xa6uy; 0xd0uy; 0xabuy; 0x1cuy; 0x4cuy
    ] in
  let input2 = createL [
    0xe5uy; 0x21uy; 0x0fuy; 0x12uy; 0x78uy; 0x68uy; 0x11uy; 0xd3uy;
    0xf4uy; 0xb7uy; 0x95uy; 0x9duy; 0x05uy; 0x38uy; 0xaeuy; 0x2cuy;
    0x31uy; 0xdbuy; 0xe7uy; 0x10uy; 0x6fuy; 0xc0uy; 0x3cuy; 0x3euy;
    0xfcuy; 0x4cuy; 0xd5uy; 0x49uy; 0xc7uy; 0x15uy; 0xa4uy; 0x93uy
    ] in
  let expected1 = createL [
    0xc3uy; 0xdauy; 0x55uy; 0x37uy; 0x9duy; 0xe9uy; 0xc6uy; 0x90uy;
    0x8euy; 0x94uy; 0xeauy; 0x4duy; 0xf2uy; 0x8duy; 0x08uy; 0x4fuy;
    0x32uy; 0xecuy; 0xcfuy; 0x03uy; 0x49uy; 0x1cuy; 0x71uy; 0xf7uy;
    0x54uy; 0xb4uy; 0x07uy; 0x55uy; 0x77uy; 0xa2uy; 0x85uy; 0x52uy
    ] in
  let expected2 = createL [
    0x95uy; 0xcbuy; 0xdeuy; 0x94uy; 0x76uy; 0xe8uy; 0x90uy; 0x7duy;
    0x7auy; 0xaduy; 0xe4uy; 0x5cuy; 0xb4uy; 0xb8uy; 0x73uy; 0xf8uy;
    0x8buy; 0x59uy; 0x5auy; 0x68uy; 0x79uy; 0x9fuy; 0xa1uy; 0x52uy;
    0xe6uy; 0xf8uy; 0xf7uy; 0x64uy; 0x7auy; 0xacuy; 0x79uy; 0x57uy
    ] in
  Hacl.EC.Curve25519.exp result input1 scalar1;
  let curve25519 = createL [
    0x43y; 0x75y; 0x72y; 0x76y; 0x65y; 0x32y; 0x35y; 0x35y;
    0x31y; 0x39y; 0y
  ] (* Buffer literal for 'Curve25519' *) in
  TestLib.compare_and_print curve25519 expected1 result keysize;
  Hacl.EC.Curve25519.exp result input2 scalar2;
  TestLib.compare_and_print curve25519 expected2 result keysize;
  pop_frame()

val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  test_poly1305_64 ();
  test_xsalsa20 ();
  test_curve25519 ();
  C.exit_success
