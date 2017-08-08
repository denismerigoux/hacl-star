#include "kremlib.h"
#include "Curve25519.h"
#include "Chacha20.h"
#include "Salsa20.h"
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_poly
#include "Poly1305_64.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_aead
#include "Chacha20Poly1305.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state

#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_ed
#include "Ed25519.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha256
#include "SHA2_256.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha512
#include "SHA2_512.h"
#undef K___uint32_t_uint8_t_
#include "NaCl.h"


/* API file for HACL* cryptographic primitives */

/* X25519 ECDH computation primitive.
   Takes:
   - secret: a 32-bytes private key
   - point: a public value, either the X25519 basepoint (uint8_t basepoint[32] = {9}) or the other parties 32-bytes public key
   Returns:
   - stores the result of the computation in out */
void curve25519_scalarmult(uint8_t *out, uint8_t *secret, uint8_t *point);

/* Chacha20 cipher primitive.
   Takes:
   - plain: the plaintext
   - plain_len: the plaintext length
   - key: a 32-bytes private key
   - nonce: a 12-bytes nonce
   - ctr: a counter - WARNING the nonce/ctr combination must never be used more than once per key
   Stores:
   - output: the Chacha20 stream XORed with the content of plain */
void
chacha20(
         uint8_t *output,
         uint8_t *plain,
         uint32_t plain_len,
         uint8_t *key,
         uint8_t *nonce,
         uint32_t ctr
         );

/* Salsa20 cipher primitive.
   Takes:
   - plain: the plaintext
   - plain_len: the plaintext length
   - key: a 32-bytes private key
   - nonce: a 8-bytes nonce
   - ctr: a counter - WARNING the nonce/ctr combination must never be used more than once per key
   Stores:
   - output: the Salsa20 stream XORed with the content of plain
 */
void
salsa20(
        uint8_t *output,
        uint8_t *plain,
        uint32_t len,
        uint8_t *key,
        uint8_t *nonce,
        uint64_t ctr
        );


/* Poly1305 MAC primitive.
   Takes:
   - input: the input to be MACed
   - input_len: the length of the input
   - key: a private key
   Stores:
   - output: the 16-bytes of the MACed input
 */
void
poly1305_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key);

/* IETF AEAD Chacha20 Poly1305 encrypt construction.
   Takes:
   - msg: the message to be encrypted then MACed
   - msg_len: the length of the message
   - aad: associated non-encrypted data
   - aad_len: associated non-encrypted data length
   - key:private key
   - nonce:nonce
   Stores:
   - cipher: the result of the encryption
   - mac: the result of the MAC */
uint32_t
aead_chacha20_poly1305_encrypt(
  uint8_t *cipher,
  uint8_t *mac,
  uint8_t *msg,
  uint32_t msg_len,
  uint8_t *aad,
  uint32_t aad_len,
  uint8_t *key,
  uint8_t *nonce
);

/* IETF AEAD Chacha20 Poly1305 encrypt construction.
   Takes:
   - cipher: the cipher to be decrypted
   - msg_len: the length of the message to retrieve
   - mac: the MAC to check the integrity
   - aad: associated non-encrypted data
   - aad_len: associated non-encrypted data length
   - key:private key
   - nonce:nonce
   Stores:
   - msg: the result of the decryption if the MAC verification succeeds */
uint32_t
aead_chacha20_poly1305__decrypt(
  uint8_t *msg,
  uint8_t *cipher,
  uint32_t msg_len,
  uint8_t *mac,
  uint8_t *aad,
  uint32_t aad_len,
  uint8_t *key,
  uint8_t *nonce
);

/* 
   Ed25519 Eddsa signature public key generation function
   Takes:
   - secret_key : private key
   Stores:
   - public_key: the public key associated with the private key */
void ed25519_secret_to_public(uint8_t *public_key, uint8_t *secret_key);

/* 
   Ed25519 Eddsa signature
   Takes:
   - secret: private key
   - msg: the message to sign
   - msg_len: the length of the message
   Stores:
   - signature: the signature of the message with the private key */
void ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t msg_len);

/* 
   Ed25519 Eddsa signature verification
   Takes:
   - public: other party public key
   - msg: the message that has been signed
   - msg_len: the length of the message
   - signature: the signature of the message
   Returns:
   - true: if the signature of the message is successfully verified
   - false otherwise */
bool ed25519_verify(uint8_t *public, uint8_t *msg, uint32_t msg_len, uint8_t *signature);

/*
  SHA2-512 Hash function
  Takes:
  - input: the data to be hashed
  - len: the length of the data to be hashed
  Stores:
  - hash: 64-bytes of the resulting hash
 */
void sha2_512_hash(uint8_t *hash, uint8_t *input, uint32_t len);