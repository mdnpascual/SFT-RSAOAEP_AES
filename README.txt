# An Encrypted Hybrid File transfer using RSA public key cryptosystem to encrypt the AES Keys to encrypt the payload with Chinese remaindering implemented as well as the OAEP Protocol

RSATool - The class that is responsible for RSA encryption and decryption of the AES key used to encrypt and decrypt the file.

-----------------------------------

Compile with:
Client: javac Client.java
Server: javac Server.java
RSATool: javac RSATool.java

-----------------------------------

Everything is implemented including the Chinese remainter theorem implementation and the RSA-OAEP

-----------------------------------

Bugs: None

-----------------------------------

RSA Key generation:

p and q primes are generated as strong primes by picking a prime r and s and calculating p = 2r + 1 and q = 2s + 1.

n is computed by multiplying n and q
phi is computed by doing (p-1)(q-1)

e generation is done by looping until gcd(e,phi) = 1. e starts with 3 and is incremented by 2 every trial since we generally want.

d is generated by getting the inverse of e mod phi.

RSA Encrypt:

RSA Encrypt is done by doing the OAEP protocol.
do:
- Create a random BigInteger r with K0*8 bit length
- Create a 0 byte padding with K-K0-plaintext.length 
- Concatenate the plaintext and the zero padding
- Convert the plaintext with padding to BigInteger
- Hash the BigInteger r with G()
- xor the result of that to the plaintext with padding, that is your s
- Compute the hash of s and xor it with BigInteger r, that is your t
- Concatenate s and t
while(s||t is less than n AND s||t is positive)

Encrypt s||t with e mod n and return the result

RSA Decrypt:

Decrypt is done by doing the chinese remainder tecnique first:

- compute d_p and d_q by modding d with p-1 and q-1
- m_p and m_q is computed by doing C^(d_p) mod p and C^(d_q) mod q
- we compute the x and y coefficient pairs of p and q
- we then finally decrypt the whole thing to p*x*m_q + q*y*m_p all modded to n

After the chinese remainder decryption, we do the OAEP decryption:
do:
- start with i = 39 which is used to determine t length
- Split the decrypted data back to s and t by starting with i length
- check if t is greater than 2^128 (only done on the first loop), reset to step 1 if fail
- Compute u by hashing s and xoring with t
- compute v by hashing u and xoring with s
- check if 0 padding at the end is in correct size
- reset to step 1 if fail
- break and return the result removing the 0 padding if success.
while(the integer length is greater than 35)
