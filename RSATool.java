import java.io.*;
import java.math.*;
import java.security.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import javax.crypto.*;
import javax.crypto.spec.*;

/**
 * This class provides an implementation of 1024-bit RSA-OAEP.
 */
public class RSATool {
    // OAEP constants
    private final static int K = 128;   // size of RSA modulus in bytes
    private final static int K0 = 16;  // K0 in bytes
    private final static int K1 = 16;  // K1 in bytes

    // RSA key data
    private BigInteger n;
    private BigInteger e, d, p, q, phi;

    // SecureRandom for OAEP and key generation
    private SecureRandom rnd;

    private boolean debug = false;



    /**
     * Utility for printing protocol messages
     * @param s protocol message to be printed
     */
    private void debug(String s) {
	if(debug) 
	    System.out.println("Debug RSA: " + s);
    }


    /**
     * G(M) = 1st K-K0 bytes of successive applications of SHA1 to M
     */
    private byte[] G(byte[] M) {
        MessageDigest sha1 = null;
	try {
	    sha1 = MessageDigest.getInstance("SHA1");
	}
	catch (NoSuchAlgorithmException e) {
	    System.out.println(e);
	    System.exit(1);
	}


	byte[] output = new byte[K-K0];
	byte[] input = M;

	int numBytes = 0;
	while (numBytes < K-K0) {
          byte[] hashval = sha1.digest(input);

	  if (numBytes + 20 < K-K0)
	      System.arraycopy(hashval,0,output,numBytes,K0);
	  else
	      System.arraycopy(hashval,0,output,numBytes,K-K0-numBytes);

	  numBytes += 20;
	  input = hashval;
	}

	return output;
    }



    /**
     * H(M) = the 1st K0 bytes of SHA1(M)
     */
    private byte[] H(byte[] M) {
        MessageDigest sha1 = null;
	try {
	    sha1 = MessageDigest.getInstance("SHA1");
	}
	catch (NoSuchAlgorithmException e) {
	    System.out.println(e);
	    System.exit(1);
	}

        byte[] hashval = sha1.digest(M);
 
	byte[] output = new byte[K0];
	System.arraycopy(hashval,0,output,0,K0);

	return output;
    }



    /**
     * Construct instance for decryption.  Generates both public and private key data.
     *
     */
    public RSATool(boolean setDebug) {
	// set the debug flag
	debug = setDebug;

	rnd = new SecureRandom();

	//////////////////P GENERATION//////////////////
	BigInteger RandPrime = new BigInteger(K*4-1, rnd);
	p = RandPrime.multiply(new BigInteger("2")).add(new BigInteger("1"));	
	
	if (debug)System.out.println ("RSATool DEBUG: \t Trial 1 P generation " + p.toString());
	
	int cnt = 2;
	
	while (!p.isProbablePrime(3)){
		if (debug)System.out.println ("RSATool DEBUG: \t P generated not Prime");
		RandPrime = new BigInteger(K*4-1, rnd);
		p = RandPrime.multiply(new BigInteger("2")).add(new BigInteger("1"));
				
		if (debug)System.out.println ("RSATool DEBUG: \t Trial " + cnt + " " + p.toString());
		cnt++;
	}
	
	if (debug)System.out.println ("RSATool DEBUG: \t P Generated " + p.toString());
	else System.out.println ("P generated");
	
	//////////////////Q GENERATION//////////////////
	rnd = new SecureRandom();
	RandPrime = new BigInteger(K*4-1, rnd);
	q = RandPrime.multiply(new BigInteger("2")).add(new BigInteger("1"));
	
	if (debug)System.out.println ("RSATool DEBUG: \t Trial 1 Q generation " + q.toString());
	
	cnt = 2;
	
	while (!q.isProbablePrime(3)){
		if (debug)System.out.println ("RSATool DEBUG: \t Q generated not Prime");
		RandPrime = new BigInteger(K*4-1, rnd);
		q = RandPrime.multiply(new BigInteger("2")).add(new BigInteger("1"));
		
		if (debug)System.out.println ("RSATool DEBUG: \t Trial " + cnt + " " + q.toString());
		cnt++;
	}
	
	if (debug)System.out.println ("RSATool DEBUG: \t Q Generated " + q.toString());
	else System.out.println ("Q generated");
	
	//////////////////n and phi GENERATION//////////////////
	n = p.multiply(q);
	phi = (p.subtract(BigInteger.ONE)).multiply(q.subtract(BigInteger.ONE));
	
	//////////////////E GENERATION//////////////////
	cnt = 1;
	e = new BigInteger("3");
	
	while(!(e.gcd(phi)).equals(BigInteger.ONE)){
		if (debug)System.out.println ("RSATool DEBUG: \t Trial " + cnt + " " + e.toString());
		cnt++;
		e = e.add(new BigInteger("2"));
		//e = e.add(BigInteger.ONE);
	}
	
	if (debug)System.out.println ("RSATool DEBUG: \t E Generated " + e.toString());
	else System.out.println ("E generated");
	
	//////////////////D GENERATION//////////////////
	
	d = e.modInverse(phi);
	//d = exEuclidean(e,phi);

	if (debug)System.out.println ("RSATool DEBUG: \t D Generated " + d.toString());
	else System.out.println ("D generated");
	
	//d = BigInteger.ONE;
	//n = BigInteger.ONE;
	//e = BigInteger.ONE;
    }


    /**
     * Construct instance for encryption, with n and e supplied as parameters.  No
     * key generation is performed - assuming that only a public key is loaded
     * for encryption.
     */
    public RSATool(BigInteger new_n, BigInteger new_e, boolean setDebug) {
		// set the debug flag
		debug = setDebug;
	
		// initialize random number generator
		rnd = new SecureRandom();
	
		n = new_n;
		e = new_e;
	
		d = p = q = null;
    }
	
	
	
    public BigInteger get_n() {
    	return n;
    }
	
    public BigInteger get_e() {
    	return e;
    }



    /**
     * Encrypts the given byte array using RSA-OAEP.
     *
     *
     * @param plaintext  byte array representing the plaintext
     * @throw IllegalArgumentException if the plaintext is longer than K-K0-K1 bytes
     * @return resulting ciphertext
     */
    public byte[] encrypt(byte[] plaintext) {
		debug("In RSA encrypt");
	
		// make sure plaintext fits into one block
		if (plaintext.length > K-K0-K1)
		    throw new IllegalArgumentException("plaintext longer than one block");
		
		//RSA-OAEP
		byte [] s_t = new byte[K]; 
		BigInteger intS_T, s, t;
		int cnt = 1;
		do{
			//Generate a random k_0 - bit number r
			rnd = new SecureRandom();
			BigInteger r = new BigInteger(K0*8, rnd);
			
			//Compute s = (M_k||0^{k1}) xor G(r)
			byte [] zeroPad = new byte[K-K0-plaintext.length];
			byte [] concat = new byte[K-K0];
			
			System.arraycopy(plaintext, 0, concat, 0, plaintext.length);
		    System.arraycopy(zeroPad, 0, concat, plaintext.length, zeroPad.length);
		    
		    BigInteger concatInt = new BigInteger(concat);
		    BigInteger rByte = new BigInteger(G(r.toByteArray()));
		    s = concatInt.xor(rByte);
		    
		    // Compute t = r xor H(s)
		    BigInteger H_s = new BigInteger(1, H(s.toByteArray()));
		    t = r.xor(H_s);

		    // Concatenate s and t
		    intS_T = new BigInteger(s.toString() + t.toString());
		    if (debug)System.out.println ("RSATool:Encrypt:OAEP DEBUG: \t Trial " + cnt + " s||t generation " + intS_T.toString());
		    cnt++;
		    //If (s||t) greater than or equal to N, go to 1
		}while((intS_T.compareTo(n) > 0) || (intS_T.signum() < 0));
		
		if (debug)System.out.println ("RSATool:Encrypt:OAEP DEBUG: \t s||t Generated " + intS_T.toString() + " less than " + n.toString());
		else System.out.println ("s||t generated");
	
		if (debug)System.out.println ("RSATool:Encrypt:OAEP DEBUG: \t C Generated " + intS_T.modPow(e, n).toString());
		if (debug)System.out.println ("RSATool:Encrypt:OAEP DEBUG: \t s Generated " + new BigInteger(s.toString()));
		if (debug)System.out.println ("RSATool:Encrypt:OAEP DEBUG: \t t Generated " + new BigInteger(t.toString()));
		
		//compute C = (s||t)^e (mod N)
		return (intS_T.modPow(e, n).toByteArray());
    }


    /**
     * Decrypts the given byte array using RSA.
     *
     * @param ciphertext  byte array representing the ciphertext
     * @throw IllegalArgumentException if the ciphertext is not valid
     * @throw IllegalStateException if the class is not initialized for decryption
     * @return resulting plaintexttext
     */
    public byte[] decrypt(byte[] ciphertext) {
		debug("In RSA decrypt");
		byte [] returnMe = new byte[K0];
	
		// make sure class is initialized for decryption
		if (d == null)
		    throw new IllegalStateException("RSA class not initialized for decryption");
		
		//Chinese remainder sequence
		BigInteger C = new BigInteger(ciphertext);
		
		BigInteger d_p = d.mod(p.subtract(BigInteger.ONE));
		BigInteger d_q = d.mod(q.subtract(BigInteger.ONE));
		
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t d_p Computed " + d_p.toString());
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t d_q Computed " + d_q.toString());
		
		BigInteger m_p = C.modPow(d_p, p);
		BigInteger m_q = C.modPow(d_q, q);
		
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t m_p Computed " + m_p.toString());
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t m_q Computed " + m_q.toString());
		
		BigInteger[] euclid = ExtendedEuclid(p,q);
		BigInteger x = euclid[1];
		BigInteger y = euclid[2];
		
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t P coeficcient in EEA Computed " + x.toString());
		if (debug)System.out.println ("RSATool:Dencrypt:CRT DEBUG: \t Q coeficcient in EEA Computed " + y.toString());
		
		BigInteger left = p.multiply(x).multiply(m_q);
		BigInteger right = q.multiply(y).multiply(m_p);
		BigInteger mPadded = (left.add(right)).mod(n);
		
		//////////////////OAEP PART//////////////////
		//BigInteger mPadded2 = C.modPow(d, n);
		
		//This method is the one that separates s and t. 
		int i = 39;
	
		do{
			char[] sChr = new char[mPadded.toString().length()-i];
			char[] tChr = new char[i];
			
			mPadded.toString().getChars(0, mPadded.toString().length()-i, sChr, 0);
			mPadded.toString().getChars(mPadded.toString().length()-i, mPadded.toString().length(), tChr, 0);
			
			BigInteger s = new BigInteger(String.valueOf(sChr));
			BigInteger t = new BigInteger(String.valueOf(tChr));
			
			i--;
			if (t.compareTo(new BigInteger("340282366920938463463374607431768211456")) > 0)
				continue;
			
			BigInteger H_s = new BigInteger(1, H(s.toByteArray()));
			BigInteger u = t.xor(H_s);
			BigInteger G_u = new BigInteger(G(u.toByteArray()));
			BigInteger v = s.xor(G_u);
			
			byte[] vByte = v.toByteArray();
			
			int j = 0; 
			boolean state = true;
			while (j < K-K0-K1 && state){
				if(vByte[vByte.length-1-j] != 0)
					state = false;
				j++;
			}
			
			if (!state)
				continue;
			
			System.arraycopy(vByte,0,returnMe,0,K0);
			break;
		}while (i > 35);
		
		if ( i <= 35 )
			System.out.println ("Something Wrong Happened");
		
		return returnMe;
    }
    
    public BigInteger[] ExtendedEuclid(BigInteger a, BigInteger b)

    { 
        BigInteger[] ans = new BigInteger[3];
        BigInteger c;

        if (b.equals(BigInteger.ZERO))  {  /*  If b = 0, then we're done...  */
            ans[0] = a;
            ans[1] = BigInteger.ONE;
            ans[2] = BigInteger.ZERO;
        }
        else
            {     /*  Otherwise, make a recursive function call  */ 
               c = a.divide(b);
               ans = ExtendedEuclid (b, a.mod(b));
               BigInteger temp = ans[1].subtract(ans[2].multiply(c));
               ans[1] = ans[2];
               ans[2] = temp;
            }

        return ans;
    }
}