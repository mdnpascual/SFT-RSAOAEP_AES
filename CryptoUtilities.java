import java.io.*;
import java.util.Arrays;
import java.security.*;
import javax.crypto.*;
import javax.crypto.spec.*;

/**
 * This class contains various utility functions for working with AES encryption
 * and decryption, and for working with HMAC-SHA1 message digests.
 */
public class CryptoUtilities {

    // AES key length to be used (in bytes)
    public static final int AES_KEY_LEN = 16;

    // HMAC-SHA1 digest length (in bytes)
    public static final int HMAC_SHA1_LEN = 20;

    // AES/CBC/PKCS5Padding parameter length
    public static final int AES_PARAM_LEN = 18;

    // Bit length of prime modulus for Diffie-Hellman
    //   public static final int DH_PRIME_SIZE = 3072;
    public static final int DH_PRIME_SIZE = 1024;

    // Certainty value for probably primes
    public static final int CERTAINTY = 3;


    /**
     * Constructs a AES_KEY_LEN byte AES key from a given seed
     *
     * @param seed (array of bytes)
     * @return the resulting AES key
     */
    public static SecretKeySpec key_from_seed(byte[] seed) {
	// compute SHA-1 hash of the seed
	byte[] hashval = null;
	try {
	    MessageDigest sha1 = MessageDigest.getInstance("SHA1");
	    hashval = sha1.digest(seed);
	}
	catch (Exception e) {
	    e.printStackTrace();
	}

	// extract 1st AES_KEY_LEN bytes for the key material
	byte[] key = new byte[AES_KEY_LEN];
	System.arraycopy(hashval, 0, key, 0, AES_KEY_LEN);

	// initialize the key
	SecretKeySpec keySpec = new SecretKeySpec(key, "AES");

	return keySpec;
    }



    /**
     * Computes a HMAC-SHA1 message digest of a given message, appends it to the 
     * message, returns the output.
     *
     * @param message  the message (in bytes)
     * @param keySpec  the secret key for HMAC-SHA1
     * @return message concatenated with the HMAC-SHA1 digest
     */
    public static byte[] append_hash(byte[] message, SecretKeySpec keySpec)
    {
	byte[] ret = null;
		
	try {
	    // Initialize the MAC with the given key
	    Mac mac = Mac.getInstance("HmacSHA1");
	    mac.init(keySpec);
			
	    // Compute the MAC
	    byte[] m = mac.doFinal(message);
			
	    // Append the MAC to the message
	    ret = new byte[message.length+m.length];
	    System.arraycopy(message, 0, ret, 0, message.length);
	    System.arraycopy(m, 0, ret, message.length, m.length);
			
	} catch (Exception e) {
	    e.printStackTrace();
	}
		
	return ret;
    }
	

    /**
     * Extracts a message from a message/digest pair.
     *
     * @param hash_message  the message and digest (in bytes)
     * @return message concatenated with the HMAC-SHA1 digest
     */
    public static byte[] extract_message(byte[] hash_message)
    {
	byte[] plaintext = new byte[hash_message.length - HMAC_SHA1_LEN];
	System.arraycopy(hash_message, 0, plaintext, 0, plaintext.length);

	return plaintext;
    }



    /**
     * Extracts a HMAC-SHA1 message digest form the end of the given message and
     * deterimines whether it is valid.
     *
     * @param messageHash  the message including digest (in bytes)
     * @param keySpec  the secret key for HMAC-SHA1
     * @return true if the extracted digest matches the computed digest
     */
    public static boolean verify_hash(byte[] messageHash, SecretKeySpec keySpec)
    {
	boolean ret = false;
		
	try {
	    // Split the array into the message and the digest
	    byte[] message = new byte[messageHash.length - HMAC_SHA1_LEN];
	    byte[] hash = new byte[HMAC_SHA1_LEN];
			
	    System.arraycopy(messageHash, 0, message, 0, message.length);
	    System.arraycopy(messageHash, message.length, hash, 0, hash.length);
			
	    // Initialize the MAC with the given key
	    Mac mac = Mac.getInstance("HmacSHA1");
	    mac.init(keySpec);
			
	    // Get the MAC of the message
	    byte[] m = mac.doFinal(message);
			
	    // compare the the MAC sent and the one calculated
	    ret = Arrays.equals(m, hash);
			
	} catch (Exception e) {
	    // if there is an error, we know that hash can't be correct
	    ret = false;
	}
		
	return ret;
    }

	

    /**
     * Encrypts the given message using the given key with AES-CBC.
     *
     * @param message  the message (in bytes)
     * @param keySpec  the secret key
     * @return encrypted message (with algorithm parameters appended
     */
    public static byte[] encrypt(byte[] message, SecretKeySpec keySpec)
    {
	byte[] ret = null;
		
	try {
	    // Initialize the cipher with the given key
	    Cipher cipher = Cipher.getInstance("AES/CBC/PKCS5Padding");
	    cipher.init(Cipher.ENCRYPT_MODE, keySpec);
			
	    // encrypt the message
	    byte[] cipherText = cipher.doFinal(message);
	    byte[] params = cipher.getParameters().getEncoded();
			
	    // Combine the ciphertext and cipher parameters into one byte array
	    ret = new byte[cipherText.length+params.length];
	    System.arraycopy(cipherText, 0, ret, 0, cipherText.length); 
	    System.arraycopy(params, 0, ret, cipherText.length, params.length);
	} catch (Exception e) {
	    e.printStackTrace();
	}
		
	return ret;
    }



	
    /**
     * Decrypts the given message using the given key with AES-CBC.
     *
     * @param decrypt  the message (in bytes)
     * @param keySpec  the secret key
     * @return decrypted message
     */
    public static byte[] decrypt(byte[] decrypt, SecretKeySpec keySpec)
    {
	byte[] message = null;
		
	try {
	    // Extract the cipher parameters from the end of the input array
	    byte[] cipherText = new byte[decrypt.length - AES_PARAM_LEN];
	    byte[] paramsEnc = new byte[AES_PARAM_LEN];
			
	    System.arraycopy(decrypt, 0, cipherText, 0, cipherText.length);
	    System.arraycopy(decrypt, cipherText.length, paramsEnc, 0, paramsEnc.length);

	    // Initialize the parameters
	    AlgorithmParameters params = AlgorithmParameters.getInstance("AES");
	    params.init(paramsEnc);
	        
	    // Initialize the cipher for decryption
	    Cipher cipher = Cipher.getInstance("AES/CBC/PKCS5Padding");
	    cipher.init(Cipher.DECRYPT_MODE, keySpec, params);
			
	    // Decrypt the ciphertext
	    message = cipher.doFinal(cipherText);

	} catch (Exception e) {
	    e.printStackTrace();
	}
		
	return message;
    }



    /**
     * Writes the given message to the supplied stream.
     *
     * @param message  the message (in bytes)
     * @param out  the output stream
     * @throws IOException
     */
    public static void send(byte[] message, DataOutputStream out) throws IOException
    {
	// send the length of the encrypted message
	out.writeInt(message.length);

	// send the encrypted message bytes
	out.write(message);

	// flush the stream
	out.flush();
    }



    /**
     * Decrypts the given message using the given key with AES-CBC.
     *
     * @param keySpec  the secret key
     * @param in   the input stream
     * @throws IOException
     * @return received message
     */
    public static byte[] receive(DataInputStream in) throws IOException
    {
	byte[] message = null;

	// read the message size
	int size = in.readInt();

	// read the message bytes into the array		
	message = new byte[size];
	int i = 0;
	int total = 0;
	do {
	    i = in.read(message, total, size-total);
	    total += i;
	} while (total != size);

	return message;
    }



    /**
     * Encrypts the given message using the given key with AES-CBC, and writes to 
     * the supplied stream.
     *
     * @param message  the message (in bytes)
     * @param keySpec  the secret key
     * @param out  the output stream
     * @throws IOException
     */
    public static void encryptAndSend(byte[] message, SecretKeySpec keySpec, DataOutputStream out) throws IOException
    {
	// encrypt the message
	byte[] ciphertext = encrypt(message,keySpec);

	// send the message
	send(ciphertext,out);
    }



    /**
     * Decrypts the given message using the given key with AES-CBC.
     *
     * @param keySpec  the secret key
     * @param in   the input stream
     * @throws IOException
     * @return decrypted message
     */
    public static byte[] receiveAndDecrypt(SecretKeySpec keySpec, DataInputStream in) throws IOException
    {
	// get the message
	byte[] message = receive(in);

	// decrypt the received message and return the result
	return decrypt(message,keySpec);
    }



    /**
     * Converts a byte array to hex string
     * This code from http://java.sun.com/j2se/1.4.2/docs/guide/security/jce/JCERefGuide.html#HmacEx
     */
    public static String toHexString(byte[] block) {
        StringBuffer buf = new StringBuffer();

        int len = block.length;

        for (int i = 0; i < len; i++) {
	    byte2hex(block[i], buf);
	    if (i < len-1) {
		buf.append(":");
	    }
        } 
        return buf.toString();
    }


    /**
     * Converts a byte to hex digit and writes to the supplied buffer
     * This code from http://java.sun.com/j2se/1.4.2/docs/guide/security/jce/JCERefGuide.html#HmacEx
     */
    public static void byte2hex(byte b, StringBuffer buf) {
        char[] hexChars = { '0', '1', '2', '3', '4', '5', '6', '7', '8',
                            '9', 'A', 'B', 'C', 'D', 'E', 'F' };
        int high = ((b & 0xf0) >> 4);
        int low = (b & 0x0f);
        buf.append(hexChars[high]);
        buf.append(hexChars[low]);
    }

}
