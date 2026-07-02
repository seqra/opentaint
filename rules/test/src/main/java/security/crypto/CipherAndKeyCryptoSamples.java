package security.crypto;


import javax.crypto.Cipher;
import javax.crypto.KeyGenerator;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import java.security.NoSuchAlgorithmException;
import java.security.spec.ECGenParameterSpec;

/**
 * Samples for cipher algorithms, modes, IVs and key sizes.
 */
public class CipherAndKeyCryptoSamples {

    // weak-ec-key-size

    public void weakEcKeySize() throws Exception {
        java.security.KeyPairGenerator kpg = java.security.KeyPairGenerator.getInstance("EC");
        // VULNERABLE: use a weak curve
        ECGenParameterSpec spec = new ECGenParameterSpec("secp112r1");
        kpg.initialize(spec);
    }

    public void strongEcKeySize() throws Exception {
        java.security.KeyPairGenerator kpg = java.security.KeyPairGenerator.getInstance("EC");
        ECGenParameterSpec spec = new ECGenParameterSpec("secp256r1");
        kpg.initialize(spec);
    }

    // des-is-deprecated

    public Cipher useDesCipher() throws Exception {
        // VULNERABLE: DES is deprecated
        return Cipher.getInstance("DES/CBC/PKCS5Padding");
    }

    public Cipher useAesCipherInsteadOfDes() throws Exception {
        return Cipher.getInstance("AES/GCM/NoPadding");
    }

    // desede-is-deprecated

    public Cipher useTripleDesCipher() throws Exception {
        // VULNERABLE: 3DES / DESede is deprecated
        return Cipher.getInstance("DESede/CBC/PKCS5Padding");
    }

    public Cipher useAesInsteadOfTripleDes() throws Exception {
        return Cipher.getInstance("AES/CBC/PKCS5Padding");
    }

    // ecb-cipher

    public Cipher genericEcbCipher() throws Exception {
        // VULNERABLE: generic ECB mode
        return Cipher.getInstance("DES/ECB/PKCS5Padding");
    }

    public Cipher nonEcbCipher() throws Exception {
        return Cipher.getInstance("AES/CBC/PKCS5Padding");
    }

    // cbc-padding-oracle

    public Cipher cbcWithPkcs5Padding() throws Exception {
        // VULNERABLE: CBC with PKCS5Padding
        return Cipher.getInstance("AES/CBC/PKCS5Padding");
    }

    public Cipher gcmModeCipher() throws Exception {
        return Cipher.getInstance("AES/GCM/NoPadding");
    }

    // use-of-blowfish

    public Cipher blowfishCipher() throws Exception {
        // VULNERABLE: Blowfish cipher
        return Cipher.getInstance("Blowfish");
    }

    public Cipher nonBlowfishCipher() throws Exception {
        return Cipher.getInstance("AES/CBC/PKCS5Padding");
    }

    // use-of-default-aes

    public Cipher defaultAesCipher() throws Exception {
        // VULNERABLE: AES without explicit mode/padding defaults to ECB
        return Cipher.getInstance("AES");
    }

    public Cipher explicitAesCipher() throws Exception {
        return Cipher.getInstance("AES/CBC/PKCS5Padding");
    }

    // aes-hardcoded-key

    public void aesWithHardcodedKey() throws Exception {
        byte[] keyBytes = "...".getBytes();
        SecretKeySpec key = new SecretKeySpec(keyBytes, "AES");
        Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
        // VULNERABLE: hardcoded key used for AES init
        cipher.init(Cipher.ENCRYPT_MODE, key);
    }

    public void aesWithGeneratedKey() throws Exception {
        KeyGenerator keyGen = KeyGenerator.getInstance("AES");
        keyGen.init(256);
        Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
        cipher.init(Cipher.ENCRYPT_MODE, keyGen.generateKey());
    }

    // no-static-initialization-vector

    public IvParameterSpec staticIvInsecure() {
        // VULNERABLE: static IV bytes
        byte[] iv = new byte[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
        return new IvParameterSpec(iv, 0, iv.length);
    }

    public IvParameterSpec randomIvSecure() {
        byte[] iv = new byte[16];
        new java.security.SecureRandom().nextBytes(iv);
        return new IvParameterSpec(iv, 0, iv.length);
    }

    // rsa-no-padding

    public Cipher rsaNoPaddingCipher() throws Exception {
        // VULNERABLE: RSA without OAEP padding
        return Cipher.getInstance("RSA/None/NoPadding");
    }

    public Cipher rsaOaepCipher() throws Exception {
        return Cipher.getInstance("RSA/ECB/OAEPWithSHA-256AndMGF1Padding");
    }

    // blowfish-insufficient-key-size

    public KeyGenerator blowfishWeakKeySize() throws NoSuchAlgorithmException {
        KeyGenerator keyGen = KeyGenerator.getInstance("Blowfish");
        // VULNERABLE: less than 128 bits
        keyGen.init(40);
        return keyGen;
    }

    public KeyGenerator blowfishStrongKeySize() throws NoSuchAlgorithmException {
        KeyGenerator keyGen = KeyGenerator.getInstance("Blowfish");
        keyGen.init(128);
        return keyGen;
    }
}
