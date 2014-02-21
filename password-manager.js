"use strict";

// Question 2: argument?
// Extra credit?
// Questinos 4 and 5?
/*
Short-Answer Questions:

1. Briefly describe your method for preventing the adversary from learning information about the lengths of the passwords stored in 
   your password manager.
	
	We used the padding function in our implementation to pad all passwords to maximum password length specified in the program. 
    Therefore all passwords stored in our password manager have same length.

2. Briefly describe your method for preventing swap attacks (Section 2.2). Provide an argument for why the attack is prevented in 
   your scheme.

    1. The key-value-store in our password stores a pair of HMAC hashed domain name, and an authentication encrypted password 
       concatenated with the HMAC hash of its domain name.  
    2. keychain  = {HMAC(domain_name), AE(padded_password || HMAC(domain_name))}

    Proof by contradition: Assume there's an adversary that can successfully perform the swap attack. This means that the adversary
    can swap the record for 
              HMAC(domain_name1), AE(padded_password1 || HMAC(domain_name1)) 
          and HMAC(domain_name2), AE(padded_password2 || HMAC(domain_name2)) 
    such that the new records are 
              HMAC(domain_name1), AE(padded_password2 || HMAC(domain_name1)) 
          and HMAC(domain_name2), AE(padded_password1 || HMAC(domain_name2)).
    However, this means that the adversary broke AE() (i.e. gcm) since he was able to correctly encrypt the new entries 
 		      padded_password2 || HMAC(domain_name1)
          gnd padded_password1 || HMAC(domain_name2).
    But AE() is secure. We have reached a contradiction. Thus, the scheme protects againts a swap attack.

3. In our proposed defense against the rollback attack (Section 2.2), we assume that we can store the SHA-256 hash in a trusted 
   location beyond the reach of an adversary. Is it necessary to assume that such a trusted location exists, in order to defend 
   against rollback attacks? Briefly justify your answer.

	Yes, it is necessary to assume that a trusted location exists. This is because if we assume that the hash is not saved in a secure
    storage location, our integrity scheme of padding the HMAC(domain_name) to the padded password only protects against swap attacks. 
    An adversary can swap the stored "AE(padded_password || HMAC(domain_name)" entry with an older 
    "AE(padded_password' || HMAC(domain_name)" entry, and the password manage won't be able to detect it because the HAMC(domain_name)
    will still match.

  4. What if we had used a different MAC (other than HMAC) on the domain names to produce the keys for the key-value store? 
     Would the scheme still satisfy the desired security properties? Either show this, or give an example of a secure MAC for which 
     the resulting password manager implementation would be insecure.
    
	The reason HMAC satisfies the requirement for generating keys is that it is a PRF and is existentially unforgeable. If another 
    MAC satisfies these properites, then it is acceptable to replace HMAC with the new MAC.
     

  5. In our specification, we leak the number of records in the password manager. Describe an approach to reduce or completely 
     eliminate the information leaked about the number of records.

    One -ideal- solution would be to set a large upper bound on the total number of passwords and have the password manager always
    occupying the same space on disk (with the unused space padded with random bits). However, this design would suffer from inefficient
    use of memory and storage.
    
	Another solution would be to pad the password manager with a random number of dummy records. So, every time we dump the password 
    manager, we pad it with a random number of dummy records. For example, if the password manager has 10 records, the dumped version 
    could be padded to 30 records at one intance and could be padded to 49 records at another intance.
 
*/

/*
  k <-- PBKDF(pwd||salt)
  k_hmac <-- HMAC(k, r0) // r1 is random bits (or any value, like 0, that's different from r2) saved in priv.data
  k_gcm <-- HMAC(k, r1)  // r2 is random bits (or any value, like 1, that's different from r2) saved in priv.data
  tag that is stored on disk and used for verifying key, t <-- HMAC(k, r2) // r3 is random bits (or any value, like 0, 
																		   // that's different from r2) saved in priv.data.
  To argue security, say that we're only using k_prf, k_gcm, and t, which are "pseudorandom" bits, and that the only
  dependence on k is through PRF(k, 0), PRF(k, 1), and PRF(k, 2)  
*/

/********* External Imports ********/

var lib = require("./lib");

var KDF = lib.KDF,
    HMAC = lib.HMAC,
    SHA256 = lib.SHA256,
    setup_cipher = lib.setup_cipher,
    enc_gcm = lib.enc_gcm,
    dec_gcm = lib.dec_gcm,
    bitarray_slice = lib.bitarray_slice,
    bitarray_to_string = lib.bitarray_to_string,
    string_to_bitarray = lib.string_to_bitarray,
    bitarray_to_hex = lib.bitarray_to_hex,
    hex_to_bitarray = lib.hex_to_bitarray,
    bitarray_to_base64 = lib.bitarray_to_base64,
    base64_to_bitarray = lib.base64_to_bitarray,
    byte_array_to_hex = lib.byte_array_to_hex,
    hex_to_byte_array = lib.hex_to_byte_array,
    string_to_padded_byte_array = lib.string_to_padded_byte_array,
    string_to_padded_bitarray = lib.string_to_padded_bitarray,
    string_from_padded_byte_array = lib.string_from_padded_byte_array,
    string_from_padded_bitarray = lib.string_from_padded_bitarray,
    random_bitarray = lib.random_bitarray,
    bitarray_equal = lib.bitarray_equal,
    bitarray_len = lib.bitarray_len,
    bitarray_concat = lib.bitarray_concat,
    dict_num_keys = lib.dict_num_keys;


/********* Implementation ********/


var keychain = function() {
  // Class-private instance variables.
  var priv = {
    secrets: { /* Your secrets here */ },
    data: { /* Non-secret data here */ }
  };

  // Maximum length of each record in bytes
  var MAX_PW_LEN_BYTES = 64;
  
  // Flag to indicate whether password manager is "ready" or not
  var ready = false;

  var keychain = {};
  
  var kdf_salt = "10000000";
  var k_nonces = new Array();
  k_nonces[0] = "0";
  k_nonces[1] = "1";
  k_nonces[2] = "2";
  

  /** 
    * Creates an empty keychain with the given password. Once init is called,
    * the password manager should be in a ready state.
    *
    * Arguments:
    *   password: string
    * Return Type: void
    */
  keychain.init = function(password) {
	  // Iniitialize a new password manager.
	  priv.secrets.masterKDF = KDF(password, kdf_salt); 
	  
	  // Private Data, will NOT be seriliazed into disk
	  priv.secrets.k_hmac = HMAC(priv.secrets.masterKDF, k_nonces[0]);
	  priv.secrets.k_gcm = HMAC(priv.secrets.masterKDF, k_nonces[1]);
	  
	  // Public Data, will be seriliazed into disk
	  priv.data.k_verification_tag = HMAC(priv.secrets.masterKDF, k_nonces[2]);
	  
	  ready = true;
  };

  /**
    * Loads the keychain state from the provided representation (repr). The
    * repr variable will contain a JSON encoded serialization of the contents
    * of the KVS (as returned by the save function). The trusted_data_check
    * is an *optional* SHA-256 checksum that can be used to validate the 
    * integrity of the contents of the KVS. If the checksum is provided and the
    * integrity check fails, an exception should be thrown. You can assume that
    * the representation passed to load is well-formed (e.g., the result of a 
    * call to the save function). Returns true if the data is successfully loaded
    * and the provided password is correct. Returns false otherwise.
    *
    * Arguments:
    *   password:           string
    *   repr:               string
    *   trusted_data_check: string
    * Return Type: boolean
    */
    keychain.load = function(password, repr, trusted_data_check) {
	  if (trusted_data_check = undefined || !bitarray_equal(string_to_bitarray(SHA256(string_to_bitarray(repr))),string_to_bitarray(trusted_data_check))){
	    throw "Failed integrity check.";
      }
	  var deserialized = JSON.parse(repr);
	  var priv_JSON = deserialized.substr(0, deserialized.indexOf("#"));
	  var keychain_JSON = deserialized.substr(deserialized.indexOf("#")+1, deserialized.length);
	  priv.data = JSON.parse(priv_JSON);
	  keychain = JSON.parse(keychain_JSON);
	  var masterKDF = KDF(password, kdf_salt);
	  if (!bitarray_equal(HMAC(masterKDF, k_nonces[2]), priv.data.k_verification_tag)) {
		  return false;
	  }
	  
  	// Private Data, will NOT be seriliazed into disk
  	priv.secrets.masterKDF = masterKDF;
	  priv.secrets.k_hmac = HMAC(priv.secrets.masterKDF, k_nonces[0]);
	  priv.secrets.k_gcm = HMAC(priv.secrets.masterKDF, k_nonces[1]);
	  
	  // Public Data, will be seriliazed into disk
	  priv.data.k_verification_tag = HMAC(priv.secrets.masterKDF, k_nonces[2]);
	  
	  ready = true; 
	  return true;
  };

  /**
    * Returns a JSON serialization of the contents of the keychain that can be 
    * loaded back using the load function. The return value should consist of
    * an array of two strings:
    *   arr[0] = JSON encoding of password manager
    *   arr[1] = SHA-256 checksum
    * As discussed in the handout, the first element of the array should contain
    * all of the data in the password manager. The second element is a SHA-256
    * checksum computed over the password manager to preserve integrity. If the
    * password manager is not in a ready-state, return null.
    *
    * Return Type: array
    */ 
  keychain.dump = function() {
	  var ret_val = [];
	  var s = JSON.stringify(priv.data);
	  s = s.concat('#');
	  s = s.concat(JSON.stringify(keychain));
	  ret_val[0] = JSON.stringify(s);
	  ret_val[1] = SHA256(string_to_bitarray(ret_val[0]));
	  return ret_val;
  }

  /**
    * Fetches the data (as a string) corresponding to the given domain from the KVS.
    * If there is no entry in the KVS that matches the given domain, then return
    * null. If the password manager is not in a ready state, throw an exception. If
    * tampering has been detected with the records, throw an exception.
    *
    * Arguments:
    *   name: string
    * Return Type: string
    */
  keychain.get = function(name) {
	  if (!ready) {
		  throw "Keychain not initialized.";
	  }
	  var masterKDF = priv.secrets.masterKDF;
	  var k_hmac = priv.secrets.k_hmac;
	  var k_gcm = priv.secrets.k_gcm;
	  var hmac = HMAC(k_hmac, name);
	  var ciphertext = keychain[hmac];
	  if (!ciphertext) {
		  return null;
	  }
	  var cipher = setup_cipher(bitarray_slice(k_gcm, 0, 128));	 
	  var dec = dec_gcm(cipher, ciphertext);
	  var dec_pwd = bitarray_slice(dec, 0, bitarray_len(dec)-bitarray_len(hmac));
	  var verification_hmac = bitarray_slice(dec, bitarray_len(dec)-bitarray_len(hmac), bitarray_len(dec));
	  if (!bitarray_equal(hmac, verification_hmac)) {
		  throw "Tampering detected";
	  }
	  var pwd = string_from_padded_bitarray(dec_pwd, MAX_PW_LEN_BYTES);
	  return pwd;
  }

  /** 
  * Inserts the domain and associated data into the KVS. If the domain is
  * already in the password manager, this method should update its value. If
  * not, create a new entry in the password manager. If the password manager is
  * not in a ready state, throw an exception.
  *
  * Arguments:
  *   name: string
  *   value: string
  * Return Type: void
  */
  keychain.set = function(name, value) {
	  if (!ready) {
		  throw "Keychain not initialized.";
	  }
	  var masterKDF = priv.secrets.masterKDF;
	  var k_hmac = priv.secrets.k_hmac;
	  var k_gcm = priv.secrets.k_gcm;
	  var hmac = HMAC(k_hmac, name);
	  var cipher = setup_cipher(bitarray_slice(k_gcm, 0, 128));
	  var padded_pwd = string_to_padded_bitarray(value, MAX_PW_LEN_BYTES);
	  padded_pwd = bitarray_concat(padded_pwd, hmac);
	  var ciphertext = enc_gcm(cipher, padded_pwd);
	  keychain[hmac] = ciphertext;
  }

  /**
    * Removes the record with name from the password manager. Returns true
    * if the record with the specified name is removed, false otherwise. If
    * the password manager is not in a ready state, throws an exception.
    *
    * Arguments:
    *   name: string
    * Return Type: boolean
  */
  keychain.remove = function(name) {
	  if (!ready) {
		  throw "Keychain not initialized.";
	  }
	  var k_hmac = priv.secrets.k_hmac;
	  var hmac = HMAC(k_hmac, name);
	  if (!keychain[hmac]) {
		  return false;
	  }
	  delete keychain[hmac];
	  return true;
  }

  return keychain;
}

module.exports.keychain = keychain;
