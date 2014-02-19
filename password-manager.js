"use strict";

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
	  priv.secrets.masterKDF = KDF(password, "10000000"); 
      //priv.data.version = "CS 255 Password Manager v1.0";
	  priv.data.k_verification_tag = HMAC(priv.secrets.masterKDF, "2");
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
	  priv = JSON.parse(priv_JSON);
	  keychain = JSON.parse(keychain_JSON);
	  if (!bitarray_equal(HMAC(KDF(password, "10000000"), "2"), priv.data.k_verification_tag)) {
		  return false;
	  }
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
	  var s = JSON.stringify(priv);
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
	  var k_hmac = HMAC(masterKDF, "0");
	  var k_gcm = HMAC(masterKDF, "1");
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
	  var k_hmac = HMAC(masterKDF, "0");
	  var k_gcm = HMAC(masterKDF, "1");
	  var hmac = HMAC(k_hmac, name);
	  var cipher = setup_cipher(bitarray_slice(k_gcm, 0, 128));
	  var padded_pwd = string_to_padded_bitarray(value, MAX_PW_LEN_BYTES);
	  padded_pwd = bitarray_concat(padded_pwd, hmac);
	  var ciphertext = enc_gcm(cipher, padded_pwd);
	  keychain[hmac] = ciphertext;
	//throw "Not implemented!";
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
	  var k_hmac = HMAC(priv.secrets.masterKDF, "0");
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
