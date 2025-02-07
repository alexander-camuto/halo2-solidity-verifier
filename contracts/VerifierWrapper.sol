// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract VerifierWrappper {
    function verifyWithDataAttestation(
        address verifier,
        bytes calldata encoded
    ) public view returns (bool) {
        // static call the verifier contract to verify the proof
        (bool success, bytes memory returndata) = verifier.staticcall(encoded);

        if (success) {
            return abi.decode(returndata, (bool));
        } else {
            revert("low-level call to verifier failed");
        }
    }
}
