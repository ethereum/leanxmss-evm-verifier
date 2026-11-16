// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

/// EIP-7002's `fake_exponential(MIN_FEE, exponent, FEE_UPDATE_FRACTION)`: the fee in wei at a given
/// exponent, written independently of the contracts.
function feeAt(uint256 exponent) pure returns (uint256) {
    uint256 output;
    uint256 accum = 17;
    for (uint256 i = 1; accum > 0; i++) {
        output += accum;
        accum = (accum * exponent) / (17 * i);
    }
    return output / 17;
}
