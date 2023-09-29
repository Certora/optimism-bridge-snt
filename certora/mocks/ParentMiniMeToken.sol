// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.18;

import "../../contracts/token/MiniMeToken.sol";

contract ParentMiniMeToken is MiniMeToken {

    constructor(
        address _tokenFactory,
        address payable _parentToken,
        uint _parentSnapShotBlock,
        string memory _tokenName,
        uint8 _decimalUnits,
        string memory _tokenSymbol,
        bool _transfersEnabled
    ) public MiniMeToken(_tokenFactory, payable(address(0)), 0, _tokenName, _decimalUnits, _tokenSymbol, _transfersEnabled) {}

}