// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.18;

import "../../contracts/token/MiniMeToken.sol";

contract MiniMeTokenHarness is MiniMeToken {
    constructor(
        address _tokenFactory,
        address payable _parentToken,
        uint _parentSnapShotBlock,
        string memory _tokenName,
        uint8 _decimalUnits,
        string memory _tokenSymbol,
        bool _transfersEnabled
    ) public MiniMeToken(_tokenFactory, _parentToken, _parentSnapShotBlock, _tokenName, _decimalUnits, _tokenSymbol, _transfersEnabled) {}

    // function getBalancesLengthByAddress(address user) public view returns (uint256) {
    //     return balances[user].length;
    // }

    function getCheckpointsLengthByAddress(address user) public view returns (uint256) {
        return balances[user].length;
    }

    function getLatestBlockNumberByAddress(address user) public view returns (uint256) {
        uint256 checkpointsLength = getCheckpointsLengthByAddress(user);
        if (checkpointsLength == 0) revert();
        Checkpoint memory latestCheckPoint = getCheckpointByAddressAndIndex(user, checkpointsLength - 1);
        return latestCheckPoint.fromBlock;
    }

    function getCheckpointByAddressAndIndex(address user, uint256 index) public view returns (Checkpoint memory) {
        uint256 checkpointsLength = getCheckpointsLengthByAddress(user);
        if (checkpointsLength == 0 || index >= checkpointsLength) revert();
        return balances[user][index];
    }

    function getFromBlockByAddressAndIndex(address user, uint256 index) public view returns (uint256) {
        uint256 checkpointsLength = getCheckpointsLengthByAddress(user);
        if (checkpointsLength == 0 || index >= checkpointsLength) revert();
        return balances[user][index].fromBlock;
    }

    // function balanceOfAtHarness(address owner, uint blockNumber) public view returns (uint) {
    //     return balanceOfAt(owner, _blockNumber);
    // }

}
