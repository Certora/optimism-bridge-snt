methods {
    function transfer(address _to, uint256 _amount) external returns (bool);
    function transferFrom(address _from, address _to, uint256 _amount) external returns (bool);
    function doTransfer(address _from, address _to, uint _amount) internal returns (bool);
    function doApprove(address _from, address _spender, uint256 _amount) internal  returns (bool);
    function _mint(address, uint) internal;
    function _burn(address _owner, uint _amount) internal;
    function balanceOf(address _owner) external returns (uint256);
    function approve(address _spender, uint256 _amount) external returns (bool);
    function allowance(address _owner, address _spender) external returns (uint256) envfree;
    function approveAndCall(address _spender, uint256 _amount, bytes memory _extraData) external returns (bool);
    function totalSupply() external returns (uint);
    function balanceOfAt(address _owner, uint _blockNumber) external returns (uint) envfree;
    function totalSupplyAt(uint _blockNumber) external returns (uint) envfree;
    function createCloneToken(string memory _cloneTokenName, uint8 _cloneDecimalUnits, string memory _cloneTokenSymbol, uint _snapshotBlock, bool _transfersEnabled) external returns(address);
    function generateTokens(address _owner, uint _amount) external returns (bool); // onlyController
    function destroyTokens(address _owner, uint _amount) external returns (bool); // onlyController
    function enableTransfers(bool _transfersEnabled) external; // onlyController
    // function getValueAt(MiniMeToken.Checkpoint[] storage checkpoints, uint _block) internal returns (uint);
    // function updateValueAtNow(MiniMeToken.Checkpoint[] storage checkpoints, uint _value) internal;
    function isContract(address _addr) internal returns(bool);
    function min(uint a, uint b) internal returns (uint);
    function claimTokens(address _token) external; // onlyController
}

rule sanity(method f) {
    env e;
    calldataarg args;
    f(e, args);
    assert false;
}
