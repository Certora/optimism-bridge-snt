// using ParentMiniMeToken as ParentMiniMeToken;

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
    // function balanceOfAt(address _owner, uint _blockNumber) external returns (uint) envfree;
    // function totalSupplyAt(uint _blockNumber) external returns (uint) envfree;
    function _.balanceOfAt(address _owner, uint _blockNumber) external => DISPATCHER(true);
    function _.totalSupplyAt(uint _blockNumber) external => DISPATCHER(true);
    function createCloneToken(string memory _cloneTokenName, uint8 _cloneDecimalUnits, string memory _cloneTokenSymbol, uint _snapshotBlock, bool _transfersEnabled) external returns(address);
    function generateTokens(address _owner, uint _amount) external returns (bool); // onlyController
    function destroyTokens(address _owner, uint _amount) external returns (bool); // onlyController
    function enableTransfers(bool _transfersEnabled) external; // onlyController
    // function getValueAt(MiniMeToken.Checkpoint[] storage checkpoints, uint _block) internal returns (uint);
    // function updateValueAtNow(MiniMeToken.Checkpoint[] storage checkpoints, uint _value) internal;
    function isContract(address _addr) internal returns(bool);
    function min(uint a, uint b) internal returns (uint);
    function claimTokens(address _token) external; // onlyController

    // Getters:
    function creationBlock() external returns (uint) envfree;
    function transfersEnabled() external returns (bool) envfree;
    function parentSnapShotBlock() external returns (uint) envfree;


    // Harness:
    function getCheckpointsLengthByAddress(address user) external returns (uint256) envfree;
    function getLatestBlockNumberByAddress(address user) external returns (uint256) envfree;
    function getCheckpointByAddressAndIndex(address user, uint256 index) external returns (MiniMeToken.Checkpoint) envfree;
    function getFromBlockByAddressAndIndex(address user, uint256 index) external returns (uint256) envfree;
    // function balanceOfAtHarness(address owner, uint blockNumber) external returns (uint) envfree;
    
    function _.onTransfer(address _from, address _to, uint _amount) external => NONDET;
    function _.onApprove(address _from, address _spender, uint _amount) external => NONDET;

}

ghost uint256 sumAllBalnces;
ghost mapping(address => uint128) latestbalance; 
ghost mapping(address => uint128) latestFromBlock;

ghost mapping(address => uint256) checkpointsLength;

ghost mapping(address => mapping(uint256 => uint128)) fromBlocks {
    axiom forall address user . forall uint256 index1 . forall uint256 index2 . index1 > index2 =>  fromBlocks[user][index1] > fromBlocks[user][index2];
}
ghost mapping(uint256 => uint128) totalSupplyFromBlocks {
    axiom forall uint256 index1 . forall uint256 index2 . index1 > index2 =>  totalSupplyFromBlocks[index1] > totalSupplyFromBlocks[index2];
}
ghost mapping(address => mapping(uint256 => uint128)) values;
ghost mapping(uint256 => uint128) totalSupplyvalues;

hook Sload uint128 _value totalSupplyHistory[INDEX uint256 i].value STORAGE {
    require totalSupplyvalues[i] == _value;
}

hook Sstore totalSupplyHistory[INDEX uint256 i].value uint128 _value (uint128 old_value) STORAGE {
    totalSupplyvalues[i] = _value;
}

hook Sload uint128 _fromBlock totalSupplyHistory[INDEX uint256 i].fromBlock STORAGE {
    require totalSupplyFromBlocks[i] == _fromBlock;
}

hook Sstore totalSupplyHistory[INDEX uint256 i].fromBlock uint128 _fromBlock (uint128 old_fromBlock) STORAGE {
    totalSupplyFromBlocks[i] = _fromBlock;
}

hook Sload uint128 _value balances[KEY address user][INDEX uint256 i].value STORAGE {
    require values[user][i] == _value;
}

hook Sstore balances[KEY address user][INDEX uint256 i].value uint128 _value (uint128 old_value) STORAGE {
    values[user][i] = _value;
}

hook Sload uint128 _fromBlock balances[KEY address user][INDEX uint256 i].fromBlock STORAGE {
    require fromBlocks[user][i] == _fromBlock;
}

hook Sstore balances[KEY address user][INDEX uint256 i].fromBlock uint128 _fromBlock (uint128 old_fromBlock) STORAGE {
    fromBlocks[user][i] = _fromBlock;
}

// each checkpoint.fromBlock must be less than the current blocknumber (no checkpoints from the future).
invariant checkPointBlockNumberValidity(env e1)
    to_mathint(e1.block.number) >= (getLatestBlockNumberByAddress(e1.msg.sender) - 1)
    { 
        preserved with (env e) { 
            require e1.block.number < max_uint128 && e1.block.number > 0 && e.block.number == e1.block.number; 
        } 
    }

// // checkpoint.fromBlock is monotonicly increasing for each user.
// invariant _blockNumberMonotonicInc(address user, uint256 index1, uint256 index2)
//     index1 > index2 && index1 < getCheckpointsLengthByAddress(user) => getFromBlockByAddressAndIndex(user, index1) > getFromBlockByAddressAndIndex(user, index2)
//     { 
//         preserved with (env e) { 
//             requireInvariant checkPointBlockNumberValidity(e); 
//         } 
//     }

// checkpoint.fromBlock is monotonicly increasing for each user.
invariant blockNumberMonotonicInc(env e1)
    getFromBlockByAddressAndIndex(e1.msg.sender, e1.block.number) < getFromBlockByAddressAndIndex(e1.msg.sender, assert_uint256(e1.block.number + 1))
    { 
        preserved with (env e) { 
            require parentToken(e) == 0; 
            requireInvariant checkPointBlockNumberValidity(e); 
        } 
    }

// all Block Numbers Are Greater OrEqual To the Creation Block
invariant allBlockNumbersAreGreaterOrEqualToCreationBlock(address user, uint256 index)
    getFromBlockByAddressAndIndex(user, index) >= creationBlock()
    { preserved with (env e) { require e.block.number > creationBlock();} }

invariant balanceOfLessOrEqToTotalSpply(env e, address owner, uint blocknumber)
    balanceOfAt(e, owner, blocknumber) <= totalSupplyAt(e, blocknumber)
    { 
        preserved with (env e1) { 
            require parentToken(e1) == 0; //TODO: remove or handle
        } 
    }

invariant allFromBlockAreGreaterThanParentSnapShotBlock(address user, uint256 index) 
    getFromBlockByAddressAndIndex(user, index) >= parentSnapShotBlock();

function doesntChangeBalance(method f) returns bool {
    return (f.selector != sig:transfer(address,uint256).selector &&
        f.selector != sig:transferFrom(address,address,uint256).selector &&
        f.selector != sig:generateTokens(address, uint).selector &&
        f.selector != sig:claimTokens(address).selector &&
        f.selector != sig:destroyTokens(address, uint).selector);
}


rule historyMutability(method f) {
    env e1;
    env e;
    require parentToken(e) == 0;
    calldataarg args;

    uint256 balanceOfBefore = balanceOfAt(e, e.msg.sender, e.block.number);
    uint256 totalSupplyBefore = totalSupplyAt(e, e.block.number);

    f(e1, args);

    assert balanceOfBefore == balanceOfAt(e, e.msg.sender, e.block.number);
    assert totalSupplyBefore == totalSupplyAt(e, e.block.number);
}

/*
    @Description:
        Verify that there is no fee on transferFrom() (like potentially on USDT)
    @Notes:
*/
rule noFeeOnTransferFrom(address alice, address bob, uint256 amount) {
    env e;
    require alice != bob;
    require allowance(alice, e.msg.sender) >= amount;
    // require parentToken(e) == 0;
    // requireInvariant checkPointBlockNumberValidity(e);
    mathint balanceBefore = balanceOf(e, bob);
    mathint balanceAliceBefore = balanceOf(e, alice);

    bool success = transferFrom(e, alice, bob, amount);

    mathint balanceAfter = balanceOf(e, bob);
    mathint balanceAliceAfter = balanceOf(e, alice);
    assert success => balanceAfter == balanceBefore + amount;
    assert success => balanceAliceAfter == balanceAliceBefore - amount;
    assert !success => balanceAfter == balanceBefore;
    assert !success => balanceAliceAfter == balanceAliceBefore;
}

/*
    @Description:
        Verify that there is no fee on transfer() (like potentially on USDT)
    
    @Notes:
*/
rule noFeeOnTransfer(address bob, uint256 amount) {
    env e;
    require bob != e.msg.sender;
    require parentToken(e) == 0;
    // requireInvariant blockNumberMonotonicInc(e);
    // requireInvariant checkPointBlockNumberValidity(e);
    require e.block.number < max_uint128;
    mathint balanceSenderBefore = balanceOf(e, e.msg.sender);
    mathint balanceBefore = balanceOf(e, bob);

    bool success = transfer(e, bob, amount);

    mathint balanceAfter = balanceOf(e, bob);
    mathint balanceSenderAfter = balanceOf(e, e.msg.sender);
    assert success => balanceAfter == balanceBefore + amount;
    assert success => balanceSenderAfter == balanceSenderBefore - amount;
    assert !success => balanceAfter == balanceBefore;
    assert !success => balanceSenderAfter == balanceSenderBefore;
}

/*
    @Description:
        Token transfer works correctly. Balances are updated if not reverted. 
        If reverted then the transfer amount was too high, or the recipient is 0.


    @Notes:
        This rule fails on tokens with a blacklist function, like USDC and USDT.
        The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.
*/
rule transferCorrect(address to, uint256 amount) {
    env e;
    require e.msg.value == 0 && e.msg.sender != 0;

    require parentToken(e) == 0;
    requireInvariant checkPointBlockNumberValidity(e);
    uint256 fromBalanceBefore = balanceOf(e, e.msg.sender);
    uint256 toBalanceBefore = balanceOf(e, to);
    require fromBalanceBefore + toBalanceBefore <= max_uint256;

    bool success = transfer(e, to, amount);
    // bool reverted = lastReverted;
    if (success) {
        if (e.msg.sender == to) {
            assert balanceOf(e, e.msg.sender) == fromBalanceBefore;
        } else {
            assert balanceOf(e, e.msg.sender) == assert_uint256(fromBalanceBefore - amount);
            assert balanceOf(e, to) == assert_uint256(toBalanceBefore + amount);
        }
    } else {
        assert amount > fromBalanceBefore || to == 0;
    }
}

/*
    @Description:
        Test that transferFrom works correctly. Balances are updated if not reverted. 
        If reverted, it means the transfer amount was too high, or the recipient is 0

    @Notes:
        This rule fails on tokens with a blacklist and or pause function, like USDC and USDT.
        The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.
*/

rule transferFromCorrect(address from, address to, uint256 amount) {
    env e;
    require e.msg.value == 0;
    require parentToken(e) == 0;
    // requireInvariant checkPointBlockNumberValidity(e);
    uint256 fromBalanceBefore = balanceOf(e, from);
    uint256 toBalanceBefore = balanceOf(e, to);
    uint256 allowanceBefore = allowance(from, e.msg.sender);
    require fromBalanceBefore + toBalanceBefore <= max_uint256;

    bool success = transferFrom(e, from, to, amount);

    assert (success && from != to) =>
        balanceOf(e, from) == assert_uint256(fromBalanceBefore - amount) &&
        balanceOf(e, to) == assert_uint256(toBalanceBefore + amount) &&
        allowance(from, e.msg.sender) == assert_uint256(allowanceBefore - amount);
}

/*
    @Description:
        transferFrom should revert if and only if the amount is too high or the recipient is 0.

    @Notes:
        Fails on tokens with pause/blacklist functions, like USDC.
*/
rule transferFromReverts(address from, address to, uint256 amount) {
    env e;
    uint256 allowanceBefore = allowance(from, e.msg.sender);
    uint256 fromBalanceBefore = balanceOf(e, from);
    requireInvariant allFromBlockAreGreaterThanParentSnapShotBlock(e.msg.sender, e.block.number);
    require from != 0 && e.msg.sender != 0;
    require e.msg.value == 0;
    require fromBalanceBefore + balanceOf(e, to) <= max_uint256;
    bool transfersEnabled = transfersEnabled();

    bool success = transferFrom@withrevert(e, from, to, amount);

    assert lastReverted || !success <=> (allowanceBefore < amount || amount > fromBalanceBefore || to == 0 || to == currentContract || !transfersEnabled);
}

/*
    @Description:
        Balance of address 0 is always 0

    @Notes:
*/
invariant ZeroAddressNoBalance(env e)
    balanceOf(e, 0) == 0
    { 
        preserved { 
            require parentToken(e) == 0; 
            // requireInvariant checkPointBlockNumberValidity(e); 
        } 
    }


/*
    @Description:
        Contract calls don't change token total supply.


    @Notes:
        This rule should fail for any token that has functions that change totalSupply(), like mint() and burn().
        It's still important to run the rule and see if it fails in functions that _aren't_ supposed to modify totalSupply()
*/
rule NoChangeTotalSupply(method f) {
    env e;
    calldataarg args;
    require doesntChangeBalance(f);
    uint256 totalSupplyBefore = totalSupply(e);
    f(e, args);
    assert totalSupply(e) == totalSupplyBefore;
}

// /*
//  The two rules cover the same ground as NoChangeTotalSupply.
 
//  The split into two rules is in order to make the burn/mint features of a tested token even more obvious
// */
// rule noBurningTokens(method f) {
//     uint256 totalSupplyBefore = totalSupply();
//     env e;
//     calldataarg args;
//     f(e, args);
//     assert totalSupply() >= totalSupplyBefore;
// }

// rule noMintingTokens(method f) {
//     uint256 totalSupplyBefore = totalSupply();
//     env e;
//     calldataarg args;
//     f(e, args);
//     assert totalSupply() <= totalSupplyBefore;
// }

// /*
//     @Description:
//         Allowance changes correctly as a result of calls to approve, transfer, increaseAllowance, decreaseAllowance


//     @Notes:
//         Some ERC20 tokens have functions like permit() that change allowance via a signature. 
//         The rule will fail on such functions.
// */
// // rule ChangingAllowance(method f, address from, address spender) {
// //     uint256 allowanceBefore = allowance(from, spender);
// //     env e;
// //     if (f.selector == sig:approve(address, uint256).selector) {
// //         address spender_;
// //         uint256 amount;
// //         approve(e, spender_, amount);
// //         if (from == e.msg.sender && spender == spender_) {
// //             assert allowance(from, spender) == amount;
// //         } else {
// //             assert allowance(from, spender) == allowanceBefore;
// //         }
// //     } else if (f.selector == sig:transferFrom(address,address,uint256).selector) {
// //         address from_;
// //         address to;
// //         address amount;
// //         transferFrom(e, from_, to, amount);
// //         uint256 allowanceAfter = allowance(from, spender);
// //         if (from == from_ && spender == e.msg.sender) {
// //             assert from == to || allowanceBefore == max_uint256 || allowanceAfter == allowanceBefore - amount;
// //         } else {
// //             assert allowance(from, spender) == allowanceBefore;
// //         }
// //     } else if (f.selector == sig:decreaseAllowance(address, uint256).selector) {
// //         address spender_;
// //         uint256 amount;
// //         require amount <= allowanceBefore;
// //         decreaseAllowance(e, spender_, amount);
// //         if (from == e.msg.sender && spender == spender_) {
// //             assert allowance(from, spender) == allowanceBefore - amount;
// //         } else {
// //             assert allowance(from, spender) == allowanceBefore;
// //         }
// //     } else if (f.selector == sig:increaseAllowance(address, uint256).selector) {
// //         address spender_;
// //         uint256 amount;
// //         require amount + allowanceBefore < max_uint256;
// //         increaseAllowance(e, spender_, amount);
// //         if (from == e.msg.sender && spender == spender_) {
// //             assert allowance(from, spender) == allowanceBefore + amount;
// //         } else {
// //             assert allowance(from, spender) == allowanceBefore;
// //         }
// //     } else
// //     {
// //         calldataarg args;
// //         f(e, args);
// //         assert allowance(from, spender) == allowanceBefore;
// //     }
// // }

// /*
//     @Rule

//     @Description:
//         Transfer from a to b doesn't change the sum of their balances

//     @Notes:

//     @Link:

// */
// rule TransferSumOfFromAndToBalancesStaySame(address to, uint256 amount) {
//     env e;
//     mathint sum = balanceOf(e.msg.sender) + balanceOf(to);
//     require sum < max_uint256;
//     transfer(e, to, amount); 
//     assert balanceOf(e.msg.sender) + balanceOf(to) == sum;
// }

// /*
//     @Description:
//         Transfer using transferFrom() from a to b doesn't change the sum of their balances


//     @Notes:
// */
// rule TransferFromSumOfFromAndToBalancesStaySame(address from, address to, uint256 amount) {
//     env e;
//     mathint sum = balanceOf(from) + balanceOf(to);
//     require sum < max_uint256;
//     transferFrom(e, from, to, amount); 
//     assert balanceOf(from) + balanceOf(to) == sum;
// }

// /*
//     @Description:
//         Transfer from msg.sender to alice doesn't change the balance of other addresses


//     @Notes:
// */
// rule TransferDoesntChangeOtherBalance(address to, uint256 amount, address other) {
//     env e;
//     require other != e.msg.sender;
//     require other != to && other != currentContract;
//     uint256 balanceBefore = balanceOf(other);
//     transfer(e, to, amount); 
//     assert balanceBefore == balanceOf(other);
// }

// /*
//     @Description:
//         Transfer from alice to bob using transferFrom doesn't change the balance of other addresses


//     @Notes:
// */
// rule TransferFromDoesntChangeOtherBalance(address from, address to, uint256 amount, address other) {
//     env e;
//     require other != from;
//     require other != to;
//     uint256 balanceBefore = balanceOf(other);
//     transferFrom(e, from, to, amount); 
//     assert balanceBefore == balanceOf(other);
// }

// /*
//     @Description:
//         Balance of an address, who is not a sender or a recipient in transfer functions, doesn't decrease 
//         as a result of contract calls


//     @Notes:
//         USDC token has functions like transferWithAuthorization that use a signed message for allowance. 
//         FTT token has a burnFrom that lets an approved spender to burn owner's token.
//         Certora prover finds these counterexamples to this rule.
//         In general, the rule will fail on all functions other than transfer/transferFrom that change a balance of an address.
// */
// rule OtherBalanceOnlyGoesUp(address other, method f) {
//     env e;
//     require other != currentContract;
//     uint256 balanceBefore = balanceOf(other);

//     if (f.selector == sig:transferFrom(address, address, uint256).selector) {
//         address from;
//         address to;
//         uint256 amount;
//         require(other != from);
//         require balanceOf(from) + balanceBefore < max_uint256;
//         transferFrom(e, from, to, amount);
//     } else if (f.selector == sig:transfer(address, uint256).selector) {
//         require other != e.msg.sender;
//         require balanceOf(e.msg.sender) + balanceBefore < max_uint256;
//         calldataarg args;
//         f(e, args);
//     } else {
//         require other != e.msg.sender;
//         calldataarg args;
//         f(e, args);
//     }

//     assert balanceOf(other) >= balanceBefore;
// }
