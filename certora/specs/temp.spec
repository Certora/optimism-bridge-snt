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

    // Getters:
    function creationBlock() external returns (uint) envfree;

    // Harness:
    function getCheckpointsLengthByAddress(address user) external returns (uint256) envfree;
    function getLatestBlockNumberByAddress(address user) external returns (uint256) envfree;
    function getCheckpointByAddressAndIndex(address user, uint256 index) external returns (MiniMeToken.Checkpoint) envfree;
    function getFromBlockByAddressAndIndex(address user, uint256 index) external returns (uint256) envfree;

}

ghost uint256 sumAllBalnces;

ghost mapping(address => uint256) chackpoints;

// each checkpoint.fromBlock must be less than the current blocknumber (no checkpoints from the future).
invariant checkPointBlockNumberValidity(env e1)
    to_mathint(e1.block.number) >= (getLatestBlockNumberByAddress(e1.msg.sender) - 1)
    { preserved with (env e) { require e1.block.number < max_uint128 && e1.block.number > 0 && e.block.number == e1.block.number; } }

// checkpoint.fromBlock is monotonicly increasing for each user.
invariant blockNumberMonotonicInc(address user, uint256 index)
    getFromBlockByAddressAndIndex(user, index) < getFromBlockByAddressAndIndex(user, assert_uint256(index + 1))
    { preserved with (env e) { requireInvariant checkPointBlockNumberValidity(e); } }


// all Block Numbers Are Greater OrEqual To the Creation Block
invariant allBlockNumbersAreGreaterOrEqualToCreationBlock(address user, uint256 index)
    getFromBlockByAddressAndIndex(user, index) >= creationBlock()
    { preserved with (env e) { requireInvariant blockNumberMonotonicInc(e.msg.sender, index); require e.block.number > creationBlock(); } }

// // all parents fromBlock should be less than the fromBlock in the cloned miniMe token (if exists).

// invariant balanceOfLessOrEqToTotalSpply(env e)
//     balanceOfAt(e.msg.sender, e.block.number) <= totalSupplyAt(e.block.number)
//     { preserved with (env e1) { requireInvariant checkPointBlockNumberValidity(e1); } }

// invariant cantChangeHistory(env e) 
//     balanceOfAt(e.msg.sender, e.blocknumber) == balanceOfAt(e.msg.sender, e.blocknumber) &&
//     totalSupplyAt(e.block.number) == totalSupplyAt(e.block.number)
//     { preserved with (env e1) { require e1.block.number > 0 && e.block.number == e1.block.number; } }


// // rule sanity(method f) {
// //     env e;
// //     calldataarg args;
// //     f(e, args);
// //     assert false;
// // }

// // Rule Ideas:
// // - cant change balnces history
// // - cant change totalSupply history
// // sum all latest balances equals total supply
// // sum all balances at any given point (block number) should be equal to the total supply at the same point.
// // Questions:
// // what happens to a cloned coin when his parent coin changes state?

// function doesntChangeBalance(method f) returns bool {
//     return (f != sig:transfer(address,uint256).selector &&
//         f.selector != sig:transferFrom(address,address,uint256).selector &&
//         f.selector != sig:generateTokens(address, uint).selector &&
//         f.selector != sig:claimTokens(address).selector &&
//         f.selector != sig:destroyTokens(address, uint).selector);
// }

// /*
//     @Description:
//         Verify that there is no fee on transferFrom() (like potentially on USDT)
//     @Notes:
// */
// rule noFeeOnTransferFrom(address alice, address bob, uint256 amount) {
//     env e;
//     require alice != bob;
//     require allowance(alice, e.msg.sender) >= amount;
//     uint256 balanceBefore = balanceOf(e, bob);
//     uint256 balanceAliceBefore = balanceOf(e, alice);

//     transferFrom(e, alice, bob, amount);

//     uint256 balanceAfter = balanceOf(e, bob);
//     uint256 balanceAliceAfter = balanceOf(e, alice);
//     assert balanceAfter == balanceBefore + amount;
//     assert balanceAliceAfter == balanceAliceBefore - amount;
// }

// /*
//     @Description:
//         Verify that there is no fee on transfer() (like potentially on USDT)
    
//     @Notes:
// */
// rule noFeeOnTransfer(address bob, uint256 amount) {
//     env e;
//     require bob != e.msg.sender;
//     uint256 balanceSenderBefore = balanceOf(e.msg.sender);
//     uint256 balanceBefore = balanceOf(bob);

//     transfer(e, bob, amount);

//     uint256 balanceAfter = balanceOf(bob);
//     uint256 balanceSenderAfter = balanceOf(e.msg.sender);
//     assert balanceAfter == balanceBefore + amount;
//     assert balanceSenderAfter == balanceSenderBefore - amount;
// }

// /*
//     @Description:
//         Token transfer works correctly. Balances are updated if not reverted. 
//         If reverted then the transfer amount was too high, or the recipient is 0.


//     @Notes:
//         This rule fails on tokens with a blacklist function, like USDC and USDT.
//         The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.
// */
// rule transferCorrect(address to, uint256 amount) {
//     env e;
//     require e.msg.value == 0 && e.msg.sender != 0;
//     uint256 fromBalanceBefore = balanceOf(e.msg.sender);
//     uint256 toBalanceBefore = balanceOf(to);
//     require fromBalanceBefore + toBalanceBefore <= max_uint256;

//     transfer@withrevert(e, to, amount);
//     bool reverted = lastReverted;
//     if (!reverted) {
//         if (e.msg.sender == to) {
//             assert balanceOf(e.msg.sender) == fromBalanceBefore;
//         } else {
//             assert balanceOf(e.msg.sender) == fromBalanceBefore - amount;
//             assert balanceOf(to) == toBalanceBefore + amount;
//         }
//     } else {
//         assert amount > fromBalanceBefore || to == 0;
//     }
// }

// /*
//     @Description:
//         Test that transferFrom works correctly. Balances are updated if not reverted. 
//         If reverted, it means the transfer amount was too high, or the recipient is 0

//     @Notes:
//         This rule fails on tokens with a blacklist and or pause function, like USDC and USDT.
//         The prover finds a counterexample of a reverted transfer to a blacklisted address or a transfer in a paused state.
// */

// rule transferFromCorrect(address from, address to, uint256 amount) {
//     env e;
//     require e.msg.value == 0;
//     uint256 fromBalanceBefore = balanceOf(from);
//     uint256 toBalanceBefore = balanceOf(to);
//     uint256 allowanceBefore = allowance(from, e.msg.sender);
//     require fromBalanceBefore + toBalanceBefore <= max_uint256;

//     transferFrom(e, from, to, amount);

//     assert from != to =>
//         balanceOf(from) == fromBalanceBefore - amount &&
//         balanceOf(to) == toBalanceBefore + amount &&
//         allowance(from, e.msg.sender) == allowanceBefore - amount;
// }

// /*
//     @Description:
//         transferFrom should revert if and only if the amount is too high or the recipient is 0.

//     @Notes:
//         Fails on tokens with pause/blacklist functions, like USDC.
// */
// rule transferFromReverts(address from, address to, uint256 amount) {
//     env e;
//     uint256 allowanceBefore = allowance(from, e.msg.sender);
//     uint256 fromBalanceBefore = balanceOf(from);
//     require from != 0 && e.msg.sender != 0;
//     require e.msg.value == 0;
//     require fromBalanceBefore + balanceOf(to) <= max_uint256;

//     transferFrom@withrevert(e, from, to, amount);

//     assert lastReverted <=> (allowanceBefore < amount || amount > fromBalanceBefore || to == 0);
// }

// /*
//     @Description:
//         Balance of address 0 is always 0

//     @Notes:
// */
// invariant ZeroAddressNoBalance()
//     balanceOf(0) == 0;


// /*
//     @Description:
//         Contract calls don't change token total supply.


//     @Notes:
//         This rule should fail for any token that has functions that change totalSupply(), like mint() and burn().
//         It's still important to run the rule and see if it fails in functions that _aren't_ supposed to modify totalSupply()
// */
// rule NoChangeTotalSupply(method f) {
//     // require f.selector != burn(uint256).selector && f.selector != mint(address, uint256).selector;
//     uint256 totalSupplyBefore = totalSupply();
//     env e;
//     calldataarg args;
//     f(e, args);
//     assert totalSupply() == totalSupplyBefore;
// }

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
