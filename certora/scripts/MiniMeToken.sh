certoraRun certora/harness/MiniMeTokenHarness.sol \
--verify MiniMeTokenHarness:certora/specs/MiniMeToken.spec \
--solc solc8.18 \
--loop_iter 3 \
--optimistic_loop \
--server staging \
--rule_sanity
--msg "MiniMeToken invariants - noFeeOnTransferFrom"