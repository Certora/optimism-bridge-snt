certoraRun certora/harness/MiniMeTokenHarness.sol certora/mocks/DummyERC20Impl.sol \
--verify MiniMeTokenHarness:certora/specs/MiniMeToken.spec \
--link MiniMeTokenHarness:parentToken=DummyERC20Impl \
--solc solc8.18 \
--loop_iter 3 \
--optimistic_loop \
--server staging \
--rule_sanity \
--msg "MiniMeToken invariants - all rules balances length less than 1000" 