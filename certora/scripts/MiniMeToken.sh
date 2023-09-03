certoraRun contracts/token/MiniMeToken.sol \
--verify MiniMeToken:certora/specs/MiniMeToken.spec \
--solc solc8.18 \
--loop_iter 3 \
--optimistic_loop \
--server staging \
--msg "MiniMeToken Sanity"