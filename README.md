# emil

Emulation of Binary Ninja LLIL.

This project allows for emulation of programs that have been analyzed in a
Binary Ninja database. This allows for emulating programs that you don't trust
to run on your host or don't match the architecture of your host environment.

Emil is done as a capstone project for the Master of Science in Cybersecurity
program at Georgia Institute of Technology.

This work is currently a work in progress.

## Important for Upgrades
Things can just break when updating the binaryninja-api dependency. Had a weird
issue where the `echo` program stopped working. It worked on
`92d75df37c76813ac4a71e35096dcb31ac1b18af` then stopped working on
`stable/5.2.8614` but then started working again at some point after that.

git bisect told me the commit `183ef5e2f0ba6124efac98efba67757f1e8b2aa9` broke it.
That doesn't seem to be relevant at all so not sure what happened.
