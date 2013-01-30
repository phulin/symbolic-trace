symbolic-trace
==============

Symbolic execution of LLVM IR traces for program understanding.

To get a trace to evaluate, run a command like:
~/panda/qemu/x86_64-linux-user/qemu-x86_64 -panda-plugin ~/panda/qemu/x86_64-linux-user/panda_plugins/panda_llvm_trace.so program args

To evaluate it, run:
cabal build
dist/build/Eval/Eval | less

This will give you a symbolic execution of the program between the first and last basic block inside main, so programs with exit() won't get handled well.

Files
=====
Memlog.hs: functions for parsing and processing the Panda dynamic log
Instances.hs: miscellanous instances of Show, mostly for debugging
Pretty.hs: The Pretty class for pretty-printing; probably could be done in a much nicer way
Expr.hs: Definition of our expression format, pretty printing, operations for working with it
Eval.hs: Main functions - meat of the symbolic evaluation engine

Look at the functions exported by each file to see the important ones. The relevant monads for each file should be described (although probably insufficiently) in the file.
