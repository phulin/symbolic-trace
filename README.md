RESET
=====
Reverse Engineering through Symbolic Execution of Traces: Symbolic execution of LLVM IR traces for program understanding.

To evaluate a trace, first run:

	cabal configure
	cabal build

Then, to run a program, grab a trace

	dist/build/Eval/Eval -q <qemu_build_dir> <program> <program-args>

The qemu\_build\_dir should be the build directory, such as ~/qemu/x86\_64-linux-user.

For a trace in whole-system mode, you need to gather the trace manually. First, make a PANDA record/replay recording of the execution you want to look at. Next, use Volatility or a similar tool to find the CR3 you're looking for, and then run a command like

	echo "begin_replay <recording>" | ~/qemu/i386-softmmu/qemu-system-i386 -panda-plugin ~/qemu/i386-softmmu/panda_plugins/panda_llvm_trace.so -panda-arg llvm_trace:cr3=0xDEADBEEF -monitor stdio ~/win7.1.qcows2

followed by

	dist/build/Eval/Eval

You can do `Eval --help` to see a list of command line options. By default, PANDA stores trace information in /tmp; if you want to change this, use `Eval -d` and `qemu -panda-arg llvm_trace:base=/other/dir`. Eval will also probably run out stack space; increase that by adding the arguments `+RTS -K1G -RTS`, where the 1G specifies 1 GB of stack space.

This will start a server that accepts JSON requests for symbolic execution data from the RESET IDA plugin (github.com/phulin/RESETPlugin)

Files
=====
`types/`: Definitions of basic types. This is in a separate Cabal package due to GHC bug #3333 - you can't have Template Haskell code in a package that links to C++ code. We use TH for the JSON parsing; aeson provides a nice auto-serialization interface.

`AppList.hs`: Definition of a linked list type which is optimized for appending; we use this instead of normal List for pretty much everything.
`Memlog.hs`: Functions for parsing and processing the Panda dynamic log
`Instances.hs`: Miscellanous instances of Show, mostly for debugging
`Options.hs`: Definition and parsing of command-line arguments.
`Pretty.hs`: The Pretty class for pretty-printing; probably could be done in a much nicer way
`Expr.hs`: Operations for working with our expression format
`Eval.hs`: Main functions - meat of the symbolic evaluation engine
`Main.hs`: Server code and command-line argument processing, etc
