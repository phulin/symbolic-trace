{-# LANGUAGE TemplateHaskell #-}
module Data.RESET.Memlog where

import Control.DeepSeq.TH
import Data.LLVM.Types
import Data.Word

type InstOpList = [(Instruction, Maybe MemlogOp)]
type MemlogList = [(BasicBlock, InstOpList)]

-- Haskell version of C dynamic log structs
data MemlogOp = BeginBlockOp Word64 Word64 | -- Translation counter and eip
                MemoryOp AddrOp AddrEntry |
                BranchOp Word64 | -- INDEX of branch taken - 0 for true, 1 for false
                SelectOp Word64 | -- Index of select statement result
                SwitchOp Word64 | -- Index of switch statement result
                ExceptionOp |
                HelperFuncOp MemlogList | -- For calls out to helper functions
                MemsetOp AddrEntry |
                MemcpyOp AddrEntry AddrEntry
    deriving (Eq, Ord, Show)
data AddrOp = LoadOp | StoreOp
    deriving (Eq, Ord, Show)
data AddrEntry = AddrEntry { addrType :: AddrEntryType
                           , addrVal :: Word64
                           , addrFlag :: AddrFlag }
    deriving (Eq, Ord, Show)
data AddrEntryType = HAddr | MAddr | IAddr | PAddr | LAddr | GReg | GSpec | Unk | Const | Ret
    deriving (Eq, Ord, Show, Enum)
data AddrFlag = IrrelevantFlag | NoFlag | ExceptionFlag | ReadlogFlag | FuncargFlag
    deriving (Eq, Ord, Show)

$(deriveNFData ''AddrFlag)
$(deriveNFData ''AddrEntryType)
$(deriveNFData ''AddrEntry)
$(deriveNFData ''AddrOp)
$(deriveNFData ''MemlogOp)
