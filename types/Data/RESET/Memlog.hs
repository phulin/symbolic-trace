{-# LANGUAGE TemplateHaskell #-}
module Data.RESET.Memlog where

import Control.DeepSeq.TH
import Data.LLVM.Types
import Data.Word

type InstOpList = [(Instruction, Maybe MemlogOp)]
type MemlogList = [(BasicBlock, InstOpList)]

-- Haskell version of C dynamic log structs
data MemlogOp = AddrMemlogOp AddrOp AddrEntry |
                BranchOp Word32 |
                SelectOp Word32 |
                SwitchOp Word32 | 
                ExceptionOp |
                HelperFuncOp MemlogList | -- For calls out to helper functions
                MemsetOp AddrEntry |
                MemcpyOp AddrEntry AddrEntry
    deriving (Eq, Ord, Show)
data AddrOp = LoadOp | StoreOp | BranchAddrOp | SelectAddrOp | SwitchAddrOp
    deriving (Eq, Ord, Show, Enum)
data AddrEntry = AddrEntry { addrType :: AddrEntryType
                           , addrVal :: Word64
                           , addrOff :: Word32
                           , addrFlag :: AddrFlag }
    deriving (Eq, Ord, Show)
data AddrEntryType = HAddr | MAddr | IAddr | LAddr | GReg | GSpec | Unk | Const | Ret
    deriving (Eq, Ord, Show, Enum)
data AddrFlag = IrrelevantFlag | NoFlag | ExceptionFlag | ReadlogFlag | FuncargFlag
    deriving (Eq, Ord, Show)

$(deriveNFData ''AddrFlag)
$(deriveNFData ''AddrEntryType)
$(deriveNFData ''AddrEntry)
$(deriveNFData ''AddrOp)
$(deriveNFData ''MemlogOp)
