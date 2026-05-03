import Mathlib.Data.Nat.Defs
import EBPFSpec.A_Memory

-------------------------------------------------
------------------ Instruction ----------------------
-------------------------------------------------

inductive opCode where
  | add_K (dst : Reg) (imm : ℕ )
  | add_X (dst src : Reg)
  | and_K (dst : Reg) (imm : ℕ )
  | and_X (dst src : Reg)
  | mov_K (dst : Reg) (imm : ℕ )
  | mov_X (dst src : Reg)
  | jgt_K (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jgt_X (dst src : Reg) (offset : ℕ )
  | jne_K (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jne_X (dst src : Reg) (offset : ℕ )
  | jeq_K (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jeq_X (dst src : Reg) (offset : ℕ )
  | jset_K (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jset_X (dst src : Reg) (offset : ℕ )
  | ldh_X (dst : Reg) (src : Reg) (index : ℕ )
  | sth_K (imm index : ℕ )
  | sth_X (src : Reg) (index : ℕ )
  | exit

abbrev Code := List opCode
