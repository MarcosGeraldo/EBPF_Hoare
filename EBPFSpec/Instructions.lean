import Mathlib.Data.Nat.Defs
import EBPFSpec.Memory

-------------------------------------------------
------------------ Instruction ----------------------
-------------------------------------------------

inductive opCode where
  | add_K_32 (dst : Reg) (imm : ℕ )
  | add_X_32 (dst src : Reg)
  | and_K_32 (dst : Reg) (imm : ℕ )
  | and_X_32 (dst src : Reg)
  --| add_K_64 (dst : Reg) (imm : ℕ )
  --| add_X_64 (dst src : Reg)
  | mov_K_32 (dst : Reg) (imm : ℕ )
  | mov_X_32 (dst src : Reg)
  --| jmp_K_32 (offset : ℕ )
  --| jmp_X_32 (offset : ℕ )
  | jgt_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jgt_X_32 (dst src : Reg) (offset : ℕ )
  | jne_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jne_X_32 (dst src : Reg) (offset : ℕ )
  | jeq_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jeq_X_32 (dst src : Reg) (offset : ℕ )
  | jset_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ )
  | jset_X_32 (dst src : Reg) (offset : ℕ )
  --| ldh_K_32 (imm : ℕ ) (index : ℕ )
  | ldh_X_32 (dst : Reg) (src : Reg) (index : ℕ )
  --| ldxh_K_32 (imm : ℕ ) (index : ℕ )
  | ldxh_X_32 (dst : Reg) (index : ℕ )
  | sth_K_32 (imm index : ℕ )
  | sth_X_32 (src : Reg) (index : ℕ )
  | exit

-- (ℕ → ℕ → Prop)

/-
Qual o tipos do operadores <,>,=, criar uma classe JMP operador reg reg offset
-/

abbrev Code := List opCode
