import Mathlib.Data.Nat.Defs
import EBPFSpec.Instructions
import EBPFSpec.Memory


inductive step (code : List opCode) : PC → MachineState → MachineState → Prop where

  | rule_exit : ∀
      (pc : PC)
      {s : MachineState},
      code.get? pc = .some (opCode.exit) →
      step code pc s s

  | rule_mov_X_32 : ∀
      (pc : PC)
      {s : MachineState} {dst src : Reg},
      code.get? pc = some (opCode.mov_X_32 dst src) →
      step code (pc+1) s (s.[dst↦ s.(src)])

  | rule_mov_K_32 : ∀
      (pc : PC)
      {s : MachineState} {dst : Reg} {imm : ℕ},
      code.get? pc = some (opCode.mov_K_32 dst imm) →
      step code (pc+1) s (s.[dst↦ imm])

  | rule_add_X_32 : ∀
      (pc : PC)
      {s : MachineState}
      {dst src : Reg},
      code.get? pc = .some (opCode.add_X_32 dst src) →
      step code (pc+1) s (s.[dst↦ s.(dst) + s.(src) ])

  | rule_add_K_32 : ∀
      (pc : PC)
      {s : MachineState}
      {imm : ℕ }
      {dst : Reg},
      code.get? pc = .some (opCode.add_K_32 dst imm) →
      step code (pc+1) s (s.[dst↦ s.(dst) + imm ])

  | rule_and_X_32 : ∀
      (pc : PC)
      {s : MachineState}
      {dst src : Reg},
      code.get? pc = .some (opCode.and_X_32 dst src) →
      step code (pc+1) s (s.[dst↦ s.(dst) &&& s.(src) ])

  | rule_and_K_32 : ∀
      (pc : PC)
      {s : MachineState}
      {imm : ℕ }
      {dst : Reg},
      code.get? pc = .some (opCode.and_K_32 dst imm) →
      step code (pc+1) s (s.[dst↦ s.(dst) &&& imm ])

  | rule_ldh_X_32 :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ} {v},
      code.get? pc = some (opCode.ldh_X_32 dst src index) →
      s.[index + s.(src)] = some v →
      step code (pc+1) s (s.[dst↦ v ])

  | rule_ldh_X_32_none :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ},
      code.get? pc = some (opCode.ldh_X_32 dst src index) →
      s.[index + s.(src)] = none →
      step code (pc+1) s s
  | rule_ldxh_X_32 :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ} {v},
      code.get? pc = some (opCode.ldxh_X_32 dst index) →
      s.[index] = some v →
      step code (pc+1) s (s.[dst↦ v])

  | rule_ldxh_X_32_none :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ},
      code.get? pc = some (opCode.ldxh_X_32 dst index) →
      s.[index] = none →
      step code (pc+1) s s

  | rule_sth_X_32 :
      ∀ {s : MachineState} {src : Reg} {index : ℕ},
      code.get? pc = some (opCode.sth_X_32 src index) →
      step code (pc+1) s (s.[index]:= s.(src))

  | rule_sth_K_32 :
      ∀ {s : MachineState} {imm index : ℕ},
      code.get? pc = some (opCode.sth_K_32 imm index) →
      step code (pc+1) s (s.[index]:= imm)

  | jgt_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_X_32 dst src offset) →
      s.(dst) > s.(src) →
      step code (pc+offset+1) s s

  | jgt_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_X_32 dst src offset) →
      s.(dst) ≤ s.(src) →
      step code (pc+1) s s

  | jgt_K_true :
      ∀ {s : MachineState} { imm : ℕ } {dst : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_K_32 dst imm offset) →
      s.(dst) > imm →
      step code (pc+offset+1) s s

  | jgt_K_false :
      ∀ {s : MachineState} { imm : ℕ } {dst : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_K_32 dst imm offset) →
      s.(dst) ≤ imm →
      step code (pc+1) s s

  | jne_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jne_X_32 dst src offset) →
      s.(dst) ≠ s.(src) →
      step code (pc+offset+1) s s

  | jne_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jne_X_32 dst src offset) →
      s.(dst) = s.(src) →
      step code (pc+1) s s

  | jne_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jne_K_32 dst imm offset) →
      s.(dst) ≠ imm →
      step code (pc+offset+1) s s

  | jne_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jne_K_32 dst imm offset) →
      s.(dst) = imm →
      step code (pc+1) s s

  | jeq_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jeq_X_32 dst src offset) →
      s.(dst) = s.(src) →
      step code (pc+offset+1) s s

  | jeq_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jeq_X_32 dst src offset) →
      s.(dst) ≠ s.(src) →
      step code (pc+1) s s

  | jeq_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jeq_K_32 dst imm offset) →
      s.(dst) = imm →
      step code (pc+offset+1) s s

  | jeq_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jeq_K_32 dst imm offset) →
      s.(dst) ≠ imm →
      step code (pc+1) s s

  | jset_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jset_X_32 dst src offset) →
      (Nat.land (s.(dst)) (s.(src))) ≠ 0 →
      step code (pc+offset+1) s s

  | jset_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jset_X_32 dst src offset) →
      (Nat.land (s.(dst)) (s.(src))) = 0 →
      step code (pc+1) s s

  | jset_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jset_K_32 dst imm offset) →
      (Nat.land (s.(dst)) imm ) ≠ 0 →
      step code (pc+offset+1) s s

  | jset_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jset_K_32 dst imm offset) →
      (Nat.land (s.(dst)) imm ) = 0 →
      step code (pc+1) s s



inductive run (code : Code) : PC → MachineState → MachineState → Prop where
  | halt (pc : PC) (s : MachineState) :
      code.get? pc = some .exit →
      run code pc s s
  | seq (pc next_pc : PC) (s next_s s_final : MachineState) :
      step code next_pc s next_s →
      run code next_pc next_s s_final →
      run code pc s s_final
