import Mathlib.Data.Nat.Defs
import EBPFSpec.B_Instructions


inductive step (code : List opCode) : PC → PC → MachineState → MachineState → Prop where

  | rule_exit : ∀
      (pc : PC)
      {s : MachineState},
      code.get? pc = .some (opCode.exit) →
      step code pc pc s s

  | rule_mov_X : ∀
      (pc : PC)
      {s : MachineState} {dst src : Reg},
      code.get? pc = some (opCode.mov_X dst src) →
      step code pc (pc+1) s (s.[dst↦ s.(src)])

  | rule_mov_K : ∀
      (pc : PC)
      {s : MachineState} {dst : Reg} {imm : ℕ},
      code.get? pc = some (opCode.mov_K dst imm) →
      step code pc (pc+1) s (s.[dst↦ imm])

  | rule_add_X : ∀
      (pc : PC)
      {s : MachineState}
      {dst src : Reg},
      code.get? pc = .some (opCode.add_X dst src) →
      step code pc (pc+1) s (s.[dst↦ s.(dst) + s.(src) ])

  | rule_add_K : ∀
      (pc : PC)
      {s : MachineState}
      {imm : ℕ }
      {dst : Reg},
      code.get? pc = .some (opCode.add_K dst imm) →
      step code pc (pc+1) s (s.[dst↦ s.(dst) + imm ])

  | rule_and_X : ∀
      (pc : PC)
      {s : MachineState}
      {dst src : Reg},
      code.get? pc = .some (opCode.and_X dst src) →
      step code pc (pc+1) s (s.[dst↦ s.(dst) &&& s.(src) ])

  | rule_and_K : ∀
      (pc : PC)
      {s : MachineState}
      {imm : ℕ }
      {dst : Reg},
      code.get? pc = .some (opCode.and_K dst imm) →
      step code pc (pc+1) s (s.[dst↦ s.(dst) &&& imm ])

  | rule_ldh_X :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ} {v},
      code.get? pc = some (opCode.ldh_X dst src index) →
      s.[index + s.(src)] = some v →
      step code pc (pc+1) s (s.[dst↦ v ])

  | rule_ldh_X_none :
      ∀ {s : MachineState} {dst : Reg} {index : ℕ},
      code.get? pc = some (opCode.ldh_X dst src index) →
      s.[index + s.(src)] = none →
      step code pc (pc+1) s s

  | rule_sth_X :
      ∀ {s : MachineState} {src : Reg} {index : ℕ},
      code.get? pc = some (opCode.sth_X src index) →
      step code pc (pc+1) s (s.[index]:= s.(src))

  | rule_sth_K :
      ∀ {s : MachineState} {imm index : ℕ},
      code.get? pc = some (opCode.sth_K imm index) →
      step code pc (pc+1) s (s.[index]:= imm)

  | jgt_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_X dst src offset) →
      s.(dst) > s.(src) →
      step code pc (pc+offset+1) s s

  | jgt_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_X dst src offset) →
      s.(dst) ≤ s.(src) →
      step code pc (pc+1) s s

  | jgt_K_true :
      ∀ {s : MachineState} { imm : ℕ } {dst : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_K dst imm offset) →
      s.(dst) > imm →
      step code pc (pc+offset+1) s s

  | jgt_K_false :
      ∀ {s : MachineState} { imm : ℕ } {dst : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jgt_K dst imm offset) →
      s.(dst) ≤ imm →
      step code pc (pc+1) s s

  | jne_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jne_X dst src offset) →
      s.(dst) ≠ s.(src) →
      step code pc (pc+offset+1) s s

  | jne_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jne_X dst src offset) →
      s.(dst) = s.(src) →
      step code pc (pc+1) s s

  | jne_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jne_K dst imm offset) →
      s.(dst) ≠ imm →
      step code pc (pc+offset+1) s s

  | jne_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jne_K dst imm offset) →
      s.(dst) = imm →
      step code pc (pc+1) s s

  | jeq_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jeq_X dst src offset) →
      s.(dst) = s.(src) →
      step code pc (pc+offset+1) s s

  | jeq_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jeq_X dst src offset) →
      s.(dst) ≠ s.(src) →
      step code pc (pc+1) s s

  | jeq_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jeq_K dst imm offset) →
      s.(dst) = imm →
      step code pc (pc+offset+1) s s

  | jeq_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jeq_K dst imm offset) →
      s.(dst) ≠ imm →
      step code pc (pc+1) s s

  | jset_X_true :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jset_X dst src offset) →
      (Nat.land (s.(dst)) (s.(src))) ≠ 0 →
      step code pc (pc+offset+1) s s

  | jset_X_false :
      ∀ {s : MachineState} {dst src : Reg} {offset : ℕ},
      code.get? pc = some (opCode.jset_X dst src offset) →
      (Nat.land (s.(dst)) (s.(src))) = 0 →
      step code pc (pc+1) s s

  | jset_K_true :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jset_K dst imm offset) →
      (Nat.land (s.(dst)) imm ) ≠ 0 →
      step code pc (pc+offset+1) s s

  | jset_K_false :
      ∀ {s : MachineState} {dst : Reg} {imm offset : ℕ},
      code.get? pc = some (opCode.jset_K dst imm offset) →
      (Nat.land (s.(dst)) imm ) = 0 →
      step code pc (pc+1) s s



inductive run (code : Code) : PC → MachineState → MachineState → Prop where
  | halt (pc : PC) (s : MachineState) :
      code.get? pc = some .exit →
      run code pc s s
  | seq (pc next_pc : PC) (s next_s s_final : MachineState) :
      step code pc next_pc s next_s →
      run code next_pc next_s s_final →
      run code pc s s_final

inductive runV2 (code : Code) : PC → MachineState → MachineState → Prop where
  | halt (pc : PC) (s : MachineState) :
      code.get? pc = some .exit →
      runV2 code pc s s
  | seq (pc next_pc pc_final : PC) (s next_s s_final : MachineState) :
      step code pc next_pc s next_s →
      step code next_pc pc_final next_s s_final →
      runV2 code pc s s_final
