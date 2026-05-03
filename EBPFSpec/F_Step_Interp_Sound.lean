import EBPFSpec.C_Semantic_Step
import EBPFSpec.E_Interpreter

lemma step_instr_to_step {code : Code} {pc : PC} {s : MachineState} {instr : opCode}
    (h_fetch : code.get? pc = some instr) (h_not_exit : instr ≠ .exit) :
    let (next_s, offset) := step_instr instr s
    step code pc (pc + offset + 1) s next_s := by
  cases instr with
  | exit =>
    contradiction
  | mov_X dst src =>
    simp [step_instr]
    exact step.rule_mov_X pc h_fetch
  | mov_K dst imm =>
    simp [step_instr]
    exact step.rule_mov_K pc h_fetch
  | add_X dst src =>
    simp [step_instr]
    exact step.rule_add_X pc h_fetch
  | add_K dst imm =>
    simp [step_instr]
    exact step.rule_add_K pc h_fetch
  | and_X dst src =>
    simp [step_instr]
    exact step.rule_and_X pc h_fetch
  | and_K dst imm =>
    simp [step_instr]
    exact step.rule_and_K pc h_fetch
  | sth_X src index =>
    simp [step_instr]
    exact step.rule_sth_X h_fetch
  | sth_K imm index =>
    simp [step_instr]
    exact step.rule_sth_K h_fetch
  | ldh_X dst src index =>
    simp [step_instr]
    split
    · next h =>
      simp
      exact step.rule_ldh_X h_fetch h
    · next h =>
      simp
      exact step.rule_ldh_X_none h_fetch h
  | jgt_X dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jgt_X_true h_fetch h
    ·
      next h =>
        simp
        exact step.jgt_X_false h_fetch (Nat.le_of_not_lt h)
  | jgt_K dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jgt_K_true h_fetch h
    ·
      next h =>
        simp
        exact step.jgt_K_false h_fetch (Nat.le_of_not_lt h)
  | jne_X dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jne_X_false h_fetch h
    ·
      next h =>
        simp
        exact step.jne_X_true h_fetch h
  | jne_K dst imm offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jne_K_false h_fetch h
    ·
      next h =>
        simp
        exact step.jne_K_true h_fetch h
  | jeq_X dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jeq_X_true h_fetch h
    ·
      next h =>
        simp
        exact step.jeq_X_false h_fetch h
  | jeq_K dst imm offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jeq_K_true h_fetch h
    ·
      next h =>
        simp
        exact step.jeq_K_false h_fetch h
  | jset_X dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jset_X_false h_fetch h
    ·
      next h =>
        simp
        exact step.jset_X_true h_fetch h
  | jset_K dst src offset =>
    simp [step_instr]
    split
    ·
      next h =>
        simp
        exact step.jset_K_false h_fetch h
    ·
      next h =>
        simp
        exact step.jset_K_true h_fetch h


lemma interp_to_run {code : Code} {pc : PC} {fuel : ℕ} {s : MachineState} {instr : opCode}
    (h_fetch : code.get? pc = some instr) (h_not_exit : instr ≠ .exit) (h_fuel : fuel > 0 ) :
    some s = interp fuel code s pc →
    run code pc s next_s := by
    sorry
