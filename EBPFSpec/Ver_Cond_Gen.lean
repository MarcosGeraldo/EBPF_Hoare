import EBPFSpec.Sep_Logic

-- Make the Verification Condition Generator Here


def wp (i : opCode) (Q : Assert) : Assert :=
  match i with
  | .mov_K_32 dst imm  => fun s => Q (s.[dst ↦ imm] )
  | .mov_X_32 dst src  => fun s => Q (s.[dst ↦ s.(src)] )
  | .add_K_32 dst imm => fun s => Q ( s.[dst ↦ s.(dst) + imm] )
  | .add_X_32 dst src => fun s => Q ( s.[dst ↦ s.(dst) + s.(src)] )
  | .and_K_32 dst imm => fun s => Q ( s.[dst ↦ s.(dst) &&& imm] )
  | .and_X_32 dst src => fun s => Q ( s.[dst ↦ s.(dst) &&& s.(src)] )
  | .jgt_X_32 _ _ _ => Q
  | .jgt_K_32 _ _ _ => Q
  | .jne_X_32 _ _ _ => Q
  | .jne_K_32 _ _ _ => Q
  | .jeq_X_32 _ _ _ => Q
  | .jeq_K_32 _ _ _ => Q
  | .jset_K_32 _ _ _ => Q
  | .jset_X_32 _ _ _ => Q
  | .ldh_X_32 dst src index => fun s => ∃ val,s.[index + s.(src)] = some val ∧  Q ( s.[dst ↦ val] )
  | .ldxh_X_32 dst index => fun s => ∃ val,s.[index] = some val ∧  Q ( s.[dst ↦ val] )
  | .sth_X_32 src index => fun s => Q ( s.[index]:= s.(src) )
  | .sth_K_32 imm index => fun s => Q ( s.[index]:= imm )
  | .exit => Q

def blockWP (instrs : List opCode) (Q : Assert) : Assert :=
  instrs.foldr wp Q

-- Não precisava
abbrev InvMap := ℕ → Option Assert

structure VCGResult where
  /-- The computed weakest precondition for the code block. -/
  pre : Assert
  /-- Side conditions that must hold for the triple to be valid. -/
  vcs : List Prop

def vcg (code : Code) (Q : Assert) (inv : InvMap) : ℕ → ℕ → VCGResult
  | 0,        _  => { pre := fun _ => False, vcs := [] }
  | fuel + 1, pc =>
    match code.get? pc with
    | none => { pre := Q, vcs := [] }
    | some (.jne_X_32 dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = s.(src)) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) ≠ s.(src) → iLoop s) ∧
            (s.(dst) = s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) ≠ s.(src) → taken.pre s) ∧
            (s.(dst) = s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jne_K_32 dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = imm) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) ≠ imm → iLoop s) ∧
            (s.(dst) = imm → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) ≠ imm → taken.pre s) ∧
            (s.(dst) = imm → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jeq_X_32 dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = s.(src)) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) = s.(src) → iLoop s) ∧
            (s.(dst) ≠ s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) = s.(src) → taken.pre s) ∧
            (s.(dst) ≠ s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jeq_K_32 dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = imm) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) = imm → iLoop s) ∧
            (s.(dst) ≠ imm → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) = imm → taken.pre s) ∧
            (s.(dst) ≠ imm → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jset_X_32 dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = s.(src)) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) &&& s.(src) ≠ 0 → iLoop s) ∧
            (s.(dst) &&& s.(src) = 0 → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) &&& s.(src) ≠ 0 → taken.pre s) ∧
            (s.(dst) &&& s.(src) = 0 → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jset_K_32 dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) = imm) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) &&& imm ≠ 0 → iLoop s) ∧
            (s.(dst) &&& imm = 0 → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) &&& imm ≠ 0 → taken.pre s) ∧
            (s.(dst) &&& imm = 0 → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jgt_X_32 dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) ≤ s.(src)) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) > s.(src) → iLoop s) ∧
            (s.(dst) ≤ s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) > s.(src) → taken.pre s) ∧
            (s.(dst) ≤ s.(src) → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.jgt_K_32 dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
          /-let vcFall : Prop := ∀ s, iLoop s →
          ( s.(dst) ≤ imm) → fallThrough.pre s
          { pre := iLoop
            vcs := vcFall :: fallThrough.vcs }-/
          let pre : Assert := fun s =>
            (s.(dst) > imm → iLoop s) ∧
            (s.(dst) ≤ imm → fallThrough.pre s)
          { pre := pre
            vcs := fallThrough.vcs }
        | none =>
          let taken       := vcg code Q inv fuel (pc + offset+1)
          let fallThrough := vcg code Q inv fuel (pc + 1)
          let pre : Assert := fun s =>
            (s.(dst) > imm → taken.pre s) ∧
            (s.(dst) ≤ imm → fallThrough.pre s)
          { pre := pre
            vcs := taken.vcs ++ fallThrough.vcs }
    | some (.exit) =>
      --{ pre := Q, vcs := [] }
        --let end_prog := vcg code Q inv fuel (pc + (code.length))
        --let rest := vcg code Q inv fuel (pc + 1)
        --let pre : Assert :=
        --{ pre := wp instr rest.pre, vcs := end_prog }
        --{ pre := Q, vcs := end_prog.vcs }
        { pre := Q, vcs := [] }
      /-let rest := vcg code Q inv fuel (pc)
      match code.get? pc with
      | some instr => { pre := wp instr rest.pre, vcs := rest.vcs }
      | none => { pre := Q, vcs := [] }-/
    | some instr =>
      let rest := vcg code Q inv fuel (pc + 1)
      { pre := wp instr rest.pre, vcs := rest.vcs }



def vcgCheck (fuel : ℕ) (code : Code) (P Q : Assert) (inv : InvMap) : List Prop :=
  let result := vcg code Q inv fuel 0
  (∀ s, P s → result.pre s) :: result.vcs

/-
O Rodrigo utilizou cond para validar se o jump ira ocorrer ou não
onde cond é um registrador
em ebpf não posso alterar o valor de um registrador
para posteriormente avaliar se isso será verdadeiro ou não
Como posso fazer tal avaliação?
      -/

theorem wp_sound
    (prog : List opCode) (pc : PC)  (i : opCode) (Q : Assert)
    (hfetch : prog.get? pc = some i) :
    ⦃ wp i Q ⦄ prog @ pc ⦃ Q ⦄ := by
    --Triple wp i Q  prog  Q := by
  match i with
  | .mov_K_32 dst imm  => exact Triple.mov_K_32 hfetch
  | .mov_X_32 dst src  => exact Triple.mov_X_32 hfetch
  | .add_K_32 dst imm => exact Triple.add_K_32 hfetch
  | .add_X_32 dst src => exact Triple.add_X_32 hfetch
  | .and_K_32 dst imm => exact Triple.and_K_32 hfetch
  | .and_X_32 dst src => exact Triple.and_X_32 hfetch
  | .ldh_X_32 dst src index => exact Triple.ldh_X_32 hfetch
  | .ldxh_X_32 dst index => exact Triple.ldxh_X_32 hfetch
  | .sth_X_32 src index => exact Triple.sth_X_32 hfetch
  | .sth_K_32 imm index => exact Triple.sth_K_32 hfetch
  | .exit => exact Triple.exit hfetch
  | .jgt_X_32 dst src offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) > s.(src) ∧ Q s) ∨ ( s.(dst) ≤ s.(src) ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) ≤ s.(src))
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨Nat.lt_of_not_le h, hQs⟩
    · exact Triple.disj
            (Triple.jgt_X_32_true hfetch)
            (Triple.jgt_X_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jgt_K_32 dst imm offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) > imm ∧ Q s) ∨ ( s.(dst) ≤ imm ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) ≤ imm)
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨Nat.lt_of_not_le h, hQs⟩
    · exact Triple.disj
            (Triple.jgt_K_32_true hfetch)
            (Triple.jgt_K_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jne_X_32 dst src offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) ≠ s.(src) ∧ Q s) ∨ ( s.(dst) = s.(src) ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) = s.(src))
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨fun eq => h eq, hQs⟩
    · exact Triple.disj
            (Triple.jne_X_32_true hfetch)
            (Triple.jne_X_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jne_K_32 dst imm offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) ≠ imm ∧ Q s) ∨ ( s.(dst) = imm ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) = imm)
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨h, hQs⟩
    · exact Triple.disj
            (Triple.jne_K_32_true hfetch)
            (Triple.jne_K_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jeq_X_32 dst src offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) = s.(src) ∧ Q s) ∨ ( s.(dst) ≠ s.(src) ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) ≠ s.(src))
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨Classical.not_not.mp h, hQs⟩
    · exact Triple.disj
            (Triple.jeq_X_32_true hfetch)
            (Triple.jeq_X_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jeq_K_32 dst imm offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) = imm ∧ Q s) ∨ ( s.(dst) ≠ imm ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) ≠ imm)
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨Classical.not_not.mp h, hQs⟩
    · exact Triple.disj
            (Triple.jeq_K_32_true hfetch)
            (Triple.jeq_K_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jset_X_32 dst src offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) &&& s.(src) ≠ 0 ∧ Q s) ∨ ( s.(dst) &&& s.(src) = 0 ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) &&& s.(src) = 0)
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨ h, hQs⟩
    · exact Triple.disj
            (Triple.jset_X_32_true hfetch)
            (Triple.jset_X_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
  | .jset_K_32 dst imm offset =>
    change ⦃ Q ⦄ prog @ pc ⦃ Q ⦄
    apply Triple.consequence
      (P := fun s => ( s.(dst) &&& imm ≠ 0 ∧ Q s) ∨ ( s.(dst) &&& imm = 0 ∧ Q s))
    · -- hP : Q ⊢ₐ fun s => (cond ≠ 0 ∧ Q s) ∨ (cond = 0 ∧ Q s)
      intro s hQs
      by_cases h : (s.(dst) &&& imm = 0)
      · exact Or.inr ⟨h, hQs⟩
      · exact Or.inl ⟨h, hQs⟩
    · exact Triple.disj
            (Triple.jset_K_32_true hfetch)
            (Triple.jset_K_32_false hfetch)
    · -- hQ : Q ⊢ₐ Q
      intro s h
      exact h
