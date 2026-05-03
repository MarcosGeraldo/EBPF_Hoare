import EBPFSpec.D_Sep_Logic

@[simp]
def wp (instr : opCode) (Q_next Q_jump Q_final : Assert) : Assert :=
  match instr with
  | .exit => Q_final
  | .mov_K dst imm => fun s => Q_next (s.[dst ↦ imm])
  | .mov_X dst src  => fun s => Q_next (s.[dst ↦ s.(src)] )
  | .add_K dst imm => fun s => Q_next ( s.[dst ↦ s.(dst) + imm] )
  | .add_X dst src => fun s => Q_next ( s.[dst ↦ s.(dst) + s.(src)] )
  | .and_K dst imm => fun s => Q_next ( s.[dst ↦ s.(dst) &&& imm] )
  | .and_X dst src => fun s => Q_next ( s.[dst ↦ s.(dst) &&& s.(src)] )
  | .jgt_X dst src _ => fun s => (s.(dst) > s.(src) → Q_jump s) ∧ (s.(dst) ≤ s.(src) → Q_next s)
  | .jgt_K dst imm _ => fun s => (s.(dst) > imm → Q_jump s) ∧ (s.(dst) ≤ imm → Q_next s)
  | .jne_X dst src _ => fun s => (s.(dst) ≠ s.(src) → Q_jump s) ∧ (s.(dst) = s.(src) → Q_next s)
  | .jne_K dst imm _ => fun s => (s.(dst) ≠ imm → Q_jump s) ∧ (s.(dst) = imm → Q_next s)
  | .jeq_X dst src _ => fun s => (s.(dst) = s.(src) → Q_jump s) ∧ (s.(dst) ≠ s.(src) → Q_next s)
  | .jeq_K dst imm _ => fun s => (s.(dst) = imm → Q_jump s) ∧ (s.(dst) ≠ imm → Q_next s)
  | .jset_K dst imm _ => fun s => (s.(dst) &&& imm ≠ 0 → Q_jump s) ∧ (s.(dst) &&& imm = 0 → Q_next s)
  | .jset_X dst src _ => fun s => (s.(dst) &&& s.(src) ≠ 0 → Q_jump s) ∧ (s.(dst) &&& s.(src) = 0 → Q_next s)
  | .ldh_X dst src index => fun s => ∃ val,s.[index + s.(src)] = some val ∧  Q_next ( s.[dst ↦ val] )
  | .sth_X src index => fun s => Q_next ( s.[index]:= s.(src) )
  | .sth_K imm index => fun s => Q_next ( s.[index]:= imm )

@[simp]
def blockWP (instrs : List opCode) (Q : Assert) : Assert :=
  instrs.foldr (fun instr acc => wp instr acc (fun _ => False) Q) Q


abbrev InvMap := ℕ → Option Assert

structure VCGResult where
  /-- The computed weakest precondition for the code block. -/
  pre : Assert
  /-- Side conditions that must hold for the triple to be valid. -/
  vcs : List Prop

@[simp]
def vcg (code : Code) (Q : Assert) (inv : InvMap) : ℕ → ℕ → VCGResult
  | 0,        _  => { pre := fun _ => False, vcs := [] }
  | fuel + 1, pc =>
    match code.get? pc with
    | none => { pre := Q, vcs := [] }
    | some (.jne_X dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jne_K dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jeq_X dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jeq_K dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jset_X dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jset_K dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jgt_X dst src offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
    | some (.jgt_K dst imm offset) =>
      match inv (pc + offset + 1) with
        | some iLoop =>
          let fallThrough := vcg code Q inv fuel (pc + 1)
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
        { pre := Q, vcs := [] }
    | some instr =>
      let rest := vcg code Q inv fuel (pc + 1)
      { pre := wp instr rest.pre Q Q, vcs := rest.vcs }


@[simp]
def vcgCheck (fuel : ℕ) (code : Code) (P Q : Assert) (inv : InvMap) : List Prop :=
  let result := vcg code Q inv fuel 0
  (∀ s, P s → result.pre s) :: result.vcs
