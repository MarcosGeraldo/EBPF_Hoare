import EBPFSpec.B_Instructions

def step_instr (instr : opCode) (s : MachineState) : (MachineState × PC ) :=
  match instr with
  | .mov_K dst imm => ( s.[dst ↦ imm] , 0)
  | .mov_X dst src => ( s.[dst ↦ s.(src)] , 0)
  | .add_K dst imm => ( s.[dst ↦ s.(dst) + imm] , 0)
  | .add_X dst src => ( s.[dst ↦ s.(dst) + s.(src)] , 0)
  | .and_K dst imm => ( s.[dst ↦ s.(dst) &&& imm] , 0)
  | .and_X dst src => ( s.[dst ↦ s.(dst) &&& s.(src)] , 0)

  | .jgt_X dst src offset =>
    if s.(dst) > s.(src) then
      (s , offset)
    else
      (s , 0)

  | .jgt_K dst imm offset =>
    if s.(dst) > imm then
      (s , offset)
    else
      (s , 0)

  | .jne_X dst src offset =>
    if s.(dst) ≠ s.(src) then
      (s , offset)
    else
      (s , 0)

  | .jne_K dst imm offset =>
    if s.(dst) ≠ imm then
      (s , offset)
    else
      (s , 0)

  | .jeq_X dst src offset =>
    if s.(dst) = s.(src) then
      (s , offset)
    else
      (s , 0)

  | .jeq_K dst imm offset =>
    if s.(dst) = imm then
      (s , offset)
    else
      (s , 0)

  | .jset_X dst src offset =>
    if (s.(dst) &&& s.(src)) ≠ 0 then
      (s , offset)
    else
      (s , 0)

  | .jset_K dst imm offset =>
    if (s.(dst) &&& imm ) ≠ 0 then
      (s , offset)
    else
      (s , 0)

  | .sth_X src index => (s.[index]:= s.(src) , 0)

  | .sth_K imm index =>(s.[index]:= imm , 0)

  | .ldh_X dst src index =>
    match s.[index + s.(src)] with
    | some val => (s.[dst ↦ val ], 0)
    | none => (s, 0)
  | .exit => ( s, 0 )

def interp (fuel : ℕ) (prog : Code ) (s : MachineState) (pc : PC): Option MachineState :=
  match fuel with
  | 0 => none
  | f + 1 =>
    match prog.get? pc with
    | none => none
    | some .exit => some s
    | some instr =>
      let (next_state , offset) := step_instr instr s
      interp f prog next_state (pc+offset+1)

def emptyRegs : RegsState := fun _ => 0
def emptyStack : StackState := fun _ => none

def emptyState : MachineState := (emptyRegs, emptyStack)

instance : Repr MachineState where
  reprPrec s _ :=
    match s with
    | (regs, stack) =>
      -- 1. Mapeia todos os registradores para os seus valores atuais
      let regList : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]
      let regsVals := regList.map (fun r => (r, regs r))

      -- 2. Varre a pilha (de 0 a 511) filtrando as posições que contêm 'some v'
      let stackVals := (List.range 512).filterMap (fun i =>
        match readStackNat stack i with
        | some v => some (i, v)
        | none => none
      )

      f!"Registers: {repr regsVals}\nStack (non-empty): {repr stackVals}"


def prog_test : List opCode :=
  [ .mov_K .r1 10
  , .mov_K .r2 20
  , .add_X .r1 .r2
  , .exit
  ]

#eval interp 100 prog_test emptyState 0
