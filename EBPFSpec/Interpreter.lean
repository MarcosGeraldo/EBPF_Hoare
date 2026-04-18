import EBPFSpec.Programs

def step_instr (instr : opCode) (s : MachineState) : (MachineState × ℕ ) :=
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
  | .exit => ( s, 0 ) -- Exit não muda o estado na execução isolada


def interp (fuel : ℕ) (prog : Code ) (s : MachineState) (pc : PC): Option MachineState :=
  match fuel with
  | 0 => none -- O programa entrou em loop infinito ou o fuel acabou
  | f + 1 =>
    match prog.get? pc with
    | none => none -- Falha de segmentação: PC apontou para fora do código
    | some .exit => some s -- Parada natural e bem-sucedida do programa
    | some instr =>
      -- Aplica a instrução e chama o interpretador recursivamente
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

      -- 3. Formata a saída utilizando a interpolação f!"..." da biblioteca Std.Format
      f!"Registers: {repr regsVals}\nStack (non-empty): {repr stackVals}"

#eval interp 100 prog_only_IPv4_TCP_SSH emptyState 0

-- Programa que soma 10 e 20, guardando o resultado no registo r1
def prog_teste : List opCode :=
  [ .mov_K .r1 10
  , .mov_K .r2 20
  , .add_X .r1 .r2
  , .exit
  ]

-- Executa o programa com 100 de "combustível", iniciando no PC 0 com a memória vazia
#eval interp 100 prog_teste emptyState 0

lemma exec_to_step {code : Code} {pc : PC} {s : MachineState} {instr : opCode}
    (h_fetch : code.get? pc = some instr) (h_not_exit : instr ≠ .exit) :
    let (next_s, offset) := step_instr instr s
    step code (pc + offset + 1) s next_s := by
  -- A prova é feita analisando a instrução específica e aplicando o construtor correspondente
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

theorem hoare_step_sound {prog : List opCode} {pc next_pc : PC}
  {P Q : Assert} {s next_s : MachineState}
  (h_triple : Triple P prog pc Q)
  (h_step : step prog pc s next_s)
  (h_pre : P s) : Q next_s := by
  -- A prova é conduzida por indução estrutural sobre a derivação da tripla de Hoare
  induction h_triple generalizing s next_s next_pc
  case consequence P P' Q Q' hP hcore hQ ih =>
    -- Regra da Consequência: ajusta a pré-condição e a pós-condição
    apply hQ
    apply ih
    · exact next_pc
    · exact h_step
    · apply hP
      exact h_pre

  case seq P R Q h1 h2 ih1 ih2 =>
    -- Regra da Sequência: esse caso geralmente exige a relação `run` iterativa,
    -- pois um único `step` não processa um bloco de sequência inteiro.
    apply ih2
    . exact next_pc
    .
       sorry
    . sorry
    . sorry

  case mov_K pc' P dst imm hfetch =>
    cases h_step with
    | rule_mov_K =>
      sorry
    | _ =>
      sorry

  case add_X pc' P src dst hfetch =>
    cases h_step
    case rule_add_X _ _ _ _ =>
      sorry

  case jgt_X_true pc' P dst src offset hfetch =>
    -- Nos pulos condicionais, a pré-condição carrega a conjunção do teste
    -- h_pre : s.(dst) > s.(src) ∧ P s
    cases h_step
    case jgt_X_true _ _ _ _ _ =>
      exact h_pre.2
    case jgt_X_false _ _ _ _ _ =>
      -- Contradição: O step diz que <= mas a pré-condição (ramo true) exige >
      -- Pode ser resolvido com as táticas do Lean mostrando que não pode ser falso e verdadeiro ao mesmo tempo.
      sorry

  -- (Demais casos seguem a mesma lógica estrutural: fazer o `cases` no `step`,
  -- demonstrar a correspondência do estado e descartar ramificações inválidas)


theorem hoare_run_sound {prog : List opCode} {pc : PC} {P Q : Assert} {s s_final : MachineState}
  (h_triple : Triple P prog pc Q)
  (h_run : run prog pc s s_final)
  (h_pre : P s) :
  Q s_final := by
  -- Esta prova normalmente prossegue por indução sobre a execução (h_run)
  -- utilizando o teorema `hoare_step_sound` para cada passo isolado.
  sorry
