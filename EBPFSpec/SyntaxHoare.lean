import Mathlib.Data.Nat.Defs
import Aesop

/-
Separar em decode e encode
  Não será necessario para o meu trabalho
  Em x86 precisa pois as instruçoes fazem parte da memoria
  Decode lê memória de endereço i e tenta produzir uma instrução ι
  Definir o Step: s → s , que vai ser o decode+encode
  step : S ⇀ S que faz um pequeno passo
  decodifica a instrução apontada pelo PC/EIP
  aplica a execução da instrução (ou é indefinida em caso de falha)
Composição repetida define run(k,s) — o estado após k passos (se todos bem-sucedidos).
O run(k,s) executa k passos sobre s
Quando o Step é indefinido ocorre a falha

Estado da maquina S = (Pilha, registradores)
  Trabalha com um estado Parcial Σ
  Σ = (reg ⇀ DWORD) × (flag ⇀ {true,false,undef}) × (DWORD ⇀ (BYTE ∪ {unmapped}))
Separa as instruçoes em outro conjunto
Operador ], que faz a união de dominios disjuntos, que faz de (Σ, ]) uma logica de separação
Assertions são então predicados sobre Σ
  "r → v" significa “no fragmento considerado, o registador r tem valor v”.
  i..j → ι significa “a memória entre i e j contém os bytes que decodificam para a instrução ι”


Como Cpu não terminha, usa a premissa Safe
  Que determina que é possivel executar k passos sobre a maquina
  “a partir de um estado onde P vale, executar k passos é seguro (não falha)”.
  Isso é continuation-passing style (CPS)
  porque a especificação não afirma que um postcondition Q ocorrerá;
  antes, Q é vista como uma continuação:
  “se mais à frente for verdade que Q, então antes precisávamos de P”

A lógica de especificação (tipo spec)
  Spec — uma especificação S é um conjunto de pares (k,P)
  fechado para dois comportamentos:
  (i) fechado sob k′ ≤ k (se vale para k então vale para menos passos)
  (ii) fechado sob extensão por frames:
  se (k,P) ∈ S então para qualquer R também (k, P * R) ∈ S.
  Ou seja, S descreve “o que precisa valer no footprint relevante” e
  permite qualquer invariância extra R que estejamos a carregar.

Connectivos chave
  S ⊗ R (frame connective)
    o conjunto de (k,P) tais que (k, P * R) ∈ S. Interpretação:
    “S funcionando num contexto que também possui o invariante R”.
    Isto permite provar regras de frame de ordem superior.

  S θ R (read-only frame) exigência mais forte:
    S só é admitido se preservar exactamente R
    (pode quebrar temporariamente, mas deve restaurar R).
    Formalmente S θ R ≜ ∀σ ∈ R. S ⊗ {σ}.
    Útil para invariantes do tipo
    “essa região da memória não pode ser modificada no final”.

  .S (later / depois)
    desloca os índices de passo:
    (k,P) ∈ .S significa que para todos k′ < k temos (k′,P) ∈ S.
    Serve para fazer indução.

{P} c {Q} ≜ ∀i,j. (
    safe ⊗ (EIP 7_ j ∗ Q) ⇒
    safe ⊗ (EIP 7_ i ∗ P) ) θ i..j 7→ c
  EIP é o pc do programa, e aponta para a proxima instrução
  para todo par de endereços i..j que correspondam ao bloco c,
  se — quando estivermos na posição j com Q e um frame —
  executarmos com segurança, então antes, na posição i com P e o mesmo frame,
  também seremos seguros. Assim o post-condição Q aparece como uma continuação;

-/



/-
Como acho que ficaria o organização do ebpf

O estado da maquina iria ser representado apenas pelas memorias
  (Pilha, Registradores e PC)
  E validar o estado da maquina foi feito por meio da clausula "Safe" no trabalho

O "programa" seria na realidade uma sequencia de "c" da tripla de hoare
  {P} c {Q}
  As possiveis transformaçoes sobre o estado da maquina
  O trabalho utilizou a logica do step para definir esse C
  Ele usa a noção tambem de "footprint":
  Que seria um subconjunto da memoria que foi alterado por algo
  Porque usar estado parcial seria logica de separação?

Um Assertion é um predicado sobre um estado parcial

Iria usar a mesma logica de K operaçoes sobre os estados, para "executar" o programa
e conseguir provar por indução sobre as intruçoes
  Se eu provar separadamente para cada instrução sobre o estado S
  Estou provando para sucessivas aplicações sobre um estado S

?Verification condition generator


Desenvolver o exemplo/exercicios do Livro

Semantica do IPV4


-/

/-

Como X86 armazena as intruçoes na memoria;
A função que é State X intruction → State
Apos fazer o decode se torna State → State

Formato que vou utilizar
  Função que lê o estado dado um registrador
  Função que escreve em um estado dado um registrador
  Função que lê o estado dado uma posição da pilha
  Função que escreve em um estado dado uma posição da pilha
  Função que executa um passo
  Função que executa varios passos
  Função que determina o estado como seguro

-/

def State := String → ℕ

def update (s : State) (x : String) (n : ℕ) : State :=
  fun y => if y = x then n else s y




------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
---- Estado que representa os registradores

inductive Reg where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10
deriving Repr, DecidableEq

def RegsState := Reg → ℕ

def updateRegs (s : RegsState) (x : Reg) (n : ℕ) : RegsState :=
  fun y => if y = x then n else s y

def s_test : RegsState :=
  fun v => if v == Reg.r0 then 10
           else if v == Reg.r1 then 5
           else if v == Reg.r2 then 15
           else 0

def s1_test := updateRegs s_test Reg.r0 99

#eval s_test Reg.r0 -- 10
#eval s1_test Reg.r0 -- 99
#eval s_test Reg.r1 -- 5
-- s1_test é o novo estado apos realizar update no x
def s2_test := updateRegs s_test Reg.r2 23
#eval s2_test Reg.r2 -- 23



------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
---- Estado que representa A pilha
def StackState := Fin 512 → ℕ

abbrev pc := ℕ


def MachineState := (RegsState × StackState × pc )

inductive opCode where
  | add_K_32 (dst : Reg) (imm : ℕ ) | add_X_32 (dst src : Reg)
  | add_K_64 (dst : Reg) (imm : ℕ ) | add_X_64 (dst src : Reg)
  | mov_K_32 (dst : Reg) (imm : ℕ ) | mov_X_32 (dst src : Reg)
  | jmp_K_32 (offset : ℕ ) | jmp_X_32  (offset : ℕ )
  | jgt_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ ) | jgt_X_32 (dst src : Reg) (offset : ℕ )
  | jne_K_32 (dst : Reg) (imm : ℕ ) (offset : ℕ ) | jne_X_32 (dst src : Reg) (offset : ℕ )
  | ldh_K_32 (imm : ℕ ) (index : ℕ )| ldh_X_32 (dst : Reg) (index : ℕ )
  | ldxh_K_32 (imm : ℕ ) (index : ℕ )| ldxh_X_32 (dst : Reg) (index : ℕ )
  | sth_K_32 (imm index : ℕ )| sth_X_32 (src : Reg) (index : ℕ )
  | exit

/-
Atualização de estado
Futuro: Usar Option para tratar valores maiores que 512
Garante que só tem 512 posiçoes
Mas usa o Mod para isso, logo a posição 513 existe
-/

theorem provaFin (index : Nat) : index % 512 < 512 := by
  have h : index % 512 < 512 := Nat.mod_lt index (by decide)
  exact h

def updateStack (s : StackState) (addr : ℕ ) (n : ℕ ) : StackState :=
  fun i => if i = ⟨ addr % 512, provaFin addr ⟩ then n else s ⟨ addr % 512, provaFin addr ⟩

def readStackNat ( s : StackState) ( i : ℕ ) : ℕ :=
  s (⟨ i % 512, provaFin i ⟩)

def s_testStack : StackState :=
  fun v => if v == 0 then 10
           else if v == 1 then 5
           else if v == 2 then 15
           else 0

#eval s_testStack 0 -- 10
#eval s_testStack 1 -- 5
#eval s_testStack 2 -- 15

def s2_testStack := updateStack s_testStack 3 23
#eval s2_testStack 3 -- 23

def s3_test := updateStack s_testStack 515 25
#eval readStackNat s3_test 515 -- 23

------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------

-- Escrita e leitura dos registradores
def readReg (s : MachineState) (r : Reg) : ℕ :=
  match s with
  | (s_Reg , _ , _) => s_Reg r

def writeReg (s : MachineState) (r : Reg) (n : ℕ ) : MachineState :=
  match s with
  | (s_Reg , s_Stack , pc) => (updateRegs s_Reg r n,s_Stack, pc)

-- Escrita e leitura da pilha
def readStack (s : MachineState) (index : ℕ ) : ℕ :=
  match s with
  | (_ , s_Stack , _) => readStackNat s_Stack index

def writeStack (s : MachineState) (index : ℕ ) (n : ℕ ) : MachineState :=
  match s with
  | (s_Reg , s_Stack , pc) => ( s_Reg, updateStack s_Stack index n, pc)

-- Escrita e leitura do pc
def readPc (s : MachineState) : ℕ :=
  match s with
  | (_ , _ , pc) => pc

def incrPc (s : MachineState) (n : ℕ ) : MachineState :=
  match s with
  | (s_Reg , s_Stack , pc) => ( s_Reg, s_Stack , (pc + n) )

-- função para ler aa instrução a sser executada
def readInstruction ( prog : List opCode) (index : ℕ ) : opCode :=
  let instr' := prog.get? index
  match instr' with
  | some x => x
  | none => opCode.exit


/-
O resultado da execução de um programa eBPF
sera um estado, mas o programa sera escrito
de forma que, teremos "apenas" que provar que existe
esse estado gerado e que ele é um estado valido

Problemas:
Irei buscar a instrução por meio do PC?
Irei criar uma função separada para executar cada função?
Posso dizer que se aplicar operação X sobre estado s gerando t
  esta correto, logo aplicações sequenciais estão corretas
  mesmo sem provar essa aplicação sequencial
  Ao meu ver, são problemas diferentes:
    Um prova que as instruçoes estão corretas
    E o outro que executar um programa gera uma saida correta
-/


inductive step : opCode → MachineState → MachineState → Prop
  --
  | rule_exit {s : MachineState} {dst src : Reg} :
    step opCode.exit s s

  | rule_mov_X_32 (s : MachineState) (dst src : Reg) :
    step (opCode.mov_X_32 dst src) s ( incrPc (writeReg s dst (readReg s src)) 1)

  | rule_mov_K_32 {s : MachineState} {dst : Reg} { imm : ℕ } :
    step (opCode.mov_K_32 dst imm) s ( incrPc (writeReg s dst imm) 1)

  --Mudar para chamar uma função que aplica a operação aritmetica?
  | rule_add_X_32 {s : MachineState} {dst src : Reg} :
    step (opCode.add_X_32 dst src) s ( incrPc (writeReg s dst ((readReg s dst) + (readReg s src) )) 1)

  | rule_ldh_X_32 {s s' : MachineState} {dst : Reg} { index : ℕ } :
    readStack s index = v →
    s' = ( incrPc (writeReg s dst v) 1) →
    step (opCode.ldh_X_32 dst index) s s'

  | rule_ldxh_X_32 {s s' : MachineState} {dst : Reg} { index : ℕ } :
    readStack s index = v →
    s' = ( incrPc (writeReg s dst v) 1) →
    step (opCode.ldxh_X_32 dst index) s s'

  | rule_sth_X_32 {s : MachineState} {src : Reg} { index : ℕ}:
    readReg s src = v →
    s' = ( writeStack s index v)  →
    s'' = ( incrPc s' 1) →
    step (opCode.sth_X_32 src index) s s''

  | jgt_true {s : MachineState} {dst src : Reg} {offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = readReg s src →
    (v₁ > v₂) →
    s' = (incrPc s offset) →
    step (opCode.jgt_X_32 dst src offset ) s s'

  | jgt_false {s : MachineState} {dst src : Reg} {offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = readReg s src →
    (v₁ <= v₂) →
    s' = (incrPc s 1) →
    step (opCode.jgt_X_32 dst src offset ) s s'

  | jne_X_true {s : MachineState} {dst src : Reg} {offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = readReg s src →
    (v₁ ≠ v₂) →
    s' = (incrPc s offset) →
    step (opCode.jne_X_32 dst src offset ) s s'

  | jne_X_false {s : MachineState} {dst src : Reg} {offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = readReg s src →
    (v₁ = v₂) →
    s' = (incrPc s 1) →
    step (opCode.jne_X_32 dst src offset ) s s'

  | jne_K_true {s : MachineState} {dst : Reg} {imm offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = imm →
    (v₁ ≠ v₂) →
    s' = (incrPc s offset) →
    step (opCode.jne_K_32 dst imm offset ) s s'

  | jne_K_false {s : MachineState} {dst : Reg} {imm offset : ℕ } :
    v₁ = readReg s dst →
    v₂ = imm →
    (v₁ = v₂) →
    s' = (incrPc s 1) →
    step (opCode.jne_K_32 dst imm offset ) s s'


inductive run (prog : List opCode) :
  MachineState → MachineState → Prop
  | refl {s} :
      run prog s s

  | halt
  {s : MachineState} :
  prog.get? (readPc s) = some opCode.exit →
  run prog s s

  | step
  {s s' s'' : MachineState}
  {instr : opCode} :
  prog.get? (readPc s) = some instr →
  step instr s s' →
  run prog s' s'' →
  run prog s s''



/-

Usar só o step para avaliar as operações como corretas? Yep

Entender como o trabalho de ARM tratou os Jumps

O que entendi:
  O pc começa a fazer parte do estado
    da mesma forma que já está
  A logica trata sobre conjuntos de pc, não só um unico comando
  O jump passa a ser tratado como atribuição ao pc
  Programas tomam a forma de "grafos", não arvores
  O programa é modelado como:
    uma lista de comandos indexados pelo PC
    cada comando possui para qual pc pode ir

  O programa é correto se:
    para cada instrução no PC
    as transições preservarem o estado do Pc destino

  Regra geral:
    Se o estado atual(Memorias) tem um formato valido para o
    pc atual, o estado do pc de destino tambem ira valer,
    já que o jmp apenas altera o pc, o estado não muda

  Provar que isso é correto, é provar que o estado,
  exceto o pc, é o mesmo.

-/
--


/-
Inicio das Regras
Ideia do Jump:
    (∀ s, Inv ℓ s ∧ cond(s) → Inv (ℓ + offset) s)
    ∧
    (∀ s, Inv ℓ s ∧ ¬cond(s) → Inv (ℓ + 1) s)



-/

/-
Quero provar que
∀ estado S as proposicoes a seguir são verdade
  que o pc para um estado s é valido →
  que o valor do destino e > que source →
  que o pc será incrementado pelo offset →

  que o pc para um estado s é valido →
  que o valor do destino é ≤ que source →
  que o pc será incrementado por 1 →

  provar o step, que para um estado s e um s'
  aplicar o jump entre os dois estado
  nos saimos de um estado s valido para o pc
  vamos para um estado s' tambem valido para o pc

  Estou garantindo que o PC só muda o estado?


Se estamos em um PC Σ e:
  se a condição for verdadeira,
    o estado vai para Σ + offset
    se for falsa, vai para Σ + 1
  logo:
    Inv Σ deve implicar Inv (Σ + offset),
      no caso verdadeiro
    Inv Σ deve implicar Inv (Σ + 1),
      no caso falso

-/
theorem jgt_intro
  {Inv : pc → MachineState → Prop}
  {dst src : Reg} {offset : Nat} :
  (∀ s,
      Inv (readPc s) s →
      (readReg s dst) > (readReg s src) →
      Inv (readPc s + offset) (incrPc s offset)) →
  (∀ s,
      Inv (readPc s) s →
      readReg s dst ≤ readReg s src →
      Inv (readPc s + 1) (incrPc s 1)) →
  ∀ s s',
    step (opCode.jgt_X_32 dst src offset) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hTrue hFalse s s' hstep hInv
  cases hstep with
  | jgt_true readA readB hgt hpc =>
      subst readA
      subst readB
      simpa [hpc] using hTrue s hInv hgt
  | jgt_false readA readB hle hpc =>
      subst readA
      subst readB
      simpa [hpc] using hFalse s hInv hle

theorem mov_X_intro
  {Inv : pc → MachineState → Prop}
  {dst src : Reg} :
  (∀ s,
      Inv (readPc s) s →
      Inv (readPc s + 1)
          (incrPc (writeReg s dst (readReg s src)) 1)) →
  ∀ s s',
    step (opCode.mov_X_32 dst src) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hInvStep s s' hstep hInv
  cases hstep
  apply hInvStep
  exact hInv

theorem mov_K_intro
  {Inv : pc → MachineState → Prop}
  {dst : Reg} {imm : ℕ }  :
  (∀ s,
      Inv (readPc s) s →
      Inv (readPc s + 1)
          (incrPc (writeReg s dst imm) 1)) →
  ∀ s s',
    step (opCode.mov_K_32 dst imm) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hInvStep s s' hstep hInv
  cases hstep
  apply hInvStep
  exact hInv

theorem ldxh_X_intro
  {Inv : pc → MachineState → Prop}
  {dst : Reg} {index : Nat} :
  (∀ s v,
      Inv (readPc s) s →
      readStack s index = v →
      Inv (readPc s + 1)
          (incrPc (writeReg s dst v) 1)) →
  ∀ s s',
    step (opCode.ldxh_X_32 dst index) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hInvStep s s' hstep hInv
  cases hstep with
  | rule_ldxh_X_32 hload hpc =>
      subst hpc
      simpa using hInvStep s _ hInv hload


theorem jne_X_intro
  {Inv : pc → MachineState → Prop}
  {dst src : Reg} {offset : Nat} :
  (∀ s,
      Inv (readPc s) s →
      (readReg s dst) ≠ (readReg s src) →
      Inv (readPc s + offset) (incrPc s offset)) →
  (∀ s,
      Inv (readPc s) s →
      readReg s dst = readReg s src →
      Inv (readPc s + 1) (incrPc s 1)) →
  ∀ s s',
    step (opCode.jne_X_32 dst src offset) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hTrue hFalse s s' hstep hInv
  cases hstep with
  | jne_X_true readA readB hgt hpc =>
      subst readA
      subst readB
      simpa [hpc] using hTrue s hInv hgt
  | jne_X_false readA readB hle hpc =>
      subst readA
      subst readB
      simpa [hpc] using hFalse s hInv hle

theorem jne_K_intro
  {Inv : pc → MachineState → Prop}
  {dst : Reg} {imm : ℕ } {offset : Nat} :
  (∀ s,
      Inv (readPc s) s →
      (readReg s dst) ≠ imm →
      Inv (readPc s + offset) (incrPc s offset)) →
  (∀ s,
      Inv (readPc s) s →
      readReg s dst = imm →
      Inv (readPc s + 1) (incrPc s 1)) →
  ∀ s s',
    step (opCode.jne_K_32 dst imm offset) s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hTrue hFalse s s' hstep hInv
  cases hstep with
  | jne_K_true readA readB hgt hpc =>
      subst readA
      subst readB
      simpa [hpc] using hTrue s hInv hgt
  | jne_K_false readA readB hle hpc =>
      subst readA
      subst readB
      simpa [hpc] using hFalse s hInv hle

theorem exit_intro
  {Inv : pc → MachineState → Prop} :
  (∀ s,
      Inv (readPc s) s →
      Inv (readPc s) s) →
  ∀ s s',
    step opCode.exit s s' →
    Inv (readPc s) s →
    Inv (readPc s') s' := by
  intro hInvStep s s' hstep hInv
  cases hstep
  simpa using hInvStep s hInv


def InvIpv4 (pc : Nat) (s : MachineState) : Prop :=
match pc with
| 0 => True
| 1 =>
    readReg s Reg.r1 = readStack s 12
    --O valor de R1 tem que ser o da pilha indice 12
| 2 =>
    readReg s Reg.r1 = readStack s 12 ∧
    readReg s Reg.r0 = 1
    -- ++
    -- O valor de R0 tem que ser 1
| 3 =>
    readReg s Reg.r1 ≠ 8 ∧
    readReg s Reg.r0 = 1
    -- O valor de R1 tem que ser diff de 8
    -- o valor de R0 tem que ser 1
| 4 =>
    readReg s Reg.r1 = 8
    -- O valor de R1 tem que ser 8
| 5 =>
    readReg s Reg.r0 = 0
    -- O valor de R0 tem que ser 0
| _ => True

def progIpv4 : List opCode :=
[
  opCode.ldxh_X_32 Reg.r1 12,
  opCode.mov_K_32 Reg.r0 1,
  opCode.jne_K_32 Reg.r1 8 1,
  opCode.exit,
  opCode.mov_K_32 Reg.r0 0,
  opCode.exit
]

lemma inv_pc0 (s : MachineState) :
  InvIpv4 0 s := by
  trivial

lemma step_preserves_inv
  {prog : List opCode}
  {s s' : MachineState}
  {instr : opCode} :
  prog.get? (readPc s) = some instr →
  step instr s s' →
  InvIpv4 (readPc s) s →
  InvIpv4 (readPc s') s' := by
  --intros s s'
  intros instr hstep hInv
  sorry
--@[]
lemma step_inv :
∀ s s' instr,
step instr s s' →
InvIpv4 (readPc s) s →
InvIpv4 (readPc s') s' := by
  intro s s' instr hstep hInv
  cases hstep with
    | rule_mov_X_32 s src dst =>
      simp [readPc,writeReg,incrPc,readReg,updateRegs]
      cases s
      simp
      simp [InvIpv4]
      split <;> aesop
      sorry
    | rule_mov_K_32 =>
      sorry
    | rule_add_X_32 =>
      sorry
    | rule_exit =>
      sorry
    | rule_ldh_X_32 =>
      sorry
    | rule_ldxh_X_32 =>
      sorry
    | jne_X_false =>
      sorry
    | jne_X_true =>
      sorry
    | jne_K_false =>
      sorry
    | jne_K_true =>
      sorry
    | rule_sth_X_32 =>
      sorry
    | jgt_false =>
      sorry
    | jgt_true =>
      sorry


theorem run_preserves_inv :
∀ s s',
run progIpv4 s s' →
InvIpv4 (readPc s) s →
InvIpv4 (readPc s') s' := by
  intro s s' hrun
  induction hrun with
  | halt =>
      intro hInv
      exact hInv
  | refl =>
      intro hInv
      assumption
  | step hfetch hstep _hrun ih =>
      intro hInv
      apply ih
      apply step_preserves_inv hfetch hstep hInv


theorem prog_result :
∀ s s',
run progIpv4 s s' →
InvIpv4 (readPc s) s →
InvIpv4 (readPc s') s' := by
  intro s s' hrun
  induction hrun with
  | refl =>
      intro hInv
      exact hInv
  | halt s =>
      intro hInv
      assumption
  | step hfetch hstep hrun ih =>
      intro hInv
      cases hstep with
      | rule_ldxh_X_32 =>
        apply ih
        apply ldxh_X_intro
        exact hInv
      | rule_mov_K_32 =>
        apply ih
        apply mov_K_intro
        exact hInv
      | jne_K_false =>
        apply ih
        apply jne_K_intro
        exact hInv
      | jne_K_true =>
        apply ih
        apply jne_K_intro
        exact hInv
      | rule_exit =>
        apply ih
        assumption


      -- aqui entra sua lógica de Hoare
      -- usando as regras mov_intro, jne_intro etc
/-
PC 0: ldxh  r1, [12]
PC 1: mov32 r0, 1
PC 2: jne   r1, 0x0008, +1
PC 3: exit
PC 4: mov32 r0, 0
PC 5: exit

          r1 != 8
            ↓
PC0 → PC1 → PC2 → PC3(exit)
            ↑
          r1 == 8
            ↓
           PC4 → PC5(exit)
-/


/-
Implementar operaçoes programa only_IPV4
Avaliar Programa

def prog_only_IPV4 : TestEval :=
{exe|

asm
ldxh %r1, [12]
mov32 %r0, 1
jne %r1, 0x0008, 1
exit
mov32 %r0, 0
exit
result
0x1
}
-/


/-
Escrever regras Hoare Artigo
Latex
GitHub
-/
