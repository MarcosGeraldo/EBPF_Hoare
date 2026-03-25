import EBPFSpec.Semantic_Step

-- Make the separationlogic here


set_option quotPrecheck false


-- Um Assertiva é uma declaração sobre um estado
-- uma função do tipo, Estado -> Prop
abbrev Assert := MachineState → Prop

namespace Assert

def State_disjoint (s₁ s₂ : MachineState) : Prop :=
  ∀ a, s₁.[a] = none ∨ s₂.[a] = none

def Stack_disjoint (s₁ s₂ : StackState) : Prop :=
  ∀ a, s₁.[a] = none ∨ s₂.[a] = none

def Stack_union (s₁ s₂ : StackState) : StackState :=
 fun a => (s₁.[a]).orElse (fun _ => s₂.[a])

def State_union (s₁ s₂ : MachineState) : MachineState :=
  match s₁,s₂ with
  | ( r₁ , h₁),( _, h₂) =>
    (r₁, fun a => (h₁.[a]).orElse (fun _ => h₂.[a]))

-- Que o estado está vazio
def emp : Assert :=
  fun s => ∀ index, s.[index] = none

-- Que o valor V está presente na posição index
-- ∧ e a estado não tem mais nenhum valor
def points_To ( index v : ℕ ) : Assert :=
  fun s => s.[index] = some v -- ∧ ∀ index', s.[index'] = none

-- Ajustar tambem a união do Pc e dos registradores
-- Divide a estado em duas partes para satisfazer P e Q
def Sep_Conj (P Q : Assert) : Assert :=
  fun s => ∃ s1 s2, State_disjoint s1 s2 ∧
  s = State_union s1 s2 ∧
  P s1 ∧
  Q s2

-- Qualquer estado que satisfaça P
-- e não esteja em Q, pode ser adicionado a ele
def Magic_Wand (P Q : Assert) : Assert :=
  fun s => ∀ h , Stack_disjoint (s:Heap) h →
  P ( s:Regs , h ) ∧
  Q ( s:Regs , Stack_union (s:Heap) h)

-- Uma especie de Filter só que verificando que a pilha esta vazia
def pure (p : Prop) : Assert :=
  fun s => p ∧ ∀ a, (s:Heap) a = none

-- ???????????
def ex (α : Type) (P : α → Assert): Assert :=
  fun s => ∃ x, P x s

-- O estado satisfaz P, logo satisfaz Q
def entailment (P Q : Assert) : Prop :=
  ∀ s, P s → Q s

-- O estado satisfaz P e satisfaz Q
def and_State (P Q : Assert) : Assert :=
  fun s => P s ∧ Q s

-- A atualização do registrador deve satisfazer P
def update_Register (P : Assert) (r: Reg) (v : ℕ ) : Assert :=
  fun s => P ( s.[r ↦ v] )

end Assert


notation:50 a " ↦ₐ "  v => Assert.points_To a v
notation:35 P " ∗ "  Q => Assert.Sep_Conj P Q
notation:25 P " -∗ " Q => Assert.Magic_Wand P Q
notation:50 P " ⊢ₐ " Q => Assert.entailment P Q
notation:50 P "[" r "↦ᵣ" v "]" => Assert.update_Register P r v
notation:35 P " ∧ₛ " Q => Assert.and_State P Q

inductive Triple : Assert → List opCode → PC → Assert → Prop where
  | consequence
    {prog : List opCode}
    {pc : PC}
    {P P' Q Q' : Assert}
    (hP    : P' ⊢ₐ P)
    (hcore : Triple P prog pc Q)
    (hQ    : Q ⊢ₐ Q') :
    Triple P' prog pc Q'

  | frame
    {prog : List opCode}
    {pc : PC}
    {P Q R : Assert}
    (hcore : Triple P prog pc Q) :
    Triple (P ∗ R) prog pc (Q ∗ R)

  | seq {prog : List opCode}
    {pc pc' : ℕ}
    {P R Q : Assert}
    (h1 : Triple P prog pc R)
    (h2 : Triple R prog pc' Q) :
    Triple P prog pc Q

  | disj {prog : List opCode}
    {pc : PC}
    {P₁ P₂ Q : Assert}
    (h1 : Triple P₁ prog pc Q)
    (h2 : Triple P₂ prog pc Q) :
    Triple (fun s => P₁ s ∨ P₂ s) prog pc Q

  | exit {prog : List opCode}
    {pc : ℕ}
    {Q : Assert}
    (hfetch : prog.get? pc = some (opCode.exit)) :
         Triple Q prog pc Q

  | mov_K_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    {dst : Reg}
    {imm : ℕ}
    (hfetch : prog.get? pc = some (opCode.mov_K_32 dst imm)) :
    Triple (fun s => P ( s.[dst↦ imm ] )) prog pc P

  | mov_X_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.mov_X_32 dst src)) :
    Triple ( fun s' => P ( s'.[dst↦ s'.(src) ] )) prog pc P

  | add_K_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    { dst : Reg}
    { imm : ℕ }
    (hfetch : prog.get? pc = some (opCode.add_K_32 dst imm)) :
    Triple ( fun s' => P ( s'.[dst↦ ( s'.(dst) + imm )  ] )) prog pc P

  | add_X_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.add_X_32 dst src)) :
    Triple ( fun s' => P ( s'.[dst↦ ( s'.(dst) + s'.(src) )  ] )) prog pc P

  | and_K_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    { dst : Reg}
    { imm : ℕ }
    (hfetch : prog.get? pc = some (opCode.and_K_32 dst imm)) :
    Triple ( fun s' => P ( s'.[dst↦ ( s'.(dst) &&& imm )  ] )) prog pc P

  | and_X_32 {prog : List opCode}
    {pc : PC}
    {P : Assert}
    {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.and_X_32 dst src)) :
    Triple ( fun s' => P ( s'.[dst↦ ( s'.(dst) &&& s'.(src) )  ] )) prog pc P

  /-| ldh_K_32 {prog : List opCode}
    {pc : ℕ}
    {P : Assert}
    {imm index : ℕ }
    (hfetch : prog.get? pc = some (opCode.ldh_K_32 imm index)) :
    Triple (fun s => ∃ val, s.mem (s.regs addr) = some val ∧
                          P (State.updateReg s dst val)) prog pc P
-/
  | ldh_X_32 {prog : List opCode}
    {pc : ℕ}
    {P : Assert}
    {index : ℕ }
    {dst : Reg}
    (hfetch : prog.get? pc = some (opCode.ldh_X_32 dst src index)) :
    Triple (fun s => ∃ val, s.[index + s.(src)] = some val ∧
                          P ( s.[dst ↦ val] )) prog pc P

  | ldxh_X_32 {prog : List opCode}
    {pc : ℕ}
    {P : Assert}
    {index : ℕ }
    {dst : Reg}
    (hfetch : prog.get? pc = some (opCode.ldxh_X_32 dst index)) :
    Triple (fun s => ∃ val, s.[index] = some val ∧
                          P ( s.[dst ↦ val] )) prog pc P

  | sth_X_32 {prog : List opCode}
    {pc : ℕ}
    {P : Assert}
    {index : ℕ }
    {src : Reg}
    (hfetch : prog.get? pc = some (opCode.sth_X_32 src index)) :
    Triple (fun s => --∃ old, s.[index] = some old ∧
                          P ( s.[index]:= s.(src) )) prog pc P

  | sth_K_32 {prog : List opCode}
    {pc : ℕ}
    {P : Assert}
    {index imm : ℕ }
    (hfetch : prog.get? pc = some (opCode.sth_K_32 imm index)) :
    Triple (fun s => --∃ old i, (s.[index]:= s.(src)).[i] = some old ∧
                          P ( s.[index]:= imm )) prog pc P

  | jne_X_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_X_32 dst src offset)) :
      Triple (fun s => s.(dst) ≠ s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jne_X_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_X_32 dst src offset)) :
      Triple (fun s => s.(dst) = s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jne_K_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) ≠ imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jne_K_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) = imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jeq_X_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_X_32 dst src offset)) :
      Triple (fun s => s.(dst) = s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jeq_X_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_X_32 dst src offset)) :
      Triple (fun s => s.(dst) ≠ s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jeq_K_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) = imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jeq_K_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) ≠ imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jset_X_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_X_32 dst src offset)) :
      Triple (fun s => (s.(dst) &&& s.(src) ≠ 0) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jset_X_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_X_32 dst src offset)) :
      Triple (fun s => (s.(dst) &&& s.(src) = 0) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_X_32 dst src offset) ∧ P s) prog pc P

  | jset_K_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_K_32 dst imm offset)) :
      Triple (fun s => (s.(dst) &&& imm ≠ 0) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jset_K_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_K_32 dst imm offset)) :
      Triple (fun s => (s.(dst) &&& imm = 0) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jne_K_32 dst imm offset) ∧ P s) prog pc P

  | jgt_X_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_X_32 dst src offset)) :
      Triple (fun s => s.(dst) > s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jgt_X_32 dst src offset) = true ∧ P s) prog pc P

  | jgt_X_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst src : Reg}
      {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_X_32 dst src offset)) :
      Triple (fun s => s.(dst) ≤ s.(src) ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jgt_X_32 dst src offset) = false ∧ P s) prog pc P

  | jgt_K_32_true {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) > imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jgt_K_32 dst imm offset) ∧ P s) prog pc P

  | jgt_K_32_false {prog : List opCode}
      {pc : ℕ}
      {P : Assert}
      {dst : Reg}
      {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_K_32 dst imm offset)) :
      Triple (fun s => s.(dst) ≤ imm ∧ P s) prog pc P
      --Triple (fun s => evalJMP s (opCode.jgt_K_32 dst imm offset) ∧ P s) prog pc P

  | halt {prog : List opCode}
       {pc : ℕ}
       {Q : Assert}
       (hfetch : prog.get? pc = none) :
        Triple Q prog pc Q

notation:25 "⦃" P "⦄" prog:arg "@" pc:arg "⦃" Q "⦄" => Triple P prog pc Q
