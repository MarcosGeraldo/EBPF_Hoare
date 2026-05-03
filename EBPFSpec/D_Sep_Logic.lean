import EBPFSpec.C_Semantic_Step


set_option quotPrecheck false


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

def emp : Assert :=
  fun s => ∀ index, s.[index] = none

def points_To ( index v : ℕ ) : Assert :=
  fun s => s.[index] = some v -- ∧ ∀ index', s.[index'] = none

def Sep_Conj (P Q : Assert) : Assert :=
  fun s => ∃ s1 s2, State_disjoint s1 s2 ∧
  s = State_union s1 s2 ∧
  P s1 ∧
  Q s2

def Magic_Wand (P Q : Assert) : Assert :=
  fun s => ∀ h , Stack_disjoint (s:Heap) h →
  P ( s:Regs , h ) ∧
  Q ( s:Regs , Stack_union (s:Heap) h)

def pure (p : Prop) : Assert :=
  fun s => p ∧ ∀ a, (s:Heap) a = none

def ex (α : Type) (P : α → Assert): Assert :=
  fun s => ∃ x, P x s

def entailment (P Q : Assert) : Prop :=
  ∀ s, P s → Q s

def and_State (P Q : Assert) : Assert :=
  fun s => P s ∧ Q s

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
/-
  | seq {prog : List opCode}
    {pc pc' : ℕ}
    {P R Q : Assert}
    (h1 : Triple P prog pc R)
    (h2 : Triple R prog pc' Q) :
    Triple P prog pc Q
-/
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

  | false_pre {prog : List opCode} {pc : PC} {Q : Assert} :
      Triple (fun _ => False) prog pc Q

  | mov_K {prog : List opCode} {pc : PC} {P Q : Assert} {dst : Reg} {imm : ℕ}
      (hfetch : prog.get? pc = some (opCode.mov_K dst imm))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => P (s.[dst ↦ imm])) prog pc Q

  | mov_X {prog : List opCode} {pc : PC} {P Q : Assert} {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.mov_X dst src))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple ( fun s' => P ( s'.[dst ↦ s'.(src) ] )) prog pc Q

  | add_K {prog : List opCode} {pc : PC} {P Q : Assert} {dst : Reg} {imm : ℕ}
    (hfetch : prog.get? pc = some (opCode.add_K dst imm))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple ( fun s' => P ( s'.[dst ↦ ( s'.(dst) + imm ) ] )) prog pc Q

  | add_X {prog : List opCode} {pc : PC} {P Q : Assert} {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.add_X dst src))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple ( fun s' => P ( s'.[dst ↦ ( s'.(dst) + s'.(src) ) ] )) prog pc Q

  | and_K {prog : List opCode} {pc : PC} {P Q : Assert} {dst : Reg} {imm : ℕ}
    (hfetch : prog.get? pc = some (opCode.and_K dst imm))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple ( fun s' => P ( s'.[dst ↦ ( s'.(dst) &&& imm ) ] )) prog pc Q

  | and_X {prog : List opCode} {pc : PC} {P Q : Assert} {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.and_X dst src))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple ( fun s' => P ( s'.[dst ↦ ( s'.(dst) &&& s'.(src) ) ] )) prog pc Q

  | ldh_X {prog : List opCode} {pc : ℕ} {P Q : Assert} {index : ℕ} {src dst : Reg}
    (hfetch : prog.get? pc = some (opCode.ldh_X dst src index))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple (fun s => ∃ val, s.[index + s.(src)] = some val ∧ P ( s.[dst ↦ val] )) prog pc Q

  | sth_X {prog : List opCode} {pc : ℕ} {P Q : Assert} {index : ℕ} {src : Reg}
    (hfetch : prog.get? pc = some (opCode.sth_X src index))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple (fun s => P ( s.[index]:= s.(src) )) prog pc Q

  | sth_K {prog : List opCode} {pc : ℕ} {P Q : Assert} {index imm : ℕ}
    (hfetch : prog.get? pc = some (opCode.sth_K imm index))
    (h_rest : Triple P prog (pc + 1) Q) :
    Triple (fun s => P ( s.[index]:= imm )) prog pc Q



  | jne_X_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_X dst src offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) ≠ s.(src) ∧ P s) prog pc Q

  | jne_X_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_X dst src offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) = s.(src) ∧ P s) prog pc Q

  | jne_K_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_K dst imm offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) ≠ imm ∧ P s) prog pc Q

  | jne_K_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jne_K dst imm offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) = imm ∧ P s) prog pc Q

  | jeq_X_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_X dst src offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) = s.(src) ∧ P s) prog pc Q

  | jeq_X_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_X dst src offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) ≠ s.(src) ∧ P s) prog pc Q

  | jeq_K_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_K dst imm offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) = imm ∧ P s) prog pc Q

  | jeq_K_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jeq_K dst imm offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) ≠ imm ∧ P s) prog pc Q

  | jset_X_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_X dst src offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => (s.(dst) &&& s.(src) ≠ 0) ∧ P s) prog pc Q

  | jset_X_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_X dst src offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => (s.(dst) &&& s.(src) = 0) ∧ P s) prog pc Q

  | jset_K_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_K dst imm offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => (s.(dst) &&& imm ≠ 0) ∧ P s) prog pc Q

  | jset_K_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jset_K dst imm offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => (s.(dst) &&& imm = 0) ∧ P s) prog pc Q

  | jgt_X_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_X dst src offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) > s.(src) ∧ P s) prog pc Q

  | jgt_X_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst src : Reg} {offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_X dst src offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) ≤ s.(src) ∧ P s) prog pc Q

  | jgt_K_true {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_K dst imm offset))
      (h_jump : Triple P prog (pc + offset + 1) Q) :
      Triple (fun s => s.(dst) > imm ∧ P s) prog pc Q

  | jgt_K_false {prog : List opCode} {pc : ℕ} {P Q : Assert} {dst : Reg} {imm offset : ℕ}
      (hfetch : prog.get? pc = some (opCode.jgt_K dst imm offset))
      (h_rest : Triple P prog (pc + 1) Q) :
      Triple (fun s => s.(dst) ≤ imm ∧ P s) prog pc Q

  | halt {prog : List opCode} {pc : ℕ} {Q : Assert}
       (hfetch : prog.get? pc = none) :
        Triple Q prog pc Q


notation:25 "⦃" P "⦄" prog:arg "@" pc:arg "⦃" Q "⦄" => Triple P prog pc Q
