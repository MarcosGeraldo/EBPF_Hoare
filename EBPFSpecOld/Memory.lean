import Mathlib.Data.Nat.Defs

-------------------------------------------------
------------------ Registers ----------------------
-------------------------------------------------

inductive Reg where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r_
deriving Repr, DecidableEq

def RegsState := Reg → ℕ

@[simp]
def updateRegs (s : RegsState) (x : Reg) (n : ℕ) : RegsState :=
  fun y => if y = x then n else s y

-------------------------------------------------
------------------ Stack ----------------------
-------------------------------------------------

def StackState := Fin 512 → Option ℕ

@[simp]
theorem provaFin (index : Nat) : index % 512 < 512 := by
  have h : index % 512 < 512 := Nat.mod_lt index (by decide)
  exact h

@[simp]
def updateStack (s : StackState) (addr : ℕ ) (n : ℕ ) : StackState :=
  fun i => if i = ⟨ addr % 512, provaFin addr ⟩ then n else s ⟨ addr % 512, provaFin addr ⟩

@[simp]
def readStackNat ( s : StackState) ( i : ℕ ) : Option ℕ :=
  s (⟨ i % 512, provaFin i ⟩)


-------------------------------------------------
------------------ State ----------------------
-------------------------------------------------


abbrev PC := ℕ

def MachineState := (RegsState × StackState)

------------------------------------------------------------
-------------------- Functions -----------------------------
------------------------------------------------------------

-- Escrita e leitura dos registradores
@[simp]
def readReg (s : MachineState) (r : Reg) : ℕ :=
  match r with
  | .r_ => 0
  | _ =>
    match s with
    | (s_Reg , _ ) => s_Reg r

@[simp]
def writeReg (s : MachineState) (r : Reg) (n : ℕ ) : MachineState :=
  match s with
  | (s_Reg , s_Stack) => (updateRegs s_Reg r n,s_Stack)

-- Escrita e leitura da pilha
@[simp]
def readStack (s : MachineState) (index : ℕ ) : Option ℕ :=
  match s with
  | (_ , s_Stack) => readStackNat s_Stack index

@[simp]
def writeStack (s : MachineState) (index : ℕ ) (n : ℕ ) : MachineState :=
  match s with
  | (s_Reg , s_Stack) => ( s_Reg, updateStack s_Stack index n)

@[simp]
def getStack (s : MachineState) : StackState :=
  match s with
  | (_,stack ) => stack

@[simp]
def getRegs (s : MachineState) : RegsState :=
  match s with
  | (regs,_ ) => regs

------------------------------------------------------------
-------------------- Macros -----------------------------
------------------------------------------------------------

-- Macro para escrita e leitura da pilha
macro s:term ".[" index:term "]:=" val:term : term =>
  `(writeStack $s $index $val)
macro s:term ".[" index:term "]" : term =>
  `(readStack $s $index )
macro s:term ".[" index:term "]" : term =>
  `(readStackNat $s $index )
macro s:term ":Heap" : term =>
  `(getStack $s )
-- s.[i]:= 10
-- s.[i]

-- Macro para escrita e leitura do registrador
macro s:term ".[" reg:term "↦" val:term "]" : term =>
  `(writeReg $s $reg $val)
macro s:term ".(" reg:term ")" : term =>
  `(readReg $s $reg )
macro s:term ":Regs" : term =>
  `(getRegs $s )
-- s.[ Reg.r0 ↦ 10]
-- s.(r0)
