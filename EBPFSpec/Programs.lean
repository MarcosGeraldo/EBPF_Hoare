import EBPFSpec.Ver_Cond_Gen_Sound


def incrMem : Code :=
  [ .ldh_X .r2 .r_ 0
  , .mov_K .r3 1
  , .add_X Reg.r2 Reg.r3
  , .sth_X Reg.r2 0
  , .exit
  ]

theorem incrMem_correct (v : ℕ) :
    ⦃ fun s => s.[0] = some v ⦄
    incrMem @ 0
    ⦃ fun s => s.[0] = some (v + 1) ⦄ := by
  apply Triple.consequence
    (P := blockWP incrMem (fun s => s.[0] = some (v + 1)))
  · -- Show user precondition implies blockWP
    intro s h1
    simp [blockWP]
    simp [incrMem]
    simp [wp]
    rcases s
    . simp
      exact h1
    -- Core triple from blockWP_sound
  .
    exact blockWP_sound incrMem incrMem 0 _ (fun k => by simp)
  · -- Postcondition is trivially implied
    intro s hs; exact hs

def test_add : Code :=
  [ .mov_K (Reg.r1) 1
  , .mov_K (Reg.r2) 2
  , .add_X Reg.r2 Reg.r1
  , .exit
  ]

theorem test_add_correct :
    ⦃ fun _ => True ⦄
    test_add @ 0
    ⦃ fun s => s.(.r2) = 3  ⦄ := by
  apply Triple.consequence
    (P := blockWP test_add (fun s => s.(.r2) = 3))
  · -- Show user precondition implies blockWP
    intro s _h1
    simp [blockWP,List.foldr,
    wp,updateRegs]
    rcases s
    . simp
  · -- Core triple from blockWP_sound
    exact blockWP_sound test_add test_add 0 _ (fun k => by simp)
  · -- Postcondition is trivially implied
    intro s hs; exact hs

theorem test_add_correct_VCG :
    ⦃ fun _ => True ⦄
    test_add @ 0
    ⦃ fun s => s.(.r2) = 3  ⦄ := by
    apply vcg_sound 10 test_add (fun _ => True) (fun s => s.(.r2) = 3) (fun _ => none)

    ·
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
      .
        simp [List.get?,vcg] at h

    . simp

def test_exit : Code :=
  [ .mov_K (Reg.r0) 1
  , .exit
  , .mov_K (Reg.r0) 0
  , .exit
  ]

theorem test_exit_correct :
    ⦃ fun _ => True ⦄
    test_exit @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
  -- Utiliza o VCG Soundness em vez de blockWP, definindo um limite de recursão (fuel)
    apply vcg_sound 10 test_exit (fun _ => True) (fun s => s.(.r0) = 1) (fun _ => none)

    · -- Show user precondition implies blockWP
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
      .
        simp [List.get?,vcg] at h

    . simp


def test_JMP : Code :=
  [ .mov_K (Reg.r0) 1
  , .mov_K (Reg.r1) 5
  , .mov_K (Reg.r2) 6
  , .jne_X .r1 .r2 1
  , .mov_K (Reg.r0) 0
  , .exit
  ]


theorem test_JMP_correct_VCG :
    ⦃ fun _ => True ⦄
    test_JMP @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
  -- Utiliza o VCG Soundness em vez de blockWP, definindo um limite de recursão (fuel)
    apply vcg_sound 10 test_JMP (fun _ => True) (fun s => s.(.r0) = 1) (fun _ => none)

    · -- Show user precondition implies blockWP
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
      .
        simp [List.get?,vcg] at h

    . simp

-- A == .r1
-- X == .r2
-- .r0 == Flag

/-
  A == .r1
  X == .r2
  .r0 == Flag

  Only allow ARP packets:

  ldh [12]
  jne #0x806, drop
  ret #-1
  drop: ret #0
  -/

def prog_only_arp : Code :=
  [ .ldh_X .r1 .r_ 12
  , .mov_K .r0 1
  , .jne_K .r1 0x0806 1
  , .exit
  , .mov_K .r0 0
  , .exit
  ]

theorem prog_only_arp_correct_VCG :
    ⦃ fun s => s.[12] = some 0x0806 ⦄
    prog_only_arp @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
    apply vcg_sound 100 prog_only_arp
      (fun s => s.[12] = some 0x0806)
      (fun s => s.(.r0) = 1) (fun _ => none)
    ·
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
      .
        simp [List.get?,vcg] at h
    . simp

/-
  A == .r1
  X == .r2
  .r0 == Flag
  Only allow IPv4 TCP packets:

  ldh [12]
  jne #0x800, drop
  ldb [23]
  jneq #6, drop
  ret #-1
  drop: ret #0
-/
def prog_only_Ipv4_TCP : Code :=
  [
    .ldh_X .r1 .r_ 12
  , .jne_K .r1 0x0800 4
  , .ldh_X .r1 .r_ 23
  , .jne_K .r1 0x06 2
  , .mov_K .r0 1 --pass
  , .exit
  , .mov_K .r0 0 --drop
  , .exit
  ]

theorem prog_only_Ipv4_correct_VCG :
    ⦃ fun s => s.[12] = some 0x0800 ∧ s.[23] = some 0x06 ⦄
    prog_only_Ipv4_TCP @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
    apply vcg_sound 100 prog_only_Ipv4_TCP
      (fun s => s.[12] = some 0x0800 ∧ s.[23] = some 0x06)
      (fun s => s.(.r0) = 1) (fun _ => none)
    ·
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
        intros v₁ v₂
        simp [v₁]
        simp [v₂]
      .
        simp [List.get?,vcg] at h
    . simp

/-
'0' '0' '0' '0' 'c' '0' '9' 'f' 'a' '0' '9' '7' '0' '0' 'a' '0' 0-7
'c' 'c' '3' 'b' 'b' 'f' 'f' 'a' '0' '8' '0' '0' '4' '5' '1' '0' 8-15
'0' '0' '3' 'c' '4' '6' '3' 'c' '4' '0' '0' '0' '4' '0' '0' '6' 16-23
'7' '3' '1' 'c' 'c' '0' 'a' '8' '0' '1' '0' '2' 'c' '0' 'a' '8' 24-31
'0' '1' '0' '1' '0' '6' '0' 'e' '0' '0' '1' '7' '9' '9' 'c' '5'
'a' '0' 'e' 'c' '0' '0' '0' '0' '0' '0' '0' '0' 'a' '0' '0' '2'
'7' 'd' '7' '8' 'e' '0' 'a' '3' '0' '0' '0' '0' '0' '2' '0' '4'
'0' '5' 'b' '4' '0' '4' '0' '2' '0' '8' '0' 'a' '0' '0' '9' 'c'
'2' '7' '2' '4' '0' '0' '0' '0' '0' '0' '0' '0' '0' '1' '0' '3'
'0' '3' '0' '0'

subnet : Code :=[
  .mov %r2, 0xe
  ,.ldxh %r3, [%r1+12] s.[0+12] == 0x0800
  ,.jne %r3, 0x81, 3
  ,.mov %r2, 0x12
  ,.ldxh %r3, [%r1+16] s.[0+12] == 0x003c
  ,.and %r3, 0xffff
  ,.jne %r3, 0x8, 5
  ,.add %r1, %r2
  ,.mov %r0, 0x1
  ,.ldxw %r1, [%r1+16] s.[14+16] == 0xc0a80101
  ,.and %r1, 0xffffff
  ,.jeq %r1, 0x1a8c0, exit
  ,.mov %r0, 0x0
  ,.exit
]
-/

def prog_subnet : Code :=
  [
  .mov_K .r1  0x0
  ,.mov_K .r2  0xe
  ,.ldh_X .r3 .r1 12
  ,.jne_K .r3  0x81 4
  ,.mov_K .r2 0x12
  ,.ldh_X .r3 .r1 16
  ,.and_K .r3  0xffff
  ,.jne_K .r3  0x8  6
  ,.add_X .r1  .r2
  ,.mov_K .r0 0x1
  ,.ldh_X .r1  .r1 16
  ,.and_K .r1  0xffffff
  ,.jeq_K .r1  0x1a8c0 2
  ,.mov_K .r0  0x0
  ,.exit
  ]

-- {1,2,3,4,5,6,7,8}
-- Ldxh[0] == 1,2,3,4
-- Ldxw[0] == 1,2,3,4,5,6,7,8

theorem prog_subnet_correct_VCG :
    ⦃ fun s =>
    s.[12] = some 0x0008
    ∧ s.[16] = some 0x3c00
    ∧ s.[30] = some 0x0101a8c0
    ⦄
    prog_subnet @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
    apply vcg_sound 100 prog_subnet
      ( fun s =>
        s.[12] = some 0x0008
        ∧ s.[16] = some 0x3c00
        ∧ s.[30] = some 0x0101a8c0)
      (fun s => s.(.r0) = 1) (fun _ => none)
    ·
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
        intros v₁ v₂ v₃
        simp [v₁,v₂,v₃]
        decide
      .
        simp [List.get?,vcg] at h
    . simp
/-
  A == .r1
  X == .r2
  .r0 == Flag
  Only allow IPv4 TCP SSH traffic:
         ldh [12]
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ldh [20]
         jset #0x1fff, drop
         ldxb 4 * ([14] & 0xf)
         ldh [x + 14]
         jeq #0x16, pass
         ldh [x + 16]
         jne #0x16, drop
         pass: ret #-1
         drop: ret #0
-/

def prog_only_IPv4_TCP_SSH : Code :=
  [ .ldh_X .r1 .r_ 12
  , .jne_K .r1 0x08 11 -- drop
  , .ldh_X .r1 .r_ 23
  , .jne_K .r1 0x06 9 -- drop
  , .ldh_X .r1 .r_ 20
  , .jset_K .r1 0x1fff 7 -- drop
--  , .ldxh_X .r2 14 -- ldxb 4 bits menos ignificativos
  , .mov_K .r2 20  -- PC 6: SIMULAÇÃO: tamanho do IP Header (IHL * 4 = 20)  , .ldh_X .r1 .r2 14 --[.r2 + index]
  , .ldh_X .r1 .r2 14 --[.r2 + index]
  , .jeq_K .r1 0x16 2 -- pass
  , .ldh_X .r1 .r2 16 --[.r2 + index]
  , .jne_K .r1 0x16 2 -- drop
  , .mov_K .r0 1 --pass
  , .exit
  , .mov_K .r0 0 --drop
  , .exit
  ]


theorem prog_only_IPv4_TCP_SSH_correct_VCG :
    ⦃ fun s =>
    s.[12] = some 0x08
    ∧ s.[23] = some 0x06
    ∧ s.[20] = some 0x0
    ∧ s.[34] = some 0x16
    ∧ s.[36] = some 0x16⦄
    prog_only_IPv4_TCP_SSH @ 0
    ⦃ fun s => s.(.r0) = 1  ⦄ := by
    apply vcg_sound 100 prog_only_IPv4_TCP_SSH
      ( fun s => s.[12] = some 0x08 ∧ s.[23] = some 0x06
        ∧ s.[20] = some 0x0
        ∧ s.[34] = some 0x16 ∧ s.[36] = some 0x16)
      (fun s => s.(.r0) = 1) (fun _ => none)
    ·
      intro p h1
      simp [vcgCheck] at h1
      unfold vcg at h1
      simp only [List.mem_cons, List.mem_nil_iff, List.append] at h1
      rcases h1 with h | h
      .
        simp [List.get?,vcg] at h
        simp [wp] at h
        rw [h]
        intros s
        cases s
        simp [updateRegs]
        intros v₁ v₂ v₃ v₄ _v₅
        simp [v₁,v₂,v₃,v₄]
      .
        simp [List.get?,vcg] at h
    . simp


/-

Mostrar semantica Ebpf
Provar que a run(antiga),
  executa de acordo com a small step definida
  Se interp : fuel S p = some s₁ → run fuel S p s₁

-/
