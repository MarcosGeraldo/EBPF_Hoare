import EBPFSpec.D_Sep_Logic
import EBPFSpec.E_Interpreter

set_option maxHeartbeats 2000000

macro "run_seq" id:ident : tactic => `(tactic|
  cases h_run
  -- O simp_all acha a contradição no caso 'halt' e o fecha instantaneamente
  all_goals try simp_all only [Option.some.injEq]
  -- Sobra apenas o caso 'seq'. Batizamos as variáveis invisíveis geradas por ele:
  rename_i next_pc next_s h_step h_run_rest
  cases h_step
  all_goals
    try simp only [Option.some.injEq]
    try subst_vars
    exact $id h_run_rest h_pre
)

macro "run_jump" id:ident : tactic => `(tactic|
  cases h_run
  all_goals try simp_all only [Option.some.injEq]
  rename_i next_pc next_s h_step h_run_rest
  cases h_step
  all_goals
    try simp only [Option.some.injEq]
    try subst_vars
    try omega
    try contradiction
    exact $id h_run_rest h_pre.right
)

theorem hoare_run_sound {prog : List opCode} {pc : PC} {P Q : Assert} {s s_final : MachineState}
  (h_triple : Triple P prog pc Q)
  (h_run : run prog pc s s_final)
  (h_pre : P s) : Q s_final := by

  induction h_triple generalizing s s_final

  case consequence P P' Q Q' hP hcore hQ ih =>
    apply hQ
    apply ih
    · exact h_run
    · exact hP s h_pre

  case false_pre =>
    exact h_pre.elim

  case disj P₁ P₂ Q h1 h2 ih1 ih2 =>
    cases h_pre with
    | inl h_left =>
      apply ih1
      · exact h_run
      · exact h_left
    | inr h_right =>
      apply ih2
      · exact h_run
      · exact h_right

  case frame P Q R hcore ih =>

    sorry


  case halt pc_halt Q hfetch =>
    sorry

-- Instruções de Aridade 4 (geralmente atribuição e aritmética)
  -- Instruções de Aridade 4
-- Caso isolado para mov_K (A assinatura de ih usará updateRegs)
  case mov_K =>
    rename_i ih
    cases h_run
    all_goals try simp_all only [Option.some.injEq]
    rename_i next_pc next_s h_step h_run_rest
    cases h_step
    all_goals
      try simp only [Option.some.injEq]
      try subst_vars
      sorry
      --exact ih h_run_rest h_pre

  -- Caso isolado para mov_X (A assinatura de ih usará writeReg)
  case mov_X =>
    rename_i ih
    cases h_run
    all_goals try simp_all only [Option.some.injEq]
    rename_i next_pc next_s h_step h_run_rest
    cases h_step
    all_goals
      try simp only [Option.some.injEq]
      try subst_vars
      sorry
      --exact ih h_run_rest h_pre

  -- Caso isolado para add_K
  case add_K =>
    rename_i ih
    cases h_run
    all_goals try simp_all only [Option.some.injEq]
    rename_i next_pc next_s h_step h_run_rest
    cases h_step
    all_goals
      try simp only [Option.some.injEq]
      try subst_vars
      sorry
      --exact ih h_run_rest h_pre

  -- e assim sucessivamente para as demais instruções.  case add_K _ _ _ ih s s_final h_run h_pre => run_seq ih
  case add_X _ _ _ ih s s_final h_run h_pre =>
    sorry
  case and_K _ _ _ ih s s_final h_run h_pre => sorry
  case and_X _ _ _ ih s s_final h_run h_pre => sorry

  -- Instruções de Aridade 5 (Memória)
  case ldh_X _ _ _ _ ih s s_final h_run h_pre => sorry
  case sth_X _ _ _ _ ih s s_final h_run h_pre => sorry
  case sth_K _ _ _ _ ih s s_final h_run h_pre => sorry

  -- Saltos (Jumps)
  case jgt_X_true _ _ _ ih_jump _ _ s s_final h_run h_pre =>
    --run_jump ih_jump
    sorry

  case jgt_X_false _ _ _ _ _ ih_rest s s_final h_run h_pre =>
    --run_jump ih_jump
    sorry


  case jgt_K_true _ _ _ ih_jump _ _ s s_final h_run h_pre =>
    --run_jump ih_jump
    sorry

  case jgt_K_false _ _ _ _ _ ih_rest s s_final h_run h_pre =>
    sorry
  case jset_X_true | jset_X_false | jset_K_true | jset_K_false =>
    sorry
    --have h_cond := h_pre.left
    --have h_P := h_pre.right
    --clear h_pre

/-    cases h_run <;> simp_all
    all_goals
      try simp_all

      try contradiction

      try
        constructor
        constructor
        · assumption
        · exact h_P
-/
  case jeq_X_true | jeq_X_false | jeq_K_true | jeq_K_false =>
    sorry

  case jne_X_true | jne_X_false | jne_K_true | jne_K_false =>
    sorry

  case exit =>
    sorry
  -- (Demais instruções como add, jmp, ldh seguem a mesma lógica do mov_K)
  -- Esta prova normalmente prossegue por indução sobre a execução (h_run)
  -- utilizando o teorema `hoare_step_sound` para cada passo isolado.


theorem hoare_run_sound_V2 {prog : List opCode} {pc : PC} {P Q : Assert} {s s_final : MachineState}
  (h_triple : Triple P prog pc Q)
  (h_run : runV2 prog pc s s_final)
  (h_pre : P s) : Q s_final := by
  induction h_triple generalizing s s_final

  case consequence P P' Q Q' hP hcore hQ ih =>
    apply hQ
    apply ih
    · exact h_run
    · exact hP s h_pre

  case mov_K =>
    rename_i ih
    cases h_run <;> simp_all
    sorry

  all_goals sorry
