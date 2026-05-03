import EBPFSpec.G_Ver_Cond_Gen


private lemma get?_nil (k : ℕ) : ([] : List opCode).get? k = none := rfl

private lemma get?_cons_zero (i : opCode) (rest : List opCode) :
    (i :: rest).get? 0 = some i := rfl

private lemma get?_cons_succ (i : opCode) (rest : List opCode) (k : ℕ) :
    (i :: rest).get? (k + 1) = rest.get? k := rfl

theorem wp_sound
    (prog : List opCode) (pc : PC) (i : opCode)
    (Q_next Q_jump Q_final : Assert)
    (hfetch : prog.get? pc = some i)
    (h_rest : Triple Q_next prog (pc + 1) Q_final)
    (h_jump : ∀ offset, Triple Q_jump prog (pc + offset + 1) Q_final) :
    Triple ((wp i Q_next Q_jump) Q_final) prog pc Q_final := by

  match i with
  | .mov_K dst imm  => exact Triple.mov_K hfetch h_rest
  | .mov_X dst src  => exact Triple.mov_X hfetch h_rest
  | .add_K dst imm  => exact Triple.add_K hfetch h_rest
  | .add_X dst src  => exact Triple.add_X hfetch h_rest
  | .and_K dst imm  => exact Triple.and_K hfetch h_rest
  | .and_X dst src  => exact Triple.and_X hfetch h_rest
  | .ldh_X dst src index => exact Triple.ldh_X hfetch h_rest
  | .sth_X src index => exact Triple.sth_X hfetch h_rest
  | .sth_K imm index => exact Triple.sth_K hfetch h_rest
  | .exit => exact Triple.exit hfetch

  | .jgt_X dst src offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) > s.(src) ∧ Q_jump s) ∨ (s.(dst) ≤ s.(src) ∧ Q_next s))
    ·
      intro s h_wp
      by_cases h_cond : s.(dst) > s.(src)
      · exact Or.inl ⟨h_cond, by simp_all⟩
      · exact Or.inr ⟨le_of_not_lt h_cond, by simp_all⟩

    ·
      exact Triple.disj
        (Triple.jgt_X_true hfetch (h_jump offset))
        (Triple.jgt_X_false hfetch h_rest)

    ·
      intro s hQs
      exact hQs

  | .jgt_K dst imm offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) > imm ∧ Q_jump s) ∨ (s.(dst) ≤ imm ∧ Q_next s))
    · intro s h_wp
      by_cases h_cond : s.(dst) > imm
      · exact Or.inl ⟨h_cond, by simp_all⟩
      · exact Or.inr ⟨le_of_not_lt h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jgt_K_true hfetch (h_jump offset))
        (Triple.jgt_K_false hfetch h_rest)
    · intro s hQs
      exact hQs

  | .jne_X dst src offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) ≠ s.(src) ∧ Q_jump s) ∨ (s.(dst) = s.(src) ∧ Q_next s))
    · intro s h_wp
      by_cases h_cond : s.(dst) = s.(src)
      · exact Or.inr ⟨h_cond, by simp_all⟩
      · exact Or.inl ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jne_X_true hfetch (h_jump offset))
        (Triple.jne_X_false hfetch h_rest)
    · intro s hQs
      exact hQs

  | .jeq_X dst src offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) = s.(src) ∧ Q_jump s) ∨ (s.(dst) ≠ s.(src) ∧ Q_next s))
    · intro s h_wp
      by_cases h_cond : s.(dst) = s.(src)
      · exact Or.inl ⟨h_cond, by simp_all⟩
      · exact Or.inr ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jeq_X_true hfetch (h_jump offset))
        (Triple.jeq_X_false hfetch h_rest)
    · intro s hQs
      exact hQs

  | .jset_X dst src offset =>
    apply Triple.consequence
      (P := fun s => ((s.(dst) &&& s.(src) ≠ 0) ∧ Q_jump s) ∨ ((s.(dst) &&& s.(src) = 0) ∧ Q_next s))
    · intro s h_wp
      by_cases h_cond : s.(dst) &&& s.(src) = 0
      · exact Or.inr ⟨h_cond, by simp_all⟩
      · exact Or.inl ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jset_X_true hfetch (h_jump offset))
        (Triple.jset_X_false hfetch h_rest)
    · intro s hQs
      exact hQs

  | .jne_K dst imm offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) ≠ imm ∧ Q_jump s) ∨ (s.(dst) = imm ∧ Q_next s))
    · intro s h_wp
      unfold wp at h_wp
      by_cases h_cond : s.(dst) = imm
      · exact Or.inr ⟨h_cond, by simp_all⟩
      · exact Or.inl ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jne_K_true hfetch (h_jump offset))
        (Triple.jne_K_false hfetch h_rest)
    · intro s hQs; exact hQs

  | .jeq_K dst imm offset =>
    apply Triple.consequence
      (P := fun s => (s.(dst) = imm ∧ Q_jump s) ∨ (s.(dst) ≠ imm ∧ Q_next s))
    · intro s h_wp
      unfold wp at h_wp
      by_cases h_cond : s.(dst) = imm
      · exact Or.inl ⟨h_cond, by simp_all⟩
      · exact Or.inr ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jeq_K_true hfetch (h_jump offset))
        (Triple.jeq_K_false hfetch h_rest)
    · intro s hQs; exact hQs

  | .jset_K dst imm offset =>
    apply Triple.consequence
      (P := fun s => ((s.(dst) &&& imm ≠ 0) ∧ Q_jump s) ∨ ((s.(dst) &&& imm = 0) ∧ Q_next s))
    · intro s h_wp
      unfold wp at h_wp
      by_cases h_cond : s.(dst) &&& imm = 0
      · exact Or.inr ⟨h_cond, by simp_all⟩
      · exact Or.inl ⟨h_cond, by simp_all⟩
    · exact Triple.disj
        (Triple.jset_K_true hfetch (h_jump offset))
        (Triple.jset_K_false hfetch h_rest)
    · intro s hQs; exact hQs



theorem blockWP_sound (instrs : List opCode) (code : Code) (pc : ℕ) (Q : Assert)
    (hcode : ∀ k, instrs.get? k = code.get? (pc + k)) :
    ⦃ blockWP instrs Q ⦄ code @ pc ⦃ Q ⦄ := by
  induction instrs generalizing pc with
  | nil =>
    apply Triple.halt
    have h := hcode 0
    rw [List.get?_nil, Nat.add_zero] at h
    exact h.symm
  | cons i rest ih =>
    have hfetch : code.get? pc = some i := by
      have h := hcode 0
      simp [List.get?_cons_zero] at h
      exact h.symm
    have hrest : ∀ k, rest.get? k = code.get? (pc + 1 + k) := fun k => by
      have h := hcode (k + 1)
      simp [List.get?_cons_succ] at h
      rwa [show pc + 1 + k = pc + (k + 1) from by omega] at *
    unfold blockWP
    exact wp_sound code pc i (blockWP rest Q) (fun _ => False) Q hfetch (ih (pc + 1) hrest) (fun _ => Triple.false_pre)

theorem vcg_core_sound (fuel : ℕ) (code : Code) (Q : Assert) (inv : InvMap) (pc : ℕ)
    (hInvs : ∀ t I, inv t = some I → ⦃ I ⦄ code @ t ⦃ Q ⦄)
    (hVCs : ∀ vc ∈ (vcg code Q inv fuel pc).vcs, vc) :
    ⦃ (vcg code Q inv fuel pc).pre ⦄ code @ pc ⦃ Q ⦄ := by
  induction fuel generalizing pc with
  | zero =>
    simp only [vcg]
    cases h : code.get? pc with
    | none =>
      exact Triple.consequence (fun _ hf => hf.elim) (Triple.halt h) (fun _ hq => hq)
    | some i =>
      apply Triple.consequence (P := fun _ => False) (Q := Q)
      · intro _s hf
        exact hf.elim
      · exact Triple.false_pre
      · intro s hq
        exact hq
  | succ n ih =>
    cases h : code.get? pc with
    | none =>
      simp only [vcg, h]
      exact Triple.halt h
    | some instr =>
      cases instr with
      | jne_X dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ s.(src) ∧ I s) ∨
                           (s.(dst) = s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) = s.(src)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              -- CORREÇÃO AQUI: Remoção do Triple.seq
              (Triple.jne_X_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jne_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (by simp [List.mem_append]; exact Or.inl hvc)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (by simp [List.mem_append]; exact Or.inr hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ s.(src) ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) = s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) = s.(src))
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              -- CORREÇÃO AQUI: Remoção do Triple.seq
              (Triple.jne_X_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jne_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jne_K dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ imm ∧ I s) ∨
                           (s.(dst) = imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) = imm
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jne_K_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jne_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ imm ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) = imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) = imm)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jne_K_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jne_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jeq_X dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) = s.(src) ∧ I s) ∨
                           (s.(dst) ≠ s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) ≠ s.(src)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Classical.not_not.mp hc, h1 (Classical.not_not.mp hc)⟩
          · exact Triple.disj
              (Triple.jeq_X_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jeq_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) = s.(src) ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) ≠ s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) ≠ s.(src))
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Classical.not_not.mp hc, h1 (Classical.not_not.mp hc)⟩
          · exact Triple.disj
              (Triple.jeq_X_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jeq_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jeq_K dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) = imm ∧ I s) ∨
                           (s.(dst) ≠ imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) ≠ imm
            · exact Or.inr ⟨hc, h2  hc⟩
            · exact Or.inl ⟨Classical.not_not.mp hc, h1 (Classical.not_not.mp hc)⟩
          · exact Triple.disj
              (Triple.jeq_K_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jeq_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) = imm ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) ≠ imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) ≠ imm)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Classical.not_not.mp hc, h1 (Classical.not_not.mp hc)⟩
          · exact Triple.disj
              (Triple.jeq_K_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jeq_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jset_X dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => ( s.(dst) &&& s.(src) ≠ 0 ∧ I s) ∨
                           ( s.(dst) &&& s.(src) = 0 ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) &&& s.(src) = 0
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jset_X_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jset_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => ( s.(dst) &&& s.(src) ≠ 0 ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           ( s.(dst) &&& s.(src) = 0 ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) &&& s.(src) = 0
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jset_X_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jset_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jset_K dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => ( s.(dst) &&& imm ≠ 0 ∧ I s) ∨
                           ( s.(dst) &&& imm = 0 ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) &&& imm = 0)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jset_K_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jset_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) &&& imm ≠ 0 ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) &&& imm = 0 ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) &&& imm = 0)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨hc, h1 hc⟩
          · exact Triple.disj
              (Triple.jset_K_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jset_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jgt_X dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) > s.(src) ∧ I s) ∨
                           (s.(dst) ≤ s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) ≤ s.(src)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, h1 (Nat.lt_of_not_le hc)⟩
          · exact Triple.disj
              (Triple.jgt_X_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jgt_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) > s.(src) ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) ≤ s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) ≤ s.(src))
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, h1 (Nat.lt_of_not_le hc)⟩
          · exact Triple.disj
              (Triple.jgt_X_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jgt_X_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jgt_K dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc := fun vc hvc => hVCs vc hvc
          apply Triple.consequence
            (P := fun s => (s.(dst) > imm ∧ I s) ∨
                           (s.(dst) ≤ imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : s.(dst) ≤ imm
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, h1 (Nat.lt_of_not_le hc)⟩
          · exact Triple.disj
              (Triple.jgt_K_true h (hInvs (pc + offset + 1) I hinv))
              (Triple.jgt_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
        | none =>
          simp only [vcg, h, hinv] at hVCs ⊢
          have hVCs_taken : ∀ vc ∈ (vcg code Q inv n (pc + offset + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inl hvc))
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_append.mpr (Or.inr hvc))
          apply Triple.consequence
            (P := fun s => (s.(dst) > imm ∧ (vcg code Q inv n (pc + offset + 1)).pre s) ∨
                           (s.(dst) ≤ imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s ⟨h1, h2⟩
            by_cases hc : (s.(dst) ≤ imm)
            · exact Or.inr ⟨hc, h2 hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, h1 (Nat.lt_of_not_le hc)⟩
          · exact Triple.disj
              (Triple.jgt_K_true h (ih (pc + offset + 1) hVCs_taken))
              (Triple.jgt_K_false h (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | exit =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.exit h

      | _ =>
        simp only [vcg, h] at hVCs ⊢

        exact wp_sound code pc _
          ((vcg code Q inv n (pc + 1)).pre) -- Q_next: Pré-condição do próximo PC
          (fun _ => False)                  -- Q_jump: Falso, pois o salto é impossível
          Q                                 -- Q_final: Nosso objetivo
          h                                 -- hfetch
          (ih (pc + 1) hVCs)                -- h_rest: A hipótese indutiva!
          (fun _ => Triple.false_pre)       -- h_jump: Prova trivial de caminho morto

theorem vcg_sound (fuel : ℕ) (code : Code) (P Q : Assert) (inv : InvMap)
    (hVCs : ∀ vc ∈ vcgCheck fuel code P Q inv, vc)
    (hInvs : ∀ t I, inv t = some I → ⦃ I ⦄ code @ t ⦃ Q ⦄) :
    ⦃ P ⦄ code @ 0 ⦃ Q ⦄ := by
  have hPre : P ⊢ₐ (vcg code Q inv fuel 0).pre :=
    hVCs _ (List.mem_cons_self _ _)
  have hRest : ∀ vc ∈ (vcg code Q inv fuel 0).vcs, vc :=
    fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
  exact Triple.consequence hPre (vcg_core_sound fuel code Q inv 0 hInvs hRest) (fun _ h => h)
