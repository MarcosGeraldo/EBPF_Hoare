import EBPFSpec.Ver_Cond_Gen

-- Make the Verification Condition Generator Here

private lemma get?_nil (k : ℕ) : ([] : List opCode).get? k = none := rfl

private lemma get?_cons_zero (i : opCode) (rest : List opCode) :
    (i :: rest).get? 0 = some i := rfl

private lemma get?_cons_succ (i : opCode) (rest : List opCode) (k : ℕ) :
    (i :: rest).get? (k + 1) = rest.get? k := rfl


theorem blockWP_sound (instrs : List opCode) (code : Code) (pc : ℕ) (Q : Assert)
    (hcode : ∀ k, instrs.get? k = code.get? (pc + k)) :
    ⦃ blockWP instrs Q ⦄ code @ pc ⦃ Q ⦄ := by
  induction instrs generalizing pc with
  | nil =>
    apply Triple.halt -- code.get? pc == none
    have h := hcode 0
    rw [get?_nil, Nat.add_zero] at h
    exact h.symm
  | cons i rest ih =>
    have hfetch : code.get? pc = some i := by
      have h := hcode 0 -- h sendo 0
      simp [get?_cons_zero] at h -- provando para h 0
      exact h.symm
    have hrest : ∀ k, rest.get? k = code.get? (pc + 1 + k) := fun k => by
      have h := hcode (k + 1)
      simp [get?_cons_succ] at h
      rwa [show pc + 1 + k = pc + (k + 1) from by omega] at *
    exact Triple.seq (wp_sound code pc i (blockWP rest Q) hfetch) (ih (pc + 1) hrest)


theorem vcg_core_sound (fuel : ℕ) (code : Code) (Q : Assert) (inv : InvMap) (pc : ℕ)
    -- ∀ t, onde t é um indice do vetor de invariantes
    -- E ∀ invariane I, partindo de I , para o codigo e o pc t chego a Q
    (hInvs : ∀ t I, inv t = some I → ⦃ I ⦄ code @ t ⦃ Q ⦄)
    -- ∀ vc, onde vc pertence a lista de prendicoes
    -- vc tem que ser verdade
    -- pois todas as precondiç~eso devem ser verdadeiras
    (hVCs : ∀ vc ∈ (vcg code Q inv fuel pc).vcs, vc) :
    --Vai existir uma predoicução inicial que torna Q possivel
    ⦃ (vcg code Q inv fuel pc).pre ⦄ code @ pc ⦃ Q ⦄ := by
  induction fuel generalizing pc with
  | zero =>
    simp only [vcg]
    cases h : code.get? pc with
    | none =>
      exact Triple.consequence (fun _ hf => hf.elim) (Triple.halt h) (fun _ hq => hq)
    | some i =>
      exact Triple.consequence (fun _ hf => hf.elim) (wp_sound code pc i Q h) (fun _ hq => hq)
  | succ n ih =>
    cases h : code.get? pc with
    | none =>
      simp only [vcg, h]
      exact Triple.halt h
    | some instr =>
      cases instr with
      | jne_X_32 dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs ⊢
          have hvcFall : ∀ s, I s → (s.(dst) = s.(src)) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ List.mem_cons_self
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ s.(src) ∧ I s) ∨
                           (s.(dst) = s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) = s.(src)
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jne_X_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jne_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jne_X_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jne_X_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jne_X_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jne_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jne_K_32 dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs
          have hvcFall : ∀ s, I s → (s.(dst) = imm) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ (List.mem_cons_self _ _)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ imm ∧ I s) ∨
                           (s.(dst) = imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) = imm
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jne_K_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jne_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jne_K_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jne_K_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jne_K_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jne_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jeq_X_32 dst src offset =>
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
              (Triple.seq (Triple.jeq_X_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jeq_X_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jeq_X_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jeq_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jeq_K_32 dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs
          have hvcFall : ∀ s, I s → (s.(dst) = imm) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ (List.mem_cons_self _ _)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ imm ∧ I s) ∨
                           (s.(dst) = imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) = imm
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jne_K_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jne_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jeq_K_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jeq_K_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jeq_K_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jeq_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jset_X_32 dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs ⊢
          have hvcFall : ∀ s, I s → (s.(dst) = s.(src)) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ List.mem_cons_self
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ s.(src) ∧ I s) ∨
                           (s.(dst) = s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) = s.(src)
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jne_X_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jne_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jset_X_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jset_X_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jset_X_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jset_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jset_K_32 dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs
          have hvcFall : ∀ s, I s → (s.(dst) = imm) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ (List.mem_cons_self _ _)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) ≠ imm ∧ I s) ∨
                           (s.(dst) = imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) = imm
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jne_K_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jne_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jset_K_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jset_K_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jset_K_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jset_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jgt_X_32 dst src offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs
          have hvcFall : ∀ s, I s → (s.(dst) ≤ s.(src)) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ (List.mem_cons_self _ _)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) > s.(src) ∧ I s) ∨
                           (s.(dst) ≤ s.(src) ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) ≤ s.(src)
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jgt_X_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jgt_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jgt_X_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jgt_X_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jgt_X_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jgt_X_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | jgt_K_32 dst imm offset =>
        simp only [vcg, h]
        cases hinv : inv (pc + offset + 1) with
        | some I =>
          /-simp only [vcg, h, hinv] at hVCs
          have hvcFall : ∀ s, I s → (s.(dst) ≤ imm) → (vcg code Q inv n (pc + 1)).pre s :=
            hVCs _ (List.mem_cons_self _ _)
          have hVCs_ft : ∀ vc ∈ (vcg code Q inv n (pc + 1)).vcs, vc :=
            fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
          apply Triple.consequence
            (P := fun s => (s.(dst) > imm ∧ I s) ∨
                           (s.(dst) ≤ imm ∧ (vcg code Q inv n (pc + 1)).pre s))
          · intro s hIs
            by_cases hc : s.(dst) ≤ imm
            · exact Or.inr ⟨hc, hvcFall s hIs hc⟩
            · exact Or.inl ⟨Nat.lt_of_not_le hc, hIs⟩
          · exact Triple.disj
              (Triple.seq (Triple.jgt_K_32_true h) (hInvs (pc + offset) I hinv))
              (Triple.seq (Triple.jgt_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs-/
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
              (Triple.seq (Triple.jgt_K_32_true h) (hInvs (pc + offset + 1) I hinv))
              (Triple.seq (Triple.jgt_K_32_false h) (ih (pc + 1) hVCs_ft))
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
              (Triple.seq (Triple.jgt_K_32_true h) (ih (pc + offset + 1) hVCs_taken))
              (Triple.seq (Triple.jgt_K_32_false h) (ih (pc + 1) hVCs_ft))
          · intro s hs; exact hs
      | exit =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.exit h
        /-
              exact Triple.consequence (fun _ hf => hf.elim) (Triple.halt h) (fun _ hq => hq)
-/
      | _ =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
/-      | add_K_32 dst imm =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
      | MUL src dest =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
      | MOV src dest =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
      | MOVI dest val =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
      | LOAD dst addr =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
      | STORE src addr =>
        simp only [vcg, h] at hVCs ⊢
        exact Triple.seq (wp_sound code pc _ _ h) (ih (pc + 1) hVCs)
-/


theorem vcg_sound (fuel : ℕ) (code : Code) (P Q : Assert) (inv : InvMap)
    (hVCs : ∀ vc ∈ vcgCheck fuel code P Q inv, vc)
    (hInvs : ∀ t I, inv t = some I → ⦃ I ⦄ code @ t ⦃ Q ⦄) :
    ⦃ P ⦄ code @ 0 ⦃ Q ⦄ := by
  have hPre : P ⊢ₐ (vcg code Q inv fuel 0).pre :=
    hVCs _ (List.mem_cons_self _ _)
  have hRest : ∀ vc ∈ (vcg code Q inv fuel 0).vcs, vc :=
    fun vc hvc => hVCs vc (List.mem_cons_of_mem _ hvc)
  exact Triple.consequence hPre (vcg_core_sound fuel code Q inv 0 hInvs hRest) (fun _ h => h)
