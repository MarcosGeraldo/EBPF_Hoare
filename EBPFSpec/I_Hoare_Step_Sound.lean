import EBPFSpec.D_Sep_Logic
import EBPFSpec.E_Interpreter

set_option maxHeartbeats 2000000

axiom step_locality {prog pc next_pc s₁ s₂ next_s} :
  step prog pc next_pc (Assert.State_union s₁ s₂) next_s →
  Assert.State_disjoint s₁ s₂ →
  ∃ next_s₁, next_s = Assert.State_union next_s₁ s₂ ∧
               Assert.State_disjoint next_s₁ s₂ ∧
               step prog pc next_pc s₁ next_s₁

theorem hoare_step_sound {prog : List opCode} {pc next_pc : PC}
  {P Q : Assert} {s next_s : MachineState}
  (h_triple : Triple P prog pc Q)
  (h_step : step prog pc next_pc s next_s)
  (h_pre : P s) : ∃ P_next, Triple P_next prog next_pc Q ∧ P_next next_s := by

  induction h_triple generalizing s next_s next_pc

  case consequence _P P' Q Q_final hP _hcore hQ ih =>
    rcases ih h_step (hP s h_pre) with ⟨P_next, h_trip_next, h_pre_next⟩
    exact ⟨P_next, Triple.consequence (fun _ h => h) h_trip_next hQ, h_pre_next⟩

  case frame P Q_core R _hcore ih =>
    rcases h_pre with ⟨s₁, s₂, h_disjoint, h_s_eq, h_P, h_R⟩
    rw [h_s_eq] at h_step
    have h_local := step_locality h_step h_disjoint
    rcases h_local with ⟨next_s₁, h_next_eq, h_next_disj, h_step_local⟩
    rcases ih h_step_local h_P with ⟨P_next, h_trip_next, h_pre_next⟩

    exact ⟨fun st => ∃ st₁ st₂, Assert.State_disjoint st₁ st₂ ∧ st = Assert.State_union st₁ st₂ ∧ P_next st₁ ∧ R st₂,
           Triple.frame h_trip_next,
           ⟨next_s₁, s₂, h_next_disj, h_next_eq, h_pre_next, h_R⟩⟩

  case disj P₁ P₂ Q_disj _h1 _h2 ih ih' =>
    cases h_pre with
    | inl h => exact ih h_step h
    | inr h => exact ih' h_step h

  case false_pre =>
    exact h_pre.elim

  case mov_K | mov_X | add_K | add_X | and_K | and_X | sth_K | sth_X | ldh_X =>
    cases h_step <;> simp_all
    exact ⟨_, by assumption , by assumption⟩

  case jset_X_true | jset_X_false | jset_K_true | jset_K_false =>

    have h_cond := h_pre.left
    have h_P := h_pre.right
    clear h_pre

    cases h_step
    all_goals
      try simp_all

      try contradiction

      try
        constructor
        constructor
        · assumption
        · exact h_P

  case jgt_X_true | jgt_X_false | jgt_K_true | jgt_K_false =>

    cases h_step <;> simp_all

    all_goals
      try simp_all

      try omega

      try
        constructor
        constructor
        · assumption
        · exact h_pre.right

  case jeq_X_true | jeq_X_false | jeq_K_true | jeq_K_false =>
    have h_cond := h_pre.left
    have h_P := h_pre.right
    clear h_pre

    cases h_step
    all_goals
      try simp_all

      try omega

      try
        constructor
        constructor
        · assumption
        · exact h_P

  case jne_K_true | jne_K_false | jne_X_true | jne_X_false =>
    have h_cond := h_pre.left
    have h_P := h_pre.right
    clear h_pre

    cases h_step <;> simp_all
    all_goals
      try simp only [Option.some.injEq]

      try subst_vars

      try omega

      try
        constructor
        constructor
        · assumption
        · exact h_P

  case halt =>
    cases h_step
    all_goals
      try simp_all
      try
        constructor

  case exit =>
    have h_P := h_pre
    cases h_step
    all_goals
      try simp_all
      try
        constructor
        constructor
        · exact Triple.exit (by assumption)
        · exact h_P
