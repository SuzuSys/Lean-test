-- Exercises (1)

section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    ⟨
      fun h : ∀x : α, p x ∧ q x =>
        ⟨
          fun y : α => (h y).1,
          fun y : α => (h y).2
        ⟩,
      fun h : (∀ x, p x) ∧ (∀ x, q x) =>
        fun y : α => ⟨h.1 y, h.2 y⟩
    ⟩

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun h₁ : (∀ x : α, p x → q x) =>
      fun h₂ : (∀ x : α, p x) =>
        fun x : α => (h₁ x) (h₂ x)

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun h₁ : (∀ x, p x) ∨ (∀ x, q x) =>
      fun x : α =>
        h₁.elim
          (fun h₂ : (∀ x, p x) => Or.intro_left (q x) (h₂ x))
          (fun h₃ : (∀ x, q x) => Or.intro_right (p x) (h₃ x))

end

-- Exercise (2)

section
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    fun h₁ : α =>
      ⟨
        show (∀ _ : α, r) → r from
        fun h₂ : (∀ _ : α, r) => h₂ h₁,
        show r → (∀ _ : α, r) from
        fun h₃ : r => fun _ : α => h₃
      ⟩

  section
    open Classical

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
      ⟨
        fun h : (∀ x, p x ∨ r) =>
          byCases
            (fun hr : r =>
              Or.intro_right (∀ x, p x) hr)
            (fun hnr : ¬r =>
              have : (∀ x, p x) :=
                fun x : α =>
                  show p x from
                  (h x).elim
                    (fun hpx : p x => hpx)
                    (fun hr : r => absurd hr hnr)
              Or.intro_left r this),
        fun h : (∀ x, p x) ∨ r =>
          fun x =>
            h.elim
              (fun hl : (∀ x, p x) => Or.intro_left r (hl x))
              (fun hr : r => Or.intro_right (p x) hr)
      ⟩

  end

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    ⟨
      fun h : (∀ x, r → p x) =>
        fun hr : r =>
          fun x =>
            h x hr,
      fun h : (r → ∀ x, p x) =>
        fun x =>
          fun hr : r =>
            h hr x
    ⟩

end

section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ _ : α, r) → r :=
    fun ⟨_, hr⟩ => hr

  example (a : α) : r → (∃ _ : α, r) :=
    fun hr => ⟨a, hr⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    ⟨
      fun ⟨(w : α), (hpw : p w), r⟩ => ⟨⟨w, hpw⟩, r⟩
      ,
      fun ⟨⟨(w : α), (hpw : p w)⟩, r⟩ => ⟨w, hpw, r⟩
    ⟩

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    ⟨
      show (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) from
      fun ⟨(w : α), (h : p w ∨ q w)⟩ =>
        h.elim
          (fun hp : p w => Or.intro_left (∃ x, q x) ⟨w, hp⟩)
          (fun hq : q w => Or.intro_right (∃ x, p x) ⟨w, hq⟩)
      ,
      show (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) from
      fun h : (∃ x, p x) ∨ (∃ x, q x) =>
        h.elim
          (fun ⟨(w : α), (hpw : p w)⟩ => ⟨w, Or.intro_left (q w) (hpw)⟩)
          (fun ⟨(w : α), (hqw : q w)⟩ => ⟨w, Or.intro_right (p w) (hqw)⟩)
    ⟩

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    ⟨
      show (∀ x, p x) → ¬ (∃ x, ¬ p x) from
      fun h : (∀ x, p x) =>
        show ¬ (∃ x, ¬ p x) from
        fun ⟨(w : α), (hnpw : ¬ p w)⟩ =>
          show False from absurd (h w) hnpw
      ,
      show ¬ (∃ x, ¬ p x) → (∀ x, p x) from
      fun h : ¬ (∃ x, ¬ p x) =>
        fun x : α =>
          byContradiction
            (fun hn : ¬ p x =>
              have : (∃ w, ¬ p w) := ⟨x, hn⟩
              h this)
    ⟩

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    ⟨
      show (∃ x, p x) → ¬ (∀ x, ¬ p x) from
      fun ⟨(w : α), (h : p w)⟩ =>
        fun hpx : ∀ x, ¬ p x => absurd h (hpx w)
      ,
      show ¬ (∀ x, ¬ p x) → (∃ x, p x) from
      fun h : ¬ (∀ x, ¬ p x) =>
      byContradiction
        (fun h₁ : ¬ (∃ x, p x) =>
          have h₂ : (∀ x, ¬ p x) :=
            fun x : α =>
              fun h₃ : p x =>
                have h₄ : (∃ x, p x) := ⟨x, h₃⟩
                show False from h₁ h₄
          show False from h h₂)
    ⟩

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    ⟨
      show (¬ ∃ x, p x) → (∀ x, ¬ p x) from
      fun h₁ : (¬ ∃ x, p x) =>
        fun x : α =>
          fun h₂ : p x =>
            have : (∃ x, p x) := ⟨x, h₂⟩
            show False from h₁ this
      ,
      show (∀ x, ¬ p x) → (¬ ∃ x, p x) from
      fun h₁ : (∀ x, ¬ p x) =>
        fun ⟨(w : α), (h₂ : p w)⟩ =>
          h₁ w h₂
    ⟩

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    ⟨
      show (¬ ∀ x, p x) → (∃ x, ¬ p x) from
      fun h₁ : (¬ ∀ x, p x) =>
      byContradiction
      (fun h₂ : ¬ (∃ x, ¬ p x) =>
        have h₄ : (∀ x, p x) :=
        fun x =>
          byContradiction
            (fun h₃ : ¬ p x =>
              have : (∃ x, ¬ p x) := ⟨x, h₃⟩
              show False from h₂ this)
        show False from h₁ h₄)
      ,
      show (∃ x, ¬ p x) → (¬ ∀ x, p x) from
      fun ⟨(w : α), (h₁ : ¬ p w)⟩ =>
        fun h₂ : (∀ x, p x) => absurd (h₂ w) h₁
    ⟩

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    ⟨
      show (∀ x, p x → r) → (∃ x, p x) → r from
      fun h₁ : (∀ x, p x → r) =>
        fun ⟨(w : α), (h₂ : p w)⟩ =>
          h₁ w h₂
      ,
      show ((∃ x, p x) → r) → (∀ x, p x → r) from
      fun h₁ : ((∃ x, p x) → r) =>
        fun x =>
          fun h₂ : p x =>
            have : (∃ x, p x) := ⟨x, h₂⟩
            h₁ this
    ⟩

  example (_ : α) : (∃ x, p x → r) → (∀ x, p x) → r :=
    fun ⟨(w : α), (h₁ : p w → r)⟩ =>
      fun h₂ : (∀ x, p x) =>
        h₁ (h₂ w)

  /- example (a : α) : ((∀ x, p x) → r) → (∃ x, p x → r) :=
    fun h₁ : ((∀ x, p x) → r) =>
      byContradiction
        (fun h₂ : ¬ (∃ x, p x → r) =>
          ) -/







  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end
