-- Exercises (1)

section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    have h₁ : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
      fun h₂ : ∀ x, p x ∧ q x =>
        have h₃ : ∀ x, p x :=
          fun x : α => (h₂ x).1
        have h₄ : ∀ x, q x :=
          fun x : α => (h₂ x).2
        ⟨h₃, h₄⟩
    have h₂ : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) :=
      fun (h₃ : (∀ x, p x) ∧ (∀ x, q x)) (x : α) => ⟨h₃.1 x, h₃.2 x⟩
    ⟨h₁, h₂⟩

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun (h₁ : ∀ x, p x → q x) (h₂: ∀ x, p x) (x : α) => (h₁ x) (h₂ x)

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun (h₁ : (∀ x, p x) ∨ (∀ x, q x)) (x : α) =>
      have h₂ : (∀ x, p x) → p x ∨ q x :=
        fun h₃ : ∀ x, p x => Or.intro_left (q x) (h₃ x)
      have h₃ : (∀ x, q x) → p x ∨ q x :=
        fun h₄ : ∀ x, q x => Or.intro_right (p x) (h₄ x)
      h₁.elim h₂ h₃

end

-- Exercise (2)

section
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    fun x : α =>
      have h₁ : (∀ _ : α, r) → r :=
        fun h₂ : ∀ _ : α, r => h₂ x
      have h₂ : r → (∀ _ : α, r) :=
        fun (h₃ : r) (_ : α) => h₃
      ⟨h₁, h₂⟩

  section
    open Classical

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
      have h₁ : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r :=
        fun h₂ : ∀ x, p x ∨ r =>
          have h₃ : r → (∀ x, p x) ∨ r :=
            fun h₄ : r => Or.intro_right (∀ x, p x) h₄
          have h₄ : ¬ r → (∀ x, p x) ∨ r :=
            fun h₅ : ¬ r =>
              have h₆ : ∀ x, p x :=
                fun x : α =>
                  have h₇ : p x ∨ r := h₂ x
                  have h₈ : r → p x :=
                    fun h₉ : r => absurd h₉ h₅
                  h₇.elim id h₈
              Or.intro_left r h₆
          byCases h₃ h₄
      have h₂ : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) :=
        fun (h₃ : (∀ x, p x) ∨ r) (x : α) =>
          have h₄ : (∀ x, p x) → p x ∨ r :=
            fun h₅ : ∀ x, p x => Or.intro_left r (h₅ x)
          have h₅ : r → p x ∨ r :=
            fun h₆ : r => Or.intro_right (p x) h₆
          h₃.elim h₄ h₅
      ⟨h₁, h₂⟩

  end

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    have h₁ : (∀ x, r → p x) → (r → ∀ x, p x) :=
      fun (h₂ : ∀ x, r → p x) (h₃ : r) (x : α) => h₂ x h₃
    have h₂ : (r → ∀ x, p x) → (∀ x, r → p x) :=
      fun (h₃ : r → ∀ x, p x) (x : α) (h₄ : r) => h₃ h₄ x
    ⟨h₁, h₂⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w : α =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

end



section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop) (s : Prop) (t : Prop)

  example : (∃ _ : α, r) → r :=
    fun ⟨_, (h₁ : r)⟩ => h₁

  example (a : α) : r → (∃ _ : α, r) :=
    fun h₁ : r => ⟨a, h₁⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    have h₁ : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r :=
      fun ⟨(w : α), (h₂ : p w), (h₃ : r)⟩ => ⟨⟨w, h₂⟩, h₃⟩
    have h₂ : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
      fun ⟨⟨(w : α), (h₃ : p w)⟩, (h₄ : r)⟩ => ⟨w, h₃, h₄⟩
    ⟨h₁, h₂⟩

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    have h₁ : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) :=
      fun ⟨(w : α), (h₂ : p w ∨ q w)⟩ =>
        have h₃ : p w → (∃ x, p x) ∨ (∃ x, q x) :=
          fun h₄ : p w => Or.intro_left (∃ x, q x) ⟨w, h₄⟩
        have h₄ : q w → (∃ x, p x) ∨ (∃ x, q x) :=
          fun h₅ : q w => Or.intro_right (∃ x, p x) ⟨w, h₅⟩
        h₂.elim h₃ h₄
    have h₂ : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) :=
      fun h₃ : (∃ x, p x) ∨ (∃ x, q x) =>
        have h₄ : (∃ x, p x) → (∃ x, p x ∨ q x) :=
          fun ⟨(w : α), (h₅ : p w)⟩ => ⟨w, Or.intro_left (q w) h₅⟩
        have h₅ : (∃ x, q x) → (∃ x, p x ∨ q x) :=
          fun ⟨(w : α), (h₆ : q w)⟩ => ⟨w, Or.intro_right (p w) h₆⟩
        h₃.elim h₄ h₅
    ⟨h₁, h₂⟩

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    have h₁ : (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
      fun (h₂ : ∀ x, p x) ⟨(w : α), (h₃ : ¬ p w)⟩ => absurd (h₂ w) h₃
    have h₂ : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
      fun (h₃ : ¬ (∃ x, ¬ p x)) (x : α) =>
        have h₄ : ¬ ¬ p x :=
          fun h₅ : ¬ p x => h₃ ⟨x, h₅⟩
        byContradiction h₄
    ⟨h₁, h₂⟩

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    have h₁ : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
      fun ⟨(w : α), (h₂ : p w)⟩ (h₃ : ∀ x, ¬ p x) => h₃ w h₂
    have h₂ : ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
      fun h₃ : ¬ (∀ x, ¬ p x) =>
        have h₄ : ¬ ¬ (∃ x, p x) :=
          fun h₅ : ¬ (∃ x, p x) =>
            have h₆ : ∀ x, ¬ p x :=
              fun (x : α) (h₈ : p x) => h₅ ⟨x, h₈⟩
            h₃ h₆
        byContradiction h₄
    ⟨h₁, h₂⟩

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    have h₁ : (¬ ∃ x, p x) → (∀ x, ¬ p x) :=
      fun (h₂ : ¬ ∃ x, p x) (x : α) (h₃ : p x) => h₂ ⟨x, h₃⟩
    have h₂ : (∀ x, ¬ p x) → (¬ ∃ x, p x) :=
      fun (h₃ : ∀ x, ¬ p x) ⟨(w : α), (h₄ : p w)⟩ => h₃ w h₄
    ⟨h₁, h₂⟩

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    have h₁ : (¬ ∀ x, p x) → (∃ x, ¬ p x) :=
      fun h₂ : ¬ ∀ x, p x =>
        have h₃ : ¬ ¬ ∃ x, ¬ p x :=
          fun h₄ : ¬ ∃ x, ¬ p x =>
            have h₅ : ∀ x, p x :=
              fun x : α =>
                have h₆ : ¬ ¬ p x :=
                  fun h₇ : ¬ p x => h₄ ⟨x, h₇⟩
                byContradiction h₆
            h₂ h₅
        byContradiction h₃
    have h₂ : (∃ x, ¬ p x) → (¬ ∀ x, p x) :=
      fun ⟨(w : α), (h₃ : ¬ p w)⟩ (h₄ : ∀ x, p x) => h₃ (h₄ w)
    ⟨h₁, h₂⟩

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    have h₁ : (∀ x, p x → r) → (∃ x, p x) → r :=
      fun (h₂ : ∀ x, p x → r) ⟨(w : α), (h₃ : p w)⟩ => h₂ w h₃
    have h₂ : ((∃ x, p x) → r) → (∀ x, p x → r) :=
      fun (h₃ : (∃ x, p x) → r) (x : α) (h₄ : p x) => h₃ ⟨x, h₄⟩
    ⟨h₁, h₂⟩

  example (_ : α) : (∃ x, p x → r) → (∀ x, p x) → r :=
    fun ⟨(w : α), (h₁ : p w → r)⟩ (h₂ : ∀ x, p x) => h₁ (h₂ w)

  example (a : α) : (∀ x, p x) → (∃ x, p x) :=
    fun h₁ : ∀ x, p x => ⟨a, h₁ a⟩

  example (a : α) : ((∀ x, p x) → r) → (∃ x, p x → r) :=
    fun h₁ : (∀ x, p x) → r =>
      have h₂ : ¬ r → (∃ x, ¬ p x) :=
        fun h₃ : ¬ r =>
          have h₄ : ¬ ¬ ∃ x, ¬ p x :=
            fun h₅ : ¬ ∃ x, ¬ p x =>
              have h₆ : ∀ x, p x :=
                fun x : α =>
                  have h₇ : ¬ ¬ p x :=
                    fun h₈ : ¬ p x => h₅ ⟨x, h₈⟩
                  byContradiction h₇
              have h₇ : ¬ ∀ x, p x :=
                fun h₈ : ∀ x, p x => h₃ (h₁ h₈)
              h₇ h₆
          byContradiction h₄
      have h₄ : ¬ r → (∃ x, p x → r) :=
        fun h₅ : ¬ r =>
          have h₆ : ∃ x, ¬ p x := h₂ h₅
          have h₇ : (∃ x, ¬ p x) → (∃ x, p x → r) :=

            fun ⟨(w : α), (h₈ : ¬ p w)⟩ =>
              have h₉ : p w → r :=
                fun h₁₀ : p w => absurd h₁₀ h₈
              ⟨w, h₉⟩
          h₇ h₆
      have h₅ : r → (∃ x, p x → r) :=
        fun h₆ : r =>
          have h₇ : p a → r :=
            fun _ : p a => h₆
          ⟨a, h₇⟩
      byCases h₅ h₄

  example (a : α) : ((∀ x, p x) → r) → (∃ x, p x → r) :=
    fun h₁ : (∀ x, p x) → r =>
      have h₂ : ¬ r → ¬ ∀ x, p x :=
        fun (h₃ : ¬ r) (h₄ : ∀ x, p x) => h₃ (h₁ h₄)
      have h₃ : (¬ ∀ x, p x) → (∃ x, ¬ p x) :=
        fun h₄ : ¬ ∀ x, p x =>
          have h₅ : ¬ ¬ ∃ x, ¬ p x :=
            fun h₆ : ¬ ∃ x, ¬ p x =>
              have h₇ : ∀ x, p x :=
                fun x : α =>
                  have h₈ : ¬ ¬ p x :=
                    fun h₉ : ¬ p x => h₆ ⟨x, h₉⟩
                  byContradiction h₈
              h₄ h₇
          byContradiction h₅
      have h₄ : ¬ r → (∃ x, p x → r) :=
        fun h₅ : ¬ r =>
          have h₆ : ∃ x, ¬ p x := h₃ (h₂ h₅)
          have h₇ : (∃ x, ¬ p x) → (∃ x, p x → r) :=
            fun ⟨(w : α), (h₈ : ¬ p w)⟩ =>
              have h₉ : p w → r :=
                fun h₁₀ : p w => absurd h₁₀ h₈
              ⟨w, h₉⟩
          h₇ h₆
      have h₅ : r → (∃ x, p x → r) :=
        fun h₆ : r =>
          have h₇ : p a → r :=
            fun _ : p a => h₆
          ⟨a, h₇⟩
      byCases h₅ h₄

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    have h₁ : (∃ x, p x → r) → (∀ x, p x) → r :=
      fun ⟨(w : α), (h₂ : p w → r)⟩ (h₃ : ∀ x, p x) => h₂ (h₃ w)
    have h₂ : ((∀ x, p x) → r) → (∃ x, p x → r) :=
      fun h₃ : (∀ x, p x) → r =>
        have h₄ : r → (∃ x, p x → r) :=
          fun h₅ : r =>
            have h₆ : p a → r :=
              fun _ : p a => h₅
            ⟨a, h₆⟩
        have h₅ : ¬ r → (∃ x, p x → r) :=
          fun h₆ : ¬ r =>
            have h₇ : ¬ ∀ x, p x :=
              fun h₈ : ∀ x, p x => h₆ (h₃ h₈)
            have h₈ : ∃ x, ¬ p x :=
              fun h₉ :
        byCases h₄ h₅
    ⟨h₁, h₂⟩

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end
