variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  have h₁ : p ∧ q → q ∧ p :=
    fun h₂ : p ∧ q => ⟨h₂.2, h₂.1⟩
  have h₂ : q ∧ p → p ∧ q :=
    fun h₃ : q ∧ p => ⟨h₃.2, h₃.1⟩
  ⟨h₁, h₂⟩

example : p ∨ q ↔ q ∨ p :=
  have h₁ : p ∨ q → q ∨ p :=
    fun h₂ : p ∨ q =>
      have h₃ : p → q ∨ p :=
        fun h₄ : p => Or.intro_right q h₄
      have h₄ : q → q ∨ p :=
        fun h₅ : q => Or.intro_left p h₅
      h₂.elim h₃ h₄
  have h₂ : q ∨ p → p ∨ q :=
    fun h₃ : q ∨ p =>
      have h₄ : q → p ∨ q :=
        fun h₅ : q => Or.intro_right p h₅
      have h₅ : p → p ∨ q :=
        fun h₆ : p => Or.intro_left q h₆
      h₃.elim h₄ h₅
  ⟨h₁, h₂⟩

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have h₁ : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    fun h₁ : (p ∧ q) ∧ r => ⟨h₁.1.1, ⟨h₁.1.2, h₁.2⟩⟩
  have h₂ : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    fun h₃ : p ∧ (q ∧ r) => ⟨⟨h₃.1, h₃.2.1⟩, h₃.2.2⟩
  ⟨h₁, h₂⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have h₁ : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    fun h₂ : (p ∨ q) ∨ r =>
      have h₃ : p ∨ q →  p ∨ (q ∨ r) :=
        fun h₄ : p ∨ q =>
          have h₅ : p → p ∨ (q ∨ r) :=
            fun h₆ : p => Or.intro_left (q ∨ r) h₆
          have h₆ : q → p ∨ (q ∨ r) :=
            fun h₇ : q => Or.intro_right p (Or.intro_left r h₇)
          h₄.elim h₅ h₆
      have h₄ : r → p ∨ (q ∨ r) :=
        fun h₅ : r => Or.intro_right p (Or.intro_right q h₅)
      h₂.elim h₃ h₄
  have h₂ : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    fun h₃ : p ∨ (q ∨ r) =>
      have h₄ : p → (p ∨ q) ∨ r :=
        fun h₅ : p => Or.intro_left r (Or.intro_left q h₅)
      have h₅ : q ∨ r → (p ∨ q) ∨ r :=
        fun h₆ : q ∨ r =>
          have h₇ : q → (p ∨ q) ∨ r :=
            fun h₈ : q => Or.intro_left r (Or.intro_right p h₈)
          have h₈ : r → (p ∨ q) ∨ r :=
            fun h₉ : r => Or.intro_right (p ∨ q) h₉
          h₆.elim h₇ h₈
      h₃.elim h₄ h₅
  ⟨h₁, h₂⟩

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have h₁ : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    fun h₂ : p ∧ (q ∨ r) =>
      have h₃ : q → (p ∧ q) ∨ (p ∧ r) :=
        fun h₄ : q => Or.intro_left (p ∧ r) ⟨h₂.1, h₄⟩
      have h₄ : r → (p ∧ q) ∨ (p ∧ r) :=
        fun h₅ : r => Or.intro_right (p ∧ q) ⟨h₂.1, h₅⟩
      have h₅ : q ∨ r → (p ∧ q) ∨ (p ∧ r) :=
        fun h₆ : q ∨ r => h₆.elim h₃ h₄
      h₅ h₂.2
  have h₂ : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
    fun h₃ : (p ∧ q) ∨ (p ∧ r) =>
      have h₄ : p ∧ q → p ∧ (q ∨ r) :=
        fun h₅ : p ∧ q => ⟨h₅.1, Or.intro_left r h₅.2⟩
      have h₅ : p ∧ r → p ∧ (q ∨ r) :=
        fun h₆ : p ∧ r => ⟨h₆.1, Or.intro_right q h₆.2⟩
      h₃.elim h₄ h₅
  ⟨h₁, h₂⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have h₁ : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
    fun h₂ : p ∨ (q ∧ r) =>
      have h₃ : p → (p ∨ q) ∧ (p ∨ r) :=
        fun h₄ : p => ⟨Or.intro_left q h₄, Or.intro_left r h₄⟩
      have h₄ : q ∧ r → (p ∨ q) ∧ (p ∨ r) :=
        fun h₅ : q ∧ r => ⟨Or.intro_right p h₅.1, Or.intro_right p h₅.2⟩
      h₂.elim h₃ h₄
  have h₂ : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
    fun h₃ : (p ∨ q) ∧ (p ∨ r) =>
      have h₄ : p → p ∨ (q ∧ r) :=
        fun h₅ : p => Or.intro_left (q ∧ r) h₅
      have h₅ : q → p ∨ (q ∧ r) :=
        fun h₆ : q =>
          have h₇ : r → p ∨ (q ∧ r) :=
            fun h₈ : r => Or.intro_right p ⟨h₆, h₈⟩
          h₃.2.elim h₄ h₇
      h₃.1.elim h₄ h₅
  ⟨h₁, h₂⟩

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  have h₁ : (p → (q → r)) → (p ∧ q → r) :=
    fun (h₂ : p → (q → r)) (h₃ : p ∧ q) => h₂ h₃.1 h₃.2
  have h₂ : (p ∧ q → r) → (p → (q → r)) :=
    fun (h₃ : p ∧ q → r) (h₄ : p) (h₅ : q) => h₃ ⟨h₄, h₅⟩
  ⟨h₁, h₂⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have h₁ : ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
    fun h₂ : ((p ∨ q) → r) =>
      have h₃ : p → r :=
        fun h₄ : p => h₂ (Or.intro_left q h₄)
      have h₄ : q → r :=
        fun h₅ : q => h₂ (Or.intro_right p h₅)
      ⟨h₃, h₄⟩
  have h₂ : (p → r) ∧ (q → r) → ((p ∨ q) → r) :=
    fun (h₃ : (p → r) ∧ (q → r)) (h₄ : p ∨ q) => h₄.elim h₃.1 h₃.2
  ⟨h₁, h₂⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have h₁ : ¬(p ∨ q) →  ¬p ∧ ¬q :=
    fun h₂ : ¬(p ∨ q) =>
      have h₃ : ¬p :=
        fun h₄ : p => h₂ (Or.intro_left q h₄)
      have h₄ : ¬q :=
        fun h₅ : q => h₂ (Or.intro_right p h₅)
      ⟨h₃, h₄⟩
  have h₂ : ¬p ∧ ¬q →  ¬(p ∨ q) :=
    fun (h₃ : ¬p ∧ ¬q) (h₄ : p ∨ q) => h₄.elim h₃.1 h₃.2
  ⟨h₁, h₂⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (h₁ :  ¬p ∨ ¬q) (h₂ : p ∧ q) =>
    have h₃ : ¬p → False :=
      fun h₄ : ¬p => h₄ h₂.1
    have h₄ : ¬q → False :=
      fun h₅ : ¬q => h₅ h₂.2
    h₁.elim h₃ h₄

example : ¬(p ∧ ¬p) :=
  fun h₁ : p ∧ ¬p => absurd h₁.1 h₁.2

example : p ∧ ¬q → ¬(p → q) :=
  fun (h₁ : p ∧ ¬q) (h₂ : p → q) => absurd (h₂ h₁.1) h₁.2

example : ¬p → (p → q) :=
  fun (h₁ : ¬p) (h₂ : p) => absurd h₂ h₁

example : (¬p ∨ q) → (p → q) :=
  fun (h₁ : ¬p ∨ q) (h₂ : p) =>
    have h₃ : ¬p → q :=
      fun h₄ : ¬p => absurd h₂ h₄
    h₁.elim h₃ id

example : p ∨ False ↔ p :=
  have h₁ : p ∨ False → p :=
    fun h₂ : p ∨ False => h₂.elim id False.elim
  have h₂ : p → p ∨ False :=
    fun h₃ : p => Or.intro_left False h₃
  ⟨h₁, h₂⟩

example : p ∧ False ↔ False :=
  have h₁ : p ∧ False → False :=
    fun h₂ : p ∧ False => h₂.2
  have h₂ : False → p ∧ False :=
    False.elim
  ⟨h₁, h₂⟩

example : (p → q) → (¬q → ¬p) :=
  fun (h₁ : p → q) (h₂ : ¬q) (h₃ : p) => h₂ (h₁ h₃)

section

  open Classical

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    fun h₁ : p → q ∨ r =>
      have h₂ : p → (p → q) ∨ (p → r) :=
        fun h₃ : p =>
          have h₄ : q ∨ r := h₁ h₃
          have h₅ : q → (p → q) ∨ (p → r) :=
            fun h₆ : q =>
              have h₇ : p → q :=
                fun _ => h₆
              Or.intro_left (p → r) h₇
          have h₆ : r → (p → q) ∨ (p → r) :=
            fun h₇ : r =>
              have h₈ : p → r :=
                fun _ => h₇
              Or.intro_right (p → q) h₈
          h₄.elim h₅ h₆
      have h₃ : ¬p → (p → q) ∨ (p → r) :=
        fun h₄ : ¬p =>
          have h₅ : p → q :=
            fun h₆ : p => absurd h₆ h₄
          Or.intro_left (p → r) h₅
      byCases h₂ h₃

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun h₁ :  ¬(p ∧ q) =>
      have h₂ : p → ¬p ∨ ¬q :=
        fun h₃ : p =>
          have h₄ : q → ¬p ∨ ¬q :=
            fun h₅ : q => absurd ⟨h₃, h₅⟩ h₁
          have h₅ : ¬q → ¬p ∨ ¬q :=
            fun h₆ : ¬q => Or.intro_right (¬p) h₆
          byCases h₄ h₅
      have h₃ : ¬p → ¬p ∨ ¬q :=
        fun h₄ : ¬p => Or.intro_left (¬q) h₄
      byCases h₂ h₃

  example : ¬(p → q) → p ∧ ¬q :=
    fun h₁ : ¬(p → q) =>
      have h₂ : p → p ∧ ¬q :=
        fun h₃ : p =>
          have h₄ : q → p ∧ ¬q :=
            fun h₅ : q =>
              have h₆ : p → q :=
                fun _ => h₅
              absurd h₆ h₁
          have h₅ : ¬q → p ∧ ¬q :=
            fun h₆ : ¬q => ⟨h₃, h₆⟩
          byCases h₄ h₅
      have h₃ : ¬p → p ∧ ¬q :=
        fun h₄ : ¬p =>
          have h₅ : p → q :=
            fun h₆ : p => absurd h₆ h₄
          absurd h₅ h₁
      byCases h₂ h₃

  example : (p → q) → (¬p ∨ q) :=
    fun h₁ : p → q =>
      have h₂ : p → ¬p ∨ q :=
        fun h₃ : p => Or.intro_right (¬p) (h₁ h₃)
      have h₃ : ¬p → ¬p ∨ q :=
        fun h₄ : ¬p => Or.intro_left q h₄
      byCases h₂ h₃

  example : (¬q → ¬p) → (p → q) :=
    fun (h₁ : ¬q → ¬p) (h₂ : p) =>
      have h₂ : ¬q → False :=
        fun h₃ : ¬q => absurd h₂ (h₁ h₃)
      byContradiction h₂

  example : p ∨ ¬p := em p

  example : (((p → q) → p) → p) :=
    fun h₁ : (p → q) → p =>
      have h₂ : ¬p → False :=
        fun h₃ : ¬p =>
          have h₄ : p → q :=
            fun h₅ : p => absurd h₅ h₃
          absurd (h₁ h₄) h₃
      byContradiction h₂

end

example : ¬(p ↔ ¬p) :=
  fun h₁ : p ↔ ¬p =>
    have h₂ : ¬p :=
      fun h₃ : p => absurd h₃ (h₁.1 h₃)
    have h₃ : p := h₁.2 h₂
    absurd h₃ h₂
