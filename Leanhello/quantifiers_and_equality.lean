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

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
