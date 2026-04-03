variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  ⟨
    fun h : p ∧ q => ⟨h.2, h.1⟩,
    fun h : q ∧ p => ⟨h.2, h.1⟩
  ⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨
    fun h: p ∨ q =>
      h.elim
        (fun hp => Or.intro_right q hp)
        (fun hq => Or.intro_left p hq),
    fun h: q ∨ p =>
      h.elim
        (fun hq => Or.intro_right p hq)
        (fun hp => Or.intro_left q hp)
  ⟩

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨
    fun h : (p ∧ q) ∧ r => ⟨ h.1.1, ⟨ h.1.2, h.2 ⟩ ⟩,
    fun h : p ∧ (q ∧ r) => ⟨ ⟨ h.1, h.2.1 ⟩, h.2.2 ⟩
  ⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
    fun h : (p ∨ q) ∨ r =>
      show p ∨ (q ∨ r) from
      h.elim
        (fun hpq : p ∨ q =>
          show p ∨ (q ∨ r) from
          hpq.elim
            (fun hp : p => Or.intro_left (q ∨ r) hp)
            (fun hq : q =>
              have hqr : q ∨ r := Or.intro_left r hq
              show p ∨ (q ∨ r) from Or.intro_right p hqr))
        (fun hr : r =>
          have hqr : q ∨ r := Or.intro_right q hr
          show p ∨ (q ∨ r) from Or.intro_right p hqr),
    fun h : p ∨ (q ∨ r) =>
      show (p ∨ q) ∨ r from
      h.elim
        (fun hp : p =>
          have hpq : p ∨ q := Or.intro_left q hp
          show (p ∨ q) ∨ r from Or.intro_left r hpq)
        (fun hqr : q ∨ r =>
          show (p ∨ q) ∨ r from
          hqr.elim
            (fun hq : q =>
              have hpq : p ∨ q := Or.intro_right p hq
              show (p ∨ q) ∨ r from Or.intro_left r hpq)
            (fun hr : r => Or.intro_right (p ∨ q) hr)),
  ⟩

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨
    fun h: p ∧ (q ∨ r) =>
      have hqr : q ∨ r := h.2
      hqr.elim
        (fun hq : q =>
          have hpq : p ∧ q := ⟨ h.1, hq ⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) hpq )
        (fun hr : r =>
          have hpr : p ∧ r := ⟨ h.1, hr ⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) hpr),
    fun h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (fun hpq : p ∧ q => ⟨ hpq.1, Or.intro_left r hpq.2 ⟩ )
        (fun hpr : p ∧ r => ⟨ hpr.1, Or.intro_right q hpr.2 ⟩ ),

  ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    fun h : p ∨ (q ∧ r) =>
      show (p ∨ q) ∧ (p ∨ r) from
      h.elim
        (fun hp : p => ⟨ Or.intro_left q hp, Or.intro_left r hp ⟩ )
        (fun hqr : q ∧ r => ⟨ Or.intro_right p hqr.1, Or.intro_right p hqr.2 ⟩ ),
    fun h : (p ∨ q) ∧ (p ∨ r) =>
      show p ∨ (q ∧ r) from
      h.1.elim
        (fun hp : p => Or.intro_left (q ∧ r) hp)
        (fun hq : q =>
          h.2.elim
            (fun hp : p => Or.intro_left (q ∧ r) hp)
            (fun hr : r => Or.intro_right p ⟨ hq, hr ⟩ ))

  ⟩

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    fun h : p → (q → r) =>
      fun hpq : p ∧ q =>
        show r from h hpq.1 hpq.2,
    fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          show r from h ⟨ hp, hq ⟩
  ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    fun h : (p ∨ q) → r =>
      ⟨
        fun hp : p =>
          show r from h (Or.intro_left q hp),
        fun hq : q =>
          show r from h (Or.intro_right p hq)
      ⟩,
    fun h : (p → r) ∧ (q → r) =>
      fun hpq : p ∨ q =>
        show r from
        hpq.elim
          (fun hp : p =>
            show r from h.1 hp)
          (fun hq : q =>
            show r from h.2 hq)
  ⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    fun h : ¬(p ∨ q) =>
      ⟨
        fun hp : p =>
          show False from h (Or.intro_left q hp),
        fun hq : q =>
          show False from h (Or.intro_right p hq)
      ⟩,
    fun h : ¬p ∧ ¬q =>
      fun hpq : p ∨ q =>
        show False from
        hpq.elim
          (fun hp : p => h.1 hp)
          (fun hq : q => h.2 hq)
  ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
    fun hpq : p ∧ q =>
      show False from
      h.elim
        (fun hnp : ¬p => hnp hpq.1)
        (fun hnq : ¬q => hnq hpq.2)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p =>
    show False from absurd h.1 h.2

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
    fun hpq : p → q =>
      show False from absurd (hpq h.1) h.2

example : ¬p → (p → q) :=
  fun h : ¬p =>
    fun hp : p =>
      show q from absurd hp h

example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
    fun hp : p =>
      show q from
      h.elim
        (fun hnp : ¬p => absurd hp hnp)
        (fun hq : q => hq)

example : p ∨ False ↔ p :=
  ⟨
    fun h : p ∨ False =>
      h.elim (fun hp : p => hp) (fun False => False.elim),
    fun h : p =>
      Or.intro_left False h
  ⟩

example : p ∧ False ↔ False :=
  ⟨
    fun h : p ∧ False => h.2,
    fun False => False.elim
  ⟩

example : (p → q) → (¬q → ¬p) :=
  fun h : p → q =>
    fun hnq : ¬q =>
      fun hp : p =>
        show False from
        absurd (h hp) hnq

section

  open Classical

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    fun h : p → q ∨ r =>
      (em q).elim
        (fun hq : q =>
          have hpq : p → q := fun _ : p => hq
          show (p → q) ∨ (p → r) from Or.intro_left (p → r) hpq)
        (fun hnq : ¬q =>
          have hpr : p → r :=
          fun hp : p =>
            have hqr : q ∨ r := h hp
            hqr.elim (fun hq : q => absurd hq hnq) (fun hr : r => hr)
          show (p → q) ∨ (p → r) from Or.intro_right (p → q) hpr)



  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    fun h : ¬(p ∧ q) =>
      (em p).elim
        (fun hp : p =>
          (em q).elim
            (fun hq : q => False.elim (h ⟨hp, hq⟩))
            (fun hnq : ¬q => Or.intro_right (¬p) hnq)
        )
        (fun hnp : ¬p => Or.intro_left (¬q) hnp)


  example : ¬(p → q) → p ∧ ¬q :=
    fun h : ¬(p → q) =>
      ⟨
        show p from
        (em q).elim
          (fun hq : q =>
            have hpq : p → q := (fun _ : p => hq)
            False.elim (h hpq))
          (fun _ : ¬q =>
            (em p).elim
              (fun hp : p => hp)
              (fun hnp : ¬p =>
                have hpq : p → q := fun hp : p => absurd hp hnp
                False.elim (h hpq))),
        show ¬q from
        fun hq : q =>
          show False from
          h fun _ : p => hq
      ⟩

  example : (p → q) → (¬p ∨ q) :=
    fun h : p → q =>
      (em q).elim
        (fun hq : q => Or.intro_right (¬p) hq)
        (fun hnq : ¬q =>
          (em p).elim
            (fun hp : p => absurd (h hp) hnq)
            (fun hnp : ¬p => Or.intro_left q hnp))


  example : (¬q → ¬p) → (p → q) :=
    fun h : ¬q → ¬p =>
      fun hp : p =>
        show q from
        (em q).elim
          (fun hq : q => hq)
          (fun hnq : ¬q => absurd (hp) (h hnq))

  example : p ∨ ¬p := em p

  example : (((p → q) → p) → p) :=
    fun h : (p → q) → p =>
      show p from
      (em p).elim
        (fun hp : p => hp)
        (fun hnp : ¬p =>
          have hpq : p → q := fun hp : p => show q from absurd hp hnp
          absurd (h hpq) hnp)

end

example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    show False from
    have hnp : ¬p := fun hp : p => absurd hp (h.1 hp)
    have hp : p := h.2 hnp
    absurd hp hnp
