import Mathlib

-- lemma myRat_nonneg_iff (r : myRat) : 0 ≤ r ↔ 0 ≤ r.num := by
--   constructor <;> intro h
--   · change 0 * r.den ≤ r.num * 1 at h; simp at h; exact h
--   · change 0 * r.den ≤ r.num * 1; simp; exact h

-- lemma myRat_add_nonneg (a b : myRat) :
--     0 ≤ a → 0 ≤ b → 0 ≤  a + b := by
--   intro ha hb

--   cases a with | mk a_num a_den _  =>
--   cases b with | mk b_num b_den _  =>

--   simp only [myRat_nonneg_iff] at ha hb ⊢

--   apply Int.add_nonneg
--   · exact Int.mul_nonneg ha (Int.natCast_nonneg b_den)
--   · exact Int.mul_nonneg hb (Int.natCast_nonneg a_den)

-- instance : Preorder myRat where
--   le r₁ r₂ := r₁.num * r₂.den ≤ r₂.num * r₁.den

--   le_refl r := by
--     apply Int.le_refl

--   le_trans a b c := by
--     intro h_ab h_bc
--     have h1 : a.num * ↑b.den * ↑c.den ≤ b.num * ↑a.den * ↑c.den :=
--       Int.mul_le_mul_of_nonneg_right h_ab (Int.natCast_nonneg _)
--     have h2 : b.num * ↑c.den * ↑a.den ≤ c.num * ↑b.den * ↑a.den :=
--       Int.mul_le_mul_of_nonneg_right h_bc (Int.natCast_nonneg _)
--     have h_mid_eq : b.num * ↑a.den * ↑c.den = b.num * ↑c.den * ↑a.den := by
--       ring
--     rw [h_mid_eq] at h1
--     have h3 := Int.le_trans h1 h2
--     have h_lhs : a.num * ↑b.den * ↑c.den = (a.num * ↑c.den) * ↑b.den := by
--       ring
--     have h_rhs : c.num * ↑b.den * ↑a.den = (c.num * ↑a.den) * ↑b.den := by
--       ring
--     rw [h_lhs, h_rhs] at h3
--     exact le_of_mul_le_mul_right h3 (Int.natCast_pos.mpr b.den_pos)

-- example : myRat.mk 2 4 (by grind) ≠ myRat.mk 1 2 (by grind) := by simp


structure myRat where
  num : Int
  den : Nat -- i can use Int
  den_pos : 0 < den

instance : OfNat myRat 0 where -- 0 = 0/1
  ofNat := { num := 0, den := 1, den_pos := by decide }

instance : LE myRat where
  le r₁ r₂ := r₁.num * ↑r₂.den ≤ r₂.num * ↑r₁.den -- a/b ≤ c/d ↔ a*d ≤ c*b

instance : Add myRat where -- a/b + c/d ↔ (a*d + c*b) / b*d
  add r₁ r₂ := {
    num := r₁.num * ↑r₂.den + r₂.num * ↑r₁.den,
    den := r₁.den * r₂.den,
    den_pos := Nat.mul_pos r₁.den_pos r₂.den_pos
  }
instance myRel : Setoid myRat where
  r p q := p.num * q.den = q.num * p.den
  iseqv := by
    constructor
    · intro p
      rfl
    · rintro ⟨p, p', hp'⟩ ⟨q, q', hq'⟩
      simp [Eq.comm]
    · rintro ⟨p, p', hp'⟩ ⟨q, q', hq'⟩ ⟨r, r', hr'⟩ hpq hqr
      simp_all
      apply mul_left_cancel₀ (mod_cast hq'.ne' : q' ≠ (0 : ℤ))
      -- use iunjectivity of integer multiplicartion mul_left_cancel₀
      grind

abbrev myBetterRat : Type := Quotient myRel



example : (⟦.mk 2 4 (by grind)⟧ : myBetterRat)
= (⟦.mk 1 2 (by grind)⟧ : myBetterRat) := by
simp only [Quotient.eq, myRel]
grind


theorem factorsLE (a₁ b₁ a₂ b₂ : myRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  intro ha hb
  change myRel a₁ a₂ at ha
  change myRel b₁ b₂ at hb
  dsimp only [myRel] at ha hb

  simp only [eq_iff_iff]
  constructor
  · intro h
    -- if a₁ ≤ b₁, then a₂ ≤ b₂
    -- if a₁.num b₁.den ≤ b₁.num a₁.den , then a₂.num * b₂.den ≤ b₂.num a₂.den
    have pos_a₁ : 0 < (a₁.den : Int) := by exact_mod_cast a₁.den_pos
    have pos_b₁ : 0 < (b₁.den : Int) := by exact_mod_cast b₁.den_pos
    have pos_prod : (0: Int) < (a₁.den * b₁.den ) := mul_pos pos_a₁ pos_b₁

    -- Multiply both sides of h by (a₂.den * b₂.den) which is positive
    --- i was actually multiply (a₂.den * b₂.num) on paper strange
    have pos_a₂ : 0 < (a₂.den : Int) := by exact_mod_cast a₂.den_pos
    have pos_b₂ : 0 < (b₂.den : Int) := by exact_mod_cast b₂.den_pos
    have pos_prod2 : 0 < (a₂.den * b₂.den : Int) := mul_pos pos_a₂ pos_b₂

    -- need to cancel (a₁.den * b₁.den) from the inequality
    --- multiplication of pos does not change the order
    apply Int.le_of_mul_le_mul_right _ pos_prod

    calc (a₂.num * b₂.den) * (a₁.den * b₁.den)
        = a₂.num * a₁.den * b₂.den * b₁.den := by ring
      _ = a₁.num * a₂.den * b₂.den * b₁.den := by rw [← ha]
      _ = a₁.num * b₁.den * (a₂.den * b₂.den) := by ring
      _ ≤ b₁.num * a₁.den * (a₂.den * b₂.den) :=
         Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt pos_prod2)
      _ = b₁.num * b₂.den * a₁.den * a₂.den := by ring
      _ = b₂.num * b₁.den * a₁.den * a₂.den := by rw [← hb]
      _ = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by ring

  · intro h
    -- Backward: symmetric
    have pos_a₁ : 0 < (a₁.den : Int) := by exact_mod_cast a₁.den_pos
    have pos_b₁ : 0 < (b₁.den : Int) := by exact_mod_cast b₁.den_pos
    have pos_prod : 0 < (a₁.den * b₁.den : Int) := mul_pos pos_a₁ pos_b₁

    have pos_a₂ : 0 < (a₂.den : Int) := by exact_mod_cast a₂.den_pos
    have pos_b₂ : 0 < (b₂.den : Int) := by exact_mod_cast b₂.den_pos
    have pos_prod2 : 0 < (a₂.den * b₂.den : Int) := mul_pos pos_a₂ pos_b₂

    apply Int.le_of_mul_le_mul_right _ pos_prod2

    calc (a₁.num * b₁.den) * (a₂.den * b₂.den)
        = a₁.num * a₂.den * b₁.den * b₂.den := by ring
      _ = a₂.num * a₁.den * b₁.den * b₂.den := by rw [ha]
      _ = a₂.num * b₂.den * (a₁.den * b₁.den) := by ring
      _ ≤ b₂.num * a₂.den * (a₁.den * b₁.den) := by
          exact Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt pos_prod)
      _ = b₂.num * b₁.den * a₂.den * a₁.den := by ring
      _ = b₁.num * b₂.den * a₂.den * a₁.den := by rw [hb]
      _ = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by ring

instance : LE myBetterRat where
  le r₁ r₂ := Quotient.lift₂ (fun a b ↦ a ≤ b) (factorsLE) r₁ r₂ -- a/b ≤ c/d ↔ a*d ≤ c*b

instance : PartialOrder myBetterRat where
  le p q := Quotient.lift₂ (fun a b ↦ a ≤ b) (factorsLE) p q

  le_refl p := by
   sorry


  le_trans p q r := by
    intro h_ab h_bc
    sorry


  le_antisymm p q := by
    intro h_ab h_ba
    sorry

theorem instPreorderMyBetterRat.reflexive (r : myBetterRat) :
  Quotient.lift₂ (fun a b ↦ a ≤ b) factorsLE r r := by

   sorry
theorem instPreorderMyBetterRat.trans (a b c : myBetterRat) :
  Quotient.lift₂ (fun a b ↦ a ≤ b) factorsLE a b →
    Quotient.lift₂ (fun a b ↦ a ≤ b) factorsLE b c → Quotient.lift₂ (fun a b ↦ a ≤ b) factorsLE a c := sorry

instance : Preorder myBetterRat where
  le r₁ r₂ := Quotient.lift₂ (fun a b ↦ a ≤ b) (factorsLE) r₁ r₂ -- a/b ≤ c/d ↔ a*d ≤ c*b

  le_refl r := by apply instPreorderMyBetterRat.reflexive

  le_trans a b c := by apply instPreorderMyBetterRat.trans
