import Mathlib
structure myRat where
  num : Int
  den : Nat
  den_pos : 0 < den

instance : OfNat myRat 0 where
  ofNat := { num := 0, den := 1, den_pos := by decide }

instance : LE myRat where
  le r1 r2 := r1.num * r2.den ≤ r2.num * r1.den

instance : Add myRat where
  add r1 r2 := {
    num := r1.num * r2.den + r2.num * r1.den,
    den := r1.den * r2.den,
    den_pos := Nat.mul_pos r1.den_pos r2.den_pos
  }

lemma myRat_nonneg_iff (r : myRat) : 0 ≤ r ↔ 0 ≤ r.num := by
  constructor
  · intro h
    change (0 : myRat).num * r.den ≤ r.num * (0 : myRat).den at h
    change 0 * r.den ≤ r.num * 1 at h
    simp at h
    exact h
  · intro h
    change (0 : myRat).num * r.den ≤ r.num * (0 : myRat).den
    change 0 * r.den ≤ r.num * 1
    simp
    exact h

lemma myRat_add_nonneg (a b : myRat) :
    0 ≤ a → 0 ≤ b → 0 ≤  a + b := by
  intro ha hb

  cases a with | mk a_num a_den _  =>
  cases b with | mk b_num b_den _  =>

  simp only [myRat_nonneg_iff] at ha hb ⊢

  apply Int.add_nonneg
  · exact Int.mul_nonneg ha (Int.natCast_nonneg b_den)
  · exact Int.mul_nonneg hb (Int.natCast_nonneg a_den)

-- instance : Preorder myRat where
--   le r1 r2 := r1.num * r2.den ≤ r2.num * r1.den

  -- le_refl r := by
  --   apply Int.le_refl

  -- le_trans a b c := by
  --   intro h_ab h_bc

  --   -- Step 1 & 2: Get the expanded inequalities
  --   have h1 : a.num * ↑b.den * ↑c.den ≤ b.num * ↑a.den * ↑c.den :=
  --     Int.mul_le_mul_of_nonneg_right h_ab (Int.natCast_nonneg _)
  --   have h2 : b.num * ↑c.den * ↑a.den ≤ c.num * ↑b.den * ↑a.den :=
  --     Int.mul_le_mul_of_nonneg_right h_bc (Int.natCast_nonneg _)

  --   -- Step 3: Connect h1 and h2
  --   -- The RHS of h1 and LHS of h2 are equal by algebra. Prove this with `ring`.
  --   have h_mid_eq : b.num * ↑a.den * ↑c.den = b.num * ↑c.den * ↑a.den := by
  --     ring
  --   -- Now rewrite h1 so we can apply transitivity with h2
  --   rw [h_mid_eq] at h1
  --   have h3 := Int.le_trans h1 h2
  --   -- h3 is now: a.num * ↑b.den * ↑c.den ≤ c.num * ↑b.den * ↑a.den

  --   -- Step 4: THE CLEAN WAY TO REARRANGE FOR CANCELLATION
  --   -- Use `have` and `ring` to state the rearranged forms you want.
  --   have h_lhs : a.num * ↑b.den * ↑c.den = (a.num * ↑c.den) * ↑b.den := by
  --     ring
  --   have h_rhs : c.num * ↑b.den * ↑a.den = (c.num * ↑a.den) * ↑b.den := by
  --     ring

  --   -- Rewrite h3 using these proven equalities.
  --   rw [h_lhs, h_rhs] at h3
  --   -- h3 is now: (a.num * ↑c.den) * ↑b.den ≤ (c.num * ↑a.den) * ↑b.den

  --   -- Step 5: Cancel the positive term `↑b.den`
  --   exact le_of_mul_le_mul_right h3 (Int.natCast_pos.mpr b.den_pos)
