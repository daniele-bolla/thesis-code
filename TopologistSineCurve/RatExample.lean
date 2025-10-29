import Mathlib

-- ========================================
-- Section 1: Basic Rational Type
-- ========================================

structure myPreRat where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace myPreRat

-- Basic operations on raw rationals
instance : LE myPreRat where
  le r₁ r₂ := r₁.num * ↑r₂.den ≤ r₂.num * ↑r₁.den

instance : Add myPreRat where
  add r₁ r₂ := {
    num := r₁.num * ↑r₂.den + r₂.num * ↑r₁.den,
    den := r₁.den * r₂.den,
    den_pos := Nat.mul_pos r₁.den_pos r₂.den_pos
  }

-- Zero as a raw rational
def zero : myPreRat := { num := 0, den := 1, den_pos := by decide }

-- Helper lemmas
lemma den_pos_int (r : myPreRat) : 0 < (r.den : Int) := by
  rw [Int.natCast_pos]
  exact r.den_pos

lemma den_prod_pos (r₁ r₂ : myPreRat) : 0 < (r₁.den * r₂.den : Int) := by
  exact mul_pos r₁.den_pos_int r₂.den_pos_int

lemma nonneg_iff (r : myPreRat) : zero ≤ r ↔ 0 ≤ r.num := by
  simp [zero, LE.le]
-- lemma nonneg_iff (r : myPreRat) : zero ≤ r ↔ 0 ≤ r.num := by
--   constructor <;> intro h
--   · change 0 * r.den ≤ r.num * 1 at h; simp at h; exact h
--   · change 0 * r.den ≤ r.num * 1; simp; exact h

lemma add_nonneg (a b : myPreRat) : zero ≤ a → zero ≤ b → zero ≤ a + b := by
  intro ha hb
  -- cases a with | mk a_num a_den _ =>
  -- cases b with | mk b_num b_den _ =>
  simp only [nonneg_iff] at ha hb ⊢
  apply Int.add_nonneg
  · exact Int.mul_nonneg ha (Int.natCast_nonneg b.den)
  · exact Int.mul_nonneg hb (Int.natCast_nonneg a.den)

-- PartialOrder properties
theorem le_refl (a : myPreRat) : a ≤ a := by
  -- change a.num * ↑a.den ≤ a.num * ↑a.den
  exact Int.le_refl _

/--
Transitivity of ≤ on pre-rationals.
If a ≤ b and b ≤ c, then a ≤ c.

In fraction notation: if a/a.den ≤ b/b.den and b/b.den ≤ c/c.den,
then a/a.den ≤ c/c.den.

Key insight: We multiply everything by b.den (which is positive) to create
a "bridge" between the two inequalities through their common middle term b.
-/
theorem le_trans (a b c : myPreRat) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  -- hab : a ≤ b, which means: a.num * b.den ≤ b.num * a.den
  -- hbc : b ≤ c, which means: b.num * c.den ≤ c.num * b.den
  -- Goal: a ≤ c, which means: a.num * c.den ≤ c.num * a.den
  -- Strategy: Prove (a.num * c.den) * b.den ≤ (c.num * a.den) * b.den
  -- then cancel the positive factor b.den from both sides
  apply Int.le_of_mul_le_mul_right _ b.den_pos_int
  -- Now we need: (a.num * c.den) * b.den ≤ (c.num * a.den) * b.den
  calc (a.num * c.den) * b.den
      -- Step 1: Rearrange to introduce a.num * b.den
      -- Why? Because hab involves a.num * b.den
      = (a.num * b.den) * c.den := by ring
      -- Step 2: Apply first inequality hab
      -- We know: a.num * b.den ≤ b.num * a.den
      -- Multiply both sides by positive c.den to preserve inequality
    _ ≤ (b.num * a.den) * c.den :=
        Int.mul_le_mul_of_nonneg_right hab (Int.le_of_lt c.den_pos_int)
        -- This gives us b in the "middle position"
      -- Step 3: Rearrange to introduce b.num * c.den
      -- Why? Because hbc involves b.num * c.den
    _  = (b.num * c.den) * a.den := by ring
      -- Step 4: Apply second inequality hbc
      -- We know: b.num * c.den ≤ c.num * b.den
      -- Multiply both sides by positive a.den to preserve inequality
    _ ≤ (c.num * b.den) * a.den :=
        Int.mul_le_mul_of_nonneg_right hbc (Int.le_of_lt a.den_pos_int)
        -- Now we have c in the final position
      -- Step 5: Rearrange to match the form needed for cancellation
    _ = (c.num * a.den) * b.den := by ring

  -- Final: We proved (a.num * c.den) * b.den ≤ (c.num * a.den) * b.den
  -- Cancel b.den (which is positive) from both sides to get a ≤ c

-- instance : HasEquiv myPreRat := ⟨fun p q => p.num * q.den = q.num * p.den⟩

theorem le_antisymm (a b : myPreRat) : a ≤ b → b ≤ a → a.num * b.den = b.num * a.den := by
  intro hab hba
  exact Int.le_antisymm hab hba

end myPreRat

-- ========================================
-- Section 2: Equivalence Relation
-- ========================================

instance myRel : Setoid myPreRat where
  r p q := p.num * q.den = q.num * p.den
  iseqv := by
    constructor
    · intro p; rfl
    · rintro ⟨p, p', hp'⟩ ⟨q, q', hq'⟩
      simp [Eq.comm]
    · rintro ⟨p, p', hp'⟩ ⟨q, q', hq'⟩ ⟨r, r', hr'⟩ hpq hqr
      simp_all
      apply mul_left_cancel₀ (mod_cast hq'.ne' : q' ≠ (0 : ℤ))
      grind

-- ========================================
-- Section 3: Respect Proofs (Operations preserve equivalence)
-- ========================================

theorem myRel_respects_le (a₁ b₁ a₂ b₂ : myPreRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  intro ha hb
  simp only [eq_iff_iff]
  constructor
  · intro h
    -- goal is ⊢ a₂ ≤ b₂ or similarly (need to explain why )
    -- is like ⊢ a₂.num * b₂.den  ≤ b₂.num * a₂.den
    -- We multiply both sides by a₂.den * b₂.den
    -- wich is positive and preserves order
    have pos_prod : (0: Int) < (a₁.den * b₁.den ) := myPreRat.den_prod_pos a₁ b₁
    have pos_prod2 : 0 < (a₂.den * b₂.den : Int) := myPreRat.den_prod_pos a₂ b₂
    apply Int.le_of_mul_le_mul_right _ pos_prod
    -- (a₂.num * b₂.den) * (a₁.den * b₁.den) ≤ (b₂.num * a₂.den) * (a₁.den * b₁.den)
    -- Then cancel the positive factor (a₁.den * b₁.den) from both sides
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
    -- similar
    have pos_prod : 0 < (a₁.den * b₁.den : Int) := myPreRat.den_prod_pos a₁ b₁
    have pos_prod2 : 0 < (a₂.den * b₂.den : Int) := myPreRat.den_prod_pos a₂ b₂
    apply Int.le_of_mul_le_mul_right _ pos_prod2
    calc (a₁.num * b₁.den) * (a₂.den * b₂.den)
        = a₁.num * a₂.den * b₁.den * b₂.den := by ring
      _ = a₂.num * a₁.den * b₁.den * b₂.den := by rw [ha]
      _ = a₂.num * b₂.den * (a₁.den * b₁.den) := by ring
      _ ≤ b₂.num * a₂.den * (a₁.den * b₁.den) :=
          Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt pos_prod)
      _ = b₂.num * b₁.den * a₂.den * a₁.den := by ring
      _ = b₁.num * b₂.den * a₂.den * a₁.den := by rw [hb]
      _ = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by ring

private theorem le_respects_equiv_forward
    (a₁ b₁ a₂ b₂ : myPreRat)
    (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
    (h : a₁ ≤ b₁) : a₂ ≤ b₂ := by
  have pos_prod : (0: Int) < (a₁.den * b₁.den) := myPreRat.den_prod_pos a₁ b₁
  have pos_prod2 : 0 < (a₂.den * b₂.den : Int) := myPreRat.den_prod_pos a₂ b₂
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

theorem myRel_respects_le_ref (a₁ b₁ a₂ b₂ : myPreRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  intro ha hb
  simp only [eq_iff_iff]
  constructor
  · -- Forward: a₁ ≤ b₁ → a₂ ≤ b₂
    exact le_respects_equiv_forward a₁ b₁ a₂ b₂ ha hb
  · -- Backward: a₂ ≤ b₂ → a₁ ≤ b₁
    -- Note: equivalence is symmetric (a₁ ≈ a₂ implies a₂ ≈ a₁)
    intro h
    have ha_symm : a₂ ≈ a₁ := Eq.symm ha
    have hb_symm : b₂ ≈ b₁ := Eq.symm hb
    exact le_respects_equiv_forward a₂ b₂ a₁ b₁ ha_symm hb_symm h

/--
Proof that addition respects the equivalence relation.
If a₁ ≈ a₂ and b₁ ≈ b₂, then (a₁ + b₁) ≈ (a₂ + b₂).

Strategy: Expand both sides of the equivalence using the definition of addition,
then use ha and hb to transform the left side into the right side.
-/
theorem myRel_respects_add (a₁ b₁ a₂ b₂ : myPreRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ + b₁) ≈ (a₂ + b₂) := by
  intro ha hb
  -- ha : a₁.num * a₂.den = a₂.num * a₁.den  (a₁ and a₂ represent same rational)
  -- hb : b₁.num * b₂.den = b₂.num * b₁.den  (b₁ and b₂ represent same rational)
  -- Goal: (a₁ + b₁) ≈ (a₂ + b₂)
  -- This means: (a₁ + b₁).num * (a₂ + b₂).den = (a₂ + b₂).num * (a₁ + b₁).den
  -- Recall addition definition:
  -- (a + b).num = a.num * b.den + b.num * a.den
  -- (a + b).den = a.den * b.den
  -- So we need to prove:
  -- (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den)
  --   = (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den)
  calc (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den)
      -- Left side: (a₁ + b₁).num * (a₂ + b₂).den
      -- Step 1: Distribute the product over the sum
      = a₁.num * b₁.den * a₂.den * b₂.den + b₁.num * a₁.den * a₂.den * b₂.den := by ring
      -- Step 2: Use equivalence relations to transform
      -- Apply ha: replace a₁.num * a₂.den with a₂.num * a₁.den
      -- Apply hb: replace b₁.num * b₂.den with b₂.num * b₁.den
      -- This "swaps" the first and second rational in each term
    _ = a₂.num * a₁.den * b₁.den * b₂.den + b₂.num * b₁.den * a₁.den * a₂.den := by
        rw [← ha, ← hb]; ring
      -- Step 3: Factor back into sum times product form
      -- This gives us (a₂ + b₂).num * (a₁ + b₁).den
    _ = (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den) := by ring
      -- Right side: (a₂ + b₂).num * (a₁ + b₁).den

-- ========================================
-- Section 4: Quotient Type and Lifted Operations
-- ========================================

abbrev myRat : Type := Quotient myRel

namespace myRat

instance : LE myRat where
  le r₁ r₂ := Quotient.lift₂ (fun a b ↦ a ≤ b) myRel_respects_le r₁ r₂

instance : Add myRat where
  add r₁ r₂ := Quotient.lift₂ (fun a b ↦ ⟦a + b⟧)
    (fun a₁ b₁ a₂ b₂ ha hb ↦ Quotient.sound (myRel_respects_add a₁ b₁ a₂ b₂ ha hb))
    r₁ r₂

instance : OfNat myRat 0 where
  ofNat := ⟦myPreRat.zero⟧

-- ========================================
-- Section 5: Lifted Properties
-- ========================================

lemma add_nonneg (a b : myRat) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  intro ha hb
  exact myPreRat.add_nonneg a b ha hb

-- ========================================
-- Section 6: Algebraic Structures
-- ========================================

instance : PartialOrder myRat where
  le_refl p := by
    induction p using Quotient.ind with | _ a =>
    exact myPreRat.le_refl a

  le_trans p q r := by
    induction p using Quotient.ind with | _ a =>
    induction q using Quotient.ind with | _ b =>
    induction r using Quotient.ind with | _ c =>
    intro hab hbc
    exact myPreRat.le_trans a b c hab hbc

  le_antisymm p q := by
    induction p using Quotient.ind with | _ a =>
    induction q using Quotient.ind with | _ b =>
    intro hab hba
    exact Quotient.sound (myPreRat.le_antisymm a b hab hba)

end myRat
