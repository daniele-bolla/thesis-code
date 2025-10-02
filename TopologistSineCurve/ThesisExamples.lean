import Mathlib
-- def Transitive {α : Type} (R : α → α → Prop) : Prop :=
--   ∀ x y z, R x y → R y z → R x z
theorem le_trans_proof : Transitive (· ≤ · : Nat → Nat → Prop) :=
  fun x y z h1 h2 => Nat.le_trans h1 h2
theorem nat_le_trans {n m k : Nat} : LE.le n m → LE.le m k → LE.le n k
  | h,  Nat.le.refl    => h
  | h₁, Nat.le.step h₂ => Nat.le.step (Nat.le_trans h₁ h₂)
theorem rational_le_trans : Transitive (· ≤ · : Rat → Rat → Prop) := by
  intro a b c hab hbc
  exact Rat.le_trans hab hbc
def half : Rat := Rat.mk' 1 2
def third : Rat := Rat.mk' 1 3
-- #eval evaluate the expression and print the result
#eval half.den -- outputs 2
#eval half + third -- outputs 5/6
-- #check prints the type of an expression
#check half.den -- outputs : Nat
#check half -- outputs : Rat
#check half + third -- outputs : Rat

variable (a b c : Rat)
-- Old code:
-- open Rat
-- lemma add_nonneg_simplified : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
--   intro ha hb
--   -- rw [Rat.divInt_nonneg_iff_of_pos_right]
--   -- Convert hypotheses to numerator conditions
--   rw [← num_nonneg] at ha hb
--   -- Express rationals in divInt form and apply addition formula
--   rw [← num_divInt_den a, ← num_divInt_den b, divInt_add_divInt]
--   -- Use divInt_nonneg_iff_of_pos_right to reduce to integer arithmetic
--   · rw [Rat.divInt_nonneg_iff_of_pos_right]
--     · -- Prove numerator ≥ 0
--       exact Int.add_nonneg (Int.mul_nonneg ha (Int.natCast_nonneg _))
--                            (Int.mul_nonneg hb (Int.natCast_nonneg _))
--     · -- Prove denominator > 0
--       norm_cast
--       exact Nat.mul_pos (Nat.pos_of_ne_zero a.den_nz) (Nat.pos_of_ne_zero b.den_nz)
--   · norm_cast; exact a.den_nz
--   norm_cast; exact b.den_nz
-- End old code

-- Proving add_nonneg by reconstructing some Rat theorems needed and
-- the addition definition

-- this is probably used to ensure the addition formula is well defined
-- theorem rat_divInt_eq_iff (n₁ n₂ :Int)(d₁ d₂ :Nat)(z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
--     n₁ /. d₁ = n₂ /. d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
--   sorry
-- lemma rat_divInt_nonneg_iff_of_pos_right {a b : ℤ} (hb : 0 < b) :
--   0 ≤ a / b ↔ 0 ≤ a := b
--       sorry
-- theorem rat_den_pos (q : Rat) : 0 < q.den := Nat.pos_of_ne_zero q.den_nz
-- lemma rat_num_nonneg (q : Rat) : 0 ≤ q.num ↔ 0 ≤ q := by
--   cases q with | div q_num q_den q_den_nz q_num_cop_den =>
--     constructor
--     · intro h_num_nonneg
--       sorry
--     · intro h_rat_nonneg
--       by_contra hn
--       push_neg at hn
--       have h_den_pos : 0 < q_den := by
--       sorry
-- lemma rat_add_num (a b : Rat) :  a + b =
--  (a.num * ↑b.den + b.num * ↑a.den) / (↑a.den * ↑b.den) := by
--   cases b with | div b_num b_den b_den_nz b_num_cop_den =>
--   cases a with | div a_num a_den a_den_nz a_num_cop_den =>
--   sorry

-- def rat_add (a b : Rat) : Rat := (a.num * b.den + b.num * a.den) / (a.den * b.den)

-- lemma add_nonneg_simp : 0 ≤ a → 0 ≤ b → 0 ≤  rat_add a b := by
--   intro ha hb
--   cases b with | div b_num b_den b_den_nz b_num_cop_den =>
--   cases a with | div a_num a_den a_den_nz a_num_cop_den =>
--   unfold rat_add
--   have h_a_den_pos : 0 < a_den := sorry
--   have h_b_den_pos : 0 < b_den := sorry
--   rw[rat_divInt_nonneg_iff_of_pos_right]

--   have ha_num_nonneg : 0 ≤ a_num := by
--     have h_a_den_pos : (0: ℤ) < ↑a_den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero a_den_nz)
--     rw [← rat_divInt_nonneg_iff_of_pos_right h_a_den_pos]
--     norm_cast at ha;

--   have hb_num_nonneg : 0 ≤ b_num := by
--     have h_b_den_pos : (0: ℤ) < ↑b_den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero b_den_nz)
--     rw [← rat_divInt_nonneg_iff_of_pos_right h_b_den_pos]
--     norm_cast at hb;

--   · refine Int.add_nonneg ?_ ?_
--     · refine Int.mul_nonneg ha_num_nonneg  ?_
--       · exact Int.natCast_nonneg b_den
--     · refine Int.mul_nonneg hb_num_nonneg  ?_
--       · exact Int.natCast_nonneg a_den
--   · refine Int.mul_pos ?_ ?_
--     · norm_cast;
--     · norm_cast;
-- #check @Rat.add
-- #print Rat.add



-- Porving Rat.add_nonneg withouth using any lemmas or theorems from Rat
-- I am anyway using @Algebra/Order/Field/Basic.lean and tactics like positivity or ring
-- Helper: positive denominators
lemma rat_den_pos (den : ℕ) (h_den_nz : den ≠ 0) : 0 < den :=
  Nat.pos_of_ne_zero h_den_nz
-- Helper: non-negative numerator from non-negative rational
-- here i am using @Algebra/Order/Field/Basic.lean div_neg_of_neg_of_pos
lemma num_nonneg_of_div_nonneg {num : ℤ} {den : ℕ} (hden : 0 < den)
    (h : 0 ≤ (num : ℚ) / den) : 0 ≤ num := by
    -- probably this part help with the coercion with the all expression (num : ℚ)
    -- how should i handle it?
  contrapose! h
  exact div_neg_of_neg_of_pos (by norm_cast) (by norm_cast : (0 : ℚ) < ↑den)
-- Helper: addition formula for rationals
-- here i am using @Algebra/Order/Field/Basic.lean div_add_div

lemma rat_add_formula {a c : ℤ} {b d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℚ) / ↑b + c / ↑d = (a * ↑d + c * ↑b) / (↑b * ↑d) := by
    rw [div_add_div]
    · ring
    · norm_cast;
    · norm_cast;
    -- or i can just use field_simp (and explain what it does )
-- Main theorem: addition preserves non-negativity
lemma rat_add_nonneg (a b : Rat) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha hb
  cases a with | div a_num a_den a_den_nz a_cop =>
  cases b with | div b_num b_den b_den_nz b_cop =>
  -- when i deconstruct a and b in this way the goal becomes:
  -- ⊢ 0 ≤ ↑a_num / ↑a_den + ↑b_num / ↑b_den
  -- type coercions are foricng both num and den to be of type ℚ
  -- i guess this is happening due to the operator "/" (HDiv.hDiv)?
  -- is there a better approach? maybe using rcases?
  -- rcases b with ⟨ b_num, b_den, b_den_nz, b_cop ⟩
  have ha_den_pos := rat_den_pos a_den a_den_nz
  have hb_den_pos := rat_den_pos b_den b_den_nz
  have ha_num_nonneg := num_nonneg_of_div_nonneg ha_den_pos ha
  have hb_num_nonneg := num_nonneg_of_div_nonneg hb_den_pos hb

  rw [rat_add_formula a_den_nz b_den_nz]
  positivity -- would it be ok top use this?
  -- have h_num_nonneg : (0 : ℚ) ≤ a_num * ↑b_den + b_num * ↑a_den := by
  --   norm_cast
  --   apply Int.add_nonneg
  --   · apply Int.mul_nonneg ha_num_nonneg (Int.natCast_nonneg b_den)
  --   · apply Int.mul_nonneg hb_num_nonneg (Int.natCast_nonneg a_den)

  -- have h_den_pos : (0 : ℚ) < ↑a_den * ↑b_den := by
  --   norm_cast
  --   apply Nat.mul_pos ha_den_pos hb_den_pos

  -- exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)


-- Type classes section

-- -- A semigroup has an associative binary operation
-- class SemigroupD (α : Type*) where
--   mul : α → α → α
--   mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
-- -- A monoid extends semigroup with an identity element
-- class MonoidD (α : Type*) extends Semigroup α where
--   one : α
--   one_mul : ∀ a : α, mul one a = a
--   mul_one : ∀ a : α, mul a one = a
-- -- A group extends monoid with inverses
-- class GroupD (α : Type*) extends Monoid α where
--   inv : α → α
--   mul_left_inv : ∀ a : α, mul (inv a) a = one

-- instance RatAddGroup : GroupD Rat where
--   mul := (· + ·)
--   mul_assoc := by intros; apply add_assoc
--   one := 0
--   one_mul := by intros; apply zero_add
--   mul_one := by intros; apply add_zero
--   inv := (· * -1)
--   mul_left_inv := by intros; ring
