import Mathlib

-- ========================================
-- Section 1: Basic Pre Rational Type
-- ========================================

structure myPreRat where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace myPreRat

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
instance : OfNat myPreRat 0 where
  ofNat := zero
-- Helper lemmas
lemma den_pos_int (r : myPreRat) : 0 < (r.den : Int) := by
  rw [Int.natCast_pos]
  exact r.den_pos

lemma den_prod_pos (r₁ r₂ : myPreRat) : 0 < (r₁.den * r₂.den : Int) := by
  exact mul_pos r₁.den_pos_int r₂.den_pos_int

lemma nonneg_iff (r : myPreRat) : 0 ≤ r ↔ 0 ≤ r.num := by
  constructor <;> intro h
  · change 0 * r.den ≤ r.num * 1 at h; simp at h; exact h
  · change 0 * r.den ≤ r.num * 1; simp; exact h

lemma add_nonneg (a b : myPreRat) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  simp only [nonneg_iff]
  intro ha hb
  apply Int.add_nonneg
  · exact Int.mul_nonneg ha (Int.natCast_nonneg b.den)
  · exact Int.mul_nonneg hb (Int.natCast_nonneg a.den)

example : myPreRat.mk 2 4 (by decide) ≠ myPreRat.mk 1 2 (by decide) := by simp

-- PartialOrder properties
theorem le_refl (a : myPreRat) : a ≤ a := by
  exact Int.le_refl _

theorem le_trans (a b c : myPreRat) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  apply Int.le_of_mul_le_mul_right _ b.den_pos_int
  calc (a.num * c.den) * b.den
      = (a.num * b.den) * c.den := by ring
    _ ≤ (b.num * a.den) * c.den :=
        Int.mul_le_mul_of_nonneg_right hab (Int.le_of_lt c.den_pos_int)
    _  = (b.num * c.den) * a.den := by ring
    _ ≤ (c.num * b.den) * a.den :=
        Int.mul_le_mul_of_nonneg_right hbc (Int.le_of_lt a.den_pos_int)
    _ = (c.num * a.den) * b.den := by ring

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
-- Section 3: Respect Proofs (Operations preserve equivalence) or Welle Definedness
-- ========================================
/--
If a₁ ≈ a₂ and b₁ ≈ b₂, then (a₁ + b₁) ≈ (a₂ + b₂).
-/
private theorem le_respects_equiv_forward
    (a₁ b₁ a₂ b₂ : myPreRat)
    (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
    (h : a₁ ≤ b₁) : a₂ ≤ b₂ := by
  have pos_prod : (0: Int) < (a₁.den * b₁.den ) := myPreRat.den_prod_pos a₁ b₁
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

theorem myRel_respects_le (a₁ b₁ a₂ b₂ : myPreRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  intro ha hb
  simp only [eq_iff_iff] -- or apply propext
  constructor
  · exact le_respects_equiv_forward a₁ b₁ a₂ b₂ ha hb
  · exact fun h => le_respects_equiv_forward a₂ b₂ a₁ b₁ ha.symm hb.symm h

theorem myRel_respects_add (a₁ b₁ a₂ b₂ : myPreRat) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ + b₁) ≈ (a₂ + b₂) := by
  intro ha hb
  calc (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den)
      = a₁.num * b₁.den * a₂.den * b₂.den + b₁.num * a₁.den * a₂.den * b₂.den := by ring
    _ = a₂.num * a₁.den * b₁.den * b₂.den + b₂.num * b₁.den * a₁.den * a₂.den := by
        rw [← ha, ← hb]; ring
    _ = (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den) := by ring

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
