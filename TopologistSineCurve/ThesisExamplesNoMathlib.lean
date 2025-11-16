
def identityFun (A : Type) : A → A := fun x => x

example : ∃ a b : Nat, a + b = 7 := Exists.intro 3 (Exists.intro 4 rfl)
example (p : Prop) (h : False) : p := by
  exfalso
  exact h

def Transitive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z

theorem le_trans_nat : Transitive (· ≤ · : Nat → Nat → Prop) :=
  fun x y z h1 h2 => Nat.le_trans h1 h2

example {a b : Prop} (ha : a) (hb : b) : (a ∧ b) := And.intro ha hb

theorem and_associative (a b c : Prop) : (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
  fun h : (a ∧ b) ∧ c =>
    -- First, from the assumption (a ∧ b) ∧ c, we can derive a:
    have hab : a ∧ b := h.left -- extracts (derive) a proof of (a ∧ b) from the assumption
    have ha : a := hab.left -- extracts a from (a ∧ b)
    -- Second, we can derive b ∧ c (here we only extract b and c and combine them in the next step)
    have hc : c := h.right
    have hb : b := hab.right
    -- Finally, combining these derivations we obtain A ∧ (B ∧ C)
    show a ∧ (b ∧ c) from ⟨ha, ⟨hb, hc⟩⟩

-- def Transitive {α : Type} (R : α → α → Prop) : Prop :=
--   ∀ x y z, R x y → R y z → R x z
theorem le_trans_nat' : Transitive (· ≤ · : Nat → Nat → Prop) :=
  fun x y z h1 h2 => Nat.le_trans h1 h2

  #check 5        -- Lean infers α = Nat
  #check "hello"  -- Lean infers α = String
