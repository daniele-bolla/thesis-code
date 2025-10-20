import Mathlib
example (a b : Prop) (ha : a) (hb : b) : (a ∧ b) := And.intro ha hb

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
theorem le_trans_proof : Transitive (· ≤ · : Nat → Nat → Prop) :=
  fun x y z h1 h2 => Nat.le_trans h1 h2

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

-- #check @Rat.add
-- #print Rat.add

-- Proving Rat.add_nonneg withouth using any lemmas or theorems from Rat
-- Helper: positive denominators
lemma nat_ne_zero_pos (den : ℕ) (h_den_nz : den ≠ 0) : 0 < den :=
  Nat.pos_of_ne_zero h_den_nz
-- Helper: non-negative numerator from non-negative rational

set_option trace.Tactic.norm_cast true
lemma rat_num_nonneg {num : ℤ} {den : ℕ} (hden_pos : 0 < den)
    (h : (0 : ℚ) ≤ num / den) : 0  ≤ num := by
  contrapose! h
  have hden_pos_to_rat : (0 : ℚ) < den := Nat.cast_pos.mpr hden_pos
  have hnum_neg_to_rat : num  < (0 : ℚ)  := Int.cast_lt.mpr h
  exact div_neg_of_neg_of_pos hnum_neg_to_rat hden_pos_to_rat

-- Main theorem: addition preserves non-negativity
lemma rat_add_nonneg (a b : Rat) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha hb
  -- Adds (ha : 0 ≤ a) in the context and similarly hb
  -- as seen temrs of type Rat are strucuters.
  -- Strucutre cna be deconstructured

  cases a with | div a_num a_den a_den_nz a_cop =>
  cases b with | div b_num b_den b_den_nz b_cop =>
  -- Goal: ⊢ 0 ≤ ↑a_num / ↑a_den + ↑b_num / ↑b_den
  rw[div_add_div]
  -- Goal: ⊢ 0 ≤ (↑a_num * ↑b_den + ↑a_den * ↑b_num) / (↑a_den * ↑b_den)
  · have ha_num_nonneg := by
      have ha_den_pos := nat_ne_zero_pos a_den a_den_nz
      exact rat_num_nonneg ha_den_pos ha
    have hb_num_nonneg := by
      have hb_den_pos := nat_ne_zero_pos b_den b_den_nz
      exact rat_num_nonneg hb_den_pos hb
    have hnum_nonneg : (0 : ℚ) ≤ a_num * b_den + a_den * b_num := by
      rw [← Int.cast_zero]
      rw [← Int.cast_natCast b_den, ← Int.cast_natCast a_den]
      rw [← Int.cast_mul, ← Int.cast_mul]
      rw [← Int.cast_add]
      rw [Int.cast_le]

      apply Int.add_nonneg
      · exact Int.mul_nonneg ha_num_nonneg (Int.natCast_nonneg _)
      · exact Int.mul_nonneg  (Int.natCast_nonneg _) hb_num_nonneg
    have hden_nonneg : (0 : ℚ) ≤ a_den * b_den := by
      rw [← Nat.cast_mul]
      exact Nat.cast_nonneg (a_den * b_den)

    exact div_nonneg hnum_nonneg hden_nonneg

  · exact Nat.cast_ne_zero.mpr a_den_nz -- Goal ⊢ ↑a_den ≠ 0
  · exact Nat.cast_ne_zero.mpr b_den_nz -- Goal ⊢ ↑b_den ≠ 0

-- Type classes section

-- A semigroup has an associative binary operation
class SemigroupD (α : Type*) where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
-- A monoid extends semigroup with an identity element

class MonoidD (α : Type*) extends Semigroup α where
  one : α
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a
-- A group extends monoid with inverses
class GroupD (α : Type*) extends Monoid α where
  inv : α → α
  mul_left_inv : ∀ a : α, mul (inv a) a = one

instance RatAddGroup : GroupD Rat where
  mul := (· + ·)
  mul_assoc := by intros; apply add_assoc
  one := 0
  one_mul := by intros; apply zero_add
  mul_one := by intros; apply add_zero
  inv := (· * -1)
  mul_left_inv := by intros; ring


open Real Set Filter Topology
def pos_real := Ioi (0 : ℝ)
noncomputable def sine_curve := fun x ↦ (x, sin (x⁻¹))

def S : Set (ℝ × ℝ) := sine_curve '' pos_real
def Z : Set (ℝ × ℝ) := { (0, 0) }
def T : Set (ℝ × ℝ) := S ∪ Z

-- lemma S_is_conn : IsConnected S := by
--   apply isConnected_Ioi.image
--   · sorry
--   -- apply ContinuousOn.prodMk continuous_id.continuousOn
--   -- apply Real.continuous_sin.comp_continuousOn
--   -- exact continuousOn_inv₀.mono fun _ hx ↦ hx.ne'

lemma sine_curve_is_continuous_on_pos_real_one_liner : ContinuousOn (fun x ↦ sin x⁻¹) (Ioi 0) :=
 continuous_sin.comp_continuousOn <| continuousOn_inv₀.mono fun _ hx ↦ hx.ne'

-- lemma S_is_conn : IsConnected S := by
--   refine isConnected_Ioi.image _ <| continuousOn_id.prodMk ?_
--   exact sine_curve_is_continuous_on_pos_real_one_liner

-- lemma inv_is_continuous_on_pos_real : ContinuousOn (fun x : ℝ => x⁻¹) (pos_real) :=
--  continuousOn_inv₀.mono fun _ hx ↦ hx.ne'

-- lemma inv_is_continuous_on_pos_real : ContinuousOn (fun x : ℝ => x⁻¹) (pos_real) := by
--   apply ContinuousOn.inv₀
--   · exact continuous_id.continuousOn
--   · intro x hx; exact ne_of_gt hx

lemma inv_is_continuous_on_pos_real : ContinuousOn (fun x : ℝ => x⁻¹) (pos_real) :=
    ContinuousOn.inv₀ (continuous_id.continuousOn) (fun _ hx =>  ne_of_gt hx)

-- lemma sin_comp_inv_is_continuous_on_pos_real : ContinuousOn
--  (sine_curve) (pos_real) := by
--   apply ContinuousOn.prodMk continuous_id.continuousOn
--   apply Real.continuous_sin.comp_continuousOn
--   exact inv_is_continuous_on_pos_real
lemma sin_comp_inv_is_continuous_on_pos_real : ContinuousOn
 (sine_curve) (pos_real) :=
 ContinuousOn.prodMk continuous_id.continuousOn <|
  Real.continuous_sin.comp_continuousOn <| (inv_is_continuous_on_pos_real)

-- lemma S_is_conn : IsConnected S := by
--   apply isConnected_Ioi.image
--   · exact sin_comp_inv_is_continuous_on_pos_real


lemma S_is_conn : IsConnected S :=
  isConnected_Ioi.image sine_curve <| continuous_id.continuousOn.prodMk <|
    continuous_sin.comp_continuousOn <|
    ContinuousOn.inv₀ continuous_id.continuousOn (fun _ hx => ne_of_gt hx)





 -- Use sequential characterization of closure.
 lemma T_sub_cls_s: T ⊆ closure S := by
  intro x hx
  simp only [mem_closure_iff_seq_limit, Prod.tendsto_iff]
  -- let f : ℕ → ℝ × ℝ := fun n => ((n * Real.pi)⁻¹, 0)
  constructor
  · sorry
  · sorry

lemma T_sub_cls_seS : T ⊆ closure S := by
  intro x hx
  cases hx with
  | inl hxS => exact subset_closure hxS
  | inr hxZ =>
      rw [hxZ]
      refine mem_closure_iff_frequently.mpr ?_
      let f : ℕ → ℝ × ℝ := fun n => ((n * Real.pi)⁻¹, 0)
      have hf : Tendsto f atTop (𝓝 (0, 0)) := by
        refine .prodMk_nhds ?_ tendsto_const_nhds
        exact tendsto_inv_atTop_zero.comp
          (Filter.Tendsto.atTop_mul_const' Real.pi_pos tendsto_natCast_atTop_atTop)
      have hf' : ∀ᶠ n in atTop, f n ∈ S := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact ⟨(n * Real.pi)⁻¹,
          inv_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) Real.pi_pos),
          by simp [f, sine_curve, inv_inv, Real.sin_nat_mul_pi]⟩
      exact hf.frequently hf'.frequently

-- lemma T_sub_cls_cS : T ⊆ closure S := by
--   intro x hx
--   cases hx with
--   | inl hxS => exact subset_closure hxS
--   | inr hxZ =>
--       rw[hxZ]
--       simp only [ mem_closure_iff_frequently]
--       refine ((tendsto_inv_atTop_zero.comp
--         (Filter.Tendsto.atTop_mul_const' Real.pi_pos tendsto_natCast_atTop_atTop))
--         Tendsto.prodMk_nhds tendsto_const_nhds).frequently ?_
--       filter_upwards [eventually_gt_atTop 0] with n hn
--       exact ⟨(n * Real.pi)⁻¹,
--         inv_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) Real.pi_pos),
--         by simp [sine_curve, inv_inv, Real.sin_nat_mul_pi]⟩

lemma T_sub_cls_sS : T ⊆ closure S := by
  intro x hx
  cases hx with
  | inl hxS => exact subset_closure hxS
  | inr hxZ =>
      refine mem_closure_iff_frequently.mpr ?_
      sorry
-- T is Connected
-- lemma T_sub_cls_S : T ⊆ closure S := by
--   intro x hx
--   cases hx with
--   | inl hxS => exact subset_closure hxS
--   | inr hxZ =>
--       rw [hxZ]
--       let f :  ℕ →  ℝ × ℝ := fun n => ((n * Real.pi)⁻¹, 0)
--       have hnMulpiAtTop : Tendsto (fun n : ℕ => n* Real.pi) atTop atTop := by
--         apply Filter.Tendsto.atTop_mul_const'
--         · exact Real.pi_pos
--         · exact tendsto_natCast_atTop_atTop
--       have hf : Tendsto f atTop (𝓝 (0, 0))  := by
--         apply Filter.Tendsto.prodMk_nhds
--         · exact tendsto_inv_atTop_zero.comp hnMulpiAtTop
--         · exact tendsto_const_nhds
--       have hf' : ∀ᶠ n in atTop, f n ∈ S := by
--         have hfInS : ∀ n : ℕ, 0 < n → f n ∈ S := by
--           intro n hn
--           use (n * Real.pi)⁻¹
--           constructor
--           unfold pos_real
--           rw [Set.mem_Ioi]
--           · apply inv_pos.mpr
--             apply mul_pos
--             · exact Nat.cast_pos.mpr hn
--             · exact Real.pi_pos
--           · unfold f
--             calc sine_curve (n * Real.pi)⁻¹ =
--               ((n * Real.pi)⁻¹, Real.sin ((n * Real.pi)⁻¹)⁻¹) := by rfl
--               _ = ((n * Real.pi)⁻¹, Real.sin (n * Real.pi)) := by
--                   congr
--                   simp only [inv_inv]
--               _ = ((n * Real.pi)⁻¹,0) := by
--                 congr
--                 apply Real.sin_nat_mul_pi
--         filter_upwards [eventually_gt_atTop 0] using hfInS
--       apply mem_closure_of_tendsto hf hf'
-- lemma S_is_conn : IsConnected S :=
--   isConnected_Ioi.image sine_curve <| continuous_id.continuousOn.prodMk <|
--     Real.continuous_sin.comp_continuousOn <|
--     ContinuousOn.inv₀ continuous_id.continuousOn (fun _ hx => ne_of_gt hx)

-- theorem T_is_onn : IsConnected T := IsConnected.subset_closure S_is_conn (by tauto_set) T_sub_cls_S
-- theorem T_is_onn : IsConnected T := by
--   apply IsConnected.subset_closure
--   · exact S_is_conn
--   · tauto_set
--   · exact T_sub_cls_S

-- theorem T_is_conn : IsConnected T := by
--   apply IsConnected.subset_closure
--   · exact S_is_conn -- ⊢ IsConnected ?s
--   · tauto_set -- ⊢ S ⊆ T
--   · exact T_sub_cls_S -- ⊢ T ⊆ closure S
