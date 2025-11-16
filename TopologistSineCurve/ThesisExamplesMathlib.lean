import Mathlib

variable (a b c : Rat)
lemma rat_le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_sub_nonneg] at hab hbc
  have := Rat.add_nonneg hab hbc
  simp_rw [sub_eq_add_neg, add_left_comm (b + -a) c (-b), add_comm (b +
  -a) (-b), add_left_comm (-b) b (-a), add_comm (-b) (-a),
  add_neg_cancel_comm_assoc, ← sub_eq_add_neg] at this
  rwa [Rat.le_iff_sub_nonneg]

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

-- CHAPTER 3 Type Classes and Algebraic Hierarchy
structure Semigroup' (α : Type*) where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

-- Simple function that works on any semigroup
def double {α : Type*} (s : Semigroup' α) (x : α) : α :=
  s.mul x x

def Semigroup'_Int : Semigroup' ℤ where
  mul := (· + ·)
  mul_assoc := Int.add_assoc

def Semigroup'_Rat : Semigroup' ℚ where
  mul := (· + ·)
  mul_assoc := Rat.add_assoc

#eval double Semigroup'_Int (-2)   -- -4
#eval double Semigroup'_Rat (1/2)   -- 1/1

class Semigroup'' (α : Type*) where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

instance : Semigroup'' ℤ where
  mul := (· + ·)
  mul_assoc := Int.add_assoc

instance : Semigroup'' ℚ where
  mul := (· + ·)
  mul_assoc := Rat.add_assoc

-- Simple function with automatic instance
def double' {α : Type*} [Semigroup'' α] (x : α) : α :=
  Semigroup''.mul x x

#eval double' (-2 : ℤ)     -- -4
#eval double' (1/2 : ℚ)    -- 1

class Group'' (α : Type*) extends Semigroup'' α where
  one : α
  left_id : ∀ a : α, mul one a = a
  right_id : ∀ a : α, mul a one = a
  inv : α → α
  left_inv : ∀ a : α, mul (inv a) a = one
  right_inv : ∀ a : α, mul a (inv a) = one

instance : Group'' ℤ where
  mul := (· + ·)
  mul_assoc := Int.add_assoc
  one := 0
  left_id := Int.zero_add
  right_id := Int.add_zero
  inv := (· * -1)
  left_inv := by intro a; ring
  right_inv := by intro a; ring

instance : Group'' ℚ where
  mul := (· + ·)
  mul_assoc := Rat.add_assoc
  one := 0
  left_id := Rat.zero_add
  right_id := Rat.add_zero
  inv := fun x => -x
  left_inv := by intro a; ring
  right_inv := by intro a; ring

theorem mul_cancel₀ {α : Type*} [Group'' α]  (a b c : α)
    (h : Semigroup''.mul a b = Semigroup''.mul a c) : b = c := by
    calc
      b = Semigroup''.mul (Group''.one) b := by rw [Group''.left_id]
      _ = Semigroup''.mul (Group''.inv a) (Semigroup''.mul a b) := by
        rw [← Semigroup''.mul_assoc, Group''.left_inv]
      _ = Semigroup''.mul (Group''.inv a) (Semigroup''.mul a c) := by rw [h]
      _ = Semigroup''.mul (Group''.one) c := by
        rw [← Semigroup''.mul_assoc, Group''.left_inv]
      _ = c := by rw [Group''.left_id]

-- CHAPTER 4
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
