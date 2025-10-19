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
  ·
    sorry
  ·  sorry

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
-- T is Not Path-connected
lemma norm_ge_abs_snd {a b : ℝ} : ‖(a, b)‖ ≥ |b| := by simp
noncomputable def xs_pos_peak := fun (k : ℕ) => 2/((4 * k + 1) * Real.pi)
lemma h_sin_xs_pos_peak_eq_one : ∀ k : ℕ, k ≥ 1 → Real.sin ((xs_pos_peak k)⁻¹) = 1 := by
  intro k hk
  sorry
lemma xs_pos_peak_tendsto_zero : Tendsto xs_pos_peak atTop (𝓝 0) := by
  sorry
lemma xs_pos_peak_nonneg : ∀ k : ℕ, 0 ≤ xs_pos_peak k := by
  sorry

-- open Real Set Filter Topology
-- def pos_real := Ioi (0 : ℝ)
-- noncomputable def sine_curve := fun x ↦ (x, sin (x⁻¹))

-- def S : Set (ℝ × ℝ) := sine_curve '' pos_real
-- def Z : Set (ℝ × ℝ) := { (0, 0) }
-- def T : Set (ℝ × ℝ) := S ∪ Z

def z : ℝ×ℝ := (0, 0)
noncomputable def w : ℝ×ℝ := sine_curve (1)

theorem T_is_not_path_conn_Rework : ¬ (IsPathConnected T)  := by
  -- Assume we have a path from z= (0, 0) to w=(1, sin(1))
  have h_z : z ∈ T := Or.inr rfl
  have h_w : w ∈ T := Or.inl ⟨1, ⟨zero_lt_one' ℝ, rfl⟩⟩
  intro p_conn
  apply IsPathConnected.joinedIn at p_conn
  specialize p_conn z h_z w h_w
  let p := JoinedIn.somePath p_conn
  -- consider the xcoordinate map wich is conituous
  -- the composition of the path with the xcoordinate map is continuous
  have xcoord_path_cont : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  -- let t₀ the last time the path is on the y-axis
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  let xcoord_path := fun t => (p t).1
  -- the path at t₀ is (0, 0) (not so sure of this proof)
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_path_cont).sSup_mem ⟨0, by aesop⟩
  -- (3.2) let ε = 1/ 2, by continuity of the path, we can find a δ > 0 such that
  -- for all t in [t₀, t₀ + δ], ||p(t) - p(t₀)|| < 1/2
  -- hence the path is in a ball of radius 1/2 around (0, 0)
  obtain ⟨δ , hδ, ht⟩ : ∃ δ > 0, ∀ t, dist t t₀ < δ →
    dist (p t) (p t₀) < 1/2 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_half_pos
  -- let t₁ be the a time the path is not on the y-axis
  -- t₁ is in (t₀, t₀ + δ]
  -- hence t₁ > t₀
  -- hence xcoord(p(t₁)) > 0
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ > t₀  ∧ dist t₀ t₁ < δ := by
    let s₀ := (t₀ : ℝ ) -- cast t₀ from unitInterval to ℝ for manipulation
    let s₁ := min (s₀ + δ/2) 1
    have h_s₀_delta_pos : 0 ≤ s₀ + δ/2 := add_nonneg t₀.2.1 (by positivity)
    have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
    have hs₁': s₁ ≤ 1 := min_le_right ..
    use ⟨s₁, hs₁, hs₁'⟩
    constructor
    · simp only [gt_iff_lt, s₁,s₀,← Subtype.coe_lt_coe]
      apply lt_min
      · exact (lt_add_iff_pos_right _).mpr (half_pos hδ)
      · apply lt_of_le_of_ne (unitInterval.le_one t₀)
        · intro ht₀
          have w_x_path : (p 1).1 = 1 := by simp [sine_curve, w]
          have t₀_eq_1 : t₀ = 1 := Subtype.ext ht₀
          have x_eq_zero : (p 1).1 = 0 := by
            rw [← t₀_eq_1]
            exact h_pt₀_x
          linarith
    · have h_le : s₁ ≤ s₀ + δ/2 := min_le_left _ _
      have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
      rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
      linarith
  --- let a = xcoord_path t₁ > 0
  -- this must follow since let t₀ : unitInterval := sSup {t | (p t).1 = 0} and  t₀ < t₀
  -- so t₀ must be in S ishc has positive x coordinate
  let a := (p t₁).1
  have ha : a > 0 := by
    obtain ⟨x, hxI, hx_eq⟩ : p t₁ ∈ S := by
      cases p_conn.somePath_mem t₁ with
      | inl hS => exact hS
      | inr h_Z =>
      -- If p t₁ ∈ Z, then (p t₁).1 = 0
        have : (p t₁).1 = 0 := by rw [h_Z]
        -- So t₁ ≤ t₀, contradicting t₁ > t₀
        have h_le : t₁ ≤ t₀ := le_sSup this
        have h_le_real : (t₁ : ℝ) ≤ (t₀ : ℝ) := Subtype.coe_le_coe.mpr h_le
        have h_gt_real : (t₁ : ℝ) > (t₀ : ℝ) := Subtype.coe_lt_coe.mpr ht₁.1
        linarith
    -- Goal: a > 0
    -- →     (p t₁).1 > 0           [unfold a]
    -- →     (sine_curve x).1 > 0   [rewrite with ← hx_eq]
    -- →     x > 0                  [simplify .1 of pair]
    simpa only [a, ← hx_eq] using hxI
  -- The image x(p([t₀, t₁])) is connected and contains 0 and a
  -- Therefore [0, a] ⊆ x(p([t₀, t₁]))
  have intervalAZeroSubOfT₀T₁Xcoord : Set.Icc 0 a ⊆ xcoord_path '' Set.Icc t₀ t₁ :=
     IsConnected.Icc_subset
      ((isConnected_Icc (le_of_lt ht₁.1)).image _ xcoord_path_cont.continuousOn)
      (⟨t₀, left_mem_Icc.mpr (le_of_lt ht₁.1), h_pt₀_x⟩)
      (⟨t₁, right_mem_Icc.mpr (le_of_lt ht₁.1), rfl⟩)
  --let xs_pos_peak a sequence of x-values where sin(1/x) = 1
  -- i.e. for any k ∈ ℕ , sin(1/xs_pos_peak(k)) = 1
  -- xs_pos_peak converges to 0 as k → ∞
  -- thus there are some indicies i for wich xs_pos_peak i is in [0, a]
  have h_existsSeqInInterval : ∃ i : ℕ, i ≥ 1 ∧ xs_pos_peak i ∈ Set.Icc 0 a := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.mp xs_pos_peak_tendsto_zero (a/2)
      (by positivity)).exists_forall_of_atTop
    use max 1 N
    refine ⟨le_max_left _ _, xs_pos_peak_nonneg _, ?_⟩
    have : dist (xs_pos_peak (max 1 N)) 0 < a / 2 := hN _ (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (xs_pos_peak_nonneg _)] at this
    linarith
  -- Now we can show that there exists s₁ in [t₀, t₁] ⊆ [t₀, t₀ + δ) such that:
  -- 1. p(s₁) = (*,1)
  have p_s₁ : ∃ s₁ ∈ Set.Icc t₀ t₁, (p s₁).2 = 1 := by
    obtain ⟨i, hige, hi⟩ := h_existsSeqInInterval
    have : xs_pos_peak i ∈ xcoord_path '' Set.Icc t₀ t₁ := intervalAZeroSubOfT₀T₁Xcoord hi
    obtain ⟨s₁, hs₁_mem, hs₁_x⟩ := this
    use s₁, hs₁_mem
    -- Show p s₁ ∈ S (not in Z, since that would make xs_pos_peak i = 0)
    have h_in_S : p s₁ ∈ S := by
      cases p_conn.somePath_mem s₁ with
      | inl hS => exact hS
      | inr h_Z =>
        have h_eq_zero : p s₁ = (0, 0) := Set.mem_singleton_iff.mp h_Z
        have : xs_pos_peak i = 0 := by
          calc xs_pos_peak i
              = (p s₁).1 := by simpa [xcoord_path] using hs₁_x.symm
            _ = (0, 0).1 := by rw [h_eq_zero]
            _ = 0 := rfl
        simpa [this] using h_sin_xs_pos_peak_eq_one i hige
    -- Since p s₁ ∈ S, we have p s₁ = (x, sin(1/x)) for some x > 0
    obtain ⟨x, _, h_eq⟩ := h_in_S
    -- But x = xs_pos_peak i (from the x-coordinate), so sin(1/x) = 1
    have hx : x = xs_pos_peak i := by
      have : (p s₁).1 = x := by simpa [sine_curve] using congrArg Prod.fst h_eq.symm
      calc x = (p s₁).1 := this.symm
          _ = xcoord_path s₁ := rfl
          _ = xs_pos_peak i := hs₁_x
    rw [← h_eq, sine_curve, hx]
    exact h_sin_xs_pos_peak_eq_one i hige
  --Derive contradiction
  obtain ⟨x₁, hx₁, h_pathx₁⟩ := p_s₁
  -- First show that p t₀ = (0, 0)
  have h_pt₀ : p t₀ = (0, 0) := by
    cases p_conn.somePath_mem t₀ with
    | inl hS =>
      obtain ⟨x, hx_pos, hx_eq⟩ := hS
      have : x = 0 := by
        calc x = (sine_curve x).1 := rfl
            _ = (p t₀).1 := by simpa [sine_curve] using congrArg Prod.fst hx_eq
            _ = 0 := h_pt₀_x
      simp [pos_real] at hx_pos
      linarith
    | inr hZ => exact Set.mem_singleton_iff.mp hZ
  -- x₁ is within δ of t₀ (since x₁ ∈ [t₀, t₁] and dist t₀ t₁ < δ)
  have x₁_close : dist x₁ t₀ < δ := by
    calc dist x₁ t₀
        ≤ dist t₁ t₀ := dist_right_le_of_mem_uIcc (Icc_subset_uIcc' hx₁)
      _ = dist t₀ t₁ := dist_comm _ _
      _ < δ := ht₁.2
  -- By continuity, p(x₁) is close to p(t₀)
  have close : dist (p x₁) (p t₀) < 1/2 := ht x₁ x₁_close
  -- But p(x₁) has y-coordinate 1, so it's far from p(t₀) = (0,0)
  have far : 1 ≤ dist (p x₁) (p t₀) := by
    calc 1 = |(p x₁).2 - (p t₀).2| := by simp [h_pathx₁, h_pt₀]
        _ ≤ ‖p x₁ - p t₀‖ := norm_ge_abs_snd
        _ = dist (p x₁) (p t₀) := by rw [dist_eq_norm]
  linarith
