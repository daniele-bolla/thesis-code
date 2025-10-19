import Mathlib
open Real Set Filter Topology

def pos_real := Set.Ioi (0 : ℝ)
noncomputable def sine_curve := fun x ↦ (x, Real.sin (x⁻¹))
def S : Set (ℝ × ℝ) := (sine_curve) '' pos_real
def Z : Set (ℝ × ℝ) := { (0, 0) }
def T : Set (ℝ × ℝ) := S ∪ Z

-- T is connected
lemma T_sub_cls_S : T ⊆ closure S := by
  intro x hx
  cases hx with
  | inl hxS => exact subset_closure hxS
  | inr hxZ =>
      rw [hxZ]
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
      exact mem_closure_of_tendsto hf hf'
theorem T_is_conn : IsConnected T :=
  IsConnected.subset_closure (isConnected_Ioi.image sine_curve <|
    continuous_id.continuousOn.prodMk <|
    Real.continuous_sin.comp_continuousOn <|
    ContinuousOn.inv₀ continuous_id.continuousOn
    (fun _ hx => ne_of_gt hx)) (by tauto_set) T_sub_cls_S

-- T is Not Path-connected
lemma norm_ge_abs_snd {a b : ℝ} : ‖(a, b)‖ ≥ |b| := by simp
noncomputable def xs_pos_peak := fun (k : ℕ) => 2/((4 * k + 1) * Real.pi)

lemma xs_pos_peak_tendsto_zero : Tendsto xs_pos_peak atTop (𝓝 0) := by
  refine Tendsto.comp (g := fun k : ℝ ↦ 2 / ((4 * k + 1) * Real.pi))
    ?_ tendsto_natCast_atTop_atTop
  simp only [div_eq_mul_inv]
  have h : Tendsto (fun k => ((4 * k + 1) * Real.pi)⁻¹) atTop (𝓝 0) := by
    apply Tendsto.comp tendsto_inv_atTop_zero
    apply Tendsto.atTop_mul_const Real.pi_pos
    apply tendsto_atTop_add_const_right
    apply Tendsto.const_mul_atTop four_pos
    exact tendsto_id
  convert Tendsto.const_mul 2 h
  · norm_num
lemma xs_pos_peak_nonneg : ∀ k : ℕ, 0 ≤ xs_pos_peak k := fun k =>
  div_nonneg (by norm_num) (by positivity)
lemma h_sin_xs_pos_peak_eq_one (k : ℕ) (hk : k ≥ 1) : Real.sin ((xs_pos_peak k)⁻¹) = 1 := by
  have : (xs_pos_peak k)⁻¹ = Real.pi / 2 + k * (2 * Real.pi) := by
    simp [xs_pos_peak]; field_simp; ring
  simp [this, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

def z : ℝ×ℝ := (0, 0)
noncomputable def w : ℝ×ℝ := sine_curve (1)

theorem T_is_not_path_conn : ¬ (IsPathConnected T)  := by
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
    simpa only [a, ← hx_eq] using hxI
  -- The image x(p([t₀, t₁])) is connected and contains 0 and a
  -- Therefore [0, a] ⊆ x(p([t₀, t₁]))
  have intervalAZeroSubOfT₀T₁Xcoord : Set.Icc 0 a ⊆ xcoord_path '' Set.Icc t₀ t₁ :=
     IsConnected.Icc_subset
      ((isConnected_Icc (le_of_lt ht₁.1)).image _ xcoord_path_cont.continuousOn)
      (⟨t₀, left_mem_Icc.mpr (le_of_lt ht₁.1), h_pt₀_x⟩)
      (⟨t₁, right_mem_Icc.mpr (le_of_lt ht₁.1), rfl⟩)
  -- let xs_pos_peak a sequence of x-values where sin(1/x) = 1
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

theorem T_isconn_not_path_conn : IsConnected T ∧ ¬IsPathConnected T :=
  ⟨T_is_conn,T_is_not_path_conn ⟩
