import Mathlib

open Topology Filter Set Order

def pos_real := Set.Ioi (0 : ℝ)
noncomputable def sine_curve := fun x ↦ (x, Real.sin (x⁻¹))

def S : Set (ℝ × ℝ) := (sine_curve) '' pos_real

def Z : Set (ℝ × ℝ) := { (0, 0) }

def T : Set (ℝ × ℝ) := S ∪ Z

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

  def z : ℝ×ℝ := (0, 0)
  noncomputable def w_x: ℝ := (2)⁻¹
  noncomputable def w : ℝ×ℝ := sine_curve w_x
  lemma h_z : z ∈ T := by
    right
    simp [Z]
    rfl
  lemma h_w : w ∈ T := by
    rw [T,S]
    left
    -- simp only [Set.mem_image]
    use w_x
    constructor
    · unfold w_x pos_real Set.Ioi
      norm_num
    · trivial

lemma norm_ge_abs_snd {a b : ℝ} : ‖(a, b)‖ ≥ |b| := by
  simp only [Prod.norm_mk, Real.norm_eq_abs, ge_iff_le, le_sup_right]

lemma xcoord_pathContinuous (h_path : unitInterval → ℝ × ℝ)
(hCont : Continuous h_path) : Continuous (fun t => (h_path t).1) :=
  continuous_fst.comp hCont

noncomputable def xs_pos_peak := fun (k : ℕ) => 2/((4 * k + 1) * Real.pi)
lemma h_sin_xs_pos_peak_eq_one : ∀ k : ℕ, k ≥ 1 → Real.sin ((xs_pos_peak k)⁻¹) = 1 := by
  intro k hk
  calc Real.sin ((xs_pos_peak k)⁻¹) = Real.sin (((4 * k + 1) * Real.pi)/2) := by
        unfold xs_pos_peak
        field_simp
      _ = Real.sin (Real.pi/2 + 2*k*Real.pi) := by
        field_simp
        ring_nf
      _ = Real.sin (Real.pi/2 + k*(2*Real.pi)) := by
        ring_nf
      _ = Real.sin (Real.pi/2) := by
        rw [Real.sin_add_nat_mul_two_pi]
      _ = 1 := by
        exact Real.sin_pi_div_two

lemma xs_pos_peak_tendsto_zero : Tendsto xs_pos_peak atTop (𝓝 0) := by
  unfold xs_pos_peak
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

lemma xs_pos_peak_pos : ∀ k : ℕ, 0 ≤ xs_pos_peak k := by
  intro k
  unfold xs_pos_peak
  apply div_nonneg
  · norm_num
  · apply mul_nonneg
    · linarith
    · exact Real.pi_pos.le

theorem T_is_not_path_conn : ¬ (IsPathConnected T)  := by
  -- Assume we have a path from z= (0, 0) to w=(1/2, sin(1/2))
  intro h_pathConn
  apply IsPathConnected.joinedIn at h_pathConn
  specialize h_pathConn z h_z w h_w
  let h_path := JoinedIn.somePath h_pathConn

  -- consider the xcoordinate map wich is conituous
  -- the composition of the path with the xcoordinate map is continuous
  let xcoord_path := fun t => (h_path t).1
  have xcoord_pathContinuous : Continuous (xcoord_path : unitInterval → ℝ) := by
    apply Continuous.comp
    · exact continuous_fst
    · exact h_path.continuous

  -- let t₀ the last time the path is on the y-axis
  let A : Set unitInterval := { t | (h_path t).1 = 0 }
  let t₀ : unitInterval := sSup A

  -- h_xcoord_path_at_zero_eq_zero = 0
    -- (3.1) let A = {t | xcoord_path t = 0}
    -- A is a closed set in unitInterval
    -- since it is the preimage of a closed set under a continuous function
    -- hence it is compact
    -- since unitInterval is compact
    -- hence it is closed
  have h_t₀_mem : t₀ ∈ A :=
    have h_A_nonempty : A.Nonempty := by
      use 0
      have h_xcoord_path0 : xcoord_path 0 = 0 := by
        simp only [xcoord_path]
        rw [h_path.source]
        rfl
      exact h_xcoord_path0
    have A_closed : IsClosed A := isClosed_singleton.preimage xcoord_pathContinuous
    IsCompact.sSup_mem A_closed.isCompact h_A_nonempty
  have h_xcoord_path_at_zero_eq_zero : xcoord_path t₀ = 0 := h_t₀_mem

  -- the path at t₀ is (0, 0) (not so sure of this proof)
  have h_pathT₀: h_path t₀ = z := by
    unfold z
    apply Prod.ext_iff.mpr

    have h_pathT₀IsInT : h_path t₀ ∈ T := by
      exact h_pathConn.somePath_mem t₀

    have h_pathT₀_x_is_0 : (h_path t₀).1 = 0 := by
      exact h_xcoord_path_at_zero_eq_zero

    unfold T at h_pathT₀IsInT

    constructor
    · apply h_xcoord_path_at_zero_eq_zero
    ·cases h_pathT₀IsInT with
    | inl hS =>
        exfalso

        obtain ⟨xpos_real, hxInpos_real, h_eq_path⟩ := hS
        let x_val : ℝ := xpos_real
        have hx_valPos : x_val > 0 := by
         dsimp [x_val] at *
         dsimp [pos_real] at hxInpos_real
         simpa using hxInpos_real

        have h_path_x_eq_x_val : (h_path t₀).1 = x_val := by
          simpa [sine_curve, x_val] using
          (congrArg Prod.fst h_eq_path).symm


        rw [h_path_x_eq_x_val] at h_pathT₀_x_is_0
        linarith [hx_valPos, h_pathT₀_x_is_0]

    | inr h_Z =>

        have h_Z_eq : h_path t₀ = (0, 0) := by
          simpa [Z] using h_Z

        have h_pathT₀_y_is_0 : (h_path t₀).2 = 0 := by
          simpa using congrArg Prod.snd h_Z_eq

        exact h_pathT₀_y_is_0

  -- (3.2) let ε = 1/ 2, by continuity of the path, we can find a δ > 0 such that
  -- for all t in [t₀, t₀ + δ], ||p(t) - p(t₀)|| < 1/2
  -- hence the path is in a ball of radius 1/2 around (0, 0)

  have eps_delta_bound_at_t₀ : ∃ δ > 0, ∀ t : unitInterval, dist t t₀ < δ →
    dist (h_path t) (h_path t₀) < 1/2 := by
    have hTendstoEventually := Metric.tendsto_nhds.mp (h_path.continuousAt t₀)
    have hEventually : ∀ᶠ (t : unitInterval) in 𝓝 t₀, dist (h_path t) (h_path t₀) < 1/2 := by
      specialize hTendstoEventually (1/2)
      apply hTendstoEventually
      norm_num
    exact Metric.eventually_nhds_iff.mp hEventually

  obtain ⟨δ , hδ, ht⟩ := eps_delta_bound_at_t₀

  -- let t₁ be the a time the path is not on the y-axis
  -- t₁ is in (t₀, t₀ + δ]
  -- hence t₁ > t₀
  -- hence xcoord(p(t₁)) > 0
  -- this is terrible

  have h_t₁_ge_t₀_in_eps_delta_bound : ∃ t₁:unitInterval, t₁ > t₀  ∧ dist t₀ t₁ < δ := by
    let s₀ := (t₀ : ℝ ) -- t₀ is in unitInterval
    let s₁ := min (s₀ + δ/2) 1
    have h_s₀_delta_pos : s₀ + δ/2 > 0 := by
      apply add_pos_of_nonneg_of_pos
      · exact unitInterval.nonneg t₀
      · exact div_pos hδ (by norm_num)

    have hs₁ : s₁ ≥ 0 := by
      have h1 : (0 : ℝ) ≤ s₀ + δ/2 := le_of_lt h_s₀_delta_pos
      have h2 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      have : (0 : ℝ) ≤ min (s₀ + δ/2) 1 := le_min h1 h2
      simpa [s₁] using this

    have h': s₁ ≤ 1 := by
      apply min_le_right

    use ⟨s₁, hs₁, h'⟩
    have t₀_lt_one : t₀ < 1 := by
      apply lt_of_le_of_ne
      · exact unitInterval.le_one t₀
      · intro h_eq_one
        have w_x_path : xcoord_path 1 = w_x := by
          simp only [xcoord_path]
          rw [h_path.target]
          simp only [w, sine_curve, w_x]
        have w_x_pos : w_x > 0 := by
          unfold w_x
          norm_num
        have x_eq_zero : xcoord_path 1 = 0 := by
          rw [h_eq_one] at h_t₀_mem
          exact h_t₀_mem
        rw [w_x_path] at x_eq_zero
        exact ne_of_gt w_x_pos x_eq_zero
    have dist_case : dist t₀ ⟨s₁, hs₁, h'⟩ < δ := by
      rw [Subtype.dist_eq]
      simp only [ Real.dist_eq]

      have h_le : s₁ ≤ s₀ + δ/2 := min_le_left _ _

      have h_ge : s₁ ≥ s₀ := by
        by_cases h : s₀ + δ/2 ≤ 1
        · have : s₁ = s₀ + δ/2 := min_eq_left h
          rw [this]
          linarith
        · push_neg at h
          have : s₁ = 1 := min_eq_right (le_of_lt h)
          rw [this]
          exact le_of_lt t₀_lt_one
      have h_diff : s₁ - s₀ ≤ δ/2 := by linarith
      have h_nonneg : 0 ≤ s₁ - s₀ := by linarith
      rw [← abs_neg, neg_sub, abs_of_nonneg h_nonneg]
      linarith
    constructor
    · simp only [gt_iff_lt, s₁,s₀,← Subtype.coe_lt_coe]
      apply lt_min
      · exact (lt_add_iff_pos_right _).mpr (half_pos hδ)
      · exact t₀_lt_one
    · simp only [ s₁, s₀]
      exact dist_case

  obtain ⟨t₁, ht₁⟩ := h_t₁_ge_t₀_in_eps_delta_bound

  --- let a = xcoord_path t₁ > 0
  let a := xcoord_path t₁
  have ha : a > 0 := by
    unfold a xcoord_path
    have h_pathT₁ : h_path t₁ ∈ S := by
      cases h_pathConn.somePath_mem t₁ with
      | inl hS => exact hS
      | inr h_Z =>
          exfalso
          have x_coord_eq_zero : (h_path t₁).1 = 0 := by rw [h_Z];
          have ht₁_in_A : t₁ ∈ A := x_coord_eq_zero
          have h_bdd : BddAbove A := by
            use 1
            intro s hs
            exact unitInterval.le_one s
          have h_le : t₁ ≤ t₀ := le_csSup h_bdd ht₁_in_A
          have h_le_real : (t₁ : ℝ) ≤ (t₀ : ℝ) := Subtype.coe_le_coe.mpr h_le
          have : ¬(t₁ > t₀) := not_lt_of_ge h_le
          exact this ht₁.1

    have h_pathT₁_x_pos : (h_path t₁).1 > 0 := by
      obtain ⟨x, hxI, hx_eq⟩ := h_pathT₁
      dsimp [pos_real] at hxI
      rw [← hx_eq]
      exact (Set.mem_Ioi.mp hxI)
    exact h_pathT₁_x_pos

  --The image x(p([t0, t1])) is connected
  let intervalT₀T₁ := Set.Icc t₀ t₁

  have xcoord_pathOfT₀T₁Conn:
      IsConnected (xcoord_path '' intervalT₀T₁) := by

    have hConn : IsConnected intervalT₀T₁ := by
      unfold intervalT₀T₁
      refine isConnected_Icc ?_
      · exact le_of_lt ht₁.1
    have hCont : ContinuousOn xcoord_path intervalT₀T₁ := by
      apply xcoord_pathContinuous.continuousOn

    exact hConn.image _ hCont

  -- and contains 0 = x(p(t₀)) and a = x(p(t₁))
  let zero :=  xcoord_path t₀

  have leftEnd :
      zero ∈ ( xcoord_path '' intervalT₀T₁) := by
      use t₀
      constructor
      · simp only [intervalT₀T₁, Set.mem_Icc]
        constructor
        · exact le_refl t₀
        · exact le_of_lt ht₁.1
      · rfl

  have rightEnd :
      a ∈ ( xcoord_path '' intervalT₀T₁) := by
      use t₁
      constructor
      · simp only [intervalT₀T₁, Set.mem_Icc]
        constructor
        · exact le_of_lt ht₁.1
        · exact le_refl t₁
      · rfl

  --and every connected subset of R is an interval, so
  -- (3.3) [0, a] ⊂ x(p([t0, t1])).
  let intervalAZero := Set.Icc zero a
  have intervalAZeroSubOfT₀T₁Xcoord : intervalAZero ⊆ xcoord_path '' intervalT₀T₁ := by

    apply IsConnected.Icc_subset
    · exact xcoord_pathOfT₀T₁Conn
    · exact leftEnd
    · exact rightEnd

  --let xs_pos_peak a sequence of x-values where sin(1/x) = 1
  -- i.e. for any k ∈ ℕ , sin(1/xs_pos_peak(k)) = 1
  -- xs_pos_peak converges to 0 as k → ∞
  -- thus there are some indicies i for wich xs_pos_peak i is in [0, a]

  have h_existsSeqInInterval :  ∃ i : ℕ, i ≥ 1 ∧ xs_pos_peak i ∈ intervalAZero  := by

    have h_conv := Metric.tendsto_nhds.mp xs_pos_peak_tendsto_zero (a/2) (by positivity)
    rw [Filter.eventually_atTop] at h_conv
    obtain ⟨N, hN⟩ :=  h_conv

    let j :=  max 1 N
    use j
    constructor
    · exact le_max_left 1 N
    · unfold intervalAZero
      simp only [Set.mem_Icc]
      constructor
      · unfold zero
        rw [h_xcoord_path_at_zero_eq_zero]
        exact xs_pos_peak_pos j
      · have h_pos : xs_pos_peak j ≤ a := by
          have hj : j ≥ N := le_max_right 1 N
          have h_dist : dist (xs_pos_peak j) 0 < a / 2 := hN j hj
          rw [Real.dist_eq] at h_dist
          have h_nonneg : 0 ≤ xs_pos_peak j := xs_pos_peak_pos j
          rw [sub_zero, abs_of_nonneg h_nonneg] at h_dist
          linarith
        exact h_pos

  -- Now we can show that there exists s₁ in [t₀, t₁] ⊆ [t₀, t₀ + δ) such that:
  -- 1. h_path(s₁) = (*,1)
  have h_Path_s₁ :  ∃ s₁ ∈ intervalT₀T₁, (h_path s₁).2 = 1 := by

    obtain ⟨i, ⟨ hige ,hi⟩ ⟩ := h_existsSeqInInterval
    obtain ⟨s₁, hs₁⟩ := intervalAZeroSubOfT₀T₁Xcoord hi
    use s₁
    constructor
    · exact hs₁.1
    · have : (h_path s₁).2 = Real.sin ((xs_pos_peak i)⁻¹) := by
        have h : (h_path s₁) ∈ S := by
          have h_in_T : h_path s₁ ∈ T := h_pathConn.somePath_mem s₁
          cases h_in_T with
                | inl hS => exact hS
                | inr h_Z =>
                  exfalso
                  have h_eq_path : h_path s₁ = (0, 0) := by simpa using h_Z
                  have h_x_zero : (h_path s₁).1 = 0 := by rw [h_eq_path];
                  have h_x_eq_seq : (h_path s₁).1 = xs_pos_peak i := hs₁.2
                  have h_seq_zero : xs_pos_peak i = 0 := by rw [← h_x_eq_seq, h_x_zero]
                  have h_sin_one : Real.sin (xs_pos_peak i)⁻¹ = 1 := h_sin_xs_pos_peak_eq_one i hige
                  rw [h_seq_zero] at h_sin_one
                  simp at h_sin_one

        obtain ⟨xpos_real, hxInpos_real, h_eq_path⟩ := h

        dsimp [sine_curve] at h_eq_path
        have xIsSeq: xpos_real = xs_pos_peak i := by
          have h_eq_x : (h_path s₁).1 = xpos_real := (congrArg Prod.fst h_eq_path).symm
          have h_eq_path_seq : (h_path s₁).1 = xs_pos_peak i := hs₁.2
          exact Eq.trans h_eq_x.symm h_eq_path_seq
        rw [xIsSeq] at h_eq_path
        rw [← h_eq_path]
      rw [this]
      exact h_sin_xs_pos_peak_eq_one i hige


  have h_path_contradiction : False := by

    obtain ⟨x₁, hx₁, h_pathx₁⟩ := h_Path_s₁

    have x₁_close_to_t₀ : dist x₁ t₀ < δ := by
      unfold intervalT₀T₁ at hx₁
      simp only [Set.mem_Icc] at hx₁
      have hx₁Delta: ∀ t ∈ intervalT₀T₁, dist t t₀ < δ := by
        intro t ht
        unfold intervalT₀T₁ at ht
        simp only [Set.mem_Icc] at ht

        have dist_t_t₀_le_dist_t₁_t₀ : dist t t₀ ≤ dist t₁ t₀ := by

          rw [Subtype.dist_eq, Subtype.dist_eq]
          have h1 : t₀ ≤ t := ht.1
          have h2 : t ≤ t₁ := ht.2
          have h3 : (t₀ : ℝ) < t₁ := Subtype.coe_lt_coe.mpr ht₁.1

          change |(t : ℝ) - (t₀ : ℝ)| ≤ |(t₁ : ℝ) - (t₀ : ℝ)|
          rw [abs_of_nonneg, abs_of_nonneg]
          · simp only [sub_le_sub_iff_right]
            exact Subtype.coe_le_coe.mpr h2
          · simp only [sub_nonneg]
            exact le_of_lt h3
          · simp only [sub_nonneg]
            exact Subtype.coe_le_coe.mpr h1
        calc dist t t₀ ≤ dist t₁ t₀ := dist_t_t₀_le_dist_t₁_t₀
            _ = dist t₀ t₁ := by rw [dist_comm t₀ t₁]
            _ < δ := ht₁.2
      apply hx₁Delta
      · exact hx₁

    have path_far : dist (h_path x₁) (h_path t₀) > 1/2 := by
      rw [h_pathT₀]
      unfold z
      simp only [dist_eq_norm]
      have : ‖h_path x₁ - (0, 0)‖ ≥ |(h_path x₁).2 - 0| := by
        exact norm_ge_abs_snd
      apply gt_of_ge_of_gt this
      simp only [h_pathx₁]
      norm_num

    have path_close : dist (h_path x₁) (h_path t₀) < 1/2 := by
      apply ht
      exact x₁_close_to_t₀

    rw [h_pathT₀] at path_close
    rw [h_pathT₀] at path_far
    exact lt_asymm path_close path_far

  exfalso
  · exact h_path_contradiction

theorem T_isconn_not_path_conn : IsConnected T ∧ ¬IsPathConnected T :=
  ⟨T_is_conn,T_is_not_path_conn ⟩
