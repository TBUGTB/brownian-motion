/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import BrownianMotion.StochasticIntegral.ConvexWeights

/-!
# Komlos lemmas

-/

variable {E Ω : Type*} {mΩ : MeasurableSpace Ω}

open Filter MeasureTheory
open scoped Topology NNReal ENNReal

lemma komlos_convex [AddCommMonoid E] [Module ℝ E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : ℝ)⁻¹ • (g n + g m)) < δ := by
  obtain ⟨M, hM⟩ := hφ_bdd
  let r : ℕ → ℝ := fun n ↦ sInf (Set.image φ (convexHull ℝ (Set.range (fun m ↦ f (n + m)))))
  have hr_nondec n : r n ≤ r (n + 1) := by
    apply_rules [csInf_le_csInf]
    · exact ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg x⟩
    · exact ⟨_, ⟨ _, subset_convexHull ℝ _ ⟨0, rfl⟩, rfl⟩⟩
    · refine Set.image_mono <| convexHull_min ?_ (convex_convexHull ℝ _)
      rintro _ ⟨m, rfl⟩; exact subset_convexHull ℝ _ ⟨m + 1, by simp [add_comm, add_left_comm]⟩
  obtain ⟨A, hA⟩ : ∃ A, Filter.Tendsto r Filter.atTop (nhds A) := by
    refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ hr_nondec) ?_⟩
    exact ⟨M, Set.forall_mem_range.mpr fun n ↦ csInf_le
      ⟨0, Set.forall_mem_image.mpr fun x hx ↦ hφ_nonneg x⟩
        (Set.mem_image_of_mem _ <| subset_convexHull ℝ _
          <| Set.mem_range_self 0) |> le_trans <| by simpa using hM n⟩
  obtain ⟨g, hg⟩ :
      ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ (Set.range (fun m ↦ f (n + m))))
          ∧ (∀ n, φ (g n) ≤ A + 1 / (n + 1)) := by
    have h_exists_g :
        ∀ n, ∃ g ∈ convexHull ℝ (Set.range (fun m ↦ f (n + m))), φ g ≤ A + 1 / (n + 1) := by
      intro n
      have h_exists_g :
          ∃ g ∈ convexHull ℝ (Set.range (fun m ↦ f (n + m))), φ g < A + 1 / (n + 1) := by
        have h_exists_g : r n < A + 1 / (n + 1) := by
          exact lt_add_of_le_of_pos (le_of_tendsto_of_tendsto tendsto_const_nhds hA
            (Filter.eventually_atTop.2 ⟨n, fun m hm ↦ by
              induction hm <;> [tauto; linarith [hr_nondec ‹_›]]⟩)) (by positivity)
        contrapose! h_exists_g
        exact le_csInf ⟨ _, Set.mem_image_of_mem _ <| subset_convexHull ℝ _
          <| Set.mem_range_self 0 ⟩ fun x hx ↦ by
            rcases hx with ⟨ g, hg, rfl ⟩; exact h_exists_g g hg
      exact ⟨h_exists_g.choose, h_exists_g.choose_spec.1, le_of_lt h_exists_g.choose_spec.2⟩
    exact ⟨fun n ↦ Classical.choose (h_exists_g n),
      fun n ↦ Classical.choose_spec (h_exists_g n) |>.1,
        fun n ↦ Classical.choose_spec (h_exists_g n) |>.2⟩
  refine ⟨g, hg.1, fun δ δpos ↦ ?_⟩
  obtain ⟨ε, εpos, hε⟩ := exists_between (div_pos δpos zero_lt_four)
  obtain ⟨N, hN⟩ : ∃ N, r N ≥ A - ε ∧ 1 / (N + 1) ≤ ε := by
    rcases Metric.tendsto_atTop.mp hA ε εpos with ⟨N, hN⟩
    exact ⟨N + ⌈ε⁻¹⌉₊, by linarith [abs_lt.mp (hN (N + ⌈ε⁻¹⌉₊) (by grind))], by
      simpa using inv_le_of_inv_le₀ εpos (by linarith [Nat.le_ceil (ε⁻¹)])⟩
  refine ⟨N, fun n m hn hm ↦ ?_⟩
  have h_convex : φ ((1 / 2 : ℝ) • (g n + g m)) ≥ A - ε := by
    have h_convex :
        (1 / 2 : ℝ) • (g n + g m) ∈ convexHull ℝ (Set.range (fun m ↦ f (N + m))) := by
      simp only [one_div, gt_iff_lt, ge_iff_le, tsub_le_iff_right, smul_add] at *
      refine convex_convexHull ℝ _ ?_ ?_ ?_ ?_ ?_ <;> norm_num
      · refine convexHull_mono (Set.range_subset_iff.2 fun m ↦ ?_) (hg.1 n)
        exact ⟨m + (n - N), by grind⟩
      · refine convexHull_mono ?_ (hg.1 m)
        exact Set.range_subset_iff.2 fun k ↦ ⟨k + (m - N), by
          simp [show N + (k + (m - N)) = m + k by grind]⟩
    refine le_trans hN.1 ?_
    exact csInf_le ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg _⟩ ⟨_, h_convex, rfl⟩
  norm_num at *
  linarith [hg.2 n, hg.2 m, inv_anti₀
    (by positivity) (by norm_cast; grind : (n : ℝ) + 1 ≥ N + 1), inv_anti₀
      (by positivity) (by norm_cast; grind : (m : ℝ) + 1 ≥ N + 1)]

set_option backward.isDefEq.respectTransparency false in
lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
      ∃ (x : E), Tendsto g atTop (𝓝 x) := by
  let φ : E → ℝ := fun f ↦ ‖f‖ ^ 2
  have φ_nonneg : 0 ≤ φ := fun f ↦ sq_nonneg ‖f‖
  have φ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M := by
    rcases h_bdd with ⟨M, hM⟩
    exact ⟨M ^ 2, fun n ↦ pow_le_pow_left₀ (norm_nonneg _) (hM n) 2⟩
  rcases komlos_convex φ_nonneg φ_bdd with ⟨g, hg, h⟩
  use g
  have parallelogram_identity (x y : E) :
      2⁻¹ * ‖x‖ ^ 2 + 2⁻¹ * ‖y‖ ^ 2 - ‖(2 : ℝ)⁻¹ • (x + y)‖ ^ 2 = ‖y - x‖ ^ 2 / 4 := by
    have : (2 : ℝ)⁻¹ • (x + y) = (2 : ℝ)⁻¹ • (x + y) := by rfl
    rw [this, norm_smul_of_nonneg (by norm_num), mul_pow, add_comm x y]
    let para := parallelogram_law_with_norm ℝ y x
    linear_combination - para / 4
  have g_cauchy : CauchySeq g := by
    rw [Metric.cauchySeq_iff]
    intro δ δpos
    rcases h (δ ^ 2 / 4) (by positivity) with ⟨N, hn⟩
    use N
    intro m mgeN n ngeN
    specialize hn n m ngeN mgeN
    dsimp [φ] at hn
    rw [parallelogram_identity (g n) (g m)] at hn
    have : ‖g m - g n‖ ^ 2 < δ ^ 2 := by linarith
    rw [dist_eq_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg (g m - g n)) (by positivity) (by norm_num)).mp this
  rcases CompleteSpace.complete g_cauchy with ⟨x, hx⟩
  sorry

def C [AddCommMonoid E] [Module ℝ E] (x : ℕ → E) : Set (ℕ → E) :=
  {g : ℕ → E | ∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ x (n + m))}

-- Lemma 2.11 in the blueprint
lemma komlos_convergence [NormedAddCommGroup E] [Module ℝ E] [IsBoundedSMul ℝ E]
  {x : ℕ → E} {xlim : E} (hxlim : Tendsto x atTop (𝓝 xlim)) :
  ∀ ε > 0, ∃ N, ∀ y ∈ C x, ∀ n ≥ N, ‖y n - xlim‖ < ε := by
  intro ε εpos
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ‖x n - xlim‖ < ε := by
    rcases Metric.tendsto_atTop.mp hxlim ε εpos with ⟨N, hN⟩
    use N
    intro n hn
    rw [← dist_eq_norm (x n) xlim]
    exact hN n hn
  use N
  intro y hy n hn
  obtain ⟨N, a, ha_sum, ha_pos, hay⟩ : (∃ N : ℕ → Finset ℕ, ∃ a : (n : ℕ) → ℕ → ℝ,
    (∑ m ∈ N n, a n m) = 1 ∧ (∀ m ∈ N n, 0 ≤ a n m) ∧ (∀ n, y n = ∑ m ∈ N n, a n m • x n)) := by
    sorry
  rw [hay n]
  rw [show xlim = (1 : ℝ) • xlim by simp]
  rw [← ha_sum]
  rw [Finset.sum_smul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  apply lt_of_le_of_lt (norm_sum_le (N n) (fun m ↦ a n m • (x n - xlim)))

  have hsum_le :
      ∑ i ∈ N n, ‖a n i • (x n - xlim)‖ ≤ ∑ i ∈ N n, ‖a n i‖ * ‖x n - xlim‖ := by
    exact Finset.sum_le_sum (fun m hm ↦ norm_smul_le (a n m) (x n - xlim))

  refine lt_of_le_of_lt hsum_le ?_
  rw [← Finset.sum_mul]

  have hanorm : ∑ i ∈ N n, ‖a n i‖ = ∑ i ∈ N n, a n i := by
      apply Finset.sum_congr rfl
      intro m hm
      refine Real.norm_of_nonneg ?_
      exact ha_pos m hm

  rw [hanorm, ha_sum]
  simp only [one_mul, gt_iff_lt]
  exact RCLike.ofReal_lt_ofReal.mp (hN n hn)

noncomputable section
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]

def gtilde (cw : ℕ → ℕ → ℕ →₀ ℝ) (x : ℕ → ℕ → E) (k : ℕ) (n : ℕ) : E :=
  ∑ m ∈ (cwIteratedMul cw k n).support, (cwIteratedMul cw k n m) • (x (k+1) m)
  -- note that it has to be k+1, not k for x!

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma gtilde_update (cw : ℕ → ℕ → ℕ →₀ ℝ) (x : ℕ → ℕ → E) {k k' : ℕ} {f : ℕ → ℕ →₀ ℝ}
    (hk' : k' > k) :
    gtilde cw x k = gtilde (Function.update cw k' f) x k := by
  funext n
  simp only [gtilde]
  rw [← cwIteratedMul_update cw hk']

lemma komlos_step [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ)
  (cw : ℕ → ℕ → ℕ →₀ ℝ) (hcw: ∀ k n m, 0 ≤ cw k n m) :
  ∃ (cw_new : ℕ → ℕ → ℕ →₀ ℝ),
    (∃ glim : E, Tendsto (fun n ↦ ∑ m ∈ (cwIteratedMul cw_new (k + 1) n).support,
      cwIteratedMul cw_new (k + 1) n m • x (k+1) m) atTop (𝓝 glim))
    ∧ (∀ i ≤ k, cw_new i = cw i)
    ∧ (∀ k n m, 0 ≤ cw_new k n m) := by

  have gtilde_bound : ∃ M, ∀ n, ‖gtilde cw x k n‖ ≤ M := by sorry -- maybe turn this into a lemma

  obtain ⟨g_step, gstep_conv, gstep_lim⟩ := komlos_norm (gtilde_bound)

  have cw_step_exists : ∃ w : ℕ → ℕ →₀ ℝ,
    (∀ n m, 0 ≤ w n m) ∧ (∀ n, ∀ m ≤ n, w n m = 0)
    ∧ (∀ n, ∑ i ∈ (w n).support, w n i = 1)
    ∧ ∀ n, ∑ i ∈ (w n).support, (w n) i • gtilde cw x k i = g_step n := by
    have original_weights : ∀ n, ∃ w : ℕ →₀ ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i ∈ w.support, w i = 1
      ∧ ∑ i ∈ w.support, w i • gtilde cw x k (n + i) = g_step n := by
      exact (fun n ↦ convex_weights_of_mem_convexHull_indexed (gstep_conv n))

    -- Need to use choice to finish this, along the lines of:
    -- exact ⟨fun n => Classical.choose (weights n), fun n => Classical.choose_spec (weights n)⟩
    sorry

  obtain ⟨cw_step, ⟨hnonneg, hzero, hsum, hcombo⟩⟩ := cw_step_exists

  let cw_new := Function.update cw (k+1) cw_step

  have g_new_expression (n : ℕ) : g_step n = ∑ m ∈ (cwIteratedMul cw_new (k + 1) n).support,
    cwIteratedMul cw_new (k + 1) n m • x (k+1) m := by
    rw [← hcombo n]

    have aux: (cwIteratedMul cw_new (k + 1) n) = (cwmul (cw_step n) (cwIteratedMul cw k)) := by
      rw [cwIteratedMul]
      beta_reduce
      unfold cw_new
      rw [Function.update_self, cwIteratedMul_update cw (show k+1 > k by omega)]

    rw [aux]
    unfold gtilde
    rw [cwmul_eq]
    beta_reduce

    set cwold := cwIteratedMul cw k
    simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]

    refine Finset.sum_congr rfl ?_
    intro i hi

    have subset: (cwold i).support ⊆ (cwmul (cw_step n) cwold).support := by
      refine support_subset_cwmul_support hi ?_ ?_
      · sorry
      · unfold cwold -- here we need to use hcw, probably through a further intermediate lemma
        sorry

    -- TODO: Use Finset.sum_subset or similar to finish this proof
    sorry

  have old_indices_untouched: ∀ i ≤ k, cw_new i = cw i := sorry -- trivial by construction

  sorry

lemma komlos_convex_weights [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
    ∃ (cw : ℕ → ℕ → ℕ →₀ ℝ),
    let g k n := ∑ m ∈ (cwIteratedMul cw (k + 1) n).support,
      cwIteratedMul cw (k + 1) n m • x (k+1) m;
    ∀ k : ℕ, ∃ glim : E, Tendsto (g k) atTop (𝓝 glim) := by
  sorry

theorem komlos_L1 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {f : ℕ → Ω → E} {P : Measure Ω}
    (hf : UniformIntegrable f 1 P) :
    ∃ (g : ℕ → Ω → E) (glim : Ω → E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
      Tendsto (fun n ↦ eLpNorm (g n - glim) 1 P) atTop (𝓝 0) := by
  sorry

-- todo: check measurability hypothesis/conclusion
lemma komlos_ennreal (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    {P : Measure Ω} [IsProbabilityMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) :=
  sorry
