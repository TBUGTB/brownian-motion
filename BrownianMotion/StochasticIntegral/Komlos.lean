/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import BrownianMotion.StochasticIntegral.ConvexWeights

/-!
# Komlos lemmas

-/

@[expose] public section

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
  tauto

noncomputable section
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gtilde (cw : ℕ → ℕ → ℕ →₀ ℝ) (x : ℕ → ℕ → E) (k : ℕ) (n : ℕ) : E :=
  (convexWeightsConvolution cw k n).sum (fun m cwm ↦ cwm • (x (k+1) m))

lemma gtilde_update (cw : ℕ → ℕ → ℕ →₀ ℝ) (x : ℕ → ℕ → E) {k k' : ℕ} {f : ℕ → ℕ →₀ ℝ}
    (hk' : k' > k) :
    gtilde cw x k = gtilde (Function.update cw k' f) x k := by
  funext n
  simp only [gtilde]
  rw [← convexWeightsConvolution_update cw hk']

def komlosFormula (x : ℕ → ℕ → E) (cw : ℕ → ℕ → ℕ →₀ ℝ) (k n : ℕ) : E :=
  (convexWeightsConvolution cw k n).sum (fun m cwm ↦ cwm • x k m)

lemma komlosFormula_cong (x : ℕ → ℕ → E) {cw1 : ℕ → ℕ → ℕ →₀ ℝ} {cw2 : ℕ → ℕ → ℕ →₀ ℝ} {k : ℕ}
  (h : ∀ k' ≤ k, cw1 k' = cw2 k') :
  komlosFormula x cw1 k = komlosFormula x cw2 k := by
  unfold komlosFormula; rw [convexWeightsConvolution_cong]
  exact h

lemma convex_weights_of_mem_convexHull_reindexed {x g : ℕ → E}
    (h_convex : ∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ x (n + m))) :
    ∀ n, ∃ w : ℕ →₀ ℝ, (∀ i, 0 ≤ w i) ∧ (∀ m < n, w m = 0)
      ∧ w.sum (fun _ wi ↦ wi) = 1
      ∧ w.sum (fun i wi ↦ wi • x i) = g n := by
  intro n
  obtain ⟨w, hw_nonneg, hw_sum, hw_combo⟩ := convex_weights_of_mem_convexHull_indexed (h_convex n)
  let w' := Finsupp.embDomain ⟨fun i ↦ n + i, add_right_injective n⟩ w
  have nonneg (i : ℕ) : 0 ≤ w' i := by grind
  have zero_lt (m : ℕ) (hm : m < n) : w' m = 0 := by
    rw [Finsupp.embDomain_apply]
    split_ifs with h
    · exfalso
      rcases h with ⟨i, hi⟩
      have hnm : n ≤ m := by
        rw [← hi]
        exact Nat.le_add_right n i
      exact (Nat.not_le_of_lt hm hnm).elim
    · rfl
  have sum_one : w'.sum (fun _ wi ↦ wi) = 1 := by grind [Finsupp.sum_embDomain]
  have sum_eq : w'.sum (fun i wi ↦ wi • x i) = g n := by
    rw [Finsupp.sum_embDomain]
    simp [hw_combo]
  exact ⟨w', nonneg, zero_lt, sum_one, sum_eq⟩

variable [CompleteSpace E]

lemma komlos_base {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
  ∃ (cw : ℕ → ℕ → ℕ →₀ ℝ),
    (∃ glim : E, Tendsto (komlosFormula x cw 0) atTop (𝓝 glim))
    ∧ (∀ k n m, 0 ≤ cw k n m) ∧ (∀ k n, (cw k n).sum (fun _ wi ↦ wi) = 1) := by
    obtain ⟨g, h_convex, h_lim⟩ := komlos_norm (hx 0)
    let cw (n : ℕ) := Classical.choose (convex_weights_of_mem_convexHull_reindexed h_convex n)
    use (fun k ↦ cw)
    refine ⟨?_, ?_, ?_⟩
    · have hg (n : ℕ) : (cw n).sum (fun m cwm ↦ cwm • x 0 m) = g n := by
        exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed h_convex n)).2.2.2
      unfold komlosFormula
      simp only [convexWeightsConvolution, hg, h_lim]
    · intro k n
      exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed h_convex n)).1
    · intro k n
      exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed h_convex n)).2.2.1

lemma komlos_step {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ)
  (cw : ℕ → ℕ → ℕ →₀ ℝ) (cw_nonneg : ∀ k n m, 0 ≤ cw k n m)
  (cw_sum_one : ∀ k n, (cw k n).sum (fun _ wi ↦ wi) = 1) :
  ∃ (cw_new : ℕ → ℕ → ℕ →₀ ℝ),
    (∃ glim : E, Tendsto (komlosFormula x cw_new (k+1)) atTop (𝓝 glim))
    ∧ (∀ i ≤ k, cw_new i = cw i)
    ∧ (∀ k n m, 0 ≤ cw_new k n m)
    ∧ (∀ k n, (cw_new k n).sum (fun _ wi ↦ wi) = 1) := by
  have gtilde_bound : ∃ M, ∀ n, ‖gtilde cw x k n‖ ≤ M := convex_combination_bounded
      (convexWeightsConvolution_sum_one cw_nonneg cw_sum_one k)
      (convexWeightsConvolution_nonneg cw_nonneg k) (hx (k+1))
  obtain ⟨g_step, gstep_conv, gstep_lim⟩ := komlos_norm (gtilde_bound)
  have cw_step_exists : ∃ w : ℕ → ℕ →₀ ℝ,
    (∀ n m, 0 ≤ w n m) ∧ (∀ n, ∀ m < n, w n m = 0)
    ∧ (∀ n, (w n).sum (fun _ wi ↦ wi) = 1)
    ∧ ∀ n, (w n).sum (fun i wi ↦ wi • gtilde cw x k i) = g_step n := by
    refine ⟨fun n ↦ Classical.choose (convex_weights_of_mem_convexHull_reindexed gstep_conv n), ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n m
      exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed gstep_conv n)).1 m
    · intro n m hm
      exact (Classical.choose_spec
        (convex_weights_of_mem_convexHull_reindexed gstep_conv n)).2.1 m hm
    · intro n
      exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed gstep_conv n)).2.2.1
    · intro n
      exact (Classical.choose_spec (convex_weights_of_mem_convexHull_reindexed gstep_conv n)).2.2.2
  obtain ⟨cw_step, ⟨hnonneg, hzero, hsum, hcombo⟩⟩ := cw_step_exists
  let cw_new := Function.update cw (k+1) cw_step
  have g_new_expression (n : ℕ) :
    g_step n = (convexWeightsConvolution cw_new (k + 1) n).sum (fun m cwm ↦ cwm • x (k+1) m) := by
    rw [← hcombo n]
    set cwold := convexWeightsConvolution cw k
    have aux: (convexWeightsConvolution cw_new (k + 1) n) = (convexWeightsMul (cw_step n) cwold)
      := by
      unfold cw_new cwold
      rw [convexWeightsConvolution, Function.update_self,
          convexWeightsConvolution_update cw (show k+1 > k by grind)]
    rw [aux]
    unfold gtilde
    simp only [Finsupp.sum]
    rw [convexWeightsMul_eq (cw_step n) (convexWeightsConvolution cw k)]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have subset: (cwold i).support ⊆ (convexWeightsMul (cw_step n) cwold).support := by
      refine support_subset_convexWeightsMul_support hi ?_ ?_
      · grind only
      · unfold cwold
        intro a ha m
        exact convexWeightsConvolution_nonneg cw_nonneg k a m
    rw [Finset.smul_sum]
    simp_rw [← smul_smul]
    apply Finset.sum_subset subset ?_
    intro m hm1 hm2
    have is_zero: cwold i m = 0 := by
      grind => instantiate only [= Finsupp.mem_support_iff]
    rw [is_zero]
    simp
  have old_indices_untouched: ∀ i ≤ k, cw_new i = cw i := by grind
  have sum_one (k' n : ℕ) : ((cw_new k' n).sum fun x wi ↦ wi) = 1 := by
    unfold cw_new
    by_cases hk': k+1 = k'
    · simp_rw [hk']
      simp only [Function.update_self]
      exact (hsum n)
    · rw [← cw_sum_one k' n, Function.update_of_ne]
      grind
  use cw_new
  refine ⟨?_, old_indices_untouched, ?_, sum_one⟩
  · obtain ⟨glim, hglim⟩ := gstep_lim
    use glim
    exact Tendsto.congr g_new_expression hglim
  · unfold cw_new
    intro k' n m
    rw [Function.update]
    split_ifs
    · simp only [eq_rec_constant]
      exact hnonneg _ _
    · exact cw_nonneg k' n m

def komlos_stage {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (stage : ℕ) :
  { w : ℕ → ℕ → ℕ →₀ ℝ // (∀ k n m, 0 ≤ w k n m) ∧ ∀ k n, (w k n).sum (fun _ wi ↦ wi) = 1} :=
  match stage with
  | 0 => by
    use Classical.choose (komlos_base hx)
    exact Classical.choose_spec (komlos_base hx) |>.2
  | stage+1 => by
      let ⟨previous, hprevious⟩ := komlos_stage hx stage
      let step := komlos_step hx stage previous hprevious.1 hprevious.2
      use Classical.choose step
      exact Classical.choose_spec step |>.2.2

lemma komlos_stage_lim {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ) :
  (∃ glim : E, Tendsto (komlosFormula x (komlos_stage hx k) k) atTop (𝓝 glim)) := by
  induction k with
  | zero => exact Classical.choose_spec (komlos_base hx) |>.1
  | succ k _ => exact
      Classical.choose_spec (komlos_step hx k
        (komlos_stage hx k).val (komlos_stage hx k).prop.1 (komlos_stage hx k).prop.2) |>.1

lemma agreement_step {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) (k : ℕ) :
  ∀ i ≤ k, (komlos_stage hx k).val i = (komlos_stage hx (k+1)).val i := by
  intro i hi
  let aux := komlos_step hx k (komlos_stage hx k).val (komlos_stage hx k).prop.1
    (komlos_stage hx k).prop.2
  let ⟨_, aux2, _⟩ := Classical.choose_spec aux
  exact Eq.symm (aux2 i hi)

lemma agreement_necessary_condition {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M)
  (i k : ℕ) (hi : i ≤ k) :
  (komlos_stage hx i).val i = (komlos_stage hx k).val i := by
  let n := k-i
  suffices (komlos_stage hx i).val i = (komlos_stage hx (i+n)).val i from by
    unfold n at this
    rw [show i + (k - i) = k by grind] at this
    exact this
  induction n with
  | zero => rfl
  | succ n hn =>
  rw [← add_assoc, hn]
  apply agreement_step hx (i+n) i (by grind)

-- TODO: Add convex weight conditions: nonnegativity and summing up to 1
lemma komlos_convex_weights
    {x : ℕ → ℕ → E} (hx : ∀ i : ℕ, ∃ M : ℝ, ∀ n, ‖x i n‖ ≤ M) :
    ∃ (cw : ℕ → ℕ → ℕ →₀ ℝ), ∀ k : ℕ,
    ∃ glim : E, Tendsto (komlosFormula x cw k) atTop (𝓝 glim) := by
  have hcwStage2 (k : ℕ) :
    ∃ glim : E, Tendsto (komlosFormula x (komlos_stage hx k).val k) atTop (𝓝 glim) := by
    apply komlos_stage_lim
  let cw (k : ℕ) : ℕ → ℕ →₀ ℝ := (komlos_stage hx k).val k
  have agreement (k i : ℕ) (hi : i ≤ k) :
    cw i = (komlos_stage hx k).val i := by
    unfold cw
    apply agreement_necessary_condition hx
    exact hi
  have transfer (k : ℕ) : komlosFormula x cw k = komlosFormula x (komlos_stage hx k).val k := by
    apply komlosFormula_cong x
    exact agreement k
  use cw
  intro k
  simp_rw [transfer k]
  exact hcwStage2 k

theorem komlos_L1 [MeasurableSpace E] [BorelSpace E] {f : ℕ → Ω → E} {P : Measure Ω}
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
