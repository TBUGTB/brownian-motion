/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.Cadlag
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset Function
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ} [IsFiniteMeasure P]

section Countable

-- TODO: Mathlib version uses `ε • (P ...) ≤ ENNReal.ofReal (∫ ω in ..., ... ∂P)`
-- which should be changed to `ε • (P.real ...) ≤ ∫ ω in ..., ... ∂P`,
-- using the more recent `Measure.real` API as follows:
lemma maximal_ineq' {𝓕 : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hsub : Submartingale f 𝓕 P)
    (hnonneg : 0 ≤ f) (ε : ℝ≥0) (n : ℕ) :
    ε • P.real {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      f n ω ∂P := by
  calc
    _ = (ε * P {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}).toReal :=
      (ENNReal.toReal_smul ..).symm
    _ ≤ _ := by
      apply ENNReal.toReal_le_of_le_ofReal (integral_nonneg (hnonneg n))
      exact maximal_ineq hsub hnonneg n

-- NB: This might be shortended, if the mathlib result is generalized to
-- a more general discrete index space.
/-- Auxiliary lemma for `maximal_ineq_countable` where the index set is a Finset. -/
lemma maximal_ineq_finset (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) {n : ι}
    {J : Finset ι} (hJn : ∀ i ∈ J, i ≤ n) (hnJ : n ∈ J) :
    ε • P.real {ω | (ε : ℝ) ≤ J.sup' ⟨n, hnJ⟩ fun i ↦ Y i ω} ≤
     ∫ ω in {ω | (ε : ℝ) ≤ J.sup' ⟨n, hnJ⟩ fun i ↦ Y i ω}, Y n ω ∂P := by
  -- Convert to ℕ-indexed submartingale defined by (Y(j₁), ⋯, Y(jₘ), Y(n), Y(n), ⋯)
  -- where J = {j₁, ⋯, jₘ, n}, and j₁ < ⋯ < jₘ = n
  classical
  let toι (k : ℕ) : ι := if hn : k < #J then J.orderEmbOfFin rfl ⟨k, hn⟩ else n
  have toι_mono : Monotone toι := fun k l hkl ↦ by
    unfold toι
    split_ifs with hk hl hl
    exacts [(J.orderEmbOfFin rfl).monotone hkl, hJn _ (orderEmbOfFin_mem ..), by omega, le_refl _]
  have hcongr (ω : Ω) : J.sup' ⟨n, hnJ⟩ (fun i ↦ Y i ω) =
      (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω := by
    unfold toι
    apply le_antisymm
    · refine sup'_le _ _ fun i hi ↦ ?_
      refine le_sup'_of_le _ (b := ((J.orderIsoOfFin rfl).symm ⟨i, hi⟩ : ℕ)) ?_ ?_
      · simp
      · simp [orderEmbOfFin]
    · refine sup'_le _ _ fun k hk ↦ ?_
      apply le_sup' fun i ↦ Y i ω
      split_ifs
      exacts [orderEmbOfFin_mem .., hnJ]
  calc
    _ = ε • P.real
        {ω | (ε : ℝ) ≤ (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω} := by
      simp_rw [hcongr]
    _ ≤ ∫ ω in {ω | (ε : ℝ) ≤ (range (#J + 1)).sup' nonempty_range_add_one fun k ↦ Y (toι k) ω},
        Y n ω ∂P := by
      convert maximal_ineq' (hsub.indexComap toι_mono) (fun _ ↦ hnonneg _) ε #J
      simp [toι]
    _ = _ := by
      congr! with ω
      simp_rw [hcongr]

variable [Countable ι]

lemma _root_.tendsto_inv_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ ((n : 𝕜) + 1)⁻¹) atTop (𝓝 0) :=
  by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜)

set_option backward.isDefEq.respectTransparency false in
lemma maximal_ineq_countable_ennReal (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0)
    (n : ι) :
    ε • P.real {ω | (ε : ℝ≥0∞) ≤ ⨆ i ≤ n, ENNReal.ofReal (Y i ω)} ≤
      ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ i ≤ n, ENNReal.ofReal (Y i ω)}, Y n ω ∂P := by
  let supY (ω : Ω) := ⨆ i ≤ n, ENNReal.ofReal (Y i ω)
  -- WLOG `ε > 0`
  rcases eq_or_ne ε 0 with rfl | hε0
  · simpa using integral_nonneg (hnonneg n)
  -- Construct an increasing sequence `J k` of finite sets with union `(-∞, n]`
  have : Nonempty ι := ⟨n⟩
  obtain ⟨f : ℕ → ι, hf⟩ := exists_surjective_nat ι
  let J (k : ℕ) : Finset ι := insert n ((range k).image f |>.filter (· ≤ n))
  have hJn (k) : ∀ i ∈ J k, i ≤ n := by simp [J]
  have hnJ (k) : n ∈ J k := by simp [J]
  have hJmono {k l : ℕ} (hkl : k ≤ l) : J k ⊆ J l := by
    unfold J
    gcongr
    exact image_mono _ (range_mono hkl)
  have hmemJ (k) (h : f k ≤ n) : f k ∈ J (k + 1) := by
    simpa [J, h] using .inr ⟨k, by omega, rfl⟩
  -- The long inequality (see blueprint)
  have hlt (ε' : ℝ≥0) (hε' : ε' < ε) :
    ε' • P.real {ω | (ε' : ℝ≥0∞) < supY ω} ≤ ∫ ω in {ω | (ε' : ℝ≥0∞) ≤ supY ω}, Y n ω ∂P := by
    have hbdd : BddAbove <| Set.range fun k ↦
        ∫ ω in {ω | (ε' : ℝ) ≤ (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω}, Y n ω ∂P := by
      use ∫ ω, Y n ω ∂P
      simpa [upperBounds] using fun k ↦
        setIntegral_le_integral (hsub.integrable n) (.of_forall (hnonneg n))
    calc
      _ = ε' • P.real (⋃ i ≤ n, {ω | (ε' : ℝ) < Y i ω}) := by
        congr!; ext ω
        simp_rw [supY, lt_iSup_iff]
        lift Y to ι → Ω → ℝ≥0 using hnonneg
        simp
      _ = ε' • P.real (⋃ k, {ω | (ε' : ℝ) < (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω}) := by
        congr!; ext ω
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, lt_sup'_iff]
        constructor
        · rintro ⟨i, hi, h⟩
          obtain ⟨k, rfl⟩ := hf i
          use k + 1, f k, hmemJ k hi
        · rintro ⟨k, i, hi, h⟩
          use i, by simp [hJn k i hi]
      _ = ⨆ k, ε' • P.real {ω | (ε' : ℝ) < (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω} := by
        rw [Measure.real, Monotone.measure_iUnion, ENNReal.toReal_iSup]
        · apply Real.mul_iSup_of_nonneg
          simp
        · finiteness
        intro k l hkl
        simpa using fun ω i hi h ↦ ⟨i, hJmono hkl hi, h⟩
      _ ≤ ⨆ k, ε' • P.real {ω | (ε' : ℝ) ≤ (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω} := by
        gcongr
        · use ε' • P.real Set.univ
          simp only [upperBounds, le_sup'_iff, Set.mem_range, forall_exists_index,
            forall_apply_eq_imp_iff, Set.mem_setOf_eq]
          intro k
          gcongr
          · finiteness -- gcongr bug?
          simp
        · finiteness -- gcongr bug?
        · exact fun h ↦ h.le
      _ ≤ ⨆ k, ∫ ω in {ω | (ε' : ℝ) ≤ (J k).sup' ⟨n, hnJ k⟩ fun i ↦ Y i ω}, Y n ω ∂P := by
        gcongr with k
        · exact hbdd
        · exact maximal_ineq_finset hsub hnonneg ε' (hJn k) (hnJ k)
      _ ≤ ∫ ω in {ω | (ε' : ℝ≥0∞) ≤ supY ω}, Y n ω ∂P := by
        refine (ciSup_le_iff hbdd).mpr fun k ↦ ?_
        gcongr with ω
        · filter_upwards; exact fun ω ↦ hnonneg _ _
        · exact (hsub.integrable n).restrict
        · simp only [le_sup'_iff, forall_exists_index, and_imp]
          intro i hi h
          apply le_iSup₂_of_le i (hJn k i hi)
          lift Y to ι → Ω → ℝ≥0 using hnonneg
          simpa using h
  -- Take `ε' := ε - 1 / (r + 1) ↑ ε` where `r → ∞`
  -- (This is needed instead of `ε' ↑ ε` directly, because `tendsto_measure_iInter_atTop` and
  -- `tendsto_setIntegral_of_antitone` lemmas require `atTop` instead of `𝓝[<] ε`)
  clear * - hε0 hsub hlt
  let ε' (r : ℕ) : ℝ≥0 := ε - (r + 1 : ℝ≥0)⁻¹
  -- TODO: is there a way to avoid duplicaiton below
  have hinter_lt (c : Ω → ℝ≥0∞) : {ω | ε ≤ c ω} = ⋂ r : ℕ, {ω | ε' r < c ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h r
      push_cast [ε']
      exact h.trans_lt' (ENNReal.sub_lt_self (by simp) (by simpa) (by simp))
    · refine fun h ↦ le_of_forall_lt fun ε' hε' ↦ ?_
      have : Tendsto (fun r : ℕ ↦ (((r + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
        rw [← ENNReal.tendsto_toNNReal_iff (by finiteness) (by finiteness)]
        change Tendsto (fun r : ℕ ↦ _) _ _
        simpa using tendsto_inv_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
      obtain ⟨r, hr⟩ := this.eventually_lt_const (tsub_pos_of_lt hε') |>.exists
      exact (lt_tsub_comm.mp hr).trans (h r)
  have hinter_le (c : Ω → ℝ≥0∞) : {ω | ε ≤ c ω} = ⋂ r : ℕ, {ω | ε' r ≤ c ω} := by
    -- same as hinter, but with ≤ instead of <
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h r
      push_cast [ε']
      exact h.trans' tsub_le_self
    · refine fun h ↦ le_of_forall_lt fun ε' hε' ↦ ?_
      have : Tendsto (fun r : ℕ ↦ (((r + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
        rw [← ENNReal.tendsto_toNNReal_iff (by finiteness) (by finiteness)]
        change Tendsto (fun r : ℕ ↦ _) _ _
        simpa using tendsto_inv_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
      obtain ⟨r, hr⟩ := this.eventually_lt_const (tsub_pos_of_lt hε') |>.exists
      exact (lt_tsub_comm.mp hr).trans_le (h r)
  have hmeasY (i : ι) : Measurable (Y i) :=
    (hsub.stronglyMeasurable i).measurable.mono (𝓕.le _) (le_refl _)
  have hε'mono : Monotone fun r ↦ (ε' r : ℝ≥0∞) := by intro _ _ _; dsimp [ε']; gcongr
  -- LHS of `hlt` tends to LHS of `⊢`
  have hl : Tendsto
      (fun r : ℕ ↦ ε' r • P.real {ω | ε' r < supY ω})
      atTop (𝓝 <| ε • P.real {ω | ε ≤ supY ω}) := by
    apply (show Tendsto .. by simpa using tendsto_inv_add_atTop_nhds_zero_nat.const_sub ε).smul
    erw [ENNReal.tendsto_toReal_iff (by finiteness) (by finiteness)]
    convert tendsto_measure_iInter_atTop ?_ ?_ ?_
    · exact hinter_lt _
    · infer_instance
    · exact fun r ↦ (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet
    · exact Set.monotone_preimage.comp_antitone hε'mono.Ioi
    · use 0; finiteness
  -- RHS of `hlt` tends to RHS of `⊢`
  have hr : Tendsto
      (fun r : ℕ ↦ ∫ ω in {ω | ε' r ≤ supY ω}, Y n ω ∂P)
      atTop (𝓝 <| ∫ ω in {ω | ε ≤ supY ω}, Y n ω ∂P) := by
    convert tendsto_setIntegral_of_antitone ?_ ?_ ?_
    · exact hinter_le _
    · infer_instance
    · exact fun r ↦ measurableSet_le measurable_const (by fun_prop)
    · exact Set.monotone_preimage.comp_antitone hε'mono.Ici
    · use 0; exact (hsub.integrable n).integrableOn
  -- Conclude
  exact le_of_tendsto_of_tendsto hl hr (.of_forall fun r ↦ hlt _ (by simpa [ε'] using hε0.bot_lt))

-- TODO: add this to Mathlib
attribute [aesop (rule_sets := [finiteness]) safe apply] ENNReal.nnreal_smul_ne_top

theorem _root_.ENNReal.ofReal_smul {a : ℝ≥0} {b : ℝ} :
    ENNReal.ofReal (a • b) = a • ENNReal.ofReal b := by
  erw [ENNReal.ofReal_mul (by simp)]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Alternative form of `Submartingale.ae_bddAbove`. -/
lemma _root_.MeasureTheory.Submartingale.iSup_ofReal_ne_top (hsub : Submartingale Y 𝓕 P)
    (hnonneg : 0 ≤ Y) (n : ι) : ∀ᵐ ω ∂P, ⨆ i ≤ n, ENNReal.ofReal (Y i ω) ≠ ∞ := by
  let supY (ω : Ω) := ⨆ i ≤ n, ENNReal.ofReal (Y i ω)
  have hmeasY (i : ι) : Measurable (Y i) :=
    (hsub.stronglyMeasurable i).measurable.mono (𝓕.le _) (le_refl _)
  change P {ω | ¬supY ω ≠ ∞} = 0
  push_neg
  convert Antitone.measure_iInter (s := fun ε : ℝ≥0 ↦ {ω | (ε : ℝ≥0∞) ≤ supY ω}) ?_ ?_ ?_
  · ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · simp +contextual
    · apply ENNReal.eq_top_of_forall_nnreal_le
  · symm
    erw [← le_bot_iff]
    calc
      _ ≤ ⨅ ε > (0 : ℝ≥0), ENNReal.ofReal (ε⁻¹ • ∫ ω in {ω | ε ≤ supY ω}, Y n ω ∂P) := by
        gcongr with ε
        refine le_iInf fun hε0 ↦ ?_
        rw [ENNReal.ofReal_smul, le_inv_smul_iff_of_pos hε0, ENNReal.le_ofReal_iff_toReal_le]
        · simpa using maximal_ineq_countable_ennReal hsub hnonneg ε n
        · finiteness
        · exact setIntegral_nonneg (measurableSet_le measurable_const (by fun_prop))
            fun ω _ ↦ hnonneg n ω
      _ ≤ ⨅ ε > (0 : ℝ≥0), ENNReal.ofReal (ε⁻¹ • ∫ ω, Y n ω ∂P) := by
        gcongr with ε hε0
        · exact .of_forall (hnonneg n)
        · exact hsub.integrable n
        · exact P.restrict_le_self
      _ = 0 := by
        apply iInf_eq_of_tendsto
        · intro ε₁ ε₂ h
          refine le_iInf fun hε₁ ↦ ?_
          simp only [iInf_pos (hε₁.trans_le h)]
          gcongr
          exact integral_nonneg (hnonneg n)
        · convert (ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero (𝕜 := ℝ≥0)).smul_const
            (∫ ω, Y n ω ∂P))).congr' ?_
          · simp
          · filter_upwards [eventually_gt_atTop 0] with ε hε0
            simp [hε0]
  · exact Set.monotone_preimage.comp_antitone ENNReal.coe_mono.Ici
  · exact fun r ↦ (measurableSet_le measurable_const (by fun_prop)).nullMeasurableSet
  · use 0; finiteness

/-- Doob's maximal inequality implies that the supremum process of a nonnegative submartingale is
a.s. bounded. -/
theorem _root_.MeasureTheory.Submartingale.ae_bddAbove_Iic (hsub : Submartingale Y 𝓕 P)
    (hnonneg : 0 ≤ Y) (n : ι) :
    ∀ᵐ ω ∂P, BddAbove ((fun i ↦ Y i ω) '' Set.Iic n) := by
  filter_upwards [hsub.iSup_ofReal_ne_top hnonneg n] with ω h
  use (⨆ i ≤ n, ENNReal.ofReal (Y i ω)).toReal
  rintro _ ⟨i, hi : i ≤ n, rfl⟩
  rw [← ENNReal.ofReal_le_iff_le_toReal h]
  exact le_iSup₂ (f := fun i _ ↦ ENNReal.ofReal (Y i ω)) i hi

/-- **Doob's maximal inequality** for a countable index set. -/
theorem maximal_ineq_countable (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    -- We use `⨆ i : Set.Iic n` instead of `⨆ i ≤ n` because of incomplete API for `cbiSup`.
    ε • P.real {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, Y i ω} ≤
      ∫ ω in {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, Y i ω}, Y n ω ∂P := by
  have (ω : Ω) : ⨆ i : Set.Iic n, Y i ω = (⨆ i ≤ n, ENNReal.ofReal (Y i ω)).toReal := by
    rw [iSup_subtype', ENNReal.toReal_iSup]
    · congr with i
      rw [ENNReal.toReal_ofReal (hnonneg _ _)]
    · finiteness
  have : {ω | ε ≤ ⨆ i : Set.Iic n, Y i ω} =ᵐ[P] {ω | ε ≤ ⨆ i ≤ n, ENNReal.ofReal (Y i ω)} := by
    filter_upwards [hsub.iSup_ofReal_ne_top hnonneg n] with ω htop
    ext
    change _ ≤ _ ↔ _ ≤ _
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_iff_le_toReal htop, this]
  rw [measureReal_congr this, setIntegral_congr_set this]
  exact maximal_ineq_countable_ennReal hsub hnonneg ε n

theorem maximal_ineq_norm_countable (hmar : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P.real {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, ‖X i ω‖} ≤
      ∫ ω in {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, ‖X i ω‖}, ‖X n ω‖ ∂P :=
  maximal_ineq_countable hmar.submartingale_norm (fun _ _ ↦ norm_nonneg _) ε n

end Countable

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

theorem continuous_of_rightContinuous {β : Type*} [TopologicalSpace β] {f : ι → β}
    (hf_cont : RightContinuous f) :
    @Continuous ι β (TopologicalSpace.generateFrom {s : Set ι | ∃ (i j : ι), s = Set.Ico i j})
    inferInstance f := by
  sorry

theorem dense_of_dense {S : Set ι} (hS : Dense S) (hi : {x | 𝓝[>] x = ⊥} ⊆ S) :
    @Dense ι (TopologicalSpace.generateFrom {s : Set ι | ∃ i j, s = Set.Ico i j}) S := by
  sorry

theorem maximal_ineq_ennReal (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι)
    (hY_cont : ∀ ω, RightContinuous (Y · ω)) :
    ε * P.real {ω | (ε : ℝ≥0∞) ≤ ⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω)} ≤
      ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω)}, Y n ω ∂P := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense (Set.Iic n)
  let S : Set (Set.Iic n) := T ∪ {x | 𝓝[>] x = ⊥}
  have hS : Countable S := by
    rw [Set.countable_coe_iff]
    exact (Set.Countable.mono (by simp) hT_countable).union countable_setOf_isolated_right
  have hn : ⟨n, le_rfl⟩ ∈ S := by
    refine Set.mem_union_right ?_ ?_
    have : Set.Ioi (⟨n, le_rfl⟩ : Set.Iic n) = ∅ := by ext x; aesop
    simp_all [nhdsWithin]
  have hc (ω : Ω) : @Continuous (Set.Iic n) ℝ≥0∞ (TopologicalSpace.generateFrom
    {s : Set (Set.Iic n) | ∃ i j, s = Set.Ico i j}) inferInstance
    (ENNReal.ofReal ∘ (Y · ω) ∘ (Subtype.val : Set.Iic n → ι)) := by
    refine continuous_of_rightContinuous ?_
    simp_all only [RightContinuous]
    refine fun a => ENNReal.continuous_ofReal.continuousWithinAt.comp (t := Set.univ) ?_ ?_
    · exact (hY_cont ω _).comp continuous_subtype_val.continuousWithinAt fun x => by simp
    · exact fun x => by simp
  have hd : @Dense (Set.Iic n) (TopologicalSpace.generateFrom
    {s : Set (Set.Iic n) | ∃ i j, s = Set.Ico i j}) S :=
    dense_of_dense (hT_dense.mono (by grind)) (by grind)
  have h1 (ω : Ω) := @Dense.ciSup' (Set.Iic n) ℝ≥0∞ inferInstance inferInstance
    inferInstance (ENNReal.ofReal ∘ (Y · ω) ∘ Subtype.val) (TopologicalSpace.generateFrom
    {s : Set (Set.Iic n) | ∃ i j, s = Set.Ico i j}) S hd (hc ω)
  have h2 (ω : Ω) : ⨆ s : S, ENNReal.ofReal (Y s ω) =
    ⨆ s ≤ (⟨⟨n, le_rfl⟩, hn⟩ : S), ENNReal.ofReal (Y s ω) := by simp_all [iSup_subtype]
  calc
  -- Use `simp_all only` because `simp_all` is very slow.
  _ = ε * P.real {ω | ε ≤ ⨆ s : S, ENNReal.ofReal (Y s ω)} := by simp_all only [comp_apply]
  _ = ε * P.real {ω | ε ≤ ⨆ s ≤ (⟨⟨n, le_rfl⟩, hn⟩ : S), ENNReal.ofReal (Y s ω)} := by
    simp_all only [comp_apply]
  _ ≤ ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ s ≤ (⟨⟨n, le_rfl⟩, hn⟩ : S), ENNReal.ofReal (Y s ω)},
    Y n ω ∂P := by
    have : Monotone (fun x : S => x.1.1) := Subtype.mono_coe _
    exact maximal_ineq_countable_ennReal (hsub.indexComap this) (fun x => hnonneg _) ε _
  _ ≤ ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ s : S, ENNReal.ofReal (Y s ω)}, Y n ω ∂P := by
    simp_all only [comp_apply, Std.le_refl]
  _ = _ := by simp_all only [comp_apply]

set_option backward.isDefEq.respectTransparency false in
lemma _root_.MeasureTheory.Submartingale.rightCont_iSup_ofReal_ne_top (hsub : Submartingale Y 𝓕 P)
    (hnonneg : 0 ≤ Y) (n : ι) (hY_cont : ∀ ω, RightContinuous (Y · ω)) :
    ∀ᵐ ω ∂P, ⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω) ≠ ∞ := by
  let supY (ω : Ω) := ⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω)
  have hmeasY (i : ι) : Measurable (Y i) :=
    (hsub.stronglyMeasurable i).measurable.mono (𝓕.le _) (le_refl _)
  change P {ω | ¬supY ω ≠ ∞} = 0
  push_neg
  convert Antitone.measure_iInter (s := fun ε : ℝ≥0 ↦ {ω | (ε : ℝ≥0∞) ≤ supY ω}) ?_ ?_ ?_
  · ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · simp +contextual
    · apply ENNReal.eq_top_of_forall_nnreal_le
  · symm
    erw [← le_bot_iff]
    calc
      _ ≤ ⨅ ε > (0 : ℝ≥0), ENNReal.ofReal (ε⁻¹ • ∫ ω in {ω | ε ≤ supY ω}, Y n ω ∂P) := by
        gcongr with ε
        refine le_iInf fun hε0 ↦ ?_
        rw [ENNReal.ofReal_smul, le_inv_smul_iff_of_pos hε0, ENNReal.le_ofReal_iff_toReal_le]
        · simpa using maximal_ineq_ennReal hsub hnonneg ε n hY_cont
        · finiteness
        · refine setIntegral_nonneg (measurableSet_le measurable_const ?_)
            fun ω _ ↦ hnonneg n ω
          sorry
      _ ≤ ⨅ ε > (0 : ℝ≥0), ENNReal.ofReal (ε⁻¹ • ∫ ω, Y n ω ∂P) := by
        gcongr with ε hε0
        · exact .of_forall (hnonneg n)
        · exact hsub.integrable n
        · exact P.restrict_le_self
      _ = 0 := by
        apply iInf_eq_of_tendsto
        · intro ε₁ ε₂ h
          refine le_iInf fun hε₁ ↦ ?_
          simp only [iInf_pos (hε₁.trans_le h)]
          gcongr
          exact integral_nonneg (hnonneg n)
        · convert (ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero (𝕜 := ℝ≥0)).smul_const
            (∫ ω, Y n ω ∂P))).congr' ?_
          · simp
          · filter_upwards [eventually_gt_atTop 0] with ε hε0
            simp [hε0]
  · exact Set.monotone_preimage.comp_antitone ENNReal.coe_mono.Ici
  · sorry
  · use 0; finiteness

theorem maximal_ineq_nonneg (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι)
    (hY_cont : ∀ ω, RightContinuous (Y · ω)) :
    ε * P.real {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, Y i ω} ≤
      ∫ ω in {ω | (ε : ℝ) ≤ ⨆ i : Set.Iic n, Y i ω}, Y n ω ∂P := by
  have (ω : Ω) : ⨆ i : Set.Iic n, Y i ω = (⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω)).toReal := by
    rw [ENNReal.toReal_iSup]
    · congr with i
      rw [ENNReal.toReal_ofReal (hnonneg _ _)]
    · finiteness
  have : {ω | ε ≤ ⨆ i : Set.Iic n, Y i ω} =ᵐ[P]
    {ω | ε ≤ ⨆ i : Set.Iic n, ENNReal.ofReal (Y i ω)} := by
    filter_upwards [hsub.rightCont_iSup_ofReal_ne_top hnonneg n hY_cont] with ω htop
    ext
    change _ ≤ _ ↔ _ ≤ _
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_iff_le_toReal htop, this]
  rw [measureReal_congr this, setIntegral_congr_set this]
  exact maximal_ineq_ennReal hsub hnonneg ε n hY_cont

-- Remove the nonnegative constraint on `ε`.
theorem maximal_ineq (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ) (n : ι)
    (hY_cont : ∀ ω, RightContinuous (Y · ω)) :
    ε * P.real {ω | ε ≤ ⨆ i : Set.Iic n, Y i ω} ≤
      ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic n, Y i ω}, Y n ω ∂P := by
  by_cases! hε : 0 ≤ ε
  · exact maximal_ineq_nonneg hsub hnonneg ⟨ε, hε⟩ n hY_cont
  · exact (mul_nonpos_of_nonpos_of_nonneg hε.le measureReal_nonneg).trans
      (integral_nonneg (hnonneg n))

theorem maximal_ineq_norm (hmar : Martingale X 𝓕 P) (ε : ℝ) (n : ι)
    (hX_cont : ∀ ω, RightContinuous (X · ω)) :
    ε • P.real {ω | ε ≤ ⨆ i : Set.Iic n, ‖X i ω‖} ≤
      ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic n, ‖X i ω‖}, ‖X n ω‖ ∂P := by
  refine maximal_ineq hmar.submartingale_norm (fun _ _ ↦ norm_nonneg _) ε n fun ω => ?_
  exact (hX_cont ω).continuous_comp continuous_norm

end ProbabilityTheory
