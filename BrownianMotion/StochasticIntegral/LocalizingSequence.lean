/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Probability.Process.Stopping
import BrownianMotion.StochasticIntegral.Predictable
import BrownianMotion.Auxiliary.WithTop
import BrownianMotion.Auxiliary.IsStoppingTime
import BrownianMotion.Auxiliary.StoppedProcess
import BrownianMotion.StochasticIntegral.Cadlag

/-! # Localizing sequences of stopping times

-/

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A pre-localizing sequence is a sequence of stopping times that tends almost surely
to infinity. -/
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)

lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := by filter_upwards with ω using tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι] {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω; exact hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

lemma measure_iInter_of_ae_antitone {ι : Type*}
    [Countable ι] [Preorder ι] [IsDirected ι fun (x1 x2 : ι) ↦ x1 ≤ x2]
    {s : ι → Set Ω} (hs : ∀ᵐ ω ∂P, Antitone (s · ω))
    (hsm : ∀ (i : ι), MeasureTheory.NullMeasurableSet (s i) P) (hfin : ∃ (i : ι), P (s i) ≠ ⊤) :
    P (⋂ (i : ι), s i) = ⨅ (i : ι), P (s i) := by
  set t : ι → Set Ω := fun i ↦ ⋂ j ≤ i, s j with ht
  have hst (i : ι) : s i =ᵐ[P] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i by
      exact propext this
    simp only [ht, Set.mem_iInter]
    refine ⟨fun (h : s i ω) j hj ↦ ?_, fun h ↦ h i le_rfl⟩
    change s j ω
    specialize hω hj
    simp only [le_Prop_eq] at hω
    exact hω h
  rw [measure_congr <| Filter.EventuallyEq.countable_iInter hst, Antitone.measure_iInter]
  · exact iInf_congr <| fun i ↦ measure_congr <| (hst i).symm
  · intros i j hij
    simp only [ht]
    rw [(_ : ⋂ k ≤ j, s k = (⋂ k ≤ i, s k) ∩ (⋂ k ∈ {k | k ≤ j ∧ ¬ k ≤ i}, s k))]
    · exact Set.inter_subset_left
    · ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_inter_iff, and_imp]
      grind
  · exact fun _ ↦ NullMeasurableSet.iInter <| fun j ↦ NullMeasurableSet.iInter <| fun _ ↦ hsm j
  · obtain ⟨i, hi⟩ := hfin
    refine ⟨i, (lt_of_le_of_lt ?_ <| lt_top_iff_ne_top.2 hi).ne⟩
    rw [measure_congr (hst i)]

lemma isLocalizingSequence_of_isPreLocalizingSequence
    {τ : ℕ → Ω → WithTop ι} (h𝓕 : IsRightContinuous 𝓕) (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime (n : ℕ) := IsStoppingTime.biInf (s := {j | j ≥ n})
    (Set.to_countable {j | j ≥ n}) (fun j _ ↦ hτ.isStoppingTime j)
  mono :=  ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup ?_
    intro n m hnm
    simp only [ge_iff_le, le_iInf_iff, iInf_le_iff]
    intro k hk i hi
    grind

section

omit [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
variable [SecondCountableTopology ι] [IsFiniteMeasure P]

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, ∃ k, P {ω | σ n k ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n ↦ ?_⟩
  by_contra hn; push Not at hn
  suffices (1 / 2) ^ n ≤ P (⋂ k : ℕ, {ω | σ n k ω < min (τ n ω) (T n)}) by
    refine (by simp : ¬ (1 / 2 : ℝ≥0∞) ^ n ≤ 0) <| this.trans <| nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    rw [WithTop.tendsto_atTop_nhds_top_iff] at hTop
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone, le_iInf_iff]
  · exact fun k ↦ (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp only [lt_inf_iff, le_Prop_eq] at *
    change σ n j ω < τ n ω ∧ σ n j ω < T n → σ n i ω < τ n ω ∧ σ n i ω < T n
    grind
  · intro i
    refine MeasurableSet.nullMeasurableSet ?_
    have hMσ := ((hσ n).isStoppingTime i).measurable
    have hMτ := (hτ.isStoppingTime n).measurable
    simp_rw [lt_inf_iff]
    rw [(_ : {ω | σ n i ω < τ n ω ∧ σ n i ω < T n} = {ω | σ n i ω < τ n ω} ∩ {ω | σ n i ω < T n})]
    · exact MeasurableSet.inter
        (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
        <| measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
    · rfl
  · exact ⟨0, measure_ne_top P _⟩

/-- Auxliary defintion for `isPreLocalizingSequence_of_isLocalizingSequence` which constructs a
strictly increasing sequence from a given sequence. -/
def mkStrictMonoAux (x : ℕ → ℕ) : ℕ → ℕ
| 0 => x 0
| n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1

lemma mkStrictMonoAux_strictMono (x : ℕ → ℕ) : StrictMono (mkStrictMonoAux x) := by
  refine strictMono_nat_of_lt_succ <| fun n ↦ ?_
  simp only [mkStrictMonoAux]
  exact lt_of_le_of_lt (le_max_right (x (n + 1)) _) (lt_add_one (max (x (n + 1)) _))

lemma le_mkStrictMonoAux (x : ℕ → ℕ) : ∀ n, x n ≤ mkStrictMonoAux x n
| 0 => by simp [mkStrictMonoAux]
| n + 1 => by
    simp only [mkStrictMonoAux]
    exact (le_max_left (x (n + 1)) (mkStrictMonoAux x n)).trans <|
       Nat.le_add_right (max (x (n + 1)) (mkStrictMonoAux x n)) 1

lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk ∧ ∃ T : ℕ → ι, Tendsto T atTop atTop
      ∧ ∀ n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, mkStrictMonoAux_strictMono nk, T, hT, fun n ↦
    le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp only [lt_inf_iff, le_Prop_eq]
  change σ n (mkStrictMonoAux nk n) ω < τ n ω ∧ σ n (mkStrictMonoAux nk n) ω < T n →
    σ n (nk n) ω < τ n ω ∧ σ n (nk n) ω < T n
  grind

lemma isPreLocalizingSequence_of_isLocalizingSequence
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk
      ∧ IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, hnk, T, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n ↦ (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by norm_num)
  have hτTop := hτ.tendsto_top
  filter_upwards [ae_eventually_notMem this.ne, hτTop] with ω hω hωτ
  replace hT := hωτ.min hT.tendsto_withTop_atTop_nhds_top
  simp_rw [eventually_atTop, not_lt, ← eventually_atTop] at hω
  rw [min_self] at hT
  rw [← min_self ⊤]
  refine hωτ.min <| tendsto_of_tendsto_of_tendsto_of_le_of_le' hT tendsto_const_nhds hω ?_
  simp only [le_top, eventually_atTop, ge_iff_le, implies_true, exists_const]

end

end ConditionallyCompleteLinearOrderBot

section cadlag

section LinearOrder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

open Classical in
/-- Given a property on paths which holds almost surely for a stochastic process, we construct a
localizing sequence by setting the stopping time to be ∞ whenever the property holds. -/
noncomputable
def LocalizingSequenceOfProp (X : ι → Ω → E) (p : (ι → E) → Prop) : ℕ → Ω → WithTop ι :=
  Function.const _ <| fun ω ↦ if p (X · ω) then ⊤ else ⊥

omit [OrderBot ι] in
lemma isStoppingTime_ae_const [HasUsualConditions 𝓕 P] (τ : Ω → WithTop ι) (c : WithTop ι)
    (hτ : τ =ᵐ[P] Function.const _ c) :
    IsStoppingTime 𝓕 τ := by
  intros i
  suffices P {ω | τ ω ≤ i} = 0 ∨ P {ω | τ ω ≤ ↑i}ᶜ = 0 by
    obtain h | h := this
    · exact HasUsualConditions.IsComplete h i
    · exact (HasUsualConditions.IsComplete h i).of_compl
  obtain hle | hgt := le_or_gt c i
  · refine Or.inr <| ae_iff.1 ?_
    filter_upwards [hτ] with ω rfl using hle
  · refine Or.inl ?_
    rw [← compl_compl {ω | τ ω ≤ i}]
    refine ae_iff.1 ?_
    filter_upwards [hτ] with ω hω
    simp [hω, hgt]

variable [TopologicalSpace ι] [OrderTopology ι]

lemma isLocalizingSequence_localizingSequenceOfProp [HasUsualConditions 𝓕 P] {p : (ι → E) → Prop}
    (hpX : ∀ᵐ ω ∂P, p (X · ω)) :
    IsLocalizingSequence 𝓕 (LocalizingSequenceOfProp X p) P where
  isStoppingTime n := by
    refine isStoppingTime_ae_const (P := P) _ ⊤ ?_
    filter_upwards [hpX] with ω hω
    rw [LocalizingSequenceOfProp, Function.const_apply, Function.const_apply, if_pos hω]
  mono := ae_of_all _ <| fun ω i j hij ↦ by simp [LocalizingSequenceOfProp]
  tendsto_top := by
    filter_upwards [hpX] with ω hω
    simp [LocalizingSequenceOfProp, if_pos hω]

variable [Zero E]

end LinearOrder

end cadlag

end ProbabilityTheory
