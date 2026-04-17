module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Predictable

@[expose] public section

open Filter Set TopologicalSpace Function MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {ι : Type*} [LinearOrder ι] [OrderBot ι]

def round_down (times : Finset ι) (j : ι) :=
  (insert ⊥ {s ∈ times | s < j}).max' (by simp)

lemma round_down_bot {s : Finset ι}
    : round_down s ⊥ = ⊥ :=
  eq_bot_iff.mpr <| Finset.max'_le _ _ _ (by simp)

lemma round_down_lt_of_ne_bot {s : Finset ι} {i : ι} (hi : i ≠ ⊥)
    : round_down s i < i := by
  apply lt_of_le_of_ne
  · apply Finset.max'_le
    intro y hy
    obtain rfl | hy_mem := Finset.mem_insert.mp hy
    · simp
    · apply le_of_lt (by aesop)
  · simp_rw [round_down]
    contrapose! hi
    rw [Finset.max'_eq_iff] at hi
    aesop

lemma round_down_le {s : Finset ι} {i : ι}
    : round_down s i ≤ i := by
  by_cases! h : i = ⊥
  · simpa [h] using round_down_bot
  · exact le_of_lt <| round_down_lt_of_ne_bot h

lemma round_down_le_of_subset {s t : Finset ι} {i : ι}
    (h : s ⊆ t) : round_down s i ≤ round_down t i := by
  apply Finset.max'_le
  intro y hy
  apply Finset.le_max'
  aesop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma measurableSet_predictable_univ_prod {m : MeasurableSpace Ω}
    {𝓕 : MeasureTheory.Filtration ι m} {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s)
    : MeasurableSet[𝓕.predictable] (univ ×ˢ s) := by
  rw [(by simp : univ = {⊥} ∪ Set.Ioi ⊥), Set.union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioi_prod hs

lemma measurableSet_predictable_Iic_prod {m : MeasurableSpace Ω}
    {𝓕 : MeasureTheory.Filtration ι m} {i} {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s)
    : MeasurableSet[𝓕.predictable] (Set.Iic i ×ˢ s) := by
  rw [(by simp : Set.Iic i = {⊥} ∪ Set.Ioc ⊥ i), Set.union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioc_prod ⊥ i hs

variable {β : Type*} {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β]
variable {X : ι → Ω → β} {𝓕 : Filtration ι mΩ}

lemma StronglyAdapted.isPredictable_rounddown {times : Finset ι} (h_adap : StronglyAdapted 𝓕 X) :
      MeasureTheory.IsPredictable 𝓕 (fun i ω ↦ X (round_down times i) ω) := by
  let Y t (x : ι × Ω) := X (round_down t x.1) x.2
  let api n i := (h_adap i).approx n
  let Z n times (x : ι × Ω) := api n (round_down times x.1) x.2
  apply stronglyMeasurable_of_tendsto (u := atTop) (f := fun n x ↦ api n (round_down times x.1) x.2)
  · intro n
    apply (@SimpleFunc.mk _ 𝓕.predictable _ (Z n times) _ _).stronglyMeasurable
    · intro b
      refine times.induction_on_max ?_ ?_
      · have : Z n ∅ ⁻¹' {b} = univ ×ˢ (api n ⊥ ⁻¹' {b}) := by aesop
        simp_rw [Z] at this
        rw [this]
        refine measurableSet_predictable_univ_prod ?_
        have := (h_adap ⊥); measurability
      intro t times ht_max hm
      have : Z n (insert t times) ⁻¹' {b} =
          ((Z n times ⁻¹' {b}) ∩ (Set.Iic t ×ˢ univ)) ∪ (Set.Ioi t) ×ˢ (api n t ⁻¹' {b}) := by
        ext ⟨i, ω⟩
        simp_rw [Z]
        by_cases! hi : i ≤ t
        · have : round_down (insert t times) i = round_down times i := by
            simp_rw [round_down]; congr 2; grind
          rw [mem_preimage, this]; aesop
        · have : round_down (insert t times) i = t := by
            rw [round_down, Finset.max'_eq_iff]
            refine ⟨by aesop, ?_⟩
            grind -- maybe remove?
          rw [mem_preimage, this]; aesop
      rw [this]
      apply MeasurableSet.union
      · apply MeasurableSet.inter
        · assumption
        · refine measurableSet_predictable_Iic_prod (by measurability)
      · refine measurableSet_predictable_Ioi_prod (by measurability)
    · simp_rw [Z]
      apply Set.Finite.subset (s := (⋃ i ∈ (range (round_down times)), range (api n i)))
      · apply Set.Finite.biUnion
        · apply Set.Finite.subset (s := insert ⊥ times) (by aesop)
          intro i hi
          obtain ⟨j, rfl⟩ := mem_range.mp hi
          rw [← Finset.coe_insert, Finset.mem_coe]
          apply Finset.mem_of_subset (s₁ := insert ⊥ ({s ∈ times | s < j})) (by simp)
          apply Finset.max'_mem
        exact fun i _ ↦ by apply @(api n i).finite_range
      exact fun _ _ ↦ by aesop
  · rw [tendsto_pi_nhds]
    exact fun x ↦ by apply StronglyMeasurable.tendsto_approx

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]

lemma StronglyAdapted.isPredictable_of_leftContinuous (h_adap : StronglyAdapted 𝓕 X)
    (h_cont : ∀ ω a, ContinuousWithinAt (X · ω) (Set.Iic a) a) :
    MeasureTheory.IsPredictable 𝓕 X := by
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  rw [IsPredictable]
  let times n := Finset.image (Set.enumerateCountable hd_count ⊥) (Finset.range n)
  apply stronglyMeasurable_of_tendsto (u := atTop) (f := fun n x ↦ X (round_down (times n) x.1) x.2)
  · exact fun _ ↦ StronglyAdapted.isPredictable_rounddown (by aesop)
  rw [tendsto_pi_nhds]
  intro ⟨i, ω⟩
  specialize h_cont ω i; simp only [uncurry_apply_pair]
  apply h_cont.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall <| fun _ ↦ by simpa using round_down_le⟩
  apply tendsto_atTop_isLUB
  · intro a b hab
    apply round_down_le_of_subset
    simp_rw [times]
    exact Finset.image_subset_image (by aesop)
  · by_cases! hi_bot : i = ⊥
    · simp [hi_bot, round_down_bot]
    rw [isLUB_congr (t := (Set.Iio i))]
    · apply isLUB_Iio
    ext j; simp_rw [mem_upperBounds]; constructor
    · intro hj k hk
      rw [mem_Iio] at hk
      obtain ⟨r, hr_mem, hr_lt⟩ := hd_dense.exists_between hk
      have := Set.subset_range_enumerate hd_count ⊥ hr_mem
      obtain ⟨n, h_rn⟩ := mem_range.mp this
      trans round_down (times (n + 1)) i
      · trans r
        · apply le_of_lt (by aesop)
        apply Finset.le_max' _ _ (by aesop)
      · apply hj _ (by aesop)
    · intro hj k hk
      apply hj
      rw [mem_Iio]
      obtain ⟨y, rfl⟩ := mem_range.1 hk
      apply round_down_lt_of_ne_bot hi_bot
end MeasureTheory
