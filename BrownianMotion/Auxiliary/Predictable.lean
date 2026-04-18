module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Predictable

@[expose] public section

open Filter Set TopologicalSpace Function MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {ι : Type*} [LinearOrder ι] [OrderBot ι]

/-- a helper function which (strictly) rounds down `i` onto the set `{⊥} ∪ s` -/
private def round_down (s : Finset ι) (i : ι) :=
  (insert ⊥ {j ∈ s | j < i}).max' (by simp)

private lemma round_down_bot {s : Finset ι} : round_down s ⊥ = ⊥ :=
  eq_bot_iff.mpr <| Finset.max'_le _ _ _ (by simp)

private lemma round_down_lt_of_ne_bot {s : Finset ι} {i : ι} (h : i ≠ ⊥) :
    round_down s i < i := by
  apply lt_of_le_of_ne
  · apply Finset.max'_le _ _ _ (fun _ _ ↦ by grind)
  · contrapose! h
    simp [round_down, Finset.max'_eq_iff] at h
    aesop

private lemma round_down_le_of_subset {s t : Finset ι} {i : ι} (h : s ⊆ t) :
    round_down s i ≤ round_down t i :=
  Finset.max'_le _ _ _ <| fun _ _ ↦ by apply Finset.le_max'; aesop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ}

lemma measurableSet_predictable_univ_prod {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) :
    MeasurableSet[𝓕.predictable] (univ ×ˢ s) := by
  rw [(by simp : univ = {⊥} ∪ Ioi ⊥), union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioi_prod hs

lemma measurableSet_predictable_Iic_prod {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) {i} :
    MeasurableSet[𝓕.predictable] (Iic i ×ˢ s) := by
  rw [(by simp : Iic i = {⊥} ∪ Ioc ⊥ i), union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioc_prod ⊥ i hs

variable {β : Type*} {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β]
variable {X : ι → Ω → β}

/- a 'rounded down' function is predictable -/
private lemma StronglyAdapted.isPredictable_rounddown {times : Finset ι}
    (h_adap : StronglyAdapted 𝓕 X) :
    IsPredictable 𝓕 (fun i ω ↦ X (round_down times i) ω) := by
  -- `X_ap i` approximates X at times `i`
  let X_ap n i := (h_adap i).approx n
  -- For `Y` and `Y_ap`, we keep `s` as a variable for use in the induction step
  -- `Y` is the uncurried version of the rounded down `X`
  let Y s (x : ι × Ω) := X (round_down s x.1) x.2
  -- `Y_ap` approximates `Y`
  let Y_ap n s (x : ι × Ω) := X_ap n (round_down s x.1) x.2
  apply stronglyMeasurable_of_tendsto (u := atTop) (f := fun n x ↦ Y_ap n times x)
  · intro n
    apply (@SimpleFunc.mk _ 𝓕.predictable _ (Y_ap n times) _ _).stronglyMeasurable
    · intro b
      -- induction on the largest element of `times`
      refine times.induction_on_max ?_ ?_
      · apply MeasurableSet.congr (s := univ ×ˢ (X_ap n ⊥ ⁻¹' {b})) _ (by aesop)
        exact measurableSet_predictable_univ_prod (by measurability)
      intro t times ht_max hm
      apply MeasurableSet.congr
          (s := ((Y_ap n times ⁻¹' {b}) ∩ (Iic t ×ˢ univ)) ∪ (Ioi t) ×ˢ (X_ap n t ⁻¹' {b}))
      · apply MeasurableSet.union
        · apply MeasurableSet.inter (by assumption)
          exact measurableSet_predictable_Iic_prod (by measurability)
        · exact measurableSet_predictable_Ioi_prod (by measurability)
      · ext ⟨i, ω⟩
        simp_rw [Y_ap, mem_preimage]
        by_cases! hi : i ≤ t
        · have : round_down (insert t times) i = round_down times i := by
            rw [round_down]; congr 2; grind
          rw [this]; aesop
        · have : round_down (insert t times) i = t := by
            rw [round_down, Finset.max'_eq_iff]; grind
          rw [this]; aesop
    · apply Finite.subset (s := (⋃ i ∈ (range (round_down times)), range (X_ap n i)))
          _ <| fun _ _ ↦ by aesop
      apply Finite.biUnion _ <| fun i _ ↦ by apply @(X_ap n i).finite_range
      apply Finite.subset (s := insert ⊥ times) (by aesop)
      intro i hi
      obtain ⟨j, rfl⟩ := mem_range.mp hi
      rw [← Finset.coe_insert, Finset.mem_coe]
      apply Finset.mem_of_subset (s₁ := insert ⊥ ({s ∈ times | s < j})) (by simp)
      apply Finset.max'_mem
  · simpa [Y_ap, tendsto_pi_nhds] using fun _ ↦ by apply StronglyMeasurable.tendsto_approx

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]

lemma StronglyAdapted.isPredictable_of_leftContinuous (h_adap : StronglyAdapted 𝓕 X)
    (h_cont : ∀ ω a, ContinuousWithinAt (X · ω) (Iio a) a) :
    IsPredictable 𝓕 X := by
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  let times n := Finset.image (enumerateCountable hd_count ⊥) (Finset.range n)
  rw [IsPredictable]
  apply stronglyMeasurable_of_tendsto atTop (f := fun n x ↦ X (round_down (times n) x.1) x.2)
  · exact fun _ ↦ isPredictable_rounddown (by aesop)
  rw [tendsto_pi_nhds]
  intro ⟨i, ω⟩
  apply (h_cont ω i).insert.tendsto.comp
  simp_rw [Iio_insert, tendsto_nhdsWithin_iff]
  by_cases! hi_bot : i = ⊥
  · simp [hi_bot, round_down_bot]
  refine ⟨?_, .of_forall <| fun _ ↦ le_of_lt <| round_down_lt_of_ne_bot hi_bot⟩
  apply tendsto_atTop_isLUB
      (fun _ _ _ ↦ round_down_le_of_subset <| Finset.image_subset_image (by aesop))
  by_cases! hi_bot : i = ⊥
  · simp [hi_bot, round_down_bot]
  apply (isLUB_congr _).mp (isLUB_Iio (a := i))
  -- TODO: clean up below
  ext j; simp_rw [mem_upperBounds]; constructor
  · intro hj k hk
    apply hj
    rw [mem_Iio]
    obtain ⟨y, rfl⟩ := mem_range.1 hk
    apply round_down_lt_of_ne_bot hi_bot
  · intro hj k hk
    rw [mem_Iio] at hk
    obtain ⟨r, hr_mem, hr_lt⟩ := hd_dense.exists_between hk
    have := subset_range_enumerate hd_count ⊥ hr_mem
    obtain ⟨n, h_rn⟩ := mem_range.mp this
    trans round_down (times (n + 1)) i
    · trans r
      · apply le_of_lt (by aesop)
      apply Finset.le_max' _ _ (by aesop)
    · apply hj _ (by aesop)


end MeasureTheory
