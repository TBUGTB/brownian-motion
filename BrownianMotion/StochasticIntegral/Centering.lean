/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Centering

/-!
# Lemmas about the Doob decomposition

-/

@[expose] public section

open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

@[simp]
lemma martingalePart_zero : martingalePart X 𝓕 μ 0 = X 0 := by
  simp [martingalePart]

lemma predictablePart_add_one (n : ℕ) :
    predictablePart X 𝓕 μ (n + 1) =
      predictablePart X 𝓕 μ n + μ[X (n + 1) - X n | 𝓕 n] := by
  simp [predictablePart, Finset.sum_range_add]

lemma predictablePart_smul (c : ℝ) (n : ℕ) :
    predictablePart (c • X) 𝓕 μ n =ᵐ[μ] c • predictablePart X 𝓕 μ n := by
  unfold predictablePart
  have hsum :
      (∑ i ∈ Finset.range n, fun ω ↦ μ[(c • X) (i + 1) - (c • X) i | 𝓕 i] ω) =ᵐ[μ]
        ∑ i ∈ Finset.range n, fun ω ↦ c • μ[X (i + 1) - X i | 𝓕 i] ω := by
    refine (eventuallyEq_sum (s := Finset.range n)
      (f := fun i : ℕ ↦ fun ω ↦ μ[(c • X) (i + 1) - (c • X) i | 𝓕 i] ω)
      (g := fun i : ℕ ↦ fun ω ↦ c • μ[X (i + 1) - X i | 𝓕 i] ω)
      (fun i _ ↦ ?_)).trans ?_
    · simpa [Pi.smul_apply, sub_eq_add_neg, smul_add, smul_neg] using
        (condExp_smul c (X (i + 1) - X i) (𝓕 i))
    · exact Filter.EventuallyEq.rfl
  filter_upwards [hsum] with ω hω
  simpa [Finset.smul_sum] using hω

lemma martingalePart_smul (c : ℝ) (n : ℕ) :
    martingalePart (c • X) 𝓕 μ n =ᵐ[μ] c • martingalePart X 𝓕 μ n := by
  filter_upwards [predictablePart_smul (X := X) c n] with ω hω
  calc
    martingalePart (c • X) 𝓕 μ n ω = c • X n ω - predictablePart (c • X) 𝓕 μ n ω := by
      simp [martingalePart, Pi.smul_apply]
    _ = c • X n ω - c • predictablePart X 𝓕 μ n ω := by simpa [Pi.smul_apply] using congrArg id hω
    _ = c • martingalePart X 𝓕 μ n ω := by
      simp [martingalePart, sub_eq_add_neg, smul_add, smul_neg]

lemma predictablePart_add {Y : ℕ → Ω → E} (hXint : ∀ n, Integrable (X n) μ)
    (hYint : ∀ n, Integrable (Y n) μ) (n : ℕ) :
    predictablePart (X + Y) 𝓕 μ n =ᵐ[μ] predictablePart X 𝓕 μ n + predictablePart Y 𝓕 μ n := by
  unfold predictablePart
  have hsum :
      (∑ i ∈ Finset.range n, fun ω ↦ μ[(X + Y) (i + 1) - (X + Y) i | 𝓕 i] ω) =ᵐ[μ]
        ((∑ i ∈ Finset.range n, fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω) +
          ∑ i ∈ Finset.range n, fun ω ↦ μ[Y (i + 1) - Y i | 𝓕 i] ω) := by
    refine (eventuallyEq_sum (s := Finset.range n)
      (f := fun i : ℕ ↦ fun ω ↦ μ[(X + Y) (i + 1) - (X + Y) i | 𝓕 i] ω)
      (g := fun i : ℕ ↦ fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω + μ[Y (i + 1) - Y i | 𝓕 i] ω)
      (fun i _ ↦ ?_)).trans ?_
    · simpa [Pi.add_apply, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
        (condExp_add ((hXint (i + 1)).sub (hXint i)) ((hYint (i + 1)).sub (hYint i)) (𝓕 i))
    · exact (by
        ext ω
        simp [Finset.sum_add_distrib] : (∑ i ∈ Finset.range n,
          fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω + μ[Y (i + 1) - Y i | 𝓕 i] ω) =
            ((∑ i ∈ Finset.range n, fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω) +
              ∑ i ∈ Finset.range n, fun ω ↦ μ[Y (i + 1) - Y i | 𝓕 i] ω)).eventuallyEq
  filter_upwards [hsum] with ω hω
  simpa using hω

lemma martingalePart_add {Y : ℕ → Ω → E} (hXint : ∀ n, Integrable (X n) μ)
    (hYint : ∀ n, Integrable (Y n) μ) (n : ℕ) :
    martingalePart (X + Y) 𝓕 μ n =ᵐ[μ] martingalePart X 𝓕 μ n + martingalePart Y 𝓕 μ n := by
  filter_upwards [predictablePart_add (𝓕 := 𝓕) hXint hYint n] with ω hω
  simp_all [martingalePart, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

lemma isPredictable_predictablePart : IsPredictable 𝓕 (predictablePart X 𝓕 μ) :=
  isPredictable_of_measurable_add_one (by simp [measurable_const'])
    fun n ↦ (stronglyAdapted_predictablePart n).measurable

lemma IsPredictable.predictablePart_eq [SigmaFiniteFiltration μ 𝓕]
    (hX : IsPredictable 𝓕 X) (hXint : ∀ n, Integrable (X n) μ)
    (n : ℕ) :
    predictablePart X 𝓕 μ n =ᵐ[μ] X n - X 0 := by
  unfold predictablePart
  have hsum :
      (∑ i ∈ Finset.range n, fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω) =ᵐ[μ]
        ∑ i ∈ Finset.range n, fun ω ↦ (X (i + 1) - X i) ω := by
    refine (eventuallyEq_sum (s := Finset.range n)
      (f := fun i : ℕ ↦ fun ω ↦ μ[X (i + 1) - X i | 𝓕 i] ω)
      (g := fun i : ℕ ↦ fun ω ↦ (X (i + 1) - X i) ω)
      (fun i _ ↦ ?_)).trans ?_
    · exact condExp_of_aestronglyMeasurable' (𝓕.le i)
        (((hX.measurable_add_one i).stronglyMeasurable.aestronglyMeasurable).sub
          (hX.adapted i).aestronglyMeasurable)
        ((hXint (i + 1)).sub (hXint i))
    · exact Filter.EventuallyEq.rfl
  filter_upwards [hsum] with ω hω
  apply eq_sub_iff_add_eq.mpr
  have htel : X n ω = X 0 ω + ∑ i ∈ Finset.range n, (X (i + 1) - X i) ω := by
    simpa using congrArg (fun f => f ω) (Finset.eq_sum_range_sub X n)
  simpa [hω, add_comm, add_left_comm, add_assoc] using htel.symm

lemma IsPredictable.martingalePart_eq [SigmaFiniteFiltration μ 𝓕]
    (hX : IsPredictable 𝓕 X) (hXint : ∀ n, Integrable (X n) μ)
    (n : ℕ) :
    martingalePart X 𝓕 μ n =ᵐ[μ] X 0 := by
  filter_upwards [hX.predictablePart_eq (μ := μ) hXint n] with ω hω
  simp_all [martingalePart]

-- todo: feel free to replace `Preorder E` by something stonger if needed
lemma Submartingale.monotone_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart X 𝓕 μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hX.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

lemma Submartingale.nonneg_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart X 𝓕 μ n ω := by
  filter_upwards [hX.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

end MeasureTheory
