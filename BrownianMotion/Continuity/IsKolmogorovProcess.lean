/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.Chaining
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.LogSizeBallSequence

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

open MeasureTheory
open scoped ENNReal NNReal Finset

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {p q : ℝ} {M : ℝ≥0}
  {P : Measure Ω}
  {X : T → Ω → E}

structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop where
  aemeasurablePair : ∀ s t : T, @AEMeasurable _ _ (borel (E × E)) _ (fun ω ↦ (X s ω, X t ω)) P
  kolmogorovCondition : ∀ s t : T,
    ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q

section Measurability

lemma IsKolmogorovProcess.aemeasurable (hX : IsKolmogorovProcess X P p q M) (s : T) :
    AEMeasurable (X s) P := by
  have : Measurable[borel (E × E), _] (Prod.fst : E × E → E) :=
    measurable_fst.mono prod_le_borel_prod le_rfl
  exact @Measurable.comp_aemeasurable Ω E (E × E) _ _ _ (borel (E × E)) _ _ this
    (hX.aemeasurablePair s s)

omit [PseudoEMetricSpace T] in
lemma aemeasurable_pair_of_aemeasurable [SecondCountableTopology E] (hX : ∀ s, AEMeasurable (X s) P)
    (s t : T) :
    @AEMeasurable _ _ (borel (E × E)) _ (fun ω ↦ (X s ω, X t ω)) P := by
  suffices AEMeasurable (fun ω ↦ (X s ω, X t ω)) P by
    rwa [(Prod.borelSpace (α := E) (β := E)).measurable_eq] at this
  fun_prop

lemma IsKolmogorovProcess.mk_of_secondCountableTopology [SecondCountableTopology E]
    (h_meas : ∀ s, AEMeasurable (X s) P)
    (h_kol : ∀ s t : T, ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q) :
    IsKolmogorovProcess X P p q M where
  aemeasurablePair := aemeasurable_pair_of_aemeasurable h_meas
  kolmogorovCondition := h_kol

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.aestronglyMeasurable_edist
    (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    AEStronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := by
  have h_str : StronglyMeasurable[borel (E × E)] (fun p : E × E ↦ edist p.1 p.2) := by
    refine @Continuous.stronglyMeasurable _ _ (borel (E × E)) _ ?_ _ _ _ _ continuous_edist
    refine @BorelSpace.opensMeasurable _ _ (borel (E × E)) ?_
    exact @BorelSpace.mk _ _ (borel (E × E)) rfl
  exact h_str.aestronglyMeasurable.comp_aemeasurable (hX.aemeasurablePair s t)

omit [MeasurableSpace E] [BorelSpace E] in
lemma IsKolmogorovProcess.aemeasurable_edist (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    AEMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := hX.aestronglyMeasurable_edist.aemeasurable

end Measurability

lemma lintegral_sup_rpow_edist_le_card_mul_rpow (hX : IsKolmogorovProcess X P p q M)
    {ε : ℝ≥0∞} (C : Finset (T × T)) (hC : ∀ u ∈ C, edist u.1 u.2 ≤ ε) :
    ∫⁻ ω, ⨆ u ∈ C, edist (X u.1 ω) (X u.2 ω) ^ p ∂P
      ≤ #C * M * ε ^ q := by
  sorry

lemma lintegral_sup_rpow_edist_le_card_mul_rpow_of_dist_le
    (hX : IsKolmogorovProcess X P p q M) {J : Finset T} {a c : ℝ≥0∞} {n : ℕ}
    (hJ_card : #J ≤ a ^ n) (ha : 1 < a) (hc : c ≠ 0) :
    ∫⁻ ω, ⨆ (s) (t) (_hs : s ∈ J) (_ht : t ∈ J) (_hd : edist s t ≤ c),
        edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ p * a * #J * M * (c * n) ^ q := by
  sorry

section FirstTerm

variable {J : Set T}

lemma lintegral_sup_rpow_edist_cover_of_dist_le
    (hX : IsKolmogorovProcess X P p q M) (hJ : J.Finite) {C : Finset T} {ε : ℝ≥0∞}
    (hC : IsCover C ε J) (hC_subset : (C : Set T) ⊆ J)
    (hC_card : #C = internalCoveringNumber ε J)
    {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∫⁻ ω, ⨆ (s) (t) (_hs : s ∈ C) (_ht : t ∈ C) (_hd : edist s t ≤ c),
        edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (p + 2) * M * (2 * c * Nat.log2 (internalCoveringNumber ε J).toNat) ^ q
        * internalCoveringNumber ε J := by
  sorry


lemma lintegral_sup_rpow_edist_cover_rescale
    (hX : IsKolmogorovProcess X P p q M) (hJ : J.Finite)
    {C : ℕ → Finset T} {ε₀ : ℝ≥0∞}
    (hC : ∀ i, IsCover (C i) (ε₀ * 2⁻¹ ^ i) J) (hC_subset : ∀ i, (C i : Set T) ⊆ J)
    (hC_card : ∀ i, #(C i) = internalCoveringNumber (ε₀ * 2⁻¹ ^ i) J)
    {δ : ℝ≥0∞} (hδ_pos : 0 < δ) (n₂ : ℕ) (hn₂ : ε₀ * 2⁻¹ ^ n₂ < δ / 2)
    (hn₂' : δ / 2 ≤ ε₀ * 2⁻¹ ^ (n₂ - 1))
    {k m : ℕ} -- todo: def of `k` missing
    (hm : m = min n₂ k) :
    ∫⁻ ω, ⨆ (s) (t) (hs : s ∈ C k) (ht : t ∈ C k) (_hd : edist s t ≤ δ),
        edist (X (chainingSequence hC hs m) ω) (X (chainingSequence hC ht m) ω) ^ p ∂P
      ≤ 2 ^ (p + 2) * M
        * (16 * δ * Nat.log2 (internalCoveringNumber (δ/4) J).toNat) ^ q
        * internalCoveringNumber (δ/4) J := by
  sorry

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0∞} {j k m : ℕ}

lemma lintegral_sup_rpow_edist_succ (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hjk : j < k) :
    ∫⁻ ω, ⨆ (t) (ht : t ∈ C k),
        edist (X (chainingSequence hC ht j) ω) (X (chainingSequence hC ht (j + 1)) ω) ^ p ∂P
      ≤ #(C (j + 1)) * M * ε j ^ q := by
  sorry

lemma lintegral_sup_rpow_edist_le_sum_rpow (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t) (ht : t ∈ C k), edist (X t ω) (X (chainingSequence hC ht m) ω) ^ p ∂P
      ≤ (∑ i ∈ Finset.range (k - m), (∫⁻ ω, ⨆ (t) (ht : t ∈ C k),
        edist (X (chainingSequence hC ht (m + i)) ω)
          (X (chainingSequence hC ht (m + i + 1)) ω) ^ p ∂P) ^ (1 / p)) ^ p := by
  sorry

lemma lintegral_sup_rpow_edist_le_sum (hX : IsKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t) (ht : t ∈ C k), edist (X t ω) (X (chainingSequence hC ht m) ω) ^ p ∂P
      ≤ M * (∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) ^ (1 / p)
              * ε (m + i) ^ (q / p)) ^ p := by
  sorry

lemma lintegral_sup_rpow_edist_le_of_minimal_cover (hX : IsKolmogorovProcess X P p q M)
    (hε : ∀ n, ε n ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε n) J)
    {c₁ : ℝ≥0} {d : ℝ} (hc₁_pos : 0 < c₁) (hd_pos : 0 < d)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t) (ht : t ∈ C k), edist (X t ω) (X (chainingSequence hC ht m) ω) ^ p ∂P
      ≤ M * c₁
        * (∑ j ∈ Finset.range (k - m), ε (m + j + 1) ^ (- d / p) * ε (m + j) ^ (q / p)) ^ p := by
  sorry

lemma lintegral_sup_rpow_edist_le_of_minimal_cover_two
    (hX : IsKolmogorovProcess X P p q M) {ε₀ : ℝ≥0∞} (hε : ε₀ ≤ EMetric.diam J)
    (hC : ∀ n, IsCover (C n) (ε₀ * 2⁻¹ ^ n) J) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = internalCoveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0} {d : ℝ} (hc₁_pos : 0 < c₁) (hd_pos : 0 < d)
    (h_cov : HasBoundedInternalCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t) (ht : t ∈ C k), edist (X t ω) (X (chainingSequence hC ht m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p := by
  sorry

end SecondTerm

section Together

variable {c M : ℝ≥0} {d p q : ℝ} {J : Set T}

theorem finite_set_bound_of_edist_le (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∫⁻ ω, ⨆ (s) (t) (_hs : s ∈ J) (_ht : t ∈ J) (_hd : edist s t ≤ δ), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ (p + 2 * q + 1) * M * δ ^ (q - d)
        * ((δ ^ d * Nat.log2 (internalCoveringNumber (δ / 4) J).toNat) ^ q
            * internalCoveringNumber (δ / 4) J
          + c / ((2 ^ ((q - d) / p)) - 1) ^ p) := by
  sorry

lemma finite_set_bound_of_edist_le_of_le_diam (hJ : HasBoundedInternalCoveringNumber J c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδ_le : δ ≤ 4 * EMetric.diam J) :
    ∫⁻ ω, ⨆ (s) (t) (_hs : s ∈ J) (_ht : t ∈ J) (_hd : edist s t ≤ δ), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ (p + 2 * q + 1) * M * c * δ ^ (q - d)
        * ((4 ^ d * ENNReal.ofReal (Real.logb 2 ((c : ℝ) * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + 1 / ((2 ^ ((q - d) / p)) - 1) ^ p) := by
  sorry

end Together

end ProbabilityTheory
