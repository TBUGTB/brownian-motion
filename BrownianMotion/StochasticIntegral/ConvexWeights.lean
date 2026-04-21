module

public import Mathlib.Analysis.InnerProductSpace.Defs

/-`
# Lemmas on Convex Weights
-/

@[expose] public section

variable {R E : Type*} [Field R] [AddCommGroup E] [Module R E]
  [LinearOrder R] [IsStrictOrderedRing R] {ι : Type*}

lemma convex_weights_of_mem_convexHull_indexed {s : ι → E} {x : E}
    (h : x ∈ convexHull R (Set.range s)) :
    ∃ (w : ι →₀ R), (∀ i, 0 ≤ w i) ∧ w.sum (fun _ wi ↦ wi) = 1
      ∧ w.sum (fun i wi ↦ wi • s i) = x := by
      sorry

noncomputable section

def convexWeightsMul (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (a.support.biUnion (fun k ↦ (b k).support))
    (fun m ↦ ∑ k ∈ a.support, a k * (b k m))
    (fun m hm ↦ by
      simp only [Finset.mem_biUnion, Finsupp.mem_support_iff]
      by_contra h
      push_neg at h
      apply hm
      apply Finset.sum_eq_zero
      intro k hk
      rcases eq_or_ne (a k) 0 with ha | ha
      · simp [ha]
      · simp [h k (Finsupp.mem_support_iff.mp hk)])


lemma convexWeightsMul_eq (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) :
  convexWeightsMul a b = fun m ↦ ∑ k ∈ a.support, a k * (b k m) := rfl

variable {a : ℕ →₀ ℝ} {b : ℕ → ℕ →₀ ℝ}

lemma convexWeightsMul_nonneg (ha : ∀ n, a n ≥ 0) (hb : ∀ n m, b n m ≥ 0) (m : ℕ) :
  convexWeightsMul a b m ≥ 0 := by sorry

lemma convexWeightsMul_sum_one (ha_nonneg : ∀ n, a n ≥ 0) (hb_nonneg : ∀ n m, b n m ≥ 0)
  (ha_sum_one : a.sum (fun _ ai ↦ ai) = 1) (hb_sum_one : ∀ n, (b n).sum (fun _ bi ↦ bi) = 1) :
  (convexWeightsMul a b).sum (fun _ mi ↦ mi) = 1 := by sorry

def convexWeightsConvolution (cw : ℕ → ℕ → ℕ →₀ ℝ) : ℕ → ℕ → ℕ →₀ ℝ
  | 0 => fun n ↦ cw 0 n
  | k + 1 => fun n ↦ convexWeightsMul (cw (k+1) n) (convexWeightsConvolution cw k)

lemma convexWeightsConvolution_cong {cw1 cw2 : ℕ → ℕ → ℕ →₀ ℝ} {k : ℕ}
    (h : ∀ i ≤ k, cw1 i = cw2 i) :
    convexWeightsConvolution cw1 k = convexWeightsConvolution cw2 k := by
  induction k with
  | zero => simp_all only [convexWeightsConvolution, nonpos_iff_eq_zero, forall_eq]
  | succ n hn =>
    have : convexWeightsConvolution cw1 n = convexWeightsConvolution cw2 n :=
      hn (fun i hi => h i (Nat.le_succ_of_le hi))
    simp only [convexWeightsConvolution, Std.le_refl, h, this]

lemma convexWeightsConvolution_update (cw : ℕ → ℕ → ℕ →₀ ℝ) {k k' : ℕ} {f : ℕ → ℕ →₀ ℝ}
    (hk' : k' > k) :
    convexWeightsConvolution cw k = convexWeightsConvolution (Function.update cw k' f) k := by
  rw [convexWeightsConvolution_cong]
  grind

lemma convexWeightsMul_support_subset (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) :
    (convexWeightsMul a b).support ⊆ a.support.biUnion (fun k ↦ (b k).support) :=
  Finsupp.support_onFinset_subset

lemma support_subset_convexWeightsMul_support {a : ℕ →₀ ℝ} {b : ℕ → ℕ →₀ ℝ} {i : ℕ}
    (hi : i ∈ a.support) (ha : ∀ k ∈ a.support, 0 ≤ a k) (hb : ∀ k ∈ a.support, ∀ m, 0 ≤ b k m) :
    (b i).support ⊆ (convexWeightsMul a b).support := by
  intro j hj
  simp only [convexWeightsMul, Finsupp.mem_support_onFinset]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (ha k hk) (hb k hk j)
  · refine ⟨i, hi, mul_pos ?_ ?_⟩
    · exact lt_of_le_of_ne (ha i hi) (Ne.symm (Finsupp.mem_support_iff.mp hi))
    · exact lt_of_le_of_ne (hb i hi j) (Ne.symm (Finsupp.mem_support_iff.mp hj))

lemma convexWeightsConvolution_nonneg {cw : ℕ → ℕ → ℕ →₀ ℝ}
  (h : ∀ k n m, 0 ≤ cw k n m) (k n m : ℕ) :
  0 ≤ convexWeightsConvolution cw k n m := by sorry

lemma convexWeightsConvolution_sum_one {cw : ℕ → ℕ → ℕ →₀ ℝ} (h_nonneg : ∀ k n m, 0 ≤ cw k n m)
  (h_sum_one : ∀ k n, (cw k n).sum (fun _ wi ↦ wi) = 1) (k n : ℕ) :
  (convexWeightsConvolution cw k n).sum (fun _ wi ↦ wi) = 1 := by sorry
