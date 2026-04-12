import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Ring.Basic

/-
# Lemmas on Convex Weights
-/

variable {R E : Type*} [Field R] [AddCommGroup E] [Module R E]
  [LinearOrder R] [IsStrictOrderedRing R] {ι : Type*}

lemma convex_weights_of_mem_convexHull_indexed {s : ι → E} {x : E}
  (h : x ∈ convexHull R (Set.range s)) :
    ∃ (w : ι →₀ R), (∀ i, 0 ≤ w i) ∧ ∑ i ∈ w.support, w i = 1 ∧ ∑ i ∈ w.support, w i • s i = x := by
      sorry

lemma finsupp_choice {X ι₁ ι₂ : Type*} [Zero X] {P : ι₁ → (ι₂ → X) → Prop}
  (h : ∀ i : ι₁, ∃ (w : ι₂ →₀ X), P i w) :
  ∃ W : ι₁ → ι₂ →₀ X, ∀ i : ι₁, P i (W i) :=
  ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

def convexWeights (cw : ι →₀ ℝ) : Prop :=
  ∀ n ∈ cw.support, 0 ≤ cw n ∧ ∑ n ∈ cw.support, cw n = 1

noncomputable section

def cwmul (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) : ℕ →₀ ℝ :=
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

lemma cwmul_eq (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) :
  cwmul a b = fun m ↦ ∑ k ∈ a.support, a k * (b k m) := rfl

lemma cwmul_eq' (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) :
  cwmul a b = fun m ↦ ∑ k ∈ a.support.biUnion (fun k ↦ (b k).support), a k * (b k m) :=
  sorry

lemma convexWeights_cwmul {a : ℕ →₀ ℝ} {b : ℕ → ℕ →₀ ℝ}
  (ha : convexWeights a) (hb : ∀ k, convexWeights (b k)) : convexWeights (cwmul a b) := by
  sorry

def cwIteratedMul (cw : ℕ → ℕ → ℕ →₀ ℝ) (k : ℕ) : ℕ → ℕ →₀ ℝ :=
  match k with
  | 0 => fun n ↦ cw 0 n
  | k + 1 => fun n ↦ cwmul (cw (k+1) n) (cwIteratedMul cw k)

lemma cwIteratedMul_update (cw : ℕ → ℕ → ℕ →₀ ℝ) {k k' : ℕ} {f : ℕ → ℕ →₀ ℝ} (hk' : k' > k) :
  cwIteratedMul cw k = cwIteratedMul (Function.update cw k' f) k := by
  sorry

lemma cwIteratedMul_cong (cw1 cw2 : ℕ → ℕ → ℕ →₀ ℝ) (k : ℕ) (h : ∀ i ≤ k, cw1 i = cw2 i) :
  cwIteratedMul cw1 k = cwIteratedMul cw2 k := by
  induction k with
  | zero => rw [cwIteratedMul]
            simp_all only [nonpos_iff_eq_zero, forall_eq]
            rfl
  | succ n hn =>
    have : cwIteratedMul cw1 n = cwIteratedMul cw2 n := by
      apply hn
      intro i hi
      exact h i (show i ≤ n + 1 by omega)
    rw [cwIteratedMul, this, h]
    · rw [cwIteratedMul]
    · simp

lemma cwmul_support_subset (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) :
    (cwmul a b).support ⊆ a.support.biUnion (fun k ↦ (b k).support) :=
  Finsupp.support_onFinset_subset

lemma support_subset_cwmul_support {a : ℕ →₀ ℝ} {b : ℕ → ℕ →₀ ℝ} {i : ℕ} (hi : i ∈ a.support)
    (ha : ∀ k ∈ a.support, 0 ≤ a k) (hb : ∀ k ∈ a.support, ∀ m, 0 ≤ b k m) :
    (b i).support ⊆ (cwmul a b).support := by
  intro j hj
  simp only [cwmul, Finsupp.mem_support_onFinset]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (ha k hk) (hb k hk j)
  · refine ⟨i, hi, mul_pos ?_ ?_⟩
    · exact lt_of_le_of_ne (ha i hi) (Ne.symm (Finsupp.mem_support_iff.mp hi))
    · exact lt_of_le_of_ne (hb i hi j) (Ne.symm (Finsupp.mem_support_iff.mp hj))
