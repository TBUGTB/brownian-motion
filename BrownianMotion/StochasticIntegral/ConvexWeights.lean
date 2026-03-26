import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Ring.Basic

/-
# Convex Weights
This is kept in a separate file for now, might become part of `Mathlib.Analysis.Convex.Combination`
when upstreamed.
-/

variable {R E : Type*} [Field R] [AddCommGroup E] [Module R E]
  [LinearOrder R] [IsStrictOrderedRing R] {ι : Type*}

lemma convex_weights_of_mem_convexHull_indexed {s : ι → E} {x : E}
  (h : x ∈ convexHull R (Set.range s)) :
    ∃ (w : ι →₀ R), (∀ i, 0 ≤ w i) ∧ ∑ i : w.support, w i = 1 ∧ ∑ i : w.support, w i • s i = x := by
  sorry

def convexWeights (cw : ι →₀ ℝ) : Prop :=
  ∀ n : cw.support, 0 ≤ cw n ∧ ∑ n : cw.support, cw n = 1
-- We might also choose the equivalent condition ∀ n : ι, 0 ≤ cw

noncomputable def cwmul (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) : ℕ →₀ ℝ :=
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

lemma convexWeights_cwmul {a : ℕ →₀ ℝ} {b : ℕ → ℕ →₀ ℝ}
  (ha : convexWeights a) (hb : ∀ k, convexWeights (b k)) : convexWeights (cwmul a b) := by
  sorry

noncomputable def cwIteratedMul (k : ℕ) (cw : ℕ → ℕ → ℕ →₀ ℝ) : ℕ → ℕ →₀ ℝ :=
  match k with
  | 0 => fun n ↦ cw 0 n
  | k + 1 => fun n ↦ cwmul (cw k n) (cwIteratedMul k cw)
