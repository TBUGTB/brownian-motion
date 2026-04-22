module

public import Mathlib.Analysis.InnerProductSpace.Defs

/-
# Lemmas on Convex Weights
-/

@[expose] public section

variable {R E : Type*} [Field R] [AddCommGroup E] [Module R E]
  [LinearOrder R] [IsStrictOrderedRing R] {ι : Type*}

lemma convex_weights_of_mem_convexHull_indexed {s : ι → E} {x : E}
  (hx : x ∈ convexHull R (Set.range s)) :
    ∃ (w : ι →₀ R), (∀ i, 0 ≤ w i) ∧ w.sum (fun _ wi ↦ wi) = 1
      ∧ w.sum (fun i wi ↦ wi • s i) = x := by
  rw [ mem_convexHull_iff ] at hx
  specialize hx ( { y | ∃ w : ι →₀ R, ( ∀ i, 0 ≤ w i ) ∧ w.sum (fun _ wi => wi) = 1
    ∧ w.sum (fun i wi => wi • s i) = y } ) ?_ ?_ <;> norm_num at *;
  · rintro _ ⟨ i, rfl ⟩
    exact ⟨Finsupp.single i 1, fun j => by by_cases h : j = i <;> aesop,
      by simp, by simp⟩ ;
  · rintro x ⟨w₁, hw₁, hw₁', rfl⟩ y ⟨w₂, hw₂, hw₂', rfl⟩ a b ha hb hab;
    refine ⟨a • w₁ + b • w₂, ?_, ?_, ?_⟩
    · exact fun i => add_nonneg (mul_nonneg ha ( hw₁ i )) (mul_nonneg hb ( hw₂ i ));
    · simp_all [Finsupp.sum_add_index', Finsupp.sum_smul_index];
      simp_all [← Finset.mul_sum _ _ _, Finsupp.sum]
    · simp [Finsupp.smul_sum, Finsupp.sum_add_index', Finsupp.sum_smul_index, smul_smul, add_smul];
  · exact hx

noncomputable section

/-- Given convex weights `a : ℕ →₀ ℝ` and a family of convex weights `b : ℕ → ℕ →₀ ℝ`,
`convexWeightsMul a b` is the convex combination of the `b k`, weighted by `a`. That is,
`(convexWeightsMul a b) m = ∑ k ∈ a.support, a k * b k m`. -/
def convexWeightsMul (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (a.support.biUnion (fun k ↦ (b k).support))
    (fun m ↦ ∑ k ∈ a.support, a k * (b k m))
    (fun m hm ↦ by
      simp only [Finset.mem_biUnion, Finsupp.mem_support_iff]
      by_contra h
      push Not at h
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
  convexWeightsMul a b m ≥ 0 := by
    exact Finset.sum_nonneg fun _ _ => mul_nonneg ( ha _ ) ( hb _ _ )

lemma convexWeightsMul_sum_one (ha_nonneg : ∀ n, a n ≥ 0) (hb_nonneg : ∀ n m, b n m ≥ 0)
  (ha_sum_one : a.sum (fun _ ai ↦ ai) = 1) (hb_sum_one : ∀ n, (b n).sum (fun _ bi ↦ bi) = 1) :
  (convexWeightsMul a b).sum (fun _ mi ↦ mi) = 1 := by
    convert ha_sum_one using 1
    convert Finset.sum_comm using 1
    refine Finset.sum_congr rfl fun i hi => ?_;
    rw [← Finset.mul_sum _ _ _,
      show ( ∑ x ∈ ( convexWeightsMul a b ).support, ( b i ) x ) = 1 from ?_ ];
    · norm_num;
    · rw [← hb_sum_one i, Finsupp.sum_of_support_subset];
      · intro j hj
        simp_all only [ge_iff_le, Finsupp.mem_support_iff, ne_eq, convexWeightsMul,
        Finsupp.onFinset_apply]
        exact ne_of_gt (lt_of_lt_of_le (mul_pos (lt_of_le_of_ne (ha_nonneg i ) (Ne.symm hi ) )
        (lt_of_le_of_ne (hb_nonneg i j ) (Ne.symm hj ) ) ) (Finset.single_le_sum
        (fun k _ => mul_nonneg (ha_nonneg k ) (hb_nonneg k j )) (by aesop)))
      · aesop

/-- Given a doubly-indexed family of convex weights `cw : ℕ → ℕ → ℕ →₀ ℝ`,
`convexWeightsConvolution cw k n` is the iterated convex multiplication obtained by combining
the weights `cw 0 n, cw 1 n, …, cw k n` via `convexWeightsMul`. -/
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
  0 ≤ convexWeightsConvolution cw k n m := by
    unfold convexWeightsConvolution
    induction k <;> simp only [h]
    apply_rules [convexWeightsMul_nonneg]
    rename_i k hk
    refine Nat.recOn k ?_ ?_ <;> simp only [Nat.zero_eq, ge_iff_le]
    · exact fun n m ↦ le_of_eq_of_le rfl (h 0 n m)
    · intro n hn n' m
      exact convexWeightsMul_nonneg (fun k => h _ _ _ ) (fun k m => hn _ _) _

lemma convexWeightsConvolution_sum_one {cw : ℕ → ℕ → ℕ →₀ ℝ} (h_nonneg : ∀ k n m, 0 ≤ cw k n m)
  (h_sum_one : ∀ k n, (cw k n).sum (fun _ wi ↦ wi) = 1) (k : ℕ) :
  ∀ n, (convexWeightsConvolution cw k n).sum (fun _ wi ↦ wi) = 1 := by
    refine Nat.recOn k ?_ ?_ <;> simp_all only [convexWeightsConvolution, implies_true]
    intro n hn n_1
    exact convexWeightsMul_sum_one (fun k => h_nonneg _ _ _)
      (fun k m => convexWeightsConvolution_nonneg (fun k n m => h_nonneg k n m) _ _ _)
      (h_sum_one _ _) (fun k => hn k)

omit [AddCommGroup E] in
lemma convex_combination_bounded [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {x : ℕ → E} {w : ℕ → ℕ →₀ ℝ} (hw : ∀ n, (w n).sum (fun _ wi ↦ wi) = 1)
  (hw_nonneg : ∀ n m, 0 ≤ (w n) m)
  (hx : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) :
  ∃ M, ∀ n, ‖(w n).sum (fun i wi ↦ wi • x i)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hx
  use M
  intro n
  have h_sum : ‖(w n).sum (fun i wi => wi • x i)‖ ≤ ∑ i ∈ (w n).support, (w n i) * ‖x i‖ := by
    convert norm_sum_le _ _ using 2
    simp [norm_smul, abs_of_nonneg (hw_nonneg _ _)]
  refine le_trans h_sum (le_trans (Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hM i) (hw_nonneg n i)) ?_)
  simp_all [← Finset.sum_mul _ _ _, Finsupp.sum]

lemma convexWeightsMul_sum_smul [Module ℝ E]
    (a : ℕ →₀ ℝ) (b : ℕ → ℕ →₀ ℝ) (f : ℕ → E)
    (ha : ∀ k ∈ a.support, 0 ≤ a k) (hb : ∀ k ∈ a.support, ∀ m, 0 ≤ b k m) :
    a.sum (fun i wi ↦ wi • (b i).sum (fun m bm ↦ bm • f m))
      = (convexWeightsMul a b).sum (fun m cwm ↦ cwm • f m) := by
  simp only [Finsupp.sum, Finset.smul_sum, convexWeightsMul_eq, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro k hk
  have inclusion: (b k).support ⊆ (convexWeightsMul a b).support :=
    support_subset_convexWeightsMul_support hk ha hb
  rw [← Finset.sum_subset inclusion]
  · simp only [mul_smul]
  · aesop
