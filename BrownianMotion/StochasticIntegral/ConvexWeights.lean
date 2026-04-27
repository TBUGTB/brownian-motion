module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.ConvexSpace

/-
# Lemmas on Convex Weights
-/

@[expose] public noncomputable section

variable {ι ι' E R : Type*} [AddCommGroup E] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

lemma stdSimplex_of_mem_convexHull [Module R E] {s : ι → E} {x : E}
    (hx : x ∈ convexHull R (Set.range s)) :
    ∃ (w : StdSimplex R ι), x = w.sum (fun i wi ↦ wi • s i) := by
  classical
  rw [mem_convexHull_iff] at hx
  specialize hx {y | ∃ w : StdSimplex R ι, y = w.sum (fun i wi => wi • s i)} ?_ ?_
  · rintro _ ⟨i, rfl⟩
    use StdSimplex.single i
    simp
  · rintro x ⟨w₁, hw₁⟩ y ⟨w₂, hw₂⟩ a b ha hb hab
    use (StdSimplex.duple w₁ w₂ ha hb hab).join
    simp only [StdSimplex.join, StdSimplex.duple]
    repeat rw [Finsupp.sum_add_index (by simp) (fun _ _ _ _ ↦ Module.add_smul _ _ _)]
    have aux (c : R) (w : StdSimplex R ι) : c • (w.sum fun i wi ↦ wi • s i)
      = ((Finsupp.single w c).sum fun d r ↦ r • d.weights).sum fun i wi ↦ wi • s i := by
      simp only [zero_smul, Finsupp.sum_single_index]
      rw [Finsupp.sum_smul_index (by simp only [zero_smul, implies_true])]
      simp_rw [mul_smul, ← Finsupp.smul_sum]
    simp [aux, hw₁, hw₂]
  exact hx

/-- Given convex weights `a : StdSimplex R ι` and a family of convex weights
`b : ι → StdSimplex R ι'`, `convexWeightsMul a b` is the convex combination of the `b k`, weighted
by `a`. We show that, `(convexWeightsMul a b) m = ∑ k ∈ a.support, a k * b k m` in
`convexWeightsMul_eq` and define it here more abstractly using `StdSimplex.map` and
`StdSimplex.join`. -/
def convexWeightsMul (a : StdSimplex R ι) (b : ι → StdSimplex R ι') : StdSimplex R ι' :=
  (a.map b).join

variable (a : StdSimplex R ι) (b : ι → StdSimplex R ι')

lemma convexWeightsMul_eq :
  (convexWeightsMul a b).toFun = (fun m ↦ ∑ k ∈ a.support, a.weights k * (b k).weights m)
  := by
  ext m
  rw [convexWeightsMul, StdSimplex.join, StdSimplex.map]
  change ((Finsupp.mapDomain b a.weights).sum (fun d r => r • d.weights)) m = _
  simp only [Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  simp [Finsupp.sum]

lemma convexWeightsMul_support_subset [DecidableEq ι'] :
    (convexWeightsMul a b).support ⊆ a.support.biUnion (fun k ↦ (b k).support) :=
  by
  intro m hm
  have hm_ne : (convexWeightsMul a b).weights m ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hm
  have hm_eq : (convexWeightsMul a b).weights m
      = ∑ k ∈ a.support, a.weights k * (b k).weights m := by
    simpa using congrArg (fun f => f m) (convexWeightsMul_eq a b)
  have hm_ne' : (∑ k ∈ a.support, a.weights k * (b k).weights m) ≠ 0 := by
    simpa [hm_eq] using hm_ne
  rcases Finset.exists_ne_zero_of_sum_ne_zero hm_ne' with ⟨k, hk, hkne⟩
  have hbkm_ne : (b k).weights m ≠ 0 := by
    intro hb0
    apply hkne
    simp [hb0]
  refine Finset.mem_biUnion.2 ?_
  refine ⟨k, hk, ?_⟩
  simpa [Finsupp.mem_support_iff] using hbkm_ne

lemma support_subset_convexWeightsMul_support {a : StdSimplex R ι} (b : ι → StdSimplex R ι')
    {i : ι} (hi : i ∈ a.support) :
    (b i).support ⊆ (convexWeightsMul a b).support := by
  intro m hm
  have hbim_ne : (b i).weights m ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hm
  have hai_ne : a.weights i ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hi
  have hpos_term : 0 < a.weights i * (b i).weights m := by
    have hai_pos : 0 < a.weights i := (a.nonneg i).lt_of_ne' hai_ne
    have hbim_pos : 0 < (b i).weights m := ((b i).nonneg m).lt_of_ne' hbim_ne
    exact mul_pos hai_pos hbim_pos
  have hnonneg : ∀ k ∈ a.support, 0 ≤ a.weights k * (b k).weights m := by
    intro k hk
    exact mul_nonneg (a.nonneg k) ((b k).nonneg m)
  have hle : a.weights i * (b i).weights m ≤ ∑ k ∈ a.support, a.weights k * (b k).weights m := by
    exact Finset.single_le_sum hnonneg hi
  have hsum_pos : 0 < ∑ k ∈ a.support, a.weights k * (b k).weights m :=
    lt_of_lt_of_le hpos_term hle
  have hsum_ne : (∑ k ∈ a.support, a.weights k * (b k).weights m) ≠ 0 := ne_of_gt hsum_pos
  have hm_eq : (convexWeightsMul a b).weights m
      = ∑ k ∈ a.support, a.weights k * (b k).weights m := by
    simpa using congrArg (fun f => f m) (convexWeightsMul_eq a b)
  have : (convexWeightsMul a b).weights m ≠ 0 := by
    simpa [hm_eq] using hsum_ne
  simpa [Finsupp.mem_support_iff] using this

lemma convexWeightsMul_sum_smul (f : ι' → E) [Module R E] :
    a.sum (fun i wi ↦ wi • (b i).sum (fun m bm ↦ bm • f m))
    = (convexWeightsMul a b).sum (fun m cwm ↦ cwm • f m) := by
  classical
  simp only [convexWeightsMul, StdSimplex.join, StdSimplex.map]
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun d r₁ r₂ => by simp [add_smul, Finsupp.sum_add_index, add_smul])]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hai_ne : a.weights i ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hi
  have hsupp : (a.weights i • (b i).weights).support = (b i).weights.support := by
    simpa using Finsupp.support_smul_eq hai_ne
  simp [hsupp, Finset.smul_sum, Finsupp.smul_apply, smul_smul]

/-- Given a doubly-indexed family of convex weights `cw : ℕ → ℕ → StdSimplex R ℕ`,
`convexWeightsConvolution cw k n` is the iterated convex multiplication obtained by combining
the weights `cw 0 n, cw 1 n, …, cw k n` via `convexWeightsMul`. -/
def convexWeightsConvolution (cw : ℕ → ℕ → StdSimplex R ℕ) : ℕ → ℕ → StdSimplex R ℕ
  | 0 => fun n ↦ cw 0 n
  | k + 1 => fun n ↦ convexWeightsMul (cw (k + 1) n) (convexWeightsConvolution cw k)

lemma convexWeightsConvolution_cong
    {cw1 cw2 : ℕ → ℕ → StdSimplex R ℕ} {k : ℕ} (h : ∀ i ≤ k, cw1 i = cw2 i) :
    convexWeightsConvolution cw1 k = convexWeightsConvolution cw2 k := by
  induction k with
  | zero =>
    funext n
    have h0 : cw1 0 = cw2 0 := h 0 (by simp)
    simp [convexWeightsConvolution, h0]
  | succ k ih =>
    have hk : cw1 (k + 1) = cw2 (k + 1) := h (k + 1) (Nat.le_refl _)
    have h' : ∀ i ≤ k, cw1 i = cw2 i := fun i hi => h i (Nat.le_succ_of_le hi)
    have ih' :
        convexWeightsConvolution cw1 k = convexWeightsConvolution cw2 k := ih h'
    funext n
    simp [convexWeightsConvolution, hk, ih']

omit [AddCommGroup E] in
lemma convex_combination_bounded [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} {w : ℕ → StdSimplex ℝ ℕ}
    (hx : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) :
    ∃ M, ∀ n, ‖(w n).sum (fun i wi ↦ wi • x i)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hx
  use M
  intro n
  have h_sum : ‖(w n).sum (fun i wi => wi • x i)‖ ≤ ∑ i ∈ (w n).support, ((w n).weights i) * ‖x i‖
    := by
    convert norm_sum_le _ _ using 2
    simp [norm_smul, abs_of_nonneg ((w _).nonneg _)]
  refine le_trans h_sum (le_trans (Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hM i) ((w n).nonneg i)) ?_)
  simp_all only [Finsupp.sum, ← Finset.sum_mul _ _ _]
  have bound : (∑ i ∈ (w n).support, (w n).weights i) ≤ 1 := by
    have : (∑ i ∈ (w n).support, (w n).weights i) = (1 : ℝ) := by
      simpa [Finsupp.sum] using (w n).total
    exact this.le
  refine mul_le_of_le_one_left ?_ bound
  exact le_trans (norm_nonneg (x 0)) (hM 0)
