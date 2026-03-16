/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Data.Set.Dissipate
import KolmogorovExtension4.CompactSystem

/-!
# Analytic sets in the sense of a paved space


TODO: we use `IsCompactSystem`, which corresponds to semi-compact pavings for D-M. We use this and
not compact pavings (which would be the same, but for arbitrary intersections instead of countable
ones), because it's sufficient for our applications, and because it's easier to work with.

-/

open scoped ENNReal NNReal

variable {𝓧 𝓨 𝓚 : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

namespace MeasureTheory

/-- Product of two sets of sets. -/
def memProd (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  {s | ∃ A B, A ∈ p ∧ B ∈ q ∧ s = A ×ˢ B}

lemma memProd_prod {A : Set 𝓧} {B : Set 𝓚} (hp : A ∈ p) (hq : B ∈ q) : (A ×ˢ B) ∈ memProd p q :=
  ⟨A, B, hp, hq, rfl⟩

lemma memProd.mono {p' : Set (Set 𝓧)} (hp : ∀ s, s ∈ p → s ∈ p') {q' : Set (Set 𝓚)}
    (hq : ∀ s, s ∈ q → s ∈ q') {s : Set (𝓧 × 𝓚)} (hs : s ∈ memProd p q) :
    s ∈ memProd p' q' := by
  obtain ⟨A, B, hpA, hqB, rfl⟩ := hs
  exact ⟨A, B, hp _ hpA, hq _ hqB, rfl⟩

/-- The set is a countable union of sets that satisfy the property. -/
def memSigma (p : Set (Set 𝓧)) : Set (Set 𝓧) :=
  {s | ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ s = ⋃ n, A n}

lemma memSigma_of_prop (hs : s ∈ p) : s ∈ memSigma p := ⟨fun _ ↦ s, by simp [hs, Set.iUnion_const]⟩

lemma memSigma.iUnion {s : ℕ → Set 𝓧} (hs : ∀ n, s n ∈ memSigma p) :
    ⋃ n, s n ∈ memSigma p := by
  sorry

lemma memSigma.union (hs : s ∈ memSigma p) (ht : t ∈ memSigma p) :
    s ∪ t ∈ memSigma p := by
  obtain ⟨A, hA, rfl⟩ := hs
  obtain ⟨B, hB, rfl⟩ := ht
  sorry

/-- The set is a countable intersection of sets that satisfy the property. -/
def memDelta (p : Set (Set 𝓧)) : Set (Set 𝓧) :=
  {s | ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ s = ⋂ n, A n}

lemma memDelta_of_prop (hs : s ∈ p) : s ∈ memDelta p :=
  ⟨fun _ ↦ s, by simp [hs, Set.iInter_const]⟩

lemma memDelta.iInter {s : ℕ → Set 𝓧} (hs : ∀ n, s n ∈ memDelta p) :
    ⋂ n, s n ∈ memDelta p := by
  sorry

lemma memDelta.inter (hs : s ∈ memDelta p) (ht : t ∈ memDelta p) :
    s ∩ t ∈ memDelta p := by
  sorry

/-- The set is a countable intersection of countable unions of sets that can be written as a
product of two sets, each satisfying a property. -/
def memProdSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  memDelta (memSigma (memProd p q))

/-- The set is a finite intersection of sets that satisfy the property. -/
def memFiniteInter (p : Set (Set 𝓧)) : Set (Set 𝓧) :=
  {s | ∃ (t : Finset ℕ) (A : ℕ → Set 𝓧), (∀ n ∈ t, A n ∈ p) ∧ s = ⋂ n ∈ t, A n}

lemma memFiniteInter_of_prop (hs : s ∈ p) : s ∈ memFiniteInter p :=
  ⟨{0}, fun _ ↦ s, by simp [hs]⟩

lemma memFiniteInter.inter (hs : s ∈ memFiniteInter p) (ht : t ∈ memFiniteInter p) :
    s ∩ t ∈ memFiniteInter p := by
  obtain ⟨S, A, hA, rfl⟩ := hs
  obtain ⟨T, B, hB, rfl⟩ := ht
  sorry

/-- The set is a finite union of sets that satisfy the property. -/
def memFiniteUnion (p : Set (Set 𝓧)) : Set (Set 𝓧) :=
  {s | ∃ (t : Finset ℕ) (A : ℕ → Set 𝓧), (∀ n ∈ t, A n ∈ p) ∧ s = ⋃ n ∈ t, A n}

lemma memFiniteUnion_of_prop (hs : s ∈ p) : s ∈ memFiniteUnion p :=
  ⟨{0}, fun _ ↦ s, by simp [hs]⟩

lemma memFiniteUnion.union (hs : s ∈ memFiniteUnion p) (ht : t ∈ memFiniteUnion p) :
    s ∪ t ∈ memFiniteUnion p := by
  obtain ⟨S, A, hA, rfl⟩ := hs
  obtain ⟨T, B, hB, rfl⟩ := ht
  sorry

lemma memProdSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ memProdSigmaDelta p q ↔
      ∃ (A : ℕ → ℕ → Set 𝓧) (K : ℕ → ℕ → Set 𝓚) (_ : ∀ n m, A n m ∈ p) (_ : ∀ n m, K n m ∈ q),
        s = ⋂ n, ⋃ m, A n m ×ˢ K n m := by
  unfold memProdSigmaDelta memDelta memSigma memProd
  simp only [exists_and_left, exists_prop]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB hB' using hA
    choose C hC hC' using hB
    choose D hD hD' using hC'
    refine ⟨C, D, hD, hC, ?_⟩
    rw [hs]
    simp_rw [hB', hD']
  · obtain ⟨A, K, hK, hA, rfl⟩ := h
    refine ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨fun m ↦ A n m ×ˢ K n m, fun m ↦ ?_, rfl⟩, rfl⟩
    exact ⟨A n m, hA n m, ⟨K n m, hK n m, rfl⟩⟩

lemma memSigma_memProd_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ memSigma (memProd p q) ↔
      ∃ (A : ℕ → Set 𝓧) (K : ℕ → Set 𝓚) (_ : ∀ n, A n ∈ p) (_ : ∀ n, K n ∈ q),
        s = ⋃ n, A n ×ˢ K n := by
  unfold memSigma memProd
  simp only [exists_and_left, exists_prop]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB C hC hA_eq using hA
    refine ⟨B, C, hC, hB, ?_⟩
    simp_rw [hs, hA_eq]
  · obtain ⟨A, K, hK, hA, rfl⟩ := h
    exact ⟨fun n ↦ A n ×ˢ K n, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, rfl⟩

lemma memProdSigmaDelta_of_prop {s : Set 𝓧} {t : Set 𝓚} (hs : s ∈ p) (hq : t ∈ q) :
    s ×ˢ t ∈ memProdSigmaDelta p q := by
  rw [memProdSigmaDelta_iff]
  exact ⟨fun n m ↦ s, fun n m ↦ t, fun _ _ ↦ hs, fun _ _ ↦ hq, by
    simp [Set.iInter_const, Set.iUnion_const]⟩

lemma memProdSigmaDelta.mono {p' : Set (Set 𝓧)} (hp : ∀ s, s ∈ p → s ∈ p') {q' : Set (Set 𝓚)}
    (hq : ∀ s, s ∈ q → s ∈ q') {s : Set (𝓧 × 𝓚)} (hs : s ∈ memProdSigmaDelta p q) :
    s ∈ memProdSigmaDelta p' q' := by
  simp_rw [memProdSigmaDelta_iff] at hs ⊢
  obtain ⟨A, K, hA, hK, rfl⟩ := hs
  refine ⟨A, K, fun n m ↦ hp _ (hA n m), fun n m ↦ hq _ (hK n m), rfl⟩

lemma memDelta_iff_of_inter (hp : ∀ s t, s ∈ p → t ∈ p → (s ∩ t) ∈ p) {s : Set 𝓧} :
    s ∈ memDelta p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Antitone A ∧ s = ⋂ n, A n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · obtain ⟨A, hA, _, rfl⟩ := h
    exact ⟨A, hA, rfl⟩
  · choose A hA hs using h
    refine ⟨Set.dissipate A, fun n ↦ ?_, Set.antitone_dissipate, ?_⟩
    · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp _ _ hn (hA _)
    · rwa [Set.iInter_dissipate]

lemma memSigma_iff_of_union (hp : ∀ s t, s ∈ p → t ∈ p → (s ∪ t) ∈ p) {s : Set 𝓧} :
    s ∈ memSigma p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Monotone A ∧ s = ⋃ n, A n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · obtain ⟨A, hA, _, rfl⟩ := h
    exact ⟨A, hA, rfl⟩
  · choose A hA hs using h
    refine ⟨Set.accumulate A, fun n ↦ ?_, Set.monotone_accumulate, ?_⟩
    · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.accumulate_succ]
      exact hp _ _ hn (hA _)
    · rwa [Set.iUnion_accumulate]

lemma _root_.IsCompactSystem.memProd (hp : IsCompactSystem p) (hq : IsCompactSystem q) :
    IsCompactSystem (memProd p q) := by
  sorry

lemma _root_.IsCompactSystem.memFiniteInter (hp : IsCompactSystem p) :
    IsCompactSystem (memFiniteInter p) := by
  sorry

lemma _root_.IsCompactSystem.memFiniteUnion (hp : IsCompactSystem p) :
    IsCompactSystem (memFiniteUnion p) := by
  sorry

-- He (35.1) in the proof of 1.35
lemma fst_iInter_of_memFiniteUnion_memProd_of_antitone (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, memFiniteUnion (memProd p q) (B n)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  refine le_antisymm (Set.image_iInter_subset _ _) ?_
  intro x hx
  choose S DC hDC hB_eq' using hB
  choose D' C' hD' hC' hDC_eq' using hDC
  let D : ℕ → ℕ → Set 𝓧 := fun n m ↦ if hm : m ∈ S n then D' n m hm else ∅
  let C : ℕ → ℕ → Set 𝓚 := fun n m ↦ if hm : m ∈ S n then C' n m hm else ∅
  have hD : ∀ n m, m ∈ S n → p (D n m) := by
    intro n m hm
    simp only [D, dif_pos hm]
    exact hD' n m hm
  have hC : ∀ n m, m ∈ S n → q (C n m) := by
    intro n m hm
    simp only [C, dif_pos hm]
    exact hC' n m hm
  have hDC_eq : ∀ n m, m ∈ S n → DC n m = D n m ×ˢ C n m := by
    intro n m hm
    simp only [D, C, dif_pos hm]
    exact hDC_eq' n m hm
  have hB_eq n : B n = ⋃ m ∈ S n, D n m ×ˢ C n m := by
    rw [hB_eq']
    congr
    ext m : 1
    by_cases hm : m ∈ S n
    swap; · simp [hm]
    simp only [hm, Set.iUnion_true]
    exact hDC_eq n m hm
  suffices (({x} ×ˢ .univ) ∩ ⋂ n, B n).Nonempty by
    obtain ⟨u, ⟨hu_left, hu_right⟩⟩ := this
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hu_left
    rw [← hu_left, Set.mem_image]
    exact ⟨u, hu_right, rfl⟩
  let C'' n := ⋃ (m) (hm : m ∈ S n) (hx : x ∈ D n m), C n m -- `C'' n` is `C_n` in the book
  have h_inter n : ({x} ×ˢ .univ) ∩ B n = {x} ×ˢ C'' n := by
    simp_rw [C'', hB_eq n, Set.inter_iUnion, Set.prod_iUnion]
    congr
    ext m : 1
    by_cases hm : m ∈ S n
    swap; · simp [hm]
    simp only [hm, Set.iUnion_true]
    by_cases hx : x ∈ D n m
    · simp only [hx, Set.iUnion_true]
      ext
      simp
      grind
    · simp only [hx, Set.iUnion_false]
      ext
      simp
      grind
  have h_eq_C'' : {x} ×ˢ Set.univ ∩ ⋂ n, B n = {x} ×ˢ ⋂ n, C'' n := by
    simp_rw [Set.inter_iInter, h_inter, Set.prod_iInter]
  rw [h_eq_C'']
  suffices (⋂ n, C'' n).Nonempty by
    simpa only [Set.prod_nonempty_iff, Set.singleton_nonempty, true_and]
  have h_anti : Antitone C'' := by
    have h_eq : C'' = fun n ↦ Prod.snd '' ({x} ×ˢ .univ ∩ B n) := by
      ext n
      simp [h_inter n]
    rw [h_eq]
    intro n m hnm
    refine Set.image_mono ?_
    simp only [Set.subset_inter_iff, Set.inter_subset_left, true_and]
    exact Set.inter_subset_right.trans (hB_anti hnm)
  have hC''q n : C'' n ∈ memFiniteUnion q := by
    simp only [C'']
    sorry
  have hC''_nonempty n : (C'' n).Nonempty := by
    sorry
  -- use that `memFiniteUnion q` is a compact paving (Bichteler A.5.6 (ii))
  -- if the intersection is empty, there is a finite subintersection that is empty
  -- that subintersection is just `C'' n` for some `n` since `C''` is antitone,
  -- so `C'' n` is empty, contradiction
  sorry

end MeasureTheory
