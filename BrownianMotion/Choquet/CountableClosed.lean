/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.Data.Countable.Defs
import Mathlib.Order.SupClosed

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `IsSublattice`: Predicate for a set to be closed under meet and join.
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `latticeClosure`: Smallest sublattice containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *countably sup-closed* if `⨆ n, A n ∈ s` for all `A : ℕ → α` with `A n ∈ s`. -/
def CountableSupClosed [SupSet α] (s : Set α) : Prop := ∀ ⦃A : ℕ → α⦄, (∀ n, A n ∈ s) → ⨆ n, A n ∈ s

lemma CountableSupClosed.iSup_mem_of_nonempty {ι : Type*} [hι : Countable ι] [Nonempty ι] [SupSet α]
    (hs : CountableSupClosed s) (A : ι → α) (hA : ∀ n, A n ∈ s) :
    (⨆ n, A n) ∈ s := by
  obtain ⟨g, hg⟩ := countable_iff_exists_surjective.mp hι
  have : ⨆ i, A i = ⨆ n, A (g n) := by rw [Function.Surjective.iSup_comp hg]
  rw [this]
  exact hs (fun n ↦ hA (g n))

lemma CountableSupClosed.iSup_mem {ι : Type*} [hι : Countable ι] [CompleteLattice α]
    (hs : CountableSupClosed s) (h_bot : ⊥ ∈ s) (A : ι → α) (hA : ∀ n, A n ∈ s) :
    (⨆ n, A n) ∈ s := by
  cases isEmpty_or_nonempty ι
  · rwa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty A hA

lemma CountableSupClosed.sSup_mem_of_nonempty [SupSet α] (hs : CountableSupClosed s)
    (A : Set α) [Countable A] [Nonempty A] (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (fun (a : A) ↦ a) fun a ↦ hA a a.2

lemma CountableSupClosed.sSup_mem [CompleteLattice α] (hs : CountableSupClosed s)
    (h_bot : ⊥ ∈ s) (A : Set α) [Countable A] (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rcases eq_empty_or_nonempty A with rfl | hA_nonempty
  · simpa
  · have : Nonempty A := Set.nonempty_coe_sort.mpr hA_nonempty
    exact hs.sSup_mem_of_nonempty A hA

lemma CountableSupClosed.supClosed [ConditionallyCompleteLattice α] (hs : CountableSupClosed s) :
    SupClosed s := by
  intro a ha b hb
  have : a ⊔ b = sSup {a, b} := by simp
  rw [this]
  exact hs.sSup_mem_of_nonempty (A := {a, b}) (fun u ↦ by grind)

@[simp] lemma countableSupClosed_empty [SupSet α] : CountableSupClosed (∅ : Set α) := by
  simp [CountableSupClosed]

@[simp] lemma countableSupClosed_singleton [ConditionallyCompletePartialOrderSup α] :
    CountableSupClosed ({a} : Set α) := by
  simp only [CountableSupClosed, mem_singleton_iff]
  intro A hA
  simp [hA]

@[simp] lemma countableSupClosed_univ [SupSet α] : CountableSupClosed (univ : Set α) := by
  simp [CountableSupClosed]

lemma CountableSupClosed.inter [SupSet α] (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ∩ t) :=
  fun _A hA ↦ ⟨hs (fun n ↦ (hA n).1), ht (fun n ↦ (hA n).2)⟩

lemma countableSupClosed_sInter [SupSet α] (hS : ∀ s ∈ S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) :=
  fun _A hA _s hs ↦ hS _ hs fun n ↦ hA n _ hs

lemma countableSupClosed_iInter [SupSet α] (hf : ∀ i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
  countableSupClosed_sInter <| forall_mem_range.2 hf

lemma CountableSupClosed.directedOn [ConditionallyCompleteLattice α] (hs : CountableSupClosed s) :
    DirectedOn (· ≤ ·) s :=
  hs.supClosed.directedOn

lemma CountableSupClosed.prod [SupSet α] [SupSet β] {t : Set β}
    (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) :=
  fun _a ha ↦ ⟨by rw [Prod.fst_iSup]; exact hs (fun n ↦ (ha n).1),
    by rw [Prod.snd_iSup]; exact ht (fun n ↦ (ha n).2)⟩

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma CountableSupClosed.finsetSup'_mem [ConditionallyCompleteLattice α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  hs.supClosed.finsetSup'_mem ht

lemma CountableSupClosed.finsetSup_mem [ConditionallyCompleteLattice α] [OrderBot α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset
end SemilatticeSup

section SemilatticeInf

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *countably inf-closed* if `⨅ n, A n ∈ s` for all `A : ℕ → α` with `A n ∈ s`. -/
def CountableInfClosed [InfSet α] (s : Set α) : Prop := ∀ ⦃A : ℕ → α⦄, (∀ n, A n ∈ s) → ⨅ n, A n ∈ s

lemma CountableInfClosed.iInf_mem_of_nonempty {ι : Type*} [hι : Countable ι] [Nonempty ι] [InfSet α]
    (hs : CountableInfClosed s) (A : ι → α) (hA : ∀ n, A n ∈ s) :
    (⨅ n, A n) ∈ s := by
  obtain ⟨g, hg⟩ := countable_iff_exists_surjective.mp hι
  have : ⨅ i, A i = ⨅ n, A (g n) := by rw [Function.Surjective.iInf_comp hg]
  rw [this]
  exact hs (fun n ↦ hA (g n))

lemma CountableInfClosed.iInf_mem {ι : Type*} [hι : Countable ι] [CompleteLattice α]
    (hs : CountableInfClosed s) (h_top : ⊤ ∈ s) (A : ι → α) (hA : ∀ n, A n ∈ s) :
    (⨅ n, A n) ∈ s := by
  cases isEmpty_or_nonempty ι
  · rwa [iInf_of_empty]
  · exact hs.iInf_mem_of_nonempty A hA

lemma CountableInfClosed.sInf_mem_of_nonempty [InfSet α] (hs : CountableInfClosed s)
    (A : Set α) [Countable A] [Nonempty A] (hA : ∀ a ∈ A, a ∈ s) :
    sInf A ∈ s := by
  rw [sInf_eq_iInf']
  exact hs.iInf_mem_of_nonempty (fun (a : A) ↦ a) fun a ↦ hA a a.2

lemma CountableInfClosed.sInf_mem [CompleteLattice α] (hs : CountableInfClosed s)
    (h_top : ⊤ ∈ s) (A : Set α) [Countable A] (hA : ∀ a ∈ A, a ∈ s) :
    sInf A ∈ s := by
  rcases eq_empty_or_nonempty A with rfl | hA_nonempty
  · simpa
  · have : Nonempty A := Set.nonempty_coe_sort.mpr hA_nonempty
    exact hs.sInf_mem_of_nonempty A hA

lemma CountableInfClosed.infClosed [ConditionallyCompleteLattice α] (hs : CountableInfClosed s) :
    InfClosed s := by
  intro a ha b hb
  have : a ⊓ b = sInf {a, b} := by simp
  rw [this]
  exact hs.sInf_mem_of_nonempty (A := {a, b}) (fun u ↦ by grind)

@[simp] lemma countableInfClosed_empty [InfSet α] : CountableInfClosed (∅ : Set α) := by
  simp [CountableInfClosed]

@[simp] lemma countableInfClosed_singleton [ConditionallyCompletePartialOrderInf α] :
    CountableInfClosed ({a} : Set α) := by
  simp only [CountableInfClosed, mem_singleton_iff]
  intro A hA
  simp [hA]

@[simp] lemma countableInfClosed_univ [InfSet α] : CountableInfClosed (univ : Set α) := by
  simp [CountableInfClosed]

lemma CountableInfClosed.inter [InfSet α] (hs : CountableInfClosed s) (ht : CountableInfClosed t) :
    CountableInfClosed (s ∩ t) :=
  fun _A hA ↦ ⟨hs (fun n ↦ (hA n).1), ht (fun n ↦ (hA n).2)⟩

lemma countableInfClosed_sInter [InfSet α] (hS : ∀ s ∈ S, CountableInfClosed s) :
    CountableInfClosed (⋂₀ S) :=
  fun _A hA _s hs ↦ hS _ hs fun n ↦ hA n _ hs

lemma countableInfClosed_iInter [InfSet α] (hf : ∀ i, CountableInfClosed (f i)) :
    CountableInfClosed (⋂ i, f i) :=
  countableInfClosed_sInter <| forall_mem_range.2 hf

lemma CountableInfClosed.prod [InfSet α] [InfSet β] {t : Set β}
    (hs : CountableInfClosed s) (ht : CountableInfClosed t) :
    CountableInfClosed (s ×ˢ t) :=
  fun _a ha ↦ ⟨by rw [Prod.fst_iInf]; exact hs (fun n ↦ (ha n).1),
    by rw [Prod.snd_iInf]; exact ht (fun n ↦ (ha n).2)⟩

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma CountableInfClosed.finsetInf'_mem [ConditionallyCompleteLattice α]
    (hs : CountableInfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf' ht f ∈ s :=
  hs.infClosed.finsetInf'_mem ht

lemma CountableInfClosed.finsetInf_mem [ConditionallyCompleteLattice α] [OrderTop α]
    (hs : CountableInfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf f ∈ s :=
  inf'_eq_inf ht f ▸ hs.finsetInf'_mem ht

end Finset
end SemilatticeInf


open Finset OrderDual

section Lattice
variable {ι : Sort*} [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

@[simp] lemma countableSupClosed_preimage_toDual {s : Set αᵒᵈ} :
    CountableSupClosed (toDual ⁻¹' s) ↔ CountableInfClosed s := Iff.rfl

@[simp] lemma countableInfClosed_preimage_toDual {s : Set αᵒᵈ} :
    CountableInfClosed (toDual ⁻¹' s) ↔ CountableSupClosed s := Iff.rfl

@[simp] lemma countableSupClosed_preimage_ofDual {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s := Iff.rfl

@[simp] lemma countableInfClosed_preimage_ofDual {s : Set α} :
    CountableInfClosed (ofDual ⁻¹' s) ↔ CountableSupClosed s := Iff.rfl

alias ⟨_, CountableInfClosed.dual⟩ := countableSupClosed_preimage_ofDual
alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

end Lattice

/-! ## Closure -/

section SemilatticeSup
variable {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
def countableSupClosure [ConditionallyCompletePartialOrderSup α] :
    ClosureOperator (Set α) := .ofPred
  (fun s ↦ {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a})
  CountableSupClosed
  (fun s a ha ↦ ⟨fun _ ↦ a, by simpa, by rw [ciSup_const]⟩)
  (by
    classical
    intro x A hA
    -- todo: extract lemma
    simp only [Set.mem_setOf_eq] at hA
    choose B hB hB_eq using hA

    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetSup'_mem ht fun i hi ↦ hs <| hts hi)

@[simp] lemma subset_supClosure {s : Set α} : s ⊆ supClosure s := supClosure.le_closure _

@[simp] lemma supClosed_supClosure : SupClosed (supClosure s) := supClosure.isClosed_closure _

lemma supClosure_mono : Monotone (supClosure : Set α → Set α) := supClosure.monotone

@[simp] lemma supClosure_eq_self : supClosure s = s ↔ SupClosed s := supClosure.isClosed_iff.symm

alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

lemma supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s :=
  supClosure.idempotent _

@[simp] lemma supClosure_empty : supClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma supClosure_singleton : supClosure {a} = {a} := by simp
@[simp] lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_supClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
    exact sup'_le _ _ fun b hb ↦ ha <| hts hb

@[simp] lemma isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a := by simp [IsLUB]

lemma sup_mem_supClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ supClosure s :=
  supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

lemma finsetSup'_mem_supClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ supClosure s :=
  supClosed_supClosure.finsetSup'_mem _ fun _i hi ↦ subset_supClosure <| hf _ hi

lemma supClosure_min : s ⊆ t → SupClosed t → supClosure s ⊆ t := supClosure.closure_min

/-- The semilattice generated by a finite set is finite. -/
protected lemma Set.Finite.supClosure (hs : s.Finite) : (supClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t ∈ s.powerset | t.Nonempty}.attach.image
    fun t ↦ t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma supClosure_prod (s : Set α) (t : Set β) :
    supClosure (s ×ˢ t) = supClosure s ×ˢ supClosure t :=
  le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_sup'_sup']

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β] {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
def infClosure : ClosureOperator (Set α) := ClosureOperator.ofPred
  (fun s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.inf' ht id = a})
  InfClosed
  (fun s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, inf'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetInf'_mem ht fun i hi ↦ hs <| hts hi)

@[simp] lemma subset_infClosure {s : Set α} : s ⊆ infClosure s := infClosure.le_closure _

@[simp] lemma infClosed_infClosure : InfClosed (infClosure s) := infClosure.isClosed_closure _

lemma infClosure_mono : Monotone (infClosure : Set α → Set α) := infClosure.monotone

@[simp] lemma infClosure_eq_self : infClosure s = s ↔ InfClosed s := infClosure.isClosed_iff.symm

alias ⟨_, InfClosed.infClosure_eq⟩ := infClosure_eq_self

lemma infClosure_idem (s : Set α) : infClosure (infClosure s) = infClosure s :=
  infClosure.idempotent _

@[simp] lemma infClosure_empty : infClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma infClosure_singleton : infClosure {a} = {a} := by simp
@[simp] lemma infClosure_univ : infClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma lowerBounds_infClosure (s : Set α) : lowerBounds (infClosure s) = lowerBounds s :=
  (lowerBounds_mono_set subset_infClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
    exact le_inf' _ _ fun b hb ↦ ha <| hts hb

@[simp] lemma isGLB_infClosure : IsGLB (infClosure s) a ↔ IsGLB s a := by simp [IsGLB]

lemma inf_mem_infClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊓ b ∈ infClosure s :=
  infClosed_infClosure (subset_infClosure ha) (subset_infClosure hb)

lemma finsetInf'_mem_infClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.inf' ht f ∈ infClosure s :=
  infClosed_infClosure.finsetInf'_mem _ fun _i hi ↦ subset_infClosure <| hf _ hi

lemma infClosure_min : s ⊆ t → InfClosed t → infClosure s ⊆ t := infClosure.closure_min

/-- The semilattice generated by a finite set is finite. -/
protected lemma Set.Finite.infClosure (hs : s.Finite) : (infClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t ∈ s.powerset | t.Nonempty}.attach.image
    fun t ↦ t.1.inf' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma infClosure_prod (s : Set α) (t : Set β) :
    infClosure (s ×ˢ t) = infClosure s ×ˢ infClosure t :=
  le_antisymm (infClosure_min (Set.prod_mono subset_infClosure subset_infClosure) <|
    infClosed_infClosure.prod infClosed_infClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_inf'_inf']

end SemilatticeInf

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

protected lemma SupClosed.infClosure (hs : SupClosed s) : SupClosed (infClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

protected lemma InfClosed.supClosure (hs : InfClosed s) : InfClosed (supClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [sup'_inf_sup']
  exact finsetSup'_mem_supClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[simp] lemma supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClosure s :=
  le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

@[simp] lemma infClosure_supClosure (s : Set α) : infClosure (supClosure s) = latticeClosure s :=
  le_antisymm (infClosure_min (supClosure_min subset_latticeClosure isSublattice_latticeClosure.1)
    isSublattice_latticeClosure.2) <| latticeClosure_min (subset_supClosure.trans subset_infClosure)
      ⟨supClosed_supClosure.infClosure, infClosed_infClosure⟩

end DistribLattice

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s)
    (hf : ∀ i, f i ∈ s) : ⨆ i, f i ∈ s := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ ↦ hf _

lemma InfClosed.iInf_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : InfClosed s)
    (hf : ∀ i, f i ∈ s) : ⨅ i, f i ∈ s := hs.dual.iSup_mem_of_nonempty hf

lemma SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sSup t ∈ s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

lemma InfClosed.sInf_mem_of_nonempty (hs : InfClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sInf t ∈ s := hs.dual.sSup_mem_of_nonempty ht ht' hts

end ConditionallyCompleteLattice

variable [CompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

lemma InfClosed.biInf_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem_of_nonempty ht ht' hf

lemma SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨆ i, f i ∈ s := by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

lemma InfClosed.iInf_mem [Finite ι] (hs : InfClosed s) (htop : ⊤ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨅ i, f i ∈ s := hs.dual.iSup_mem htop hf

lemma SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ ∈ s) (hts : t ⊆ s) :
    sSup t ∈ s := by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

lemma InfClosed.sInf_mem (hs : InfClosed s) (ht : t.Finite) (htop : ⊤ ∈ s) (hts : t ⊆ s) :
    sInf t ∈ s := hs.dual.sSup_mem ht htop hts

lemma SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (hbot : ⊥ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)

lemma InfClosed.biInf_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (htop : ⊤ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem ht htop hf
