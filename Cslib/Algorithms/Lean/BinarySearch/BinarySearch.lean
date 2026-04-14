/-
Copyright (c) 2026 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# BinarySearch on a list

In this file we introduce a `binarySearch` algorithm that returns a time monad
over the list `TimeM ℕ (List α)`. The time complexity of `binarySearch`
is the number of comparisons.

--
## Main results

- `mergeSort_correct`: `mergeSort` permutes the list into a sorted one.
- `mergeSort_time`:  The number of comparisons of `mergeSort` is at most `n*⌈log₂ n⌉`.

-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

def binaryContains (xs : List α) (a : α) : TimeM ℕ Bool := do
  if h0 : xs.isEmpty then return false
  else
    have h2 : 0 < xs.length := by
      simp only [List.isEmpty_iff] at h0
      rw [List.eq_nil_iff_length_eq_zero] at h0
      apply Nat.pos_iff_ne_zero.2 h0
    let halfFin := @Nat.div_lt_self xs.length 2 h2 (by simp only [Nat.one_lt_ofNat])
    ✓ if xs.get ⟨_, halfFin⟩ ≤ a then
      if xs.get ⟨_, halfFin⟩ = a then return true
      else
        let right := xs.drop (xs.length / 2 + 1) -- Nat division rounds down
        binaryContains right a
    else
      let left := xs.take (xs.length / 2)
      binaryContains left a

section Correctness

open List

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

/-- Our contains computes the one already in mathlib. -/
@[simp, grind =]
theorem ret_binaryContains (xs : List α) (hxs : IsSorted xs) (a : α) :
  ⟪binaryContains xs a⟫ = xs.contains a := by
  simp_wf
  fun_induction binaryContains with
  | case1 xs h0 =>
    simp only [List.isEmpty_iff] at h0
    rw [h0]
    simp only [ret_pure, not_mem_nil, decide_false]
  | case2 xs _ h2 halfFin ih1 ih2 =>
    simp_all only [List.isEmpty_iff, ret_bind]
    have h2 := List.take_append_drop (xs.length / 2) xs
    by_cases hc : xs.get ⟨_, halfFin⟩ ≤ a
    case pos =>
      simp_all only [↓reduceIte]
      by_cases hc2 : xs.get ⟨_, halfFin⟩ = a
      case pos =>
        simp_all only [↓reduceIte]
        rw [← hc2, ret_pure]
        simp only [get_eq_getElem, getElem_mem, decide_true]
      case neg =>
        simp_all only [↓reduceIte]
        have h4 := @Pairwise.drop _ _ xs (xs.length / 2 + 1) hxs
        rw [← IsSorted] at h4
        specialize ih1 h4
        rw [ih1]
        simp only [decide_eq_decide]
        refine ⟨mem_of_mem_drop, ?_⟩
        intros haxs
        rw [← h2, mem_append] at haxs
        have h5 : a ∉ take (xs.length / 2) xs := by
          by_contra hat
          rw [mem_take_iff_getElem] at hat
          obtain ⟨j, ⟨hj, hj2⟩⟩ := hat
          have h6 : xs[j] < a := by
            have h7 := lt_of_le_of_ne hc hc2
            rw [IsSorted] at hxs
            have h8 := (lt_min_iff.1 hj).1
            have h9 := List.pairwise_iff_get.1 hxs
            specialize h9 ⟨j, (lt_min_iff.1 hj).2⟩ ⟨_, halfFin⟩ h8
            simp only [get_eq_getElem] at h9
            simp only [get_eq_getElem] at h7
            apply lt_of_le_of_lt h9 h7
          apply ne_of_lt h6 hj2
        rw [drop_add_one_eq_tail_drop]
        have h7 : drop (xs.length / 2) xs ≠ [] := by
          simp only [ne_eq, drop_eq_nil_iff, not_le]
          apply halfFin
        simp only [get_eq_getElem] at hc2
        rw [← head_drop h7] at hc2
        have h8 := (ne_comm.1 hc2)
        apply mem_of_ne_of_mem (ne_comm.1 hc2)
        have h10 := Or.resolve_left haxs h5
        simp only [head_drop, tail_drop, getElem_cons_drop]
        apply Or.resolve_left haxs h5
    case neg =>
      simp_all only [↓reduceIte]
      have h4 := @Pairwise.take _ _ xs (xs.length / 2) hxs
      rw [← IsSorted] at h4
      specialize ih2 h4
      rw [ih2]
      simp only [decide_eq_decide]
      refine ⟨mem_of_mem_take, ?_⟩
      intros haxs
      rw [← h2, mem_append] at haxs
      have h5 : a ∉ drop (xs.length / 2) xs := by
        by_contra hat
        rw [mem_drop_iff_getElem] at hat
        obtain ⟨j, ⟨hj, hj2⟩⟩ := hat
        rw [not_le] at hc
        have h6 : a < xs.get ⟨j + xs.length / 2, hj⟩ := by
          rw [IsSorted] at hxs
          have h9 := List.pairwise_iff_get.1 hxs
          have h10 : xs.length / 2 ≤ j + xs.length / 2 := by
            simp only [le_add_iff_nonneg_left, zero_le]
          rw [le_iff_eq_or_lt] at h10
          cases h10 with
          | inl h =>
            simp only [get_eq_getElem] at hc
            rw [← hj2] at hc
            rw [add_comm j (xs.length / 2)] at h
            simp_rw [← h] at hc
            by_contra
            apply (lt_self_iff_false _).1 hc
          | inr h =>
            specialize h9 ⟨_, halfFin⟩ ⟨_, hj⟩ h
            simp only [get_eq_getElem] at h9
            simp only [get_eq_getElem, gt_iff_lt]
            simp only [get_eq_getElem] at hc
            apply lt_of_lt_of_le hc h9
        rw [← hj2] at h6
        simp only [get_eq_getElem] at h6
        simp_rw [add_comm j _] at h6
        apply (lt_self_iff_false _).1 h6
      tauto

end Correctness

section TimeComplexity

def timeBinaryContainsRec : ℕ → ℕ
| 0 => 0
| n@(_+1) => timeBinaryContainsRec (n/2) + 1

@[simp]
theorem timeBinaryContainsRec_zero : timeBinaryContainsRec 0 = 0 := by
  unfold timeBinaryContainsRec
  simp only

@[simp]
theorem timeBinaryContainsRec_one : timeBinaryContainsRec 1 = 1 := by
  unfold timeBinaryContainsRec
  simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceDiv, timeBinaryContainsRec_zero]

theorem timeBinaryContainsRec_ne_zero {n : ℕ} (hn : n ≠ 0) :
  timeBinaryContainsRec n ≠ 0 := by
  fun_induction timeBinaryContainsRec with
  | case1 => grind
  | case2 => grind

@[simp]
theorem timeBinaryContainsRec_eq_zero_iff {n : ℕ} :
  timeBinaryContainsRec n = 0 ↔ n = 0 := by
  fun_induction timeBinaryContainsRec with
  | case1 => grind
  | case2 => grind

@[simp]
theorem timeBinaryContainsRec_eq_one_iff {n : ℕ} :
  timeBinaryContainsRec n = 1 ↔ n = 1 := by
  fun_induction timeBinaryContainsRec with
  | case1 => grind
  | case2 n ih =>
    simp only [Nat.add_eq_right, timeBinaryContainsRec_eq_zero_iff, Nat.div_eq_zero_iff,
      OfNat.ofNat_ne_zero, false_or, Nat.succ_eq_add_one]
    omega

theorem timeBinaryContainsRec_eq_half_add_one {n : ℕ} (hn : 1 ≤ n) :
  timeBinaryContainsRec n = timeBinaryContainsRec (n / 2) + 1 := by
  fun_induction timeBinaryContainsRec with
  | case1 => grind
  | case2 n ih => grind

open Nat (clog)

/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
@[grind →]
lemma clog2_half_le (n : ℕ) (h : 1 < n) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  grind [Nat.clog_of_one_lt one_lt_two h]

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind →]
lemma clog2_floor_half_le (n : ℕ) (h : 1 < n) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  apply Nat.clog_monotone
  grind

/-- Upper bound function for binary search time complexity: `T(n) = ⌈log₂ n⌉ + 1` -/
abbrev T (n : ℕ) : ℕ := clog 2 n + 1

/-- Solve the recurrence -/
theorem timeBinaryContainsRec_le_T (n : ℕ) : timeBinaryContainsRec n ≤ T n := by
  fun_induction timeBinaryContainsRec with
  | case1 => grind
  | case2 n ih =>
    induction n with
    | zero => simp only [zero_add, Nat.reduceDiv, timeBinaryContainsRec_zero, Nat.succ_eq_add_one,
      le_add_iff_nonneg_left, Nat.clog_one_right, Std.le_refl]
    | succ n _ =>
      have h2 : 1 < n + 2 := by omega
      grw [ih]
      simp_rw [T] at *
      apply Nat.add_le_add_right
      have h3 := clog2_floor_half_le _ h2
      have h4 := add_le_add_left h3 1
      rw [Nat.sub_add_cancel] at h4
      · apply h4
      apply Nat.succ_le_of_lt
        (lt_of_lt_of_le (Nat.log_pos (one_lt_two) (@le_add_self _ _ _ _ 2 n))
        (Nat.log_le_clog 2 (n + 2)))

theorem timeBinaryContains_le_succ (n : ℕ) :
  timeBinaryContainsRec n ≤ timeBinaryContainsRec (n + 1) := by
  fun_induction timeBinaryContainsRec with
  | case1 =>
    simp only [zero_add, timeBinaryContainsRec_one, zero_le]
  | case2 n ih =>
    have h6 : 1 ≤ (n.succ + 1) := by
      simp only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
    rw [timeBinaryContainsRec_eq_half_add_one h6]
    grind only

theorem timeBinaryContainsRec_le {a b : ℕ} (hab : a ≤ b) :
  timeBinaryContainsRec a ≤ timeBinaryContainsRec b := by
  induction b with
  | zero =>
    grind only
  | succ n hn =>
    by_cases han : a = n + 1
    case pos => rw [han]
    case neg =>
      have hab2 := hn (Nat.lt_succ_iff.1 (lt_of_le_of_ne hab han))
      have hn := timeBinaryContains_le_succ n
      apply le_trans hab2 hn


theorem binaryContains_time_le (xs : List α) (a : α) :
    (binaryContains xs a).time ≤ timeBinaryContainsRec xs.length := by
  fun_induction binaryContains with
  | case1 =>
    grind
  | case2 xs h0 h2 halfFin ih1 ih2 =>
    simp only [time_bind, time_tick]
    by_cases hc : xs.get ⟨_, halfFin⟩ ≤ a
    case pos =>
      simp_all only [↓reduceIte]
      by_cases hc2 : xs.get ⟨_, halfFin⟩ = a
      case pos =>
        simp_all only [↓reduceIte, time_pure, add_zero]
        unfold timeBinaryContainsRec
        grind only
      case neg =>
        simp only [List.get_eq_getElem]
        simp only [List.get_eq_getElem] at hc2
        rw [ite_cond_eq_false _ _ (eq_false hc2)]
        rw [List.length_drop] at ih1
        have h5 : timeBinaryContainsRec (xs.length - (xs.length / 2 + 1)) ≤
          timeBinaryContainsRec (xs.length / 2) := by
          apply timeBinaryContainsRec_le
          grind only
        rw [timeBinaryContainsRec_eq_half_add_one (by omega)]
        grind only
    case neg =>
      rw [timeBinaryContainsRec_eq_half_add_one (by omega)]
      simp only [ite_cond_eq_false _ _ (eq_false hc)]
      simp_all only [List.isEmpty_iff, List.length_drop, List.length_take, List.get_eq_getElem,
        not_le]
      grind only [= min_def]

/-- Time complexity of binaryContains -/
theorem binaryContains_time (xs : List α) (a : α) :
  let n := xs.length
  (binaryContains xs a).time ≤ clog 2 n + 1 := by
  grind [binaryContains_time_le, timeBinaryContainsRec_le_T]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
