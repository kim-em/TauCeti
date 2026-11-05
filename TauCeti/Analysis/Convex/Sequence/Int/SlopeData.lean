/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Set.OrdConnectedLinear
public import TauCeti.Analysis.Convex.Sequence.Int.Basic
public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic

/-!
# Slope presentations at integer anchors

Finite and infinite unit-slope data can represent polygons beginning at any integer.
We reuse the natural-indexed slope data, choosing an integer coordinate origin `k`:
the absolute anchor is `k + start`. The origin is an external parameter, not another
field of slope data. For each fixed origin the represented heights determine the data.

Extraction and reconstruction are inverse for convex integer-indexed heights with a
specified finite interval or half-line as finite domain. Extension by infinity and
integer translation transfer convexity and the lower-envelope identity from the
one-sided theory. No presentation is asserted for a domain unbounded to the left.
Length zero still represents a singleton, while infinite data may represent a
terminal ray. The cumulative-sum formulas and change of values work over ordered
additive monoids, including rational slopes.
-/

public section

namespace TauCeti

variable {Γ Γ' : Type*} [Preorder Γ] [Preorder Γ']

namespace FiniteSlopeData

section AddCommMonoid

variable [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : FiniteSlopeData Γ)

/-- Heights of slope data in integer coordinates with origin `k`. The absolute
finite domain is `[k + start, k + start + length]`; all other heights are infinite. -/
noncomputable def intHeights (k : ℤ) (n : ℤ) : WithTop Γ :=
  Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ (n - k)

/-- The defining extension formula for integer-indexed heights. -/
theorem intHeights_def (k : ℤ) :
    d.intHeights k = fun n => Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ (n - k) := (rfl)

/-- Reading the heights from their coordinate origin recovers the natural-indexed heights. -/
@[simp]
theorem intHeights_add_natCast (k : ℤ) (n : ℕ) :
    d.intHeights k (k + n) = d.heights n := by
  simp [intHeights_def, Nat.cast_injective.extend_apply]

/-- Every height strictly before the coordinate origin is infinite. -/
theorem intHeights_of_lt {k n : ℤ} (hn : n < k) : d.intHeights k n = ⊤ := by
  simp [intHeights_def, Function.extend_natCast_of_neg _ _ (by omega : n - k < 0)]

/-- The finite domain in absolute integer coordinates. -/
theorem intHeights_ne_top_iff {k n : ℤ} :
    d.intHeights k n ≠ ⊤ ↔ k + d.start ≤ n ∧ n ≤ k + d.start + d.length := by
  rcases lt_or_ge n k with hn | hn
  · rw [d.intHeights_of_lt hn]
    simp only [ne_eq, not_true_eq_false, false_iff]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    rw [intHeights_add_natCast, heights_ne_top_iff]
    omega

/-- The infinite heights are exactly those outside the absolute finite domain. -/
@[simp]
theorem intHeights_eq_top_iff {k n : ℤ} :
    d.intHeights k n = ⊤ ↔ n < k + d.start ∨ k + d.start + d.length < n := by
  rw [← not_iff_not, ← ne_eq, intHeights_ne_top_iff]
  omega

/-- Changing the coordinate origin translates the represented graph. -/
theorem intHeights_add (k t n : ℤ) :
    d.intHeights (k + t) (n + t) = d.intHeights k n := by
  simp [intHeights_def]

/-- Integer-indexed heights commute with an order-preserving additive change of values. -/
@[simp]
theorem intHeights_map (f : Γ →+o Γ') (k n : ℤ) :
    (d.map f).intHeights k n = WithTop.map f (d.intHeights k n) := by
  rcases lt_or_ge n k with hn | hn
  · simp [intHeights_of_lt _ hn]
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    simp

/-- Comparing integer heights at a common origin is equivalent to comparing
the natural-indexed heights. -/
theorem intHeights_le_intHeights_iff {d e : FiniteSlopeData Γ} (k : ℤ) :
    d.intHeights k ≤ e.intHeights k ↔ d.heights ≤ e.heights := by
  refine ⟨fun hde n => ?_, fun hde n => ?_⟩
  · simpa using hde (k + n)
  · rcases lt_or_ge n k with hn | hn
    · simp [intHeights_of_lt _ hn]
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
      simpa using hde i

end AddCommMonoid

/-- At a fixed coordinate origin, integer-indexed heights determine the slope data. -/
theorem intHeights_injective [AddCancelCommMonoid Γ] (k : ℤ) :
    Function.Injective (fun d : FiniteSlopeData Γ => d.intHeights k) := by
  intro d e hde
  apply heights_injective
  funext n
  simpa using congrFun hde (k + n)

/-- Integer-indexed real slope data represents a convex height sequence. -/
theorem isIntConvexSeq_intHeights (d : FiniteSlopeData ℝ) (k : ℤ) :
    IsIntConvexSeq (d.intHeights k) := by
  simpa only [intHeights_def, sub_eq_add_neg] using
    (isIntConvexSeq_extend_iff.mpr d.isConvexSeq_heights).comp_add_right (-k)

/-- Taking the integer lower convex envelope leaves represented heights unchanged. -/
@[simp]
theorem intLowerConvexEnvelope_intHeights (d : FiniteSlopeData ℝ) (k : ℤ) :
    intLowerConvexEnvelope (d.intHeights k) = d.intHeights k :=
  (d.isIntConvexSeq_intHeights k).intLowerConvexEnvelope_eq

/-- Extract slope data relative to origin `k` from a convex integer height sequence
with the specified absolute finite domain. -/
noncomputable def ofIsIntConvexSeq {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h)
    {k : ℤ} {l length : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ k + l ≤ n ∧ n ≤ k + l + length) : FiniteSlopeData ℝ :=
  ofIsConvexSeq (hh.isConvexSeq k) (l := l) (k := length)
    (fun n => by rw [hdom]; omega)

variable {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h) {k : ℤ} {l length : ℕ}
  (hdom : ∀ n, h n ≠ ⊤ ↔ k + l ≤ n ∧ n ≤ k + l + length)

/-- The extracted starting index is measured from the chosen integer origin. -/
@[simp]
theorem ofIsIntConvexSeq_start : (ofIsIntConvexSeq hh hdom).start = l := by
  simp [ofIsIntConvexSeq]

/-- The extracted initial height is the height at the absolute anchor. -/
@[simp]
theorem ofIsIntConvexSeq_initialHeight :
    (ofIsIntConvexSeq hh hdom).initialHeight = (h (k + l)).untop₀ := by
  simp [ofIsIntConvexSeq]

/-- Extraction preserves horizontal length. -/
@[simp]
theorem ofIsIntConvexSeq_length : (ofIsIntConvexSeq hh hdom).length = length := by
  simp [ofIsIntConvexSeq]

/-- The extracted unit slopes are the successive differences in the one-sided tail. -/
@[simp]
theorem ofIsIntConvexSeq_slope (i : Fin (ofIsIntConvexSeq hh hdom).length) :
    (ofIsIntConvexSeq hh hdom).slope i =
      unitSlope (fun n : ℕ => h (k + n)) (l + i) := by
  unfold ofIsIntConvexSeq
  exact ofIsConvexSeq_slope _ _ i

/-- Extracting and reconstructing recovers every integer height, including those
outside the finite domain. -/
@[simp]
theorem intHeights_ofIsIntConvexSeq : (ofIsIntConvexSeq hh hdom).intHeights k = h := by
  funext n
  rcases lt_or_ge n k with hn | hn
  · rw [intHeights_of_lt _ hn]
    exact (not_ne_iff.mp fun hne => by have := (hdom n).mp hne; omega).symm
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    rw [intHeights_add_natCast]
    exact congrFun (heights_ofIsConvexSeq _ _) i

/-- Reconstructing integer heights and extracting at the same origin recovers the data. -/
@[simp]
theorem ofIsIntConvexSeq_intHeights (d : FiniteSlopeData ℝ) (k : ℤ) :
    ofIsIntConvexSeq (d.isIntConvexSeq_intHeights k)
      (fun _ => d.intHeights_ne_top_iff) = d :=
  intHeights_injective k (intHeights_ofIsIntConvexSeq _ _)

/-- A two-sided real height sequence admits finite slope data at some integer origin
exactly when it is convex and its finite domain is finite and nonempty. -/
theorem exists_intHeights_eq_iff {h : ℤ → WithTop ℝ} :
    (∃ k : ℤ, ∃ d : FiniteSlopeData ℝ, d.intHeights k = h) ↔
      IsIntConvexSeq h ∧ {n | h n ≠ ⊤}.Nonempty ∧ {n | h n ≠ ⊤}.Finite := by
  constructor
  · rintro ⟨k, d, rfl⟩
    have hdom : {n | d.intHeights k n ≠ ⊤} =
        Set.Icc (k + d.start) (k + d.start + d.length) := by
      ext n
      exact d.intHeights_ne_top_iff
    rw [hdom]
    exact ⟨d.isIntConvexSeq_intHeights k, Set.nonempty_Icc.mpr (by omega),
      Set.finite_Icc _ _⟩
  · rintro ⟨hh, hne, hfin⟩
    have hS := (hne.ordConnected_iff_of_bdd hfin.bddBelow hfin.bddAbove).mp hh.ordConnected
    have hle := csInf_le_csSup hne hfin.bddBelow hfin.bddAbove
    have hdom (n : ℤ) : h n ≠ ⊤ ↔
        sInf {n | h n ≠ ⊤} + (0 : ℕ) ≤ n ∧
          n ≤ sInf {n | h n ≠ ⊤} + (0 : ℕ) +
            ((sSup {n | h n ≠ ⊤} - sInf {n | h n ≠ ⊤}).toNat : ℕ) := by
      simpa [Int.toNat_of_nonneg (sub_nonneg.mpr hle)] using Set.ext_iff.mp hS n
    exact ⟨_, ofIsIntConvexSeq hh hdom, intHeights_ofIsIntConvexSeq hh hdom⟩

end FiniteSlopeData

namespace InfiniteSlopeData

section AddCommMonoid

variable [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : InfiniteSlopeData Γ)

/-- Heights of slope data in integer coordinates with origin `k`. The absolute
finite domain is `[k + start, ∞)`; all other heights are infinite. -/
noncomputable def intHeights (k : ℤ) (n : ℤ) : WithTop Γ :=
  Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ (n - k)

/-- The defining extension formula for integer-indexed heights. -/
theorem intHeights_def (k : ℤ) :
    d.intHeights k = fun n => Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ (n - k) := (rfl)

/-- Reading the heights from their coordinate origin recovers the natural-indexed heights. -/
@[simp]
theorem intHeights_add_natCast (k : ℤ) (n : ℕ) :
    d.intHeights k (k + n) = d.heights n := by
  simp [intHeights_def, Nat.cast_injective.extend_apply]

/-- Every height strictly before the coordinate origin is infinite. -/
theorem intHeights_of_lt {k n : ℤ} (hn : n < k) : d.intHeights k n = ⊤ := by
  simp [intHeights_def, Function.extend_natCast_of_neg _ _ (by omega : n - k < 0)]

/-- The finite domain in absolute integer coordinates. -/
theorem intHeights_ne_top_iff {k n : ℤ} :
    d.intHeights k n ≠ ⊤ ↔ k + d.start ≤ n := by
  rcases lt_or_ge n k with hn | hn
  · rw [d.intHeights_of_lt hn]
    simp only [ne_eq, not_true_eq_false, false_iff]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    rw [intHeights_add_natCast, heights_ne_top_iff]
    omega

/-- The infinite heights are exactly those outside the absolute finite domain. -/
@[simp]
theorem intHeights_eq_top_iff {k n : ℤ} :
    d.intHeights k n = ⊤ ↔ n < k + d.start := by
  rw [← not_iff_not, ← ne_eq, intHeights_ne_top_iff]
  omega

/-- Changing the coordinate origin translates the represented graph. -/
theorem intHeights_add (k t n : ℤ) :
    d.intHeights (k + t) (n + t) = d.intHeights k n := by
  simp [intHeights_def]

/-- Integer-indexed heights commute with an order-preserving additive change of values. -/
@[simp]
theorem intHeights_map (f : Γ →+o Γ') (k n : ℤ) :
    (d.map f).intHeights k n = WithTop.map f (d.intHeights k n) := by
  rcases lt_or_ge n k with hn | hn
  · simp [intHeights_of_lt _ hn]
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    simp

/-- Comparing integer heights at a common origin is equivalent to comparing
the natural-indexed heights. -/
theorem intHeights_le_intHeights_iff {d e : InfiniteSlopeData Γ} (k : ℤ) :
    d.intHeights k ≤ e.intHeights k ↔ d.heights ≤ e.heights := by
  refine ⟨fun hde n => ?_, fun hde n => ?_⟩
  · simpa using hde (k + n)
  · rcases lt_or_ge n k with hn | hn
    · simp [intHeights_of_lt _ hn]
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
      simpa using hde i

end AddCommMonoid

/-- At a fixed coordinate origin, integer-indexed heights determine the slope data. -/
theorem intHeights_injective [AddCancelCommMonoid Γ] (k : ℤ) :
    Function.Injective (fun d : InfiniteSlopeData Γ => d.intHeights k) := by
  intro d e hde
  apply heights_injective
  funext n
  simpa using congrFun hde (k + n)

/-- Integer-indexed real slope data represents a convex height sequence. -/
theorem isIntConvexSeq_intHeights (d : InfiniteSlopeData ℝ) (k : ℤ) :
    IsIntConvexSeq (d.intHeights k) := by
  simpa only [intHeights_def, sub_eq_add_neg] using
    (isIntConvexSeq_extend_iff.mpr d.isConvexSeq_heights).comp_add_right (-k)

/-- Taking the integer lower convex envelope leaves represented heights unchanged. -/
@[simp]
theorem intLowerConvexEnvelope_intHeights (d : InfiniteSlopeData ℝ) (k : ℤ) :
    intLowerConvexEnvelope (d.intHeights k) = d.intHeights k :=
  (d.isIntConvexSeq_intHeights k).intLowerConvexEnvelope_eq

/-- Extract slope data relative to origin `k` from a convex integer height sequence
with the specified absolute finite domain. -/
noncomputable def ofIsIntConvexSeq {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h)
    {k : ℤ} {l : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ k + l ≤ n) : InfiniteSlopeData ℝ :=
  ofIsConvexSeq (hh.isConvexSeq k) (l := l)
    (fun n => by rw [hdom]; omega)

variable {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h) {k : ℤ} {l : ℕ}
  (hdom : ∀ n, h n ≠ ⊤ ↔ k + l ≤ n)

/-- The extracted starting index is measured from the chosen integer origin. -/
@[simp]
theorem ofIsIntConvexSeq_start : (ofIsIntConvexSeq hh hdom).start = l := by
  simp [ofIsIntConvexSeq]

/-- The extracted initial height is the height at the absolute anchor. -/
@[simp]
theorem ofIsIntConvexSeq_initialHeight :
    (ofIsIntConvexSeq hh hdom).initialHeight = (h (k + l)).untop₀ := by
  simp [ofIsIntConvexSeq]

/-- The extracted unit slopes are the successive differences in the one-sided tail. -/
@[simp]
theorem ofIsIntConvexSeq_slope (i : ℕ) :
    (ofIsIntConvexSeq hh hdom).slope i =
      unitSlope (fun n : ℕ => h (k + n)) (l + i) := by
  unfold ofIsIntConvexSeq
  exact ofIsConvexSeq_slope _ _ i

/-- Extracting and reconstructing recovers every integer height, including those
outside the finite domain. -/
@[simp]
theorem intHeights_ofIsIntConvexSeq : (ofIsIntConvexSeq hh hdom).intHeights k = h := by
  funext n
  rcases lt_or_ge n k with hn | hn
  · rw [intHeights_of_lt _ hn]
    exact (not_ne_iff.mp fun hne => by have := (hdom n).mp hne; omega).symm
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
    rw [intHeights_add_natCast]
    exact congrFun (heights_ofIsConvexSeq _ _) i

/-- Reconstructing integer heights and extracting at the same origin recovers the data. -/
@[simp]
theorem ofIsIntConvexSeq_intHeights (d : InfiniteSlopeData ℝ) (k : ℤ) :
    ofIsIntConvexSeq (d.isIntConvexSeq_intHeights k)
      (fun _ => d.intHeights_ne_top_iff) = d :=
  intHeights_injective k (intHeights_ofIsIntConvexSeq _ _)

/-- A two-sided real height sequence admits infinite slope data at some integer origin
exactly when it is convex with infinite finite domain bounded below. -/
theorem exists_intHeights_eq_iff {h : ℤ → WithTop ℝ} :
    (∃ k : ℤ, ∃ d : InfiniteSlopeData ℝ, d.intHeights k = h) ↔
      IsIntConvexSeq h ∧ BddBelow {n | h n ≠ ⊤} ∧ {n | h n ≠ ⊤}.Infinite := by
  constructor
  · rintro ⟨k, d, rfl⟩
    have hdom : {n | d.intHeights k n ≠ ⊤} = Set.Ici (k + d.start) := by
      ext n
      exact d.intHeights_ne_top_iff
    rw [hdom]
    exact ⟨d.isIntConvexSeq_intHeights k, bddBelow_Ici, Set.Ici_infinite _⟩
  · rintro ⟨hh, ⟨k, hk⟩, hinf⟩
    have htail : {i : ℕ | h (k + i) ≠ ⊤}.Infinite := by
      intro hfin
      apply hinf
      refine (hfin.image (fun i : ℕ => k + i)).subset ?_
      intro n hn
      have hn' := hk hn
      have heq : k + ((n - k).toNat : ℕ) = n := by omega
      exact ⟨(n - k).toNat, by simpa only [Set.mem_ofPred_eq, heq] using hn, heq⟩
    obtain ⟨d, hd⟩ := exists_heights_eq_iff.mpr ⟨hh.isConvexSeq k, htail⟩
    refine ⟨k, d, funext fun n => ?_⟩
    rcases lt_or_ge n k with hn | hn
    · rw [intHeights_of_lt _ hn]
      exact (not_ne_iff.mp fun hne => by have := hk hne; omega).symm
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = k + i := ⟨(n - k).toNat, by omega⟩
      rw [intHeights_add_natCast, hd]

end InfiniteSlopeData

end TauCeti
