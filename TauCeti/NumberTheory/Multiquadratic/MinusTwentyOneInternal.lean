/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.Multiquadratic.GaloisGroup

/-!
# Internal proof data for the `-21` prime-discriminant examples

This module keeps the concrete root vector and square-class-independence witnesses private while
exposing packaged consequences used by the public degree and Galois-cardinality examples for
`ℚ(√-1, √-3, √-7)`.
-/

namespace TauCeti.Multiquadratic

/-- Each entry of the concrete list `[-4, -3, -7]` is a prime discriminant. -/
private theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
    ∀ i : Fin 3, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

/-- The concrete list `[-4, -3, -7]` is injective. -/
private theorem negFourNegThreeNegSevenPrimeDiscriminants_injective :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

/-- The concrete list `[-4, -3, -7]` does not contain all three even prime discriminants. -/
private theorem negFourNegThreeNegSevenPrimeDiscriminants_not_all_three_evenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

/-- The concrete roots `[i, √-3, √-7]` for the prime-discriminant list `[-4, -3, -7]`. -/
private noncomputable abbrev negFourNegThreeNegSevenPrimeDiscriminantRoots : Fin 3 → ℂ :=
  ![Complex.I, sqrtNegThree, sqrtNegSeven]

/-- Each concrete root squares to the radicand attached to the corresponding prime
discriminant in `[-4, -3, -7]`. -/
private theorem negFourNegThreeNegSevenPrimeDiscriminantRoots_sq (i : Fin 3) :
    negFourNegThreeNegSevenPrimeDiscriminantRoots i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand
          (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, hrad]

/-- The concrete root vector `[i, √-3, √-7]` has range `{i, √-3, √-7}`. -/
private theorem range_negFourNegThreeNegSevenPrimeDiscriminantRoots :
    Set.range negFourNegThreeNegSevenPrimeDiscriminantRoots =
      {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp [negFourNegThreeNegSevenPrimeDiscriminantRoots]
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
    · exact ⟨1, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
    · exact ⟨2, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩

/-- Packaged square-class independence for the radicands `-1`, `-3`, and `-7` attached to
the prime-discriminant list `[-4, -3, -7]`. -/
private theorem not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands :
    ∀ S : Finset (Fin 3), S.Nonempty →
      ¬ IsSquare
        (∏ i ∈ S,
          (((primeDiscriminantRadicand
            (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ))) := by
  exact not_isSquare_prod_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    negFourNegThreeNegSevenPrimeDiscriminants_injective
    negFourNegThreeNegSevenPrimeDiscriminants_not_all_three_evenPrimeDiscriminants

public section

namespace MinusTwentyOne

/-- Packaged degree consequence for the `-21` prime-discriminant root data. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_range
    (d := fun i =>
      (((primeDiscriminantRadicand
        (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)))
    (root := negFourNegThreeNegSevenPrimeDiscriminantRoots)
    negFourNegThreeNegSevenPrimeDiscriminantRoots_sq
    not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands
  rw [← range_negFourNegThreeNegSevenPrimeDiscriminantRoots]
  simpa [Nat.card_fin] using h

/-- Packaged Galois-cardinality consequence for the `-21` prime-discriminant root data. -/
theorem card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Nat.card
      ((IntermediateField.adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (IntermediateField.adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 8 := by
  have h := card_aut_adjoin_range
    (d := fun i =>
      (((primeDiscriminantRadicand
        (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)))
    (root := negFourNegThreeNegSevenPrimeDiscriminantRoots)
    negFourNegThreeNegSevenPrimeDiscriminantRoots_sq
    not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands
  rw [← range_negFourNegThreeNegSevenPrimeDiscriminantRoots]
  exact h.trans (by norm_num [Nat.card_fin])

end MinusTwentyOne

end

end TauCeti.Multiquadratic
