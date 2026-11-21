/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Coproducts of bifunctors of graded objects as biproducts

For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the fibre of
the addition map over `n` is `Finset.antidiagonal n`
(`CategoryTheory.GradedObject.fiberEquivAntidiagonal`). Reindexing the biproduct bicone along this
equivalence (`CategoryTheory.Limits.Bicone.whiskerIsBilimitIff`) gives a colimit cofan over the
fibre, which Mathlib's `CategoryTheory.GradedObject.CofanMapObjFun.iso` compares with the
coproduct. So the coproduct over `i + j = n` defining
`CategoryTheory.GradedObject.mapBifunctorMapObj` is the biproduct indexed by
`Finset.antidiagonal n`
(`CategoryTheory.GradedObject.mapBifunctorMapObjIsoBiproduct`). The tensor product of graded
objects is a special case (`CategoryTheory.GradedObject.Monoidal.tensorObjIsoBiproduct`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

section Antidiagonal

variable {I : Type*} [Add I] [Finset.HasAntidiagonal I]

/-- The fibre over `n` of the addition map `I × I → I` is `Finset.antidiagonal n`. -/
def fiberEquivAntidiagonal (n : I) :
    ((fun x : I × I ↦ x.1 + x.2) ⁻¹' {n}) ≃ Finset.antidiagonal n :=
  Equiv.subtypeEquivRight fun x ↦ by simp

/-- `fiberEquivAntidiagonal n` does not change the underlying pair. -/
@[simp]
lemma coe_fiberEquivAntidiagonal_apply (n : I) (x : (fun x : I × I ↦ x.1 + x.2) ⁻¹' {n}) :
    (fiberEquivAntidiagonal n x : I × I) = x :=
  (rfl)

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [HasZeroMorphisms C₃]
  (X : GradedObject I C₁) (Y : GradedObject I C₂) (F : C₁ ⥤ C₂ ⥤ C₃)
  [HasMap (((mapBifunctor F I I).obj X).obj Y) (fun x ↦ x.1 + x.2)] (n : I)
  [HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)]

/-- The biproduct of the `(F.obj (X i)).obj (Y j)` indexed by `Finset.antidiagonal n`, as a cofan
over the fibre of the addition map, through `fiberEquivAntidiagonal n`. -/
private def antidiagonalCofan :
    (((mapBifunctor F I I).obj X).obj Y).CofanMapObjFun (fun x ↦ x.1 + x.2) n :=
  -- the summands over the fibre are by definition the `(F.obj (X i)).obj (Y j)`
  Cofan.mk (⨁ fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
    fun x ↦ biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
      (fiberEquivAntidiagonal n x)

/-- The cofan `antidiagonalCofan` is a colimit: it is the biproduct bicone reindexed along
`fiberEquivAntidiagonal n`. -/
private def isColimitAntidiagonalCofan : IsColimit (antidiagonalCofan X Y F n) :=
  -- `antidiagonalCofan` is by definition the cocone of the reindexed biproduct bicone
  (((biproduct.bicone _).whiskerIsBilimitIff (fiberEquivAntidiagonal n)).symm
    (biproduct.isBilimit _)).isColimit

/-- For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the
coproduct of the `(F.obj (X i)).obj (Y j)` with `i + j = n` is the biproduct of these objects
indexed by `Finset.antidiagonal n`, the fibre of the addition map over `n`
(`CategoryTheory.GradedObject.fiberEquivAntidiagonal`). -/
def mapBifunctorMapObjIsoBiproduct :
    mapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y n ≅
      ⨁ fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2) :=
  -- `mapBifunctorMapObj` is by definition `mapObj` of the graded object of the summands, and the
  -- reindexed cofan is by definition a cofan of the summands over the fibre
  (CofanMapObjFun.iso (X := ((mapBifunctor F I I).obj X).obj Y) (p := fun x ↦ x.1 + x.2)
    (isColimitAntidiagonalCofan X Y F n)).symm

/-- `mapBifunctorMapObjIsoBiproduct` sends the summand `(F.obj (X i)).obj (Y j)` to the
corresponding summand of the biproduct. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_hom (i j : I) (h : i + j = n) :
    ιMapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).hom =
      biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ := by
  rw [mapBifunctorMapObjIsoBiproduct, Iso.symm_hom]
  -- `ιMapBifunctorMapObj` is by definition `ιMapObj`, and `mapBifunctorMapObj` is `mapObj`
  refine (CofanMapObjFun.ιMapObj_iso_inv (isColimitAntidiagonalCofan X Y F n) (i, j) h).trans ?_
  -- the inclusions of `antidiagonalCofan` are by definition those of the biproduct, through
  -- `fiberEquivAntidiagonal`, which does not change the underlying pair
  rfl

/-- The inverse of `mapBifunctorMapObjIsoBiproduct` sends each summand of the biproduct to the
corresponding summand of `mapBifunctorMapObj`. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_inv (x : Finset.antidiagonal n) :
    biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)) x ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).inv =
      ιMapBifunctorMapObj F _ X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property) := by
  rw [mapBifunctorMapObjIsoBiproduct, Iso.symm_inv]
  -- `ιMapBifunctorMapObj` is by definition `ιMapObj`, and `mapBifunctorMapObj` is `mapObj`
  refine Eq.trans ?_
    (CofanMapObjFun.inj_iso_hom (isColimitAntidiagonalCofan X Y F n) (x.val.1, x.val.2)
      (Finset.mem_antidiagonal.1 x.property))
  -- the inclusions of `antidiagonalCofan` are by definition those of the biproduct, through
  -- `fiberEquivAntidiagonal`, which does not change the underlying pair
  rfl

end Antidiagonal

end CategoryTheory.GradedObject
