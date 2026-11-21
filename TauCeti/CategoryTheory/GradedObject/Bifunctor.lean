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
# Coproducts of graded objects as biproducts

Given a graded object `X : GradedObject I C` and a map `p : I → J`, the object `X.mapObj p j` is
the coproduct of the `X i` with `p i = j`. When these objects have a biproduct, for instance when
the fibre is finite and `C` has finite biproducts, it is this biproduct
(`CategoryTheory.GradedObject.mapObjIsoBiproduct`).

For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the fibre of
the addition map over `n` is `Finset.antidiagonal n` (`Finset.mem_antidiagonal`), so the coproduct
over `i + j = n` defining `CategoryTheory.GradedObject.mapBifunctorMapObj` is the biproduct indexed
by `Finset.antidiagonal n`
(`CategoryTheory.GradedObject.mapBifunctorMapObjIsoBiproduct`). The tensor product of graded
objects is a special case (`CategoryTheory.GradedObject.Monoidal.tensorObjIsoBiproduct`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

section MapObj

variable {I J C : Type*} [Category* C] [HasZeroMorphisms C] (X : GradedObject I C) (p : I → J)
  [X.HasMap p] (j : J) [HasBiproduct (X.mapObjFun p j)]

/-- The coproduct `X.mapObj p j` of the `X i` with `p i = j` is the biproduct of these objects. -/
def mapObjIsoBiproduct : X.mapObj p j ≅ ⨁ X.mapObjFun p j where
  hom := X.descMapObj p fun i h ↦ biproduct.ι (X.mapObjFun p j) ⟨i, Set.mem_singleton_iff.2 h⟩
  inv := biproduct.desc fun i ↦ X.ιMapObj p i j (Set.mem_singleton_iff.1 i.property)
  hom_inv_id := X.mapObj_ext p _ _ fun i h ↦ by simp
  inv_hom_id := biproduct.hom_ext' _ _ fun i ↦ by
    rw [biproduct.ι_desc_assoc, X.ι_descMapObj, Category.comp_id]

/-- `mapObjIsoBiproduct` sends the summand `X i` to the corresponding summand of the biproduct. -/
@[reassoc (attr := simp)]
lemma ιMapObj_mapObjIsoBiproduct_hom (i : I) (h : p i = j) :
    X.ιMapObj p i j h ≫ (X.mapObjIsoBiproduct p j).hom =
      biproduct.ι (X.mapObjFun p j) ⟨i, Set.mem_singleton_iff.2 h⟩ := by
  simp [mapObjIsoBiproduct]

/-- The inverse of `mapObjIsoBiproduct` sends each summand of the biproduct to the corresponding
summand of `X.mapObj p j`. -/
@[reassoc (attr := simp)]
lemma ι_mapObjIsoBiproduct_inv (i : p ⁻¹' {j}) :
    biproduct.ι (X.mapObjFun p j) i ≫ (X.mapObjIsoBiproduct p j).inv =
      X.ιMapObj p i j (Set.mem_singleton_iff.1 i.property) := by
  simp [mapObjIsoBiproduct]

end MapObj

section Antidiagonal

variable {I : Type*} [Add I] [Finset.HasAntidiagonal I]
  {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [HasZeroMorphisms C₃]
  (X : GradedObject I C₁) (Y : GradedObject I C₂) (F : C₁ ⥤ C₂ ⥤ C₃)
  [HasMap (((mapBifunctor F I I).obj X).obj Y) (fun x ↦ x.1 + x.2)] (n : I)
  [HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)]

/-- For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the
coproduct of the `(F.obj (X i)).obj (Y j)` with `i + j = n` is the biproduct of these objects
indexed by `Finset.antidiagonal n`, the fibre of the addition map over `n`
(`Finset.mem_antidiagonal`). -/
def mapBifunctorMapObjIsoBiproduct :
    mapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y n ≅
      ⨁ fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2) where
  hom := mapBifunctorMapObjDesc fun i j h ↦
    biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
      ⟨(i, j), Finset.mem_antidiagonal.2 h⟩
  inv := biproduct.desc fun x ↦
    ιMapBifunctorMapObj F _ X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property)
  hom_inv_id := mapBifunctorMapObj_ext F _ fun i j h ↦ by simp
  inv_hom_id := biproduct.hom_ext' _ _ fun x ↦ by simp

/-- `mapBifunctorMapObjIsoBiproduct` sends the summand `(F.obj (X i)).obj (Y j)` to the
corresponding summand of the biproduct. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_hom (i j : I) (h : i + j = n) :
    ιMapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).hom =
      biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ := by
  simp [mapBifunctorMapObjIsoBiproduct]

/-- The inverse of `mapBifunctorMapObjIsoBiproduct` sends each summand of the biproduct to the
corresponding summand of `mapBifunctorMapObj`. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_inv (x : Finset.antidiagonal n) :
    biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)) x ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).inv =
      ιMapBifunctorMapObj F _ X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property) := by
  simp [mapBifunctorMapObjIsoBiproduct]

end Antidiagonal

end CategoryTheory.GradedObject
