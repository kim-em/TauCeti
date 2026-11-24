/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Edge
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.AlgebraicTopology.Singular.Kunneth.SpectralSequence
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# The edge map of the singular Künneth spectral sequence

Let `X` and `Y` be topological spaces and `R` a commutative ring. The **edge map**
`TopCat.singularKunnethEdge X Y R r hr q` of the singular Künneth spectral sequence
`TopCat.singularKunnethSpectralSequence X Y R` goes from the column `0` of the page `r ≥ 2`, in
degree `q`, to `H_q(X × Y; R)`: it is the edge map `HomologicalComplex₂.columnFiltrationEdge` of
the column filtration of the singular Künneth bicomplex onto the homology of its total complex,
followed by the identification `TopCat.singularKunnethTotalHomologyIso` of the latter with
`H_q(X × Y; R)`. Equivalently, it is the edge map `HomologicalComplex.kunnethEdge` of the algebraic
Künneth spectral sequence of the singular chain complexes onto `H_q(C(X; R) ⊗ C(Y; R))`, followed
by the map induced by the simplicial cross product (`TopCat.singularKunnethEdge_eq`).

On the second page, whose column `0` in degree `q` is
`⨁_{i + j = q} Tor₀(Hᵢ(X; R), Hⱼ(Y; R)) ≅ ⨁_{i + j = q} Hᵢ(X; R) ⊗ Hⱼ(Y; R)`, the edge map is the
Künneth map `TopCat.singularHomologyKunneth X Y R R q`, followed by the coefficient change along the
unitor `R ⊗ R ≅ R` (`TopCat.singularKunnethSpectralSequenceSecondPageXIso_inv_singularKunnethEdge`).

**Collapse.**

* If `Torₚ(Hᵢ(X; R), Hⱼ(Y; R))` vanishes for all `p ≥ 1`, the edge map from the second page is an
  isomorphism (`TopCat.isIso_singularKunnethEdge_of_isZero_Tor`). This is the case over a
  commutative semisimple ring, for instance a field (`TopCat.isIso_singularKunnethEdge`).
* If `Torₚ(Hᵢ(X; R), Hⱼ(Y; R))` vanishes for all `p ≥ 2`, the sequence
  `0 ⟶ ⨁_{i + j = n + 1} Hᵢ(X; R) ⊗ Hⱼ(Y; R) ⟶ H_{n+1}(X × Y; R)`
  `    ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(X; R), Hⱼ(Y; R)) ⟶ 0`
  of the Künneth map and of the projection `TopCat.singularKunnethToTorOne` onto the column `1` of
  the second page is short exact
  (`TopCat.singularHomologyKunneth_singularKunnethToTorOne_shortExact`). This is the case over a
  hereditary ring, every module of which has projective dimension at most one
  (`TopCat.singularHomologyKunneth_singularKunnethToTorOne_shortExact_of_hereditary`). The
  comparison of `TopCat.singularKunnethToTorOne` with the map `TopCat.singularHomologyToTor` of
  `TauCeti.AlgebraicTopology.Singular.Kunneth.Sequence` is not treated here.

## Main definitions and results

* `TopCat.singularKunnethEdge`: the edge map of the singular Künneth spectral sequence.
* `TopCat.singularKunnethSpectralSequenceSecondPageXIso_inv_singularKunnethEdge`: on the second
  page, the edge map is the Künneth map.
* `TopCat.isIso_singularKunnethEdge_of_isZero_Tor`, `TopCat.isIso_singularKunnethEdge`: collapse
  when the higher `Tor` vanish, for instance over a field.
* `TopCat.singularKunnethToTorOne`,
  `TopCat.singularHomologyKunneth_singularKunnethToTorOne_shortExact`,
  `TopCat.singularHomologyKunneth_singularKunnethToTorOne_shortExact_of_hereditary`: the Künneth
  short exact sequence when the `Torₚ`, `p ≥ 2`, vanish, for instance over a hereditary ring.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe u

namespace TopCat

variable (X Y : TopCat.{u}) (R : Type u) [CommRing R]

/-- **The edge map of the singular Künneth spectral sequence.** From the column `0` of the page
`r ≥ 2`, in degree `q`, it is the edge map of the column filtration of the singular Künneth
bicomplex onto the homology of its total complex, followed by the identification
`TopCat.singularKunnethTotalHomologyIso` of the latter with `H_q(X × Y; R)`. -/
def singularKunnethEdge (r : ℤ) (hr : 2 ≤ r) (q : ℕ) :
    ((singularKunnethSpectralSequence X Y R).page r).X
        (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) ⟶
      ((singularHomologyFunctor _ q).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  (singularKunnethBicomplex X Y R).columnFiltrationEdge r hr _ q (Prod.ext (by simp) (by simp)) ≫
    (singularKunnethTotalHomologyIso X Y R q).hom

/-- The edge map of the singular Künneth spectral sequence is the edge map
`HomologicalComplex.kunnethEdge` of the algebraic Künneth spectral sequence of the singular chain
complexes onto `H_q(C(X; R) ⊗ C(Y; R))`, followed by the map induced by the simplicial cross
product `TauCeti.singularCrossProduct`. -/
lemma singularKunnethEdge_eq (r : ℤ) (hr : 2 ≤ r) (q : ℕ) :
    singularKunnethEdge X Y R r hr q =
      kunnethEdge ((TauCeti.singularChains R).obj X) ((TauCeti.singularChains R).obj Y) r hr q ≫
        homologyMap (TauCeti.singularCrossProduct R X Y) q := by
  rw [singularKunnethEdge, singularKunnethTotalHomologyIso_hom, kunnethEdge_def, Category.assoc]
  -- `TopCat.singularKunnethBicomplex X Y R` is the Künneth bicomplex of the singular chain
  -- complexes by definition
  rfl

/-- **The edge map of the singular Künneth spectral sequence is the Künneth map.** Under the
identification of the column `0` of the second page in degree `q` with
`⨁_{i + j = q} Tor₀(Hᵢ(X; R), Hⱼ(Y; R)) ≅ ⨁_{i + j = q} Hᵢ(X; R) ⊗ Hⱼ(Y; R)`, the edge map onto
`H_q(X × Y; R)` is the Künneth map `TopCat.singularHomologyKunneth`, with coefficients `R` in both
factors, followed by the map induced by the unitor `R ⊗ R ≅ R`. -/
theorem singularKunnethSpectralSequenceSecondPageXIso_inv_singularKunnethEdge (q : ℕ) :
    (singularKunnethSpectralSequenceSecondPageXIso X Y R 0 q).inv ≫
        singularKunnethEdge X Y R 3 (by norm_num) q =
      (GradedObject.mapBifunctorMapObjTorZeroIso
          (fun i ↦ ((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)
          (fun j ↦ ((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y) q).hom ≫
        singularHomologyKunneth X Y (𝟙_ (ModuleCat.{u} R)) (𝟙_ (ModuleCat.{u} R)) q ≫
        ((singularHomologyFunctor _ q).map (λ_ (𝟙_ (ModuleCat.{u} R))).hom).app (X ⊗ Y) := by
  rw [singularKunnethEdge_eq, singularHomologyKunneth_def]
  -- the singular chain complex with coefficients in `R` is `TauCeti.singularChains R` and its
  -- homology is singular homology, by definition, so the second page isomorphisms agree
  refine (kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge_assoc _ _ q _).trans ?_
  rw [TauCeti.singularCrossProduct_def]
  -- the map induced on singular homology by a map of coefficients is that induced on the singular
  -- chains, by definition
  exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (homologyMap_comp _ _ q)).trans
    (Category.assoc _ _ _).symm)

/-- **Collapse of the singular Künneth spectral sequence.** If
`Torₚ(Hᵢ(X; R), Hⱼ(Y; R))` vanishes for all `p ≥ 1`, the edge map from the second page onto
`H_q(X × Y; R)` is an isomorphism. -/
theorem isIso_singularKunnethEdge_of_isZero_Tor (q : ℕ)
    (h : ∀ p i j : ℕ, 1 ≤ p → IsZero (((Tor (ModuleCat.{u} R) p).obj
      (((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)).obj
        (((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y))) :
    IsIso (singularKunnethEdge X Y R 3 (by norm_num) q) := by
  have := (singularKunnethBicomplex X Y R).isIso_columnFiltrationEdge_of_isZero
    (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) q (Prod.ext (by simp) (by simp))
    -- singular homology is by definition the homology of the singular chain complex
    (fun pq hpq ↦ isZero_kunnethSpectralSequence_page_three_X _ _ 1 pq (by exact_mod_cast hpq) h)
  rw [singularKunnethEdge]
  infer_instance

/-- **The Künneth theorem from the singular Künneth spectral sequence.** Over a commutative
semisimple ring `R`, for instance a field, every module is projective, so the higher `Tor` of the
homology vanish and the edge map from the second page onto `H_q(X × Y; R)` is an isomorphism. -/
instance isIso_singularKunnethEdge [IsSemisimpleRing R] (q : ℕ) :
    IsIso (singularKunnethEdge X Y R 3 (by norm_num) q) :=
  isIso_singularKunnethEdge_of_isZero_Tor X Y R q fun p i j hp ↦ by
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have := Module.projective_of_isSemisimpleRing R
      (((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y)
    exact isZero_Tor_succ_of_projective _ _ _ p

/-! ### The two-column case -/

section ShortExact

variable (h : ∀ p i j : ℕ, 2 ≤ p → IsZero (((Tor (ModuleCat.{u} R) p).obj
  (((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)).obj
    (((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y)))

/-- **The map onto `Tor₁` from the singular Künneth spectral sequence.** If
`Torₚ(Hᵢ(X; R), Hⱼ(Y; R))` vanishes for all `p ≥ 2`, for instance over a hereditary ring, the map
`H_{n+1}(X × Y; R) ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(X; R), Hⱼ(Y; R))`: through
`TopCat.singularKunnethTotalHomologyIso`, it is the map
`HomologicalComplex₂.columnFiltrationToColumnOne` of the singular Künneth bicomplex onto the column
`1` of the second page, identified with `Tor₁` by
`TopCat.singularKunnethSpectralSequenceSecondPageXIso`. -/
def singularKunnethToTorOne (n : ℕ) :
    ((singularHomologyFunctor _ (n + 1)).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) ⟶
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) 1) (fun x ↦ x.1 + x.2)
        (fun i ↦ ((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)
        (fun j ↦ ((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y) n :=
  (singularKunnethTotalHomologyIso X Y R (n + 1)).inv ≫
    (singularKunnethBicomplex X Y R).columnFiltrationToColumnOne
      (-((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (n + 1)
      (Prod.ext (by simp) (by simp))
      -- singular homology is by definition the homology of the singular chain complex
      (fun pq hpq ↦
        isZero_kunnethSpectralSequence_page_three_X _ _ 2 pq (by exact_mod_cast hpq) h) ≫
    (((singularKunnethSpectralSequence X Y R).page 3).XIsoOfEq
      (Prod.ext (by simp; omega) (by simp))).hom ≫
    (singularKunnethSpectralSequenceSecondPageXIso X Y R 1 n).hom

/-- The Künneth map, followed by the coefficient change along the unitor `R ⊗ R ≅ R` and by
`TopCat.singularKunnethToTorOne`, vanishes. -/
@[reassoc (attr := simp)]
lemma singularHomologyKunneth_singularKunnethToTorOne (n : ℕ) :
    (singularHomologyKunneth X Y (𝟙_ (ModuleCat.{u} R)) (𝟙_ (ModuleCat.{u} R)) (n + 1) ≫
      ((singularHomologyFunctor _ (n + 1)).map (λ_ (𝟙_ (ModuleCat.{u} R))).hom).app (X ⊗ Y)) ≫
      singularKunnethToTorOne X Y R h n = 0 := by
  rw [(Iso.eq_inv_comp _).2
    (singularKunnethSpectralSequenceSecondPageXIso_inv_singularKunnethEdge X Y R (n + 1)).symm]
  simp [singularKunnethToTorOne, singularKunnethEdge]

/-- **The Künneth short exact sequence from the singular Künneth spectral sequence.** If
`Torₚ(Hᵢ(X; R), Hⱼ(Y; R))` vanishes for all `p ≥ 2`, for instance over a hereditary ring, the
sequence

`0 ⟶ ⨁_{i + j = n + 1} Hᵢ(X; R) ⊗ Hⱼ(Y; R) ⟶ H_{n+1}(X × Y; R)`
`    ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(X; R), Hⱼ(Y; R)) ⟶ 0`

of the Künneth map (followed by the unitor `R ⊗ R ≅ R`) and of `TopCat.singularKunnethToTorOne` is
short exact. -/
theorem singularHomologyKunneth_singularKunnethToTorOne_shortExact (n : ℕ) :
    (ShortComplex.mk _ _
      (singularHomologyKunneth_singularKunnethToTorOne X Y R h n)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    ((singularKunnethBicomplex X Y R).columnFiltrationEdge_shortExact
      (-((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (n + 1)
      (Prod.ext (by simp) (by simp))
      (fun pq hpq ↦
        isZero_kunnethSpectralSequence_page_three_X _ _ 2 pq (by exact_mod_cast hpq) h))
  refine ShortComplex.isoMk (singularKunnethSpectralSequenceSecondPageXIso X Y R 0 (n + 1) ≪≫
      GradedObject.mapBifunctorMapObjTorZeroIso _ _ _)
    (singularKunnethTotalHomologyIso X Y R (n + 1))
    ((((singularKunnethSpectralSequence X Y R).page 3).XIsoOfEq
      (Prod.ext (by simp; omega) (by simp))) ≪≫
      singularKunnethSpectralSequenceSecondPageXIso X Y R 1 n) ?_ ?_
  · have e := singularKunnethSpectralSequenceSecondPageXIso_inv_singularKunnethEdge X Y R (n + 1)
    rw [Iso.inv_comp_eq] at e
    simp only [Iso.trans_hom, Category.assoc, ← e, singularKunnethEdge]
  · simp [singularKunnethToTorOne]

end ShortExact

/-- **The Künneth short exact sequence over a hereditary ring**, from the singular Künneth spectral
sequence: when every `R`-module has projective dimension at most one, the higher `Torₚ`, `p ≥ 2`,
vanish, and the sequence
`0 ⟶ ⨁_{i + j = n + 1} Hᵢ(X; R) ⊗ Hⱼ(Y; R) ⟶ H_{n+1}(X × Y; R)`
`    ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(X; R), Hⱼ(Y; R)) ⟶ 0`
of `TopCat.singularHomologyKunneth_singularKunnethToTorOne_shortExact` is short exact. -/
theorem singularHomologyKunneth_singularKunnethToTorOne_shortExact_of_hereditary
    [∀ V : ModuleCat.{u} R, HasProjectiveDimensionLE V 1] (n : ℕ) :
    (ShortComplex.mk _ _ (singularHomologyKunneth_singularKunnethToTorOne X Y R
      (fun p _ _ hp ↦ by
        obtain ⟨p, rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
        exact isZero_Tor_add_two_of_hasProjectiveDimensionLE_one _ _ p) n)).ShortExact :=
  singularHomologyKunneth_singularKunnethToTorOne_shortExact X Y R _ n

end TopCat
