/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Edge
public import TauCeti.CategoryTheory.Monoidal.TorLowDegree

/-!
# The edge map of the Künneth spectral sequence

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`. The
Künneth spectral sequence `HomologicalComplex.kunnethSpectralSequence K L` is the spectral sequence
of the column filtration of the Künneth bicomplex, whose total complex maps to `K ⊗ L` by the
augmentation `HomologicalComplex.kunnethBicomplexAugmentation`, a quasi-isomorphism when the terms
of `K` are flat. Its **edge map** `HomologicalComplex.kunnethEdge K L r hr q` goes from the column
`0` of the page `r ≥ 2`, in degree `q`, to `H_q(K ⊗ L)`: it is the edge map
`HomologicalComplex₂.columnFiltrationEdge` of the column filtration, followed by the augmentation.

On the second page (numbered `3`), whose column `0` in degree `q` is
`⨁_{i + j = q} Tor₀(Hᵢ(K), Hⱼ(L)) ≅ ⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(L)`
(`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`,
`CategoryTheory.GradedObject.mapBifunctorMapObjTorZeroIso`), the edge map is the Künneth map
`HomologicalComplex.homologyKunneth K L q`
(`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge`). No flatness
assumption is needed for this identification.

The proof computes both sides on the classes of the cycles of the first page. On the first page,
the edge map is the map induced by the augmentation `K ⊗ Q.X 0 ⟶ K ⊗ L` of the column `0`
(`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_inv_columnFiltrationEdge`),
which by naturality of the Künneth map is the Künneth map of `K` and `L` after the maps
`Hⱼ(Q.X 0) ⟶ Hⱼ(L)`. On the other side, the identification of the second page with `Tor₀` is, in
degree `0` of the complexes `HomologicalComplex.kunnethTorSumComplex K L q`, induced by these same
maps (`HomologicalComplex.homologyπ_kunnethTorSumComplexHomologyIso_hom_torZero`).

**Collapse.** Suppose that the terms of `K` are flat, so that the augmentation is a
quasi-isomorphism.

* If `Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 1`, for instance over a field, the second page
  vanishes in the columns `≥ 1` (`HomologicalComplex.isZero_kunnethSpectralSequence_page_three_X`),
  the edge map is an isomorphism (`HomologicalComplex.isIso_kunnethEdge_of_isZero_Tor`), and so is
  the Künneth map (`HomologicalComplex.isIso_homologyKunneth_of_isZero_Tor`).
* If `Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 2`, for instance over a hereditary ring, the
  spectral sequence lives in the columns `0` and `1` from the second page on, and gives the short
  exact sequence
  `0 ⟶ ⨁_{i + j = n + 1} Hᵢ(K) ⊗ Hⱼ(L) ⟶ H_{n+1}(K ⊗ L)`
  `    ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(K), Hⱼ(L)) ⟶ 0`
  whose first map is the Künneth map and whose second map `HomologicalComplex.kunnethToTorOne` is
  the projection onto the column `1`
  (`HomologicalComplex.homologyKunneth_kunnethToTorOne_shortExact`).

## Main definitions and results

* `HomologicalComplex.kunnethEdge`: the edge map of the Künneth spectral sequence.
* `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge`: on the second page,
  the edge map is the Künneth map.
* `HomologicalComplex.homologyπ_kunnethTorSumComplexHomologyIso_hom_torZero`: the identification
  of `H₀` of `HomologicalComplex.kunnethTorSumComplex K L q` with `⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(L)`.
* `HomologicalComplex.isIso_kunnethEdge_of_isZero_Tor`,
  `HomologicalComplex.isIso_homologyKunneth_of_isZero_Tor`: collapse when the higher `Tor` vanish.
* `HomologicalComplex.kunnethToTorOne`,
  `HomologicalComplex.homologyKunneth_kunnethToTorOne_shortExact`: the Künneth short exact sequence
  when `Torₚ` vanishes for `p ≥ 2`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ChainComplex cartanEilenbergResolution

universe u

namespace HomologicalComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- **`H₀` of the complexes computing `Tor`.** In degree `0`, every element of
`HomologicalComplex.kunnethTorSumComplex K L q` is a cycle, and its class, identified with an
element of `⨁_{i + j = q} Tor₀(Hᵢ(K), Hⱼ(L)) ≅ ⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(L)`, is its image in
`⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X 0)` followed by the maps `Hᵢ(K) ⊗ Hⱼ(Q.X 0) ⟶ Hᵢ(K) ⊗ Hⱼ(L)`
induced by the augmentation of the Cartan–Eilenberg resolution `Q` of `L`. -/
@[reassoc]
lemma homologyπ_kunnethTorSumComplexHomologyIso_hom_torZero (q : ℕ) :
    (kunnethTorSumComplex K L q).homologyπ 0 ≫ (kunnethTorSumComplexHomologyIso K L q 0).hom ≫
        (GradedObject.mapBifunctorMapObjTorZeroIso (fun i ↦ K.homology i)
          (fun j ↦ L.homology j) q).hom =
      (kunnethTorSumComplex K L q).iCycles 0 ≫ (tensorObjIsoKunnethTorSumComplexX K L q 0).inv ≫
        GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
          (fun j ↦ homologyMap (cartanEilenbergResolutionπ L) j) q := by
  -- in degree `0` every element is a cycle
  rw [← cancel_epi ((kunnethTorSumComplex K L q).iCyclesIso 0 0 (by simp) (by simp)).inv,
    iCyclesIso_inv_hom_id_assoc, ← cancel_epi (tensorObjIsoKunnethTorSumComplexX K L q 0).hom,
    Iso.hom_inv_id_assoc]
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
  -- the inclusion of a summand commutes with the identifications of the cycles in degree `0`
  have hι : (biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩).f 0 ≫
        ((kunnethTorSumComplex K L q).iCyclesIso 0 0 (by simp) (by simp)).inv =
      ((kunnethTorComplex K L i j).iCyclesIso 0 0 (by simp) (by simp)).inv ≫
        cyclesMap (biproduct.ι (fun x : Finset.antidiagonal q ↦
          kunnethTorComplex K L x.val.1 x.val.2) ⟨(i, j), Finset.mem_antidiagonal.2 h⟩) 0 := by
    rw [← cancel_mono ((kunnethTorSumComplex K L q).iCycles 0)]
    simp
  simp only [ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom_assoc, reassoc_of% hι,
    GradedObject.Monoidal.ι_tensorHom]
  -- `Tor₀` computed on the projective resolution `homologyResolution L j` of `Hⱼ(L)`, whose
  -- augmentation is the map induced on `Hⱼ` by that of the Cartan–Eilenberg resolution
  have hT : (kunnethTorComplex K L i j).homologyπ 0 ≫
        (kunnethTorComplexHomologyIso K L i j 0).hom ≫
        (torZeroIso (K.homology i) (L.homology j)).hom =
      (kunnethTorComplex K L i j).iCycles 0 ≫
        K.homology i ◁ homologyMap (cartanEilenbergResolutionπ L) j := by
    rw [kunnethTorComplexHomologyIso_hom, ← homologyResolution_π_f_zero]
    -- `kunnethTorComplex K L i j` is `Hᵢ(K) ⊗ homologyResolution L j` and `Tor` is the left
    -- derived functor of the tensor product, by definition
    exact homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom _ _
  rw [← homologyπ_naturality_assoc,
    homologyMap_ι_kunnethTorSumComplexHomologyIso_hom_assoc K L q 0 i j h,
    GradedObject.ι_mapBifunctorMapObjTorZeroIso_hom _ _ _ i j h, reassoc_of% hT,
    iCyclesIso_inv_hom_id_assoc,
    kunnethTorComplexXIso_eq, Iso.refl_inv]
  -- the identity of the graded object `i ↦ Hᵢ(K)` is the identity of `Hᵢ(K)` in degree `i`, and the
  -- identity of `(kunnethTorComplex K L i j).X 0` is that of `Hᵢ(K) ⊗ Hⱼ(Q.X 0)`, by definition
  exact (Category.id_comp _).trans (congrArg (· ≫ _) (id_tensorHom _ _).symm)

/-- **The edge map of the Künneth spectral sequence.** From the column `0` of the page `r ≥ 2`, in
degree `q`, it is the edge map `HomologicalComplex₂.columnFiltrationEdge` of the column filtration
of the Künneth bicomplex onto the homology of its total complex, followed by the map induced by the
augmentation `HomologicalComplex.kunnethBicomplexAugmentation` to `K ⊗ L`. -/
def kunnethEdge (r : ℤ) (hr : 2 ≤ r) (q : ℕ) :
    ((kunnethSpectralSequence K L).page r).X (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) ⟶
      (K ⊗ L).homology q :=
  (kunnethBicomplex K L).columnFiltrationEdge r hr _ q (Prod.ext (by simp) (by simp)) ≫
    homologyMap (kunnethBicomplexAugmentation K L) q

/-- The edge map `HomologicalComplex.kunnethEdge` is the edge map of the column filtration of the
Künneth bicomplex, followed by the map induced by the augmentation. -/
lemma kunnethEdge_def (r : ℤ) (hr : 2 ≤ r) (q : ℕ) :
    kunnethEdge K L r hr q =
      (kunnethBicomplex K L).columnFiltrationEdge r hr _ q (Prod.ext (by simp) (by simp)) ≫
        homologyMap (kunnethBicomplexAugmentation K L) q :=
  (rfl)

/-- The Künneth map of `K` and the row `0` of the Cartan–Eilenberg resolution `Q` of `L`, followed
by the map induced by the augmentation `K ⊗ Q.X 0 ⟶ K ⊗ L`, is the Künneth map of `K` and `L`
after the maps `Hⱼ(Q.X 0) ⟶ Hⱼ(L)`. -/
private lemma kunnethColumnHomologyKunneth_zero_homologyMap_kunnethBicomplexε (q : ℕ) :
    kunnethColumnHomologyKunneth K L 0 q ≫ homologyMap (kunnethBicomplexε K L) q =
      GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
        (fun j ↦ homologyMap (cartanEilenbergResolutionπ L) j) q ≫ homologyKunneth K L q := by
  have h := homologyKunneth_naturality (𝟙 K) (cartanEilenbergResolutionπ L) q
  -- `tensorHom` is the tensor product of morphisms of the monoidal structure on complexes by
  -- definition
  have e : tensorHom (𝟙 K) (cartanEilenbergResolutionπ L) = K ◁ cartanEilenbergResolutionπ L :=
    MonoidalCategory.id_tensorHom K (cartanEilenbergResolutionπ L)
  simp only [homologyMap_id, e] at h
  rw [kunnethColumnHomologyKunneth_eq, kunnethBicomplexε_def]
  -- `𝟙` of a graded object is the family of identities and the column `0` of the Künneth
  -- bicomplex is `K ⊗ Q.X 0`, by definition
  exact h.symm

/-- **The edge map of the Künneth spectral sequence is the Künneth map.** Under the identification
of the column `0` of the second page in degree `q` with
`⨁_{i + j = q} Tor₀(Hᵢ(K), Hⱼ(L)) ≅ ⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(L)`, the edge map onto `H_q(K ⊗ L)` is
the Künneth map `HomologicalComplex.homologyKunneth K L q`. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge (q : ℕ) :
    (kunnethSpectralSequenceSecondPageXIso K L 0 q).inv ≫ kunnethEdge K L 3 (by norm_num) q =
      (GradedObject.mapBifunctorMapObjTorZeroIso (fun i ↦ K.homology i)
        (fun j ↦ L.homology j) q).hom ≫ homologyKunneth K L q := by
  rw [← cancel_epi (((kunnethSpectralSequence K L).page 2).homologyπ
      (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) ≫
    ((kunnethSpectralSequence K L).iso 2 3 (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ))).hom ≫
    (kunnethSpectralSequenceSecondPageXIso K L 0 q).hom)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (homologyπ_kunnethSpectralSequenceSecondPageXIso_hom K L 0 q),
    homologyπ_kunnethTorSumComplexHomologyIso_hom_torZero_assoc, liftCycles_i_assoc,
    kunnethFirstPageXIsoTorSum_eq, Iso.trans_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [kunnethEdge_def,
    (kunnethBicomplex K L).homologyπ_iso_hom_columnFiltrationEdge_assoc 2 3 rfl le_rfl]
  congr 1
  rw [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, ← kunnethColumnHomologyKunneth_zero_homologyMap_kunnethBicomplexε,
    IsIso.inv_hom_id_assoc, ← Iso.inv_comp_eq, kunnethBicomplexAugmentation_def]
  -- the Künneth spectral sequence is by definition that of the column filtration
  exact HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_inv_columnFiltrationEdge
    _ _ _ q

/-- If `Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ s`, the second page (numbered `3`) of the
Künneth spectral sequence vanishes in the columns `≥ s`. -/
lemma isZero_kunnethSpectralSequence_page_three_X (s : ℕ) (pq : ℤ × ℤ) (hpq : s ≤ pq.2)
    (h : ∀ p i j : ℕ, s ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    IsZero (((kunnethSpectralSequence K L).page 3).X pq) := by
  obtain ⟨p, q, rfl⟩ | hq :
      (∃ p q : ℕ, pq = (-(q : ℤ) - 2 * p, (p : ℤ))) ∨ 0 < pq.1 + 2 * pq.2 := by
    by_cases hq : 0 < pq.1 + 2 * pq.2
    · exact Or.inr hq
    · exact Or.inl ⟨pq.2.toNat, (-(pq.1 + 2 * pq.2)).toNat, Prod.ext (by simp; omega)
        (by simp; omega)⟩
  · refine IsZero.of_iso ?_ (kunnethSpectralSequenceSecondPageXIso K L p q)
    refine (IsZero.iff_id_eq_zero _).2 (GradedObject.mapBifunctorMapObj_ext _ _ fun i j _ ↦ ?_)
    exact (h p i j (by simpa using hpq)).eq_of_src _ _
  · exact (kunnethBicomplex K L).flip.isZero_rowFiltrationSpectralSequence_page_X 3 (by norm_num)
      _ _ (Or.inr (by omega))

/-- **Collapse of the Künneth spectral sequence.** If the terms of `K` are flat and
`Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 1`, for instance over a field, the edge map from the
second page onto `H_q(K ⊗ L)` is an isomorphism. -/
theorem isIso_kunnethEdge_of_isZero_Tor [∀ p, Module.Flat R (K.X p)] (q : ℕ)
    (h : ∀ p i j : ℕ, 1 ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    IsIso (kunnethEdge K L 3 (by norm_num) q) := by
  have := (kunnethBicomplex K L).isIso_columnFiltrationEdge_of_isZero
    (-(q : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) q (Prod.ext (by simp) (by simp))
    (fun pq hpq ↦ isZero_kunnethSpectralSequence_page_three_X K L 1 pq (by exact_mod_cast hpq) h)
  have := quasiIso_kunnethBicomplexAugmentation K L
  rw [kunnethEdge_def]
  infer_instance

/-- **The Künneth theorem from the Künneth spectral sequence.** If the terms of `K` are flat and
`Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 1`, for instance over a field, the Künneth map
`⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(L) ⟶ H_q(K ⊗ L)` is an isomorphism. -/
theorem isIso_homologyKunneth_of_isZero_Tor [∀ p, Module.Flat R (K.X p)] (q : ℕ)
    (h : ∀ p i j : ℕ, 1 ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    IsIso (homologyKunneth K L q) := by
  have := isIso_kunnethEdge_of_isZero_Tor K L q h
  have e := kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge K L q
  rw [← Iso.inv_comp_eq] at e
  rw [← e]
  infer_instance

section ShortExact

variable [∀ p, Module.Flat R (K.X p)]

/-- **The map onto `Tor₁` from the Künneth spectral sequence.** If the terms of `K` are flat and
`Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 2`, for instance over a hereditary ring, the map
`H_{n+1}(K ⊗ L) ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(K), Hⱼ(L))`: through the augmentation, it is the map
`HomologicalComplex₂.columnFiltrationToColumnOne` of the Künneth bicomplex onto the column `1` of
the second page, identified with `Tor₁` by
`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`. -/
def kunnethToTorOne (n : ℕ)
    (h : ∀ p i j : ℕ, 2 ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    (K ⊗ L).homology (n + 1) ⟶ GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) 1)
      (fun x ↦ x.1 + x.2) (fun i ↦ K.homology i) (fun j ↦ L.homology j) n :=
  have := quasiIso_kunnethBicomplexAugmentation K L
  inv (homologyMap (kunnethBicomplexAugmentation K L) (n + 1)) ≫
    (kunnethBicomplex K L).columnFiltrationToColumnOne
      (-((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (n + 1)
      (Prod.ext (by simp) (by simp))
      (fun pq hpq ↦
        isZero_kunnethSpectralSequence_page_three_X K L 2 pq (by exact_mod_cast hpq) h) ≫
    (((kunnethSpectralSequence K L).page 3).XIsoOfEq
      (Prod.ext (by simp; omega) (by simp))).hom ≫
    (kunnethSpectralSequenceSecondPageXIso K L 1 n).hom

/-- The Künneth map followed by `HomologicalComplex.kunnethToTorOne` vanishes. -/
@[reassoc (attr := simp)]
lemma homologyKunneth_kunnethToTorOne (n : ℕ)
    (h : ∀ p i j : ℕ, 2 ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    homologyKunneth K L (n + 1) ≫ kunnethToTorOne K L n h = 0 := by
  have := quasiIso_kunnethBicomplexAugmentation K L
  rw [(Iso.eq_inv_comp _).2
    (kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge K L (n + 1)).symm, kunnethEdge_def]
  simp [kunnethToTorOne]

/-- **The Künneth short exact sequence from the Künneth spectral sequence.** If the terms of `K` are
flat and `Torₚ(Hᵢ(K), Hⱼ(L))` vanishes for all `p ≥ 2`, for instance over a hereditary ring, the
sequence

`0 ⟶ ⨁_{i + j = n + 1} Hᵢ(K) ⊗ Hⱼ(L) ⟶ H_{n+1}(K ⊗ L) ⟶ ⨁_{i + j = n} Tor₁(Hᵢ(K), Hⱼ(L)) ⟶ 0`

of the Künneth map and of `HomologicalComplex.kunnethToTorOne` is short exact. -/
theorem homologyKunneth_kunnethToTorOne_shortExact (n : ℕ)
    (h : ∀ p i j : ℕ, 2 ≤ p →
      IsZero (((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j))) :
    (ShortComplex.mk _ _ (homologyKunneth_kunnethToTorOne K L n h)).ShortExact := by
  have := quasiIso_kunnethBicomplexAugmentation K L
  refine ShortComplex.shortExact_of_iso ?_ ((kunnethBicomplex K L).columnFiltrationEdge_shortExact
    (-((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (n + 1)
    (Prod.ext (by simp) (by simp))
    (fun pq hpq ↦ isZero_kunnethSpectralSequence_page_three_X K L 2 pq (by exact_mod_cast hpq) h))
  refine ShortComplex.isoMk (kunnethSpectralSequenceSecondPageXIso K L 0 (n + 1) ≪≫
      GradedObject.mapBifunctorMapObjTorZeroIso _ _ _)
    (asIso (homologyMap (kunnethBicomplexAugmentation K L) (n + 1)))
    ((((kunnethSpectralSequence K L).page 3).XIsoOfEq (Prod.ext (by simp; omega) (by simp))) ≪≫
      kunnethSpectralSequenceSecondPageXIso K L 1 n) ?_ ?_
  · have e := kunnethSpectralSequenceSecondPageXIso_inv_kunnethEdge K L (n + 1)
    rw [Iso.inv_comp_eq] at e
    simp only [Iso.trans_hom, Category.assoc, asIso_hom, ← e, kunnethEdge_def]
  · simp [kunnethToTorOne]

end ShortExact

end HomologicalComplex
