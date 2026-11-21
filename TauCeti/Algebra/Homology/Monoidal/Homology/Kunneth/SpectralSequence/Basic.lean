/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.CartanEilenberg
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.FirstDifferential

/-!
# The Künneth spectral sequence and its first page

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`, and let
`Q` be the Cartan–Eilenberg resolution of `L` (`ChainComplex.cartanEilenbergResolution`). The
**Künneth spectral sequence** `HomologicalComplex.kunnethSpectralSequence K L` is the spectral
sequence of the column filtration of the Künneth bicomplex
`HomologicalComplex.kunnethBicomplex K L`, whose column `p` is `K ⊗ Q.X p`. When every term of `K`
is flat, its total complex computes `K ⊗ L`
(`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). This file computes its first page and
first differential, without any flatness assumption.

Pages are numbered as in `HomologicalComplex₂.columnFiltrationSpectralSequence`: the first page
(`E¹`) is `page 2` and the second page (`E²`) is `page 3`, and the object at column `p` and degree
`q` sits at `(-q - 2p, p)`.

* **First page.** The rows `Q.X p` have projective terms and projective homology, so the Künneth
  map `⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X p) ⟶ H_q(K ⊗ Q.X p)` is an isomorphism
  (`HomologicalComplex.isIso_homologyKunneth_of_projective_right`). This identifies the first page
  at column `p`, degree `q` with `⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X p)`
  (`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`).
* **First differential.** By naturality of the Künneth map, the first differential is `(-1)^q`
  times the map induced by the maps `Hⱼ(Q.d (p + 1) p)`
  (`HomologicalComplex.kunnethSpectralSequence_page_two_d`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.6.4 (the Künneth spectral sequence) and Section 5.7 (Cartan–Eilenberg resolutions).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.20 (the algebraic Künneth spectral sequence).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ChainComplex cartanEilenbergResolution

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- **The Künneth spectral sequence**: the spectral sequence of the column filtration of the Künneth
bicomplex `HomologicalComplex.kunnethBicomplex K L`, whose column `p` is `K ⊗ Q.X p` for the
Cartan–Eilenberg resolution `Q` of `L`. Its first page is the graded tensor product of the homology
of `K` with the homology of the rows of `Q`
(`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`). It is by definition the spectral
sequence of the row filtration of the flipped Künneth bicomplex, so the convergence results for row
filtrations apply to it: every object stabilizes after finitely many pages to a graded piece of the
abutment (`HomologicalComplex₂.rowFiltrationSpectralSequencePageXIsoEInfty`), the filtration of the
abutment is finite (`HomologicalComplex₂.isZero_rowFiltration_abutmentFiltration`,
`HomologicalComplex₂.isIso_rowFiltration_abutmentFiltrationι`), and the abutment is the homology of
the total complex of the Künneth bicomplex (`HomologicalComplex₂.columnFiltrationAbutmentIso`). When
every term of `K` is flat, the augmentation of that total complex, a quasi-isomorphism, identifies
this abutment with the homology of `K ⊗ L`
(`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). -/
abbrev kunnethSpectralSequence :=
  (kunnethBicomplex K L).columnFiltrationSpectralSequence

/-- **The first page of the Künneth spectral sequence.** Its object at column `p`, degree `k`
is `⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, through the Künneth map of `K` and `Q.X p`, which is an
isomorphism because `Q.X p` has projective terms and projective homology. -/
def kunnethSpectralSequenceFirstPageXIso (p k : ℕ) :
    ((kunnethSpectralSequence K L).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      GradedObject.Monoidal.tensorObj (fun i ↦ K.homology i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) k :=
  (kunnethBicomplex K L).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
    (asIso (kunnethColumnHomologyKunneth K L p k)).symm

/-- The identification of the first page of the Künneth spectral sequence is that of the first
page of the column filtration with the homology of the columns
(`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso`), followed by the inverse of
the Künneth map. -/
lemma kunnethSpectralSequenceFirstPageXIso_eq (p k : ℕ) :
    kunnethSpectralSequenceFirstPageXIso K L p k =
      (kunnethBicomplex K L).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
        (asIso (kunnethColumnHomologyKunneth K L p k)).symm :=
  (rfl)

/-- **The first differential of the Künneth spectral sequence.** Under the identifications
`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`, the differential of the first page from
column `p + 1` to column `p` in degree `k` is `(-1)^k` times the map
`⨁ Hᵢ(K) ⊗ Hⱼ(Q.X (p + 1)) ⟶ ⨁ Hᵢ(K) ⊗ Hⱼ(Q.X p)` induced by the maps `Hⱼ(Q.d (p + 1) p)`. -/
theorem kunnethSpectralSequence_page_two_d (p k : ℕ) :
    (kunnethSpectralSequenceFirstPageXIso K L (p + 1) k).inv ≫
      ((kunnethSpectralSequence K L).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (kunnethSpectralSequenceFirstPageXIso K L p k).hom =
    ((-1 : ℤ) ^ k) • GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
      (fun j ↦ homologyMap ((cartanEilenbergResolution L).d (p + 1) p) j) k := by
  simp only [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  rw [reassoc_of% ((kunnethBicomplex K L).columnFiltrationSpectralSequence_page_two_d p k),
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, kunnethColumnHomologyKunneth_naturality_assoc,
    IsIso.hom_inv_id, Category.comp_id]

end HomologicalComplex
