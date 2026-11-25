E1 fix 1fc6fa8ee7 signature changes to propagate into Bicomplex/Edge, Kunneth/Edge, Singular/Edge (branch roadmap/kunneth-edge-map):
- isZero_Tor_add_two_of_hasProjectiveDimensionLE_one: now [HasProjectiveDimensionLE Y 1] instead of [∀ Z, HasProjectiveDimensionLE Z 1].
- torZeroIso, torZeroIso_hom, homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom: take [PreservesFiniteColimits ((tensoringLeft C).obj X)] (section ∀X instance removed); mapBifunctorMapObjTorZeroIso, ι_mapBifunctorMapObjTorZeroIso_hom take [∀ i, PreservesFiniteColimits ((tensoringLeft C).obj (X i))].
- isIso_spectralSequencePageXToEInfty_of_isZero: h₀ now ∀ r', r ≤ r' → r' ≤ r₁ → ...; conclusion uses (h₀ r le_rfl hrr₁). In Bicomplex/Edge: (fun r' _ ↦ ...) becomes (fun r' _ _ ↦ ...). New general isIso_spectralSequencePageXToEInfty_of_d_eq_zero.
- New abutmentFiltrationMapOfLE, isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty; isIso_abutmentFiltrationι_of_isZero_EInfty unchanged signature.

E1 second review round f91e6b9b41 (on roadmap/spectral-object-edge):
- Module moves: TauCeti.CategoryTheory.Monoidal.Tor -> TauCeti.CategoryTheory.Monoidal.Tor.Basic; TorLowDegree -> TauCeti.CategoryTheory.Monoidal.Tor.LowDegree. Update imports in Kunneth/Edge etc.
- Graded Tor₀ decls (mapBifunctorMapObjTorZeroIso, ι_...) now take {I} [AddMonoid I] [Finset.HasAntidiagonal I] + [HasMap ...] [X.HasTensor Y] instances (auto at I = ℕ).
- abutmentFiltrationMapOfLE and lemmas, isIso_abutmentFiltrationι_of_isZero_EInfty now in SpectralObject/Abutment (same names/signatures).
- homologyπ_isoLeftDerivedObj_inv_fromLeftDerivedZero_app moved to CategoryTheory/Abelian/LeftDerived.
- isZero_Tor_add_two_of_hasProjectiveDimensionLE_one moved to Tor/Basic.
- New EInftyToAbutment_eq, Epi instance and characterising lemma for abutmentToEInfty.
Plan: when E1 merges, rebuild the E2/E3 branches from origin/main + Bicomplex/Edge, Kunneth/Edge, Singular/Edge files of this branch, applying the above.

E2 review round d2eb643331 (on roadmap/bicomplex-edge, PR #45740):
- All bicomplex collapse decls take (r : ℤ) (hr) right after K: 3 ≤ r for isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero, rowFiltrationToRowOne, columnFiltrationToColumnOne, rowFiltrationEdge_rowFiltrationToRowOne, columnFiltrationEdge_columnFiltrationToColumnOne, rowFiltrationEdge_shortExact, columnFiltrationEdge_shortExact; 2 ≤ r for isZero_rowFiltrationSpectralObject_EInfty, isIso_rowFiltration_abutmentFiltrationι_of_isZero, isIso_rowFiltrationEdge_of_isZero, isIso_columnFiltrationEdge_of_isZero. At r = 3 pass `3 (by norm_num)`.
- isIso_*FiltrationEdge_of_isZero conclusion: rowFiltrationEdge r hr (was rowFiltrationEdge 3 _).
- Removed isZero_rowFiltrationEdge_abutmentFiltration, isZero_rowFiltrationEdge_H: inline `K.isZero_rowFiltration_abutmentFiltration _ (by subst hpq; simp) _` and `K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)`.
- totalRowι_zero (@[simp], rfl) and isZero_rowFiltrationSpectralObject_H_bot moved to Bicomplex/Basic.
- New rowFiltrationToRowOne_comp_spectralSequencePageXToEInfty, columnFiltrationToColumnOne_def.
