E1 fix 1fc6fa8ee7 signature changes to propagate into Bicomplex/Edge, Kunneth/Edge, Singular/Edge (branch roadmap/kunneth-edge-map):
- isZero_Tor_add_two_of_hasProjectiveDimensionLE_one: now [HasProjectiveDimensionLE Y 1] instead of [∀ Z, HasProjectiveDimensionLE Z 1].
- torZeroIso, torZeroIso_hom, homologyπ_isoLeftDerivedObj_inv_torZeroIso_hom: take [PreservesFiniteColimits ((tensoringLeft C).obj X)] (section ∀X instance removed); mapBifunctorMapObjTorZeroIso, ι_mapBifunctorMapObjTorZeroIso_hom take [∀ i, PreservesFiniteColimits ((tensoringLeft C).obj (X i))].
- isIso_spectralSequencePageXToEInfty_of_isZero: h₀ now ∀ r', r ≤ r' → r' ≤ r₁ → ...; conclusion uses (h₀ r le_rfl hrr₁). In Bicomplex/Edge: (fun r' _ ↦ ...) becomes (fun r' _ _ ↦ ...). New general isIso_spectralSequencePageXToEInfty_of_d_eq_zero.
- New abutmentFiltrationMapOfLE, isIso_abutmentFiltrationMapOfLE_of_isZero_EInfty; isIso_abutmentFiltrationι_of_isZero_EInfty unchanged signature.
