/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle

/-!
# Principal coboundaries and conjugate cocycle kernels

Adding a principal coboundary preserves the cocycle law. If its coefficient is the value
`c k` of a cocycle, then it conjugates the zero subgroup by `k`:

`ker (g ↦ c g + (g • c k - c k)) = k (ker c) k⁻¹`.

In particular, for a normalized crossed projection onto an abelian normal subgroup, its value
at an element `a` of that normal subgroup is `a` itself. The formula then identifies the kernels
after a principal change of that projection, and hence the corresponding subgroup complements.
This is also the kernel calculation used when two normalized crossed transfers differ by a
principal crossed map.

The proof reuses `groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁`, so no triviality of
the coefficient action, normalization, or finiteness is required for the general result.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* K. S. Brown, *Cohomology of Groups*, Chapter IV, §2.
-/

public section

namespace groupCohomology

variable {G M : Type*} [AddCommGroup M]

/-- Adding the principal coboundary of `a` to a cocycle preserves the cocycle law. -/
theorem IsCocycle₁.add_coboundary [Monoid G] [DistribMulAction G M]
    {c : G → M} (hc : IsCocycle₁ c) (a : M) :
    IsCocycle₁ (fun g => c g + (g • a - a)) := by
  intro g h
  simp only [hc g h, smul_add, smul_sub, mul_smul]
  abel

/-- Adding the principal coboundary of `c k` conjugates the zero subgroup of a cocycle by `k`.
For a normalized crossed projection, this applies to the principal coboundary of any element
of the normal subgroup. -/
theorem IsCocycle₁.zeroLocus_add_coboundary [Group G] [DistribMulAction G M]
    {c : G → M} (hc : IsCocycle₁ c) (k : G) :
    zeroLocus (hc.add_coboundary (c k)) =
      (zeroLocus hc).map (MulAut.conj k).toMonoidHom := by
  ext g
  rw [mem_zeroLocus, Subgroup.mem_map_equiv, mem_zeroLocus, MulAut.conj_symm_apply]
  have hid := smul_apply_inv_mul_mul_of_isCocycle₁ hc k g
  rw [add_comm (c g), ← hid]
  simpa only [smul_zero] using (smul_left_cancel_iff k :
    k • c (k⁻¹ * g * k) = k • (0 : M) ↔ c (k⁻¹ * g * k) = 0)

end groupCohomology
