module

public import ArtinMatthews.GiantSignedGhostCountableAdjoint
public import ArtinMatthews.GiantSignedGhostPositiveApply


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted column identity and bound follow from the full factorial
adjoint, without replacing the residue counting measure. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {P : Finset ℕ} [∀ p : P, NeZero p.val]

omit [∀ p : P, NeZero p.val] in
theorem giantSignedGroupRealPairing_coe (ν : P → ℝ)
    (f h : GiantSignedGroupMemory P → ℝ) :
    ((∑' m, giantSignedGroupMemoryMass ν m * f m * h m : ℝ) : ℂ) =
      giantSignedGroupPairing ν (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) := by
  simp only [giantSignedGroupPairing, Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.star_def, Complex.conj_ofReal]

theorem giantSignedGhostPositiveApply_adjoint
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℝ)
    (f h : GiantSignedGroupMemory P → ℝ)
    (hfs : GiantSignedGroupSymmetric (fun m => (f m : ℂ)))
    (hhs : GiantSignedGroupSymmetric (fun m => (h m : ℂ)))
    (B F u v : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 < u) (hv : 0 < v)
    (hf : ∀ m, ‖(f m : ℂ)‖ ≤ B * u ^ m.1)
    (hh : ∀ m, ‖(h m : ℂ)‖ ≤ F * v ^ m.1) :
    (∑' m, giantSignedGroupMemoryMass ν m * f m * giantSignedGhostPositiveApply ν A C D h m) =
      ∑' m, giantSignedGroupMemoryMass ν m * h m * giantSignedGhostPositiveApply ν A D C f m := by
  apply Complex.ofReal_injective
  rw [giantSignedGroupRealPairing_coe, giantSignedGroupRealPairing_coe]
  simp_rw [giantSignedGhostPositiveApply_coe]
  have he := giantSignedGhostGroupPairing_adjoint ν hν (A : ℂ) (C : ℂ) (D : ℂ)
    (fun m => (f m : ℂ)) (fun m => (h m : ℂ)) hfs hhs B F u v hB hF hu hv hf hh
  simp only [Complex.star_def, Complex.conj_ofReal] at he
  rw [he]
  have hswap : giantSignedGhostGroupApply ν (A : ℂ) (D : ℂ) (C : ℂ)
      (fun m => (f m : ℂ)) = fun m => (giantSignedGhostPositiveApply ν A D C f m : ℂ) := by
    funext m
    exact (giantSignedGhostPositiveApply_coe ν A D C f m).symm
  rw [hswap]
  rw [← giantSignedGroupRealPairing_coe]
  exact Complex.conj_ofReal _

theorem giantSignedGroupRealPairing_summable
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p)
    (f h : GiantSignedGroupMemory P → ℝ)
    (B F u v : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hf : ∀ m, ‖(f m : ℂ)‖ ≤ B * u ^ m.1)
    (hh : ∀ m, ‖(h m : ℂ)‖ ≤ F * v ^ m.1) :
    Summable (fun m => giantSignedGroupMemoryMass ν m * f m * h m) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal] using
    giantSignedGroupPairing_summable ν hν (fun m => (f m : ℂ)) (fun m => (h m : ℂ))
      B F u v hB hF hu hv hf hh

theorem giantSignedGhostPositive_column_weight
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D v : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hv : 0 < v)
    (hc : A + C / v ≤ 1) (f : GiantSignedGroupMemory P → ℝ)
    (hf0 : ∀ m, 0 ≤ f m) (hfs : GiantSignedGroupSymmetric (fun m => (f m : ℂ)))
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 < u)
    (hf : ∀ m, f m ≤ B * u ^ m.1) :
    (∑' m, giantSignedGroupMemoryMass ν m * v ^ m.1 *
      giantSignedGhostPositiveApply ν A C D f m) ≤
      Real.exp (D * (∑ p : P, ν p) * v) *
        ∑' m, giantSignedGroupMemoryMass ν m * v ^ m.1 * f m := by
  have hw : GiantSignedGroupSymmetric (fun m : GiantSignedGroupMemory P => ((v ^ m.1 : ℝ) : ℂ)) :=
    fun _ _ _ => rfl
  have hfc : ∀ m, ‖(f m : ℂ)‖ ≤ B * u ^ m.1 := by
    intro m
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hf0 m)] using hf m
  have hwc : ∀ m : GiantSignedGroupMemory P, ‖((v ^ m.1 : ℝ) : ℂ)‖ ≤ 1 * v ^ m.1 := by
    intro m
    simp only [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hv.le _), one_mul, le_refl]
  rw [giantSignedGhostPositiveApply_adjoint ν hν A C D (fun m => v ^ m.1) f
    hw hfs 1 B v u zero_le_one hB hv hu hwc hfc]
  have hs := giantSignedGroupRealPairing_summable ν hν f (fun m => v ^ m.1)
    B 1 u v hB zero_le_one hu.le hv.le hfc hwc
  have hp : ∀ m, 0 ≤ giantSignedGroupMemoryMass ν m * f m :=
    fun m => mul_nonneg (giantSignedGroupMemoryMass_nonneg ν hν m) (hf0 m)
  have hle : ∀ m, giantSignedGroupMemoryMass ν m * f m *
      giantSignedGhostPositiveApply ν A D C (fun t => v ^ t.1) m ≤
      Real.exp (D * (∑ p : P, ν p) * v) *
        (giantSignedGroupMemoryMass ν m * f m * v ^ m.1) := by
    intro m
    calc
      _ ≤ giantSignedGroupMemoryMass ν m * f m *
          (v ^ m.1 * Real.exp (D * (∑ p : P, ν p) * v)) :=
        mul_le_mul_of_nonneg_left
          (giantSignedGhostPositiveApply_weight ν hν A D C v hA hD hC hv hc m) (hp m)
      _ = _ := by ring
  have hright := hs.mul_left (Real.exp (D * (∑ p : P, ν p) * v))
  have hleft := hright.of_nonneg_of_le
    (fun m => mul_nonneg (hp m)
      (giantSignedGhostPositiveApply_nonneg ν hν A D C hA hD hC
        (fun t => v ^ t.1) (fun t => pow_nonneg hv.le _) m)) hle
  calc
    _ ≤ ∑' m, Real.exp (D * (∑ p : P, ν p) * v) *
        (giantSignedGroupMemoryMass ν m * f m * v ^ m.1) := hleft.tsum_le_tsum hle hright
    _ = _ := by
      rw [tsum_mul_left]
      congr 1
      apply tsum_congr
      intro m
      ring

end
end ArtinMatthews
