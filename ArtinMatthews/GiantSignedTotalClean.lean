module

public import ArtinMatthews.GiantSignedTotalPhase
public import ArtinMatthews.GiantSignedAmbientClean


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}

omit [DecidableEq B] in
/-- The actual copied and auxiliary big-prime product is positive. -/
theorem giantSignedCleanBigProduct_pos {k ell : ℕ}
    (hP : ∀ g p, p ∈ PB g → p.Prime) (C : B → Finset (Fin k))
    (a : MarkedPhysicalMarking PB (k + ell)) (aux : GiantTwoSidedPatternAuxiliary PB C) :
    0 < giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux := by
  exact Nat.mul_pos (Finset.prod_pos fun g _ => Finset.prod_pos fun i _ =>
      (hP g _ (a g (Fin.castAdd ell i)).property).pos)
    (Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => (hP g _ (aux g i).property).pos)

omit [DecidableEq B] in
/-- Multiplying by the original positive small product preserves positivity. -/
theorem giantSignedCleanTotalProduct_pos {k ell : ℕ}
    (d : ℕ) (hd : 0 < d) (hP : ∀ g p, p ∈ PB g → p.Prime)
    (C : B → Finset (Fin k)) (a : MarkedPhysicalMarking PB (k + ell))
    (aux : GiantTwoSidedPatternAuxiliary PB C) :
    0 < d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux) :=
  Nat.mul_pos hd (giantSignedCleanBigProduct_pos hP C a aux)

/-- The original clean row, with the total small-times-big product in every phase and translation. -/
def giantSignedTotalCleanPattern {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) : ℂ := by
  classical
  exact ∑ aux : GiantTwoSidedPatternAuxiliary PB C, (idealAuxiliaryMass auxLaw aux : ℂ) *
    ∑ b : MarkedPhysicalMarking PB (k + ell), if IdealCopied C a b then
      let D := d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
      (idealFreshTargetMass freshLaw C b : ℂ) * K a b aux *
        (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase θ D *
          f (giantTwoSidedResidueTranslate (D : ℤ) y) b (giantSignedMemoryTranslate (D : ℤ) m)
    else 0

/-- Exact row and spectral multiplier adapter to the conditioned big-row receiver. -/
theorem giantSignedTotalCleanPattern_eq {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    giantSignedTotalCleanPattern PS freshLaw auxLaw C θ ζ K d f y a m =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        giantSignedAmbientCleanPattern PS freshLaw auxLaw C (θ * (d : ℝ)) ζ K (d : ℤ) f y a m := by
  classical
  unfold giantSignedTotalCleanPattern giantSignedAmbientCleanPattern
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IdealCopied C a b
  · simp only [hab, ite_true]
    rw [giantSignedTotalD_cpow, idealAdditivePhase_totalD]
    have hshift (D : ℕ) : ((d * D : ℕ) : ℤ) = (D : ℤ) * (d : ℤ) := by
      push_cast
      ring
    rw [hshift]
    ring
  · simp only [hab, ite_false, mul_zero]

/-- Both original pending half-dampings and slot averages surround the total clean row. -/
def giantSignedTotalCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) : ℂ :=
  (giantSignedPendingDamping ρ m : ℂ) * idealSlotAverage
    (fun b => ∑ v ∈ patterns, giantSignedTotalCleanPattern PS freshLaw auxLaw (C v) θ ζ (K v) d
      (fun y' b' m' => idealSlotAverage (fun a' => (giantSignedPendingDamping ρ m' : ℂ) * f y' a' m') b')
      y b m) a

/-- Exact full-apply adapter, retaining both rho halves and both slot averages. -/
theorem giantSignedTotalCleanApply_eq {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    giantSignedTotalCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d f y a m =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (d : ℤ) f y a m := by
  classical
  unfold giantSignedTotalCleanApply giantSignedAmbientCleanApply
  simp_rw [giantSignedTotalCleanPattern_eq, ← Finset.mul_sum]
  rw [giantSignedActiveMultiplier_slotAverage]
  ring

/-- The fixed small spectral phase preserves the literal row norm. -/
theorem giantSignedTotalCleanApply_norm {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (hd : 0 < d)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k + ell))
    (m : GiantSignedMemory PB) :
    ‖giantSignedTotalCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d f y a m‖ =
      ‖giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (d : ℤ) f y a m‖ := by
  rw [giantSignedTotalCleanApply_eq, norm_mul, giantSignedSmallD_cpow_norm d hd ζ, one_mul]

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

omit [∀ (g : B) (p : PB g), NeZero p.val] in
/-- The actual ambient energy is unchanged by the total-product adapter. -/
theorem giantSignedTotalCleanApply_energy_eq {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℕ) (hd : 0 < d)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k + ell) → GiantSignedMemory PB → ℂ) :
    giantSignedAmbientEnergy PS ν (giantSignedTotalCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d f) =
      giantSignedAmbientEnergy PS ν
        (giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (θ * (d : ℝ)) ζ ρ K (d : ℤ) f) := by
  unfold giantSignedAmbientEnergy
  apply tsum_congr
  intro m
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  rw [giantSignedTotalCleanApply_norm PS freshLaw auxLaw patterns C θ ζ ρ K d hd f y a m]

end
end ArtinMatthews
