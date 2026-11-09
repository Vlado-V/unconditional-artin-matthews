module

public import ArtinMatthews.GiantSignedCleanSector
public import ArtinMatthews.GiantSmallConditioningJoint


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed ordered-prefix clean form has the exact small-state tail
expansion and the original factorial weight on its pending sector. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

def giantSignedSectorState {k ell : ℕ}
    (w : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedMemorySectors PB)
    (z : GiantSignedSectorExtra (PB := PB) s (k+ell)) :
    GiantTwoSidedResidueState PS (k+ell) → ℂ :=
  fun a => w (a, z.1, giantSignedMemoryAt s z.2)

def giantSignedSectorConditioned {k ell : ℕ} (q : ℝ)
    (w : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedMemorySectors PB)
    (d : MarkedPhysicalMarking PS k) (x : GiantSignedResidueFiber PS s.2)
    (a : MarkedPhysicalMarking PB (k+ell)) : ℂ :=
  giantSmallConditioningMap PS k ell q d
    (fun aS => w (aS, a, giantSignedMemoryAt s x.2)) x.1

def giantSignedSectorWeightedKernel {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (κ : ℤ) (s : GiantSignedMemorySectors PB) (d : MarkedPhysicalMarking PS k)
    (y : GiantTwoSidedFullResidue PS) (z : GiantSignedSectorExtra (PB := PB) s (k+ell))
    (y' : GiantTwoSidedFullResidue PS) (z' : GiantSignedSectorExtra (PB := PB) s (k+ell)) : ℂ :=
  (giantSignedPrimeListMass ν s.2 * giantSignedActiveMass ν z.1 : ℂ) *
    giantSignedSectorCleanKernel PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
      (y, z.2) z.1 (y', z'.2) z'.1

def giantSignedSectorConditionedForm {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) : ℂ :=
  ∑ d : MarkedPhysicalMarking PS k, ∑ x : GiantSignedResidueFiber PS s.2,
    ∑ a : MarkedPhysicalMarking PB (k+ell),
      (giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2 * giantSignedActiveMass ν a : ℂ) *
        star (giantSignedSectorConditioned PS q w₁ s d x a) *
        giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
          (giantSignedSectorConditioned PS q w₂ s d) x a

def giantSignedSectorTailForm {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) : ℂ :=
  ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
    ∑ z : GiantSignedSectorExtra (PB := PB) s (k+ell),
    ∑ y' : GiantTwoSidedFullResidue PS,
    ∑ z' : GiantSignedSectorExtra (PB := PB) s (k+ell),
    ∑ r : MarkedPhysicalMarking PS ell, ∑ r' : MarkedPhysicalMarking PS ell,
      ((giantSignedSmallHaar PS *
        (markedPhysicalMass (fun j => bandReciprocalMass (PS j)) (k+ell) * giantSmallTailMass PS ell) *
        giantTwoSidedResidueDamping PS (k+ell) q y *
        giantTwoSidedResidueDamping PS (k+ell) q y' : ℝ) : ℂ) *
        star (giantSmallStateValue (giantSignedSectorState PS w₁ s z) y (giantSmallAppend d r)) *
        giantSignedSectorWeightedKernel PS ν freshLaw auxLaw patterns C θ ζ ρ K κ s d y z y' z' *
        giantSmallStateValue (giantSignedSectorState PS w₂ s z') y' (giantSmallAppend d r')

omit [DecidableEq S] in
theorem giantSignedSector_kernel_sum {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (d : MarkedPhysicalMarking PS k) (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (f : GiantSignedResidueFiber PS s.2 → MarkedPhysicalMarking PB (k+ell) → ℂ)
    (x : GiantSignedResidueFiber PS s.2) (a : MarkedPhysicalMarking PB (k+ell)) :
    (∑ y : GiantTwoSidedFullResidue PS,
      ∑ z : GiantSignedSectorExtra (PB := PB) s (k+ell),
        giantSignedSectorCleanKernel PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
          x a (y, z.2) z.1 * f (y, z.2) z.1) =
      giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s f x a := by
  rw [giantSignedSectorCleanApply_eq_sum_kernel]
  simp only [GiantSignedSectorExtra, GiantSignedResidueFiber, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_comm

theorem giantSignedSectorTailForm_eq_conditioned {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (κ : ℤ) (s : GiantSignedMemorySectors PB)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedSectorTailForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ s w₁ w₂ =
      giantSignedSectorConditionedForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ s w₁ w₂ := by
  have htail : giantSignedSectorTailForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ s w₁ w₂ =
      ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ z : GiantSignedSectorExtra (PB := PB) s (k+ell),
        ∑ y' : GiantTwoSidedFullResidue PS,
        ∑ z' : GiantSignedSectorExtra (PB := PB) s (k+ell),
          (giantSignedSmallHaar PS : ℂ) *
            star (giantSmallConditioningMap PS k ell q d (giantSignedSectorState PS w₁ s z) y) *
            giantSignedSectorWeightedKernel PS ν freshLaw auxLaw patterns C θ ζ ρ K κ s d y z y' z' *
            giantSmallConditioningMap PS k ell q d (giantSignedSectorState PS w₂ s z') y' := by
    unfold giantSignedSectorTailForm
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.sum_congr rfl
    intro z' _
    have hp := giantSmallConditioningMap_pair (P := PS) (k := k) (ell := ell)
      hV q q d (giantSignedSectorState PS w₁ s z) (giantSignedSectorState PS w₂ s z') y y'
      (giantSignedSectorWeightedKernel PS ν freshLaw auxLaw patterns C θ ζ ρ K κ s d y z y' z')
    have hh := congrArg (fun t : ℂ => (giantSignedSmallHaar PS : ℂ) * t) hp
    simpa only [Finset.mul_sum, Complex.ofReal_mul, mul_assoc] using hh.symm

  rw [htail]
  have hlocal (d : MarkedPhysicalMarking PS k) (y : GiantTwoSidedFullResidue PS)
      (z : GiantSignedSectorExtra (PB := PB) s (k+ell)) :
      (∑ y' : GiantTwoSidedFullResidue PS,
        ∑ z' : GiantSignedSectorExtra (PB := PB) s (k+ell),
          giantSignedSectorCleanKernel PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
            (y, z.2) z.1 (y', z'.2) z'.1 *
          giantSmallConditioningMap PS k ell q d (giantSignedSectorState PS w₂ s z') y') =
        giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
          (giantSignedSectorConditioned PS q w₂ s d) (y, z.2) z.1 := by
    change (∑ y' : GiantTwoSidedFullResidue PS,
      ∑ z' : GiantSignedSectorExtra (PB := PB) s (k+ell),
        giantSignedSectorCleanKernel PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
          (y, z.2) z.1 (y', z'.2) z'.1 *
        giantSignedSectorConditioned PS q w₂ s d (y', z'.2) z'.1) = _
    exact giantSignedSector_kernel_sum PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
      (giantSignedSectorConditioned PS q w₂ s d) (y, z.2) z.1
  calc
    _ = ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ z : GiantSignedSectorExtra (PB := PB) s (k+ell),
          (giantSignedSmallHaar PS : ℂ) *
            star (giantSmallConditioningMap PS k ell q d (giantSignedSectorState PS w₁ s z) y) *
            (giantSignedPrimeListMass ν s.2 * giantSignedActiveMass ν z.1 : ℂ) *
            giantSignedSectorCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ s
              (giantSignedSectorConditioned PS q w₂ s d) (y, z.2) z.1 := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      simpa only [giantSignedSectorWeightedKernel, mul_assoc, ← Finset.mul_sum] using
        congrArg (fun t : ℂ => (giantSignedSmallHaar PS : ℂ) *
          star (giantSmallConditioningMap PS k ell q d (giantSignedSectorState PS w₁ s z) y) *
          (giantSignedPrimeListMass ν s.2 * giantSignedActiveMass ν z.1 : ℂ) * t) (hlocal d y z)
    _ = _ := by
      unfold giantSignedSectorConditionedForm
      simp only [GiantSignedSectorExtra, GiantSignedResidueFiber, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro a _
      have hstate : giantSignedSectorState (k := k) (ell := ell) PS w₁ s (a, r) =
          (fun aS => w₁ (aS, a, giantSignedMemoryAt s r)) := rfl
      rw [hstate]
      dsimp only [giantSignedSectorConditioned]
      ring

end
end ArtinMatthews
