module

public import ArtinMatthews.GiantSignedCleanDisintegration


set_option backward.privateInPublic true
@[expose] public section

/-! The clean row formula on actual pending memories, and its all-degree energy bound. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}

def giantSignedAmbientCleanPattern {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ := by
  classical
  exact ∑ aux : GiantTwoSidedPatternAuxiliary PB C,
    (idealAuxiliaryMass auxLaw aux : ℂ) *
      ∑ b : MarkedPhysicalMarking PB (k+ell), if IdealCopied C a b then
        let D := giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux
        (idealFreshTargetMass freshLaw C b : ℂ) * K a b aux *
          (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase Θ D *
          f (giantTwoSidedResidueTranslate ((D : ℤ) * d) y) b
            (giantSignedMemoryTranslate ((D : ℤ) * d) m)
      else 0

theorem giantSignedAmbientCleanPattern_at {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (C : B → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (s : GiantSignedMemorySectors PB) (x : GiantSignedResidueFiber PS s.2)
    (a : MarkedPhysicalMarking PB (k+ell)) :
    giantSignedAmbientCleanPattern PS freshLaw auxLaw C Θ ζ K d f
        x.1 a (giantSignedMemoryAt s x.2) =
      giantSignedCleanFiberPattern freshLaw auxLaw C Θ ζ K
        (giantSignedResidueDiagonal PS s.2 d) (giantSignedAmbientToSectors PS f s) x a := by
  classical
  unfold giantSignedAmbientCleanPattern giantSignedCleanFiberPattern
  apply Finset.sum_congr rfl
  intro aux _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : IdealCopied C a b
  · simp only [h, ite_true]
    rw [giantSignedResidueDiagonal_nsmul, giantSignedResidueDiagonal_translate]
    simp only [giantSignedAmbientToSectors, giantSignedMemoryAt_translate]
  · simp only [h, ite_false]

def giantSignedAmbientCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (Θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ :=
  (giantSignedPendingDamping ρ m : ℂ) * idealSlotAverage
    (fun b => ∑ v ∈ patterns,
      giantSignedAmbientCleanPattern PS freshLaw auxLaw (C v) Θ ζ (K v) d
        (fun y' b' m' => idealSlotAverage
          (fun a' => (giantSignedPendingDamping ρ m' : ℂ) * f y' a' m') b') y b m) a

theorem giantSignedAmbientCleanApply_at {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (Θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ) :
    giantSignedAmbientToSectors PS
        (giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C Θ ζ ρ K d f) =
      giantSignedUnboundedCleanApply PS freshLaw auxLaw patterns C Θ ζ ρ K d
        (giantSignedAmbientToSectors PS f) := by
  classical
  funext s x a
  unfold giantSignedAmbientToSectors giantSignedAmbientCleanApply
  simp_rw [giantSignedAmbientCleanPattern_at]
  rfl

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

theorem giantSignedAmbientCleanApply_energy {I : Type*} {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (Θ ζ ρ U : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℤ)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖h a‖ ^ 2)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (hf : ∀ y m, IdealSymmetric (fun a => f y a m)) :
    giantSignedAmbientEnergy PS ν
        (giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C Θ ζ ρ K d f) ≤
      ENNReal.ofReal (U ^ 2) * giantSignedAmbientEnergy PS ν f := by
  rw [giantSignedAmbientEnergy_disintegrate PS ν hν,
    giantSignedAmbientEnergy_disintegrate PS ν hν, giantSignedAmbientCleanApply_at]
  exact giantSignedUnboundedCleanApply_energy PS ν hν freshLaw auxLaw patterns C Θ ζ ρ U
    hρ hρ1 K d hIdeal _ (fun s x => hf x.1 (giantSignedMemoryAt s x.2))

end
end ArtinMatthews
