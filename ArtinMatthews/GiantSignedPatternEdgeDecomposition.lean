module

public import ArtinMatthews.GiantSignedPatternEdgeClean


set_option backward.privateInPublic true
@[expose] public section

/-! The copied-pattern row is the literal full store/promote row. Its
zero-store, zero-promotion summand is selected from this finite sum. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}

def giantSignedPatternEdgeRow {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ)
    (C : B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ :=
  ∑ aux : GiantTwoSidedPatternAuxiliary PB C,
    let D := d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
    (idealAuxiliaryMass auxLaw aux : ℂ) * (D : ℂ) ^ ((ζ : ℂ) * Complex.I) *
      idealAdditivePhase θ D *
        giantSignedEdgeApply (fun j p => (freshLaw j p : ℂ)) V ρ (κ * (D : ℤ)) D
          (giantSignedPatternFreeLabels C a)
          (fun t m' => K a (giantSignedPatternFill C a t) aux *
            f (giantTwoSidedResidueTranslate (κ * (D : ℤ)) y) (giantSignedPatternFill C a t) m') m

theorem giantSignedPatternEdgeRow_eq_sum_terms {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ)
    (C : B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) :
    giantSignedPatternEdgeRow PS freshLaw auxLaw V C θ ζ ρ K d κ f y a m =
      ∑ stores : (j : B) → Finset (Fin (ell + (C j).card)),
        ∑ promotions : (j : B) → Finset (Fin (ell + (C j).card)),
          giantSignedPatternEdgeTerm PS freshLaw auxLaw V C θ ζ ρ K d κ
            stores promotions f y a m := by
  unfold giantSignedPatternEdgeRow giantSignedPatternEdgeTerm
  simp_rw [giantSignedEdgeApply_eq_sum_fixed]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro stores _
  exact Finset.sum_comm

end
end ArtinMatthews
