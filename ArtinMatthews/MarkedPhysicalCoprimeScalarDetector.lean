module

public import ArtinMatthews.MarkedPhysicalScalarDetector
public import ArtinMatthews.MarkedMajorLabelSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Literal coprime scalar detector sums, with the two unshared label
normalizers and the original four cofactor coefficients. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)

def markedPhysicalCoprimeLabelPairs : Finset (ℕ×ℕ) :=
  ((markedMajorLabelSet P).product (markedMajorLabelSet P)).filter (fun z => z.1.Coprime z.2)

def markedPhysicalCoprimeScalarDetectorSum
    (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass P:ℂ)^2*
    ∑ z ∈ markedPhysicalCoprimeLabelPairs P,
      markedPhysicalScalarDetectorBlock S T η Y detector α β z.1 z.2

def markedPhysicalCoprimeScalarDetectorAbsMass
    (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℝ :=
  (markedMajorLabelMass P)^2*
    ∑ z ∈ markedPhysicalCoprimeLabelPairs P,
      markedPhysicalScalarDetectorAbsBlock S T η Y detector α β z.1 z.2

variable [DecidableEq J]
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))

include hP hdis

theorem markedPhysicalCoprimeLabelPairs_sum {R : Type*} [AddCommMonoid R] (F : ℕ×ℕ → R) :
    (∑ z ∈ markedPhysicalCoprimeLabelPairs P,F z) =
      ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
        if (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) then
          F (markedPrimeBandProduct P b,markedPrimeBandProduct P a) else 0 := by
  have h (f : ℕ → R) : (∑ n ∈ markedMajorLabelSet P,f n)=
      ∑ t : (j : J) → ↥(P j), f (markedPrimeBandProduct P t) := by
    rw [markedMajorLabelSet,Finset.sum_image (fun _ _ _ _ he =>
      markedPrimeBandProduct_injective P hP hdis he)]
    congr 1
    ext t
    simp
  rw [markedPhysicalCoprimeLabelPairs,Finset.sum_filter]
  refine (Finset.sum_product _ _ _).trans ?_
  simp_rw [h]

end
end ArtinMatthews
