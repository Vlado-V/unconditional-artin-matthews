module

public import ArtinMatthews.IdealSlotPairing
public import ArtinMatthews.IdealRawAlgebra
public import ArtinMatthews.IdealResidualFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The original residual family expands into its raw member and all
nonempty selected pairs, retaining both slot normalizations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealResidualPatternPairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (ν : IdealResidualPattern G k)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) : ℂ :=
  idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
    (fun j => markedHarmonicAtom (P j)) (idealResidualCopied ν) Θ ζ (idealResidualCoefficient P Q h ξ ν) g)

theorem idealResidualOperator_pairing_expansion {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (S T : Finset (G × Fin k)) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) (hg : IdealSymmetric g) :
    idealLabelPairing P f (idealResidualOperator P S T Q h ξ Θ ζ g)=
      idealRawPairing P Θ ζ
        (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)
        (idealAverageSet P (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g)+
      ∑ A∈S.powerset.erase ∅,∑ B∈T.powerset.erase ∅,
        idealResidualPatternPairing P (some (A,B)) Q h ξ Θ ζ f g := by
  unfold idealResidualOperator idealOperator
  rw [idealOperatorWithLaws_pairing _ _ _ _ _ _ _ f g hf hg]
  change (∑ ν∈idealResidualPatterns S T,idealResidualPatternPairing P ν Q h ξ Θ ζ f g)= _
  have hd : Disjoint ({none} : Finset (IdealResidualPattern G k))
      ((S.powerset.erase ∅ ×ˢ T.powerset.erase ∅).image some) := by
    apply disjoint_singleton_left.mpr
    simp
  unfold idealResidualPatterns
  rw [sum_union hd,sum_singleton,sum_image]
  · rw [sum_product]
    congr 1
    exact idealPattern_raw_pairing P hV Θ ζ f g
  · intro a _ b _ hab
    exact Option.some.inj hab

end
end ArtinMatthews
