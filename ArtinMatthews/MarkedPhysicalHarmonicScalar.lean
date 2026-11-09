module

public import ArtinMatthews.MarkedPhysicalCofactorSupportSum
public import ArtinMatthews.MarkedPhysicalScalarDetector
public import ArtinMatthews.MarkedPhysicalPadSurvival
public import ArtinMatthews.MarkedPhysicalTypeIIDyadSum


set_option backward.privateInPublic true
@[expose] public section

/-! The physical detector sum is the literal scalar sum on coprime
last-label products, with the exact surviving harmonic pad mass. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

def markedPhysicalPadSurvivalScalarSum
    (P : J → Finset ℕ) (pads : ℕ) (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass P:ℂ)^2*
    ∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
      if (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) then
        ((1-markedPhysicalPadCollisionMass P pads b a:ℝ):ℂ)*
          markedPhysicalScalarDetectorBlock S T η Y detector α β
            (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
      else 0

theorem markedPhysicalHarmonicPaddedDetectorSum_eq_survival_scalar [Nonempty J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j,0 < bandReciprocalMass (P j)) (pads : ℕ)
    {Y Hm Hn W : ℝ} (hY : 0 < Y) (hm₀ : 0 ≤ Hm) (hn₀ : 0 ≤ Hn)
    (hbelow : ∀ j p,p ∈ P j → (p:ℝ)<W)
    {η : ℝ → ℂ} (hη : Function.support η ⊆ Set.Icc 1 4)
    {detector : ℤ → ℤ → ℤ → ℂ} (ht : ∀ b a t : ℤ,detector b a t ≠ 0 → |(t:ℝ)| < W)
    {α β : ℕ → ℂ} (S T : Finset ℕ)
    (hS : ∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm)
    (hT : ∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn)
    (hα : ∀ m,α m ≠ 0 → m ∈ S ∧ MarkedPhysicalRoughAt W m)
    (hβ : ∀ n,β n ≠ 0 → n ∈ T ∧ MarkedPhysicalRoughAt W n) :
    markedPhysicalHarmonicPaddedDetectorSum P pads (markedPhysicalTypeIIDyadBox Y Hm Hn) η Y detector α β =
      markedPhysicalPadSurvivalScalarSum P pads S T η Y detector α β := by
  let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
  have hZ (j : ℕ) : ∀ z ∈ Z j,0 ≤ z.1 ∧ 0 ≤ z.2 :=
    markedPhysicalPadBox_nonnegative (by positivity : 0 ≤ ((2:ℕ)^j:ℝ)) hY.le hm₀ hn₀
  rw [markedPhysicalHarmonicPaddedDetectorSum_eq_cofactors P hP hdis pads Z hZ,
    markedPhysicalMass_two_labelMass_sq,Complex.ofReal_pow]
  unfold markedPhysicalPadSurvivalScalarSum
  congr 1
  let F (b a : (j : J) → ↥(P j)) := markedPhysicalScalarDetectorBlock S T η Y detector α β
    (markedPrimeBandProduct P b) (markedPrimeBandProduct P a)
  have hblock (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j)) :
      (let j := Nat.log 2 (markedPhysicalMarkingProduct c)
       markedPhysicalPadCofactorBlock P hP hdis pads (Z j) (hZ j) η Y detector α β c b a)=
      if ¬MarkedPhysicalPadCollisionEvent P pads b a c ∧
        (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) then F b a else 0 := by
    let j := Nat.log 2 (markedPhysicalMarkingProduct c)
    have hj := (markedPhysicalPad_dyad_iff P hP pads c j).mpr rfl
    have hb := markedPhysicalPadCofactorBlock_eq_supported_sum P hP hdis pads c b a
      (by positivity : 0 ≤ ((2:ℕ)^j:ℝ)) hY hm₀ hn₀ hj hbelow hη ht S T hS hT hα hβ
    change markedPhysicalPadCofactorBlock P hP hdis pads (markedPhysicalPadBox ((2:ℕ)^j:ℝ) Y Hm Hn)
      (markedPhysicalPadBox_nonnegative (by positivity) hY.le hm₀ hn₀) η Y detector α β c b a=_
    rw [hb]
    simp only [markedPhysicalLastProduct_coprime_iff hP hdis b a,
      markedPhysicalScalarCofactorTerm_sum,F]
  have hμ (c : MarkedPhysicalMarking P pads) :
      (∏ j,∏ k,markedHarmonicAtom (P j) (c j k))=markedPhysicalPadHarmonicMass P pads c := rfl
  simp_rw [hblock,hμ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a)
  · rw [ite_eq_left hc]
    calc
      _ = ∑ c : MarkedPhysicalMarking P pads,(markedPhysicalPadHarmonicMass P pads c:ℂ)*
          (if ¬MarkedPhysicalPadCollisionEvent P pads b a c then F b a else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases he : MarkedPhysicalPadCollisionEvent P pads b a c
        · have he' : ¬(¬MarkedPhysicalPadCollisionEvent P pads b a c ∧
              (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a)) := fun h => h.1 he
          rw [ite_eq_right he',ite_eq_right (not_not_intro he)]
        · rw [ite_eq_left (And.intro he hc),ite_eq_left he]
      _ = _ := markedPhysicalPadHarmonicMass_survival_weighted P pads hV b a (F b a)
  · simp only [hc,and_false,ite_false,mul_zero,Finset.sum_const_zero]

end
end ArtinMatthews
