module

public import ArtinMatthews.MarkedMemoryPathChoiceBounds
public import ArtinMatthews.MarkedMemoryLineAtomBounds
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounds for the literal actual path choice masses at the
original growing moment length and slot count. The inactive atom mass
uses the proved band mass bound; the active absolute cost is explicit. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemoryActualPathChoiceMass_bounds {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0≤q → q≤1 →
      ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
        (d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ Z (markedMemoryMomentLength x)),
      markedMemoryPathActiveChoiceAbsoluteMass hZ d q≤Real.exp (16*(Fintype.card J:ℝ)*Real.log x) ∧
      markedMemoryPathInactiveAtomMass d q≤2*(Fintype.card J:ℝ) ∧
      ∀ j (p : markedRawActualPrimeBand e x j),0 ≤ markedMemoryLineBirthAtom q (markedMemoryMomentLength x) p.1 := by
  filter_upwards [markedMemoryActualLineBirthAtom_bounds e he,markedMemoryMomentLength_log_bound,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hb hl hlog
  intro q hq0 hq1 Z hZ d
  have hatom := hb q hq0 hq1
  have ha0 := fun j p => (hatom.1 j p).1.le
  constructor
  · let U := Fintype.card J*((markedMemoryMomentLength x+1)*markedPadSlots x)
    have hU : (U:ℝ)≤8*(Fintype.card J:ℝ)*(Real.log x)^(3/4:ℝ) :=
      markedMemoryActiveOccurrences_rpow_bound (Fintype.card J) hlog
    have hL : 0<Real.log x := by linarith
    have hnlog : 0≤Real.log ((markedMemoryMomentLength x:ℝ)+2) :=
      Real.log_nonneg (by have hh := Nat.cast_nonneg (markedMemoryMomentLength x) (α := ℝ); linarith)
    have hcost : (U:ℝ)*(2*Real.log ((markedMemoryMomentLength x:ℝ)+2))≤
        16*(Fintype.card J:ℝ)*Real.log x := by
      calc
        _ ≤ (8*(Fintype.card J:ℝ)*(Real.log x)^(3/4:ℝ))*(2*(Real.log x)^(1/4:ℝ)) :=
          mul_le_mul hU (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤2))
            (mul_nonneg (by norm_num) hnlog) (by positivity)
        _ = _ := by
          have hp : (Real.log x)^(3/4:ℝ)*(Real.log x)^(1/4:ℝ)=Real.log x := by
            rw [← Real.rpow_add hL]
            norm_num
          nlinarith
    calc
      _ ≤ (((markedMemoryMomentLength x:ℝ)+2)^2)^U :=
        markedMemoryPathActiveChoiceAbsoluteMass_bound hZ d q hq0 hq1 (fun j p => ⟨ha0 j p,(hatom.1 j p).2⟩)
      _ = Real.exp ((U:ℝ)*(2*Real.log ((markedMemoryMomentLength x:ℝ)+2))) := by
        have hh : Real.exp (2*Real.log ((markedMemoryMomentLength x:ℝ)+2))=
            ((markedMemoryMomentLength x:ℝ)+2)^2 := by
          rw [show 2*Real.log ((markedMemoryMomentLength x:ℝ)+2)=
            Real.log ((markedMemoryMomentLength x:ℝ)+2)+Real.log ((markedMemoryMomentLength x:ℝ)+2) by ring,
            Real.exp_add,Real.exp_log (by positivity : (0:ℝ)<(markedMemoryMomentLength x:ℝ)+2)]
          ring
        rw [Real.exp_nat_mul,hh]
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  · constructor
    · calc
        _ ≤ ∑ j,∑ p : markedRawActualPrimeBand e x j,
            markedMemoryLineBirthAtom q (markedMemoryMomentLength x) p.1 :=
          markedMemoryPathInactiveAtomMass_le d q ha0
        _ ≤ ∑ _j : J,(2:ℝ) := Finset.sum_le_sum (fun j _ => hatom.2 j)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
    · exact ha0

end
end ArtinMatthews
