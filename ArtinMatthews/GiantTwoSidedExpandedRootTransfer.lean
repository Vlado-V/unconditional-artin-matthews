module

public import ArtinMatthews.GiantTwoSidedFixedRootTransfer
public import ArtinMatthews.GiantTwoSidedResiduePathExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The complete finite pattern, permutation and auxiliary expansion
retains the original slot normalization in the root-replacement error. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedExpandedPhysicalMoment {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) (roots slice : Finset ℕ) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J:=J) (k+ell))^n:ℂ)*
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
      giantTwoSidedPhysicalMoment (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2)
        step q ζ (fun i => K i (choices i).1.val) roots slice

def giantTwoSidedExpandedIndependentMoment {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → J → Finset (Fin k)) (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) : ℂ :=
  ((giantTwoSidedResidueSlotNormalization (J:=J) (k+ell))^n:ℂ)*
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
      giantTwoSidedIndependentMoment (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2)
        step q ζ (fun i => K i (choices i).1.val)

theorem giantCandidateExpandedMoment_root_error {I : Type*} (k ell : ℕ) (C₂ A : ℝ) (hA : 0 ≤ A)
    {γ q : ℝ} (hγ : 0<γ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k))
        (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ) ≤ (Real.log x)^C₂) → ∀ X : ℝ,x^γ ≤ X →
        ∀ (ζ : Fin n → ℝ) (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell),
          ‖giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K
              (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X) -
            (((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ):ℂ)*
              giantTwoSidedExpandedIndependentMoment patterns C step q ζ K‖ ≤ 
          (2*(Real.log x)^(-A*(n:ℝ))+Real.exp (-γ*Real.log x/4))*
            ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*giantTwoSidedResidueExpandedRootMass patterns C step q ζ K := by
  filter_upwards [giantCandidateFixedMoment_root_error k ell C₂ A hA hγ hq0 hq1]
    with x hfixed
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro patterns C step hstep X hX ζ K
  let n := giantTwoSidedSourceMomentLength x
  let L := ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)
  let E := 2*(Real.log x)^(-A*(n:ℝ))+Real.exp (-γ*Real.log x/4)
  let a := (giantTwoSidedResidueSlotNormalization (J:=S) (k+ell))^n
  let F (choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell) :=
    giantTwoSidedPhysicalMoment (fun i => C i (choices i).1.val)
      (fun i => (choices i).2.1) (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2)
      step q ζ (fun i => K i (choices i).1.val) (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X)
  let G (choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell) :=
    giantTwoSidedIndependentMoment (fun i => C i (choices i).1.val)
      (fun i => (choices i).2.1) (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2)
      step q ζ (fun i => K i (choices i).1.val)
  let B (choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell) :=
    giantTwoSidedIndependentFixedPathMass (fun i => C i (choices i).1.val)
      (fun i => (choices i).2.1) (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2)
      step q ζ (fun i => K i (choices i).1.val)
  have ha : 0 ≤ a := by
    apply pow_nonneg
    unfold giantTwoSidedResidueSlotNormalization
    exact inv_nonneg.mpr (sq_nonneg _)
  have hh (choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell) :
      ‖F choices-(L:ℂ)*G choices‖ ≤ E*L*B choices :=
    hfixed S nz (fun i => C i (choices i).1.val) (fun i => (choices i).2.1)
      (fun i => (choices i).2.2.1) (fun i => (choices i).2.2.2) step hstep X hX ζ
      (fun i => K i (choices i).1.val)
  simp only [giantTwoSidedExpandedPhysicalMoment,giantTwoSidedExpandedIndependentMoment,
    giantTwoSidedResidueExpandedRootMass,← Complex.ofReal_pow]
  change ‖(a:ℂ)*(∑ choices,F choices)-(L:ℂ)*((a:ℂ)*(∑ choices,G choices))‖ ≤ 
    E*L*(a*(∑ choices,B choices))
  have he : (a:ℂ)*(∑ choices,F choices)-(L:ℂ)*((a:ℂ)*(∑ choices,G choices)) =
      (a:ℂ)*(∑ choices,(F choices-(L:ℂ)*G choices)) := by
    rw [sum_sub_distrib,← mul_sum]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg ha]
  calc
    _ ≤ a*(∑ choices,‖F choices-(L:ℂ)*G choices‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) ha
    _ ≤ a*(∑ choices,E*L*B choices) := mul_le_mul_of_nonneg_left (sum_le_sum fun choices _ => hh choices) ha
    _ = E*L*(a*(∑ choices,B choices)) := by rw [← mul_sum];ring

end
end ArtinMatthews
