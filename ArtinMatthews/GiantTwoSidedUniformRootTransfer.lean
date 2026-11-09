module

public import ArtinMatthews.GiantTwoSidedRootTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! The original selected-carrier CRT replacement is uniform over the
finite pattern types chosen after the growing source parameter. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem giantCandidateUniformResidueExpandedRoot_pathMass_eventually (ell m₀ : ℕ)
    {q : ℝ} (hq : 0<q) (hq1 : q<1) (C₁ : ℝ) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (I : Type u) (k n : ℕ),n≠0 →
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
        giantTwoSidedResidueExpandedRootMass patterns C step q ζ K ≤ ((Real.log x)^(C₁+A))^n := by
  obtain ⟨A,hA,hrows⟩ := giantCandidateResiduePattern_absolute_rows_columns_eventually ell m₀ hq hq1
  refine ⟨A,hA,?_⟩
  filter_upwards [hrows,giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hx hgeo hprime hL
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
  intro I k n hn
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    intro patterns C hC step ζ K K₀ hK hmass
    have hP (j : S) (p : ℕ) (hp : p ∈ P j) : p.Prime :=
      (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
    have hV (j : S) : 0 < bandReciprocalMass (P j) :=
      (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 j).1
    rw [giantTwoSidedResidueExpandedRootMass_eq hP (hgeo S).1 hV patterns C step hq.le ζ K]
    apply giantTwoSidedResidueFamilyPathMass_le hP (hgeo S).1 hV patterns C step q ζ K
      (Real.rpow_nonneg hL.le _)
    intro i s
    have hsum : (∑ p∈patterns i, K₀ i p*(Real.log x)^A) ≤ (Real.log x)^(C₁+A) := by
      rw [← Finset.sum_mul,Real.rpow_add hL]
      exact mul_le_mul_of_nonneg_right (hmass i) (Real.rpow_nonneg hL.le _)
    unfold giantTwoSidedResidueFamilyAbsoluteEntry
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum fun p hp => (hx S nz k (C i p) (hC i p hp) (step i) (ζ i)
      (K i p) (K₀ i p) (hK i p hp).1 (hK i p hp).2).1 s).trans hsum

theorem giantCandidateUniformExpandedMoment_root_error (k ell : ℕ) (C₂ A : ℝ) (hA : 0 ≤ A)
    {γ q : ℝ} (hγ : 0<γ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      ∀ (I : Type u) (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k))
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
  intro I patterns C step hstep X hX ζ K
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


theorem giantCandidateUniformWeightedRootTransfer (k ell m₀ : ℕ)
    (C₁ C₂ G : ℝ) (hG : 0 ≤ G) {γ q : ℝ} (hγ : 0<γ) (hq0 : 0<q) (hq1 : q<1) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      ∀ (I : Type u) (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ) ≤ (Real.log x)^C₂) →
      ∀ (ζ : Fin n → ℝ) (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell)
        (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
      ∀ X : ℝ,x^γ ≤ X →
        ‖giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K
            (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X) -
          (((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ):ℂ)*giantTwoSidedExpandedIndependentMoment patterns C step q ζ K‖ /
            ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) ≤ (Real.log x)^(-G*(n:ℝ)) := by
  obtain ⟨B,_hB,hpaths⟩ := giantCandidateUniformResidueExpandedRoot_pathMass_eventually.{u}
    ell m₀ hq0 hq1 C₁
  let D := max (C₁+B) 0
  have hD : 0 ≤ D := le_max_right _ _
  have hA : 0 ≤ D+G+1 := by linarith
  filter_upwards [giantCandidateUniformExpandedMoment_root_error.{u} k ell C₂ (D+G+1) hA
      hγ hq0.le hq1.le,hpaths,giantCandidateRootError_absorb hD hG hγ,
    giantCandidateRootInterval_budget hγ,Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x herr hmass habs hinterval hlog
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro I patterns C hC step hstep ζ K K₀ hK hKmass X hX
  let n := giantTwoSidedSourceMomentLength x
  let L := Real.log x
  let length := ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)
  let E := 2*L^(-(D+G+1)*(n:ℝ))+Real.exp (-γ*L/4)
  have hlength : 0<length := (Real.exp_pos _).trans_le (hinterval X hX).2
  have hL : 0<L := zero_lt_one.trans_le hlog
  have hE : 0 ≤ E := add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _)) (Real.exp_nonneg _)
  have hmass' : giantTwoSidedResidueExpandedRootMass patterns C step q ζ K ≤ L^(D*(n:ℝ)) := by
    calc
      _ ≤ (L^(C₁+B))^n := hmass S nz I k n (giantTwoSidedSourceMomentLength_pos hL).ne'
        patterns C hC step ζ K K₀ hK hKmass
      _ ≤ (L^D)^n := pow_le_pow_left₀ (Real.rpow_nonneg hL.le _)
        (Real.rpow_le_rpow_of_exponent_le hlog (le_max_left _ _)) _
      _ = _ := (Real.rpow_mul_natCast hL.le D n).symm
  apply (div_le_iff₀ hlength).mpr
  calc
    _ ≤ E*length*giantTwoSidedResidueExpandedRootMass patterns C step q ζ K :=
      herr S nz I patterns C step hstep X hX ζ K
    _ ≤ E*length*L^(D*(n:ℝ)) := mul_le_mul_of_nonneg_left hmass' (mul_nonneg hE hlength.le)
    _ = length*(E*L^(D*(n:ℝ))) := by ring
    _ ≤ length*L^(-G*(n:ℝ)) := mul_le_mul_of_nonneg_left habs hlength.le
    _ = _ := by ring


end
end ArtinMatthews
