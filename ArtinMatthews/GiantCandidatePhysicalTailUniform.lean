module

public import ArtinMatthews.GiantCandidatePhysicalAbsolutePairing
public import ArtinMatthews.GiantTwoSidedPhysicalReciprocalTail
public import ArtinMatthews.GiantTwoSidedPhysicalMellinPairing
public import ArtinMatthews.GiantTwoSidedEndpointBudget
public import ArtinMatthews.GiantTwoSidedRootMargin


set_option backward.privateInPublic true
@[expose] public section

/-! The selected residual pattern type can vary with the scale. The single
pattern Schur estimate supplies a common exponent and threshold before the
family is introduced. The physical absolute mass uses those same bounds. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

universe u

theorem giantCandidatePatternFamily_absolute_rows_columns_uniform_eventually (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (C₁ : ℝ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ x : ℝ in atTop, ∀ (I : Type u) (S : Finset (GiantCandidateGroupIndex x)),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν∈patterns,∀ i,(C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν∈patterns,0≤K₀ ν ∧ ∀ b c a,‖K ν b c a‖≤K₀ ν) →
        (∑ ν∈patterns,K₀ ν) ≤ (Real.log x)^C₁ → ∀ Z Z' : Finset ℕ,
        (∀ s : GiantTwoSidedEndpointState P (k+ell) Z,
          (∑ t : GiantTwoSidedEndpointState P (k+ell) Z',∑ ν∈patterns,giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ (K ν)) s t) ≤ (Real.log x)^(C₁+A)) ∧
        (∀ t : GiantTwoSidedEndpointState P (k+ell) Z',
          (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,∑ ν∈patterns,giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ (K ν)) s t) ≤ (Real.log x)^(C₁+A)) := by
  obtain ⟨A,hA,h⟩ := giantCandidatePattern_absolute_rows_columns_eventually ell m₀ hq hq1
  refine ⟨A,hA,?_⟩
  filter_upwards [h,Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hx hL
  intro I S
  dsimp only
  intro k patterns C hC step ζ K K₀ hK hmass Z Z'
  have hsum : (∑ ν∈patterns,K₀ ν*(Real.log x)^A) ≤ (Real.log x)^(C₁+A) := by
    rw [← sum_mul,Real.rpow_add hL]
    exact mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hL.le _)
  constructor
  · intro s
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2 Z Z').1 s).trans hsum
  · intro t
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2 Z Z').2 t).trans hsum

theorem giantCandidatePhysicalFamily_absolute_pairing_uniform_eventually (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (C₁ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, ∀ (I : Type u) (S : Finset (GiantCandidateGroupIndex x)),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν ∈ patterns, ∀ i, (C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν ∈ patterns, 0 ≤ K₀ ν ∧ ∀ b c a, ‖K ν b c a‖ ≤ K₀ ν) →
        (∑ ν ∈ patterns, K₀ ν) ≤ (Real.log x)^C₁ → ∀ (Z : Finset ℕ)
        (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ),
        giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K f g ≤
          (Real.log x)^(C₁+A) *
            Real.sqrt (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
              markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖f s.val.1.val‖^2) *
            Real.sqrt (∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
              markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖g t‖^2) := by
  obtain ⟨A,hA,hrows⟩ := giantCandidatePatternFamily_absolute_rows_columns_uniform_eventually.{u} ell m₀ hq hq1 C₁
  refine ⟨A,hA,?_⟩
  filter_upwards [hrows, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hx hL
  intro I S
  dsimp only
  intro k patterns C hC step ζ K K₀ hK hmass Z f g
  have h := hx I S k patterns C hC step ζ K K₀ hK hmass Z Z
  exact giantTwoSidedPhysicalFamilyAbsolutePairing_le_of_rows_columns patterns C step q ζ K
    (Real.rpow_nonneg hL.le (C₁+A)) h.1 h.2 f g

theorem giantCandidatePhysicalFamily_absolute_tail_uniform_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (χ : DirichletCharacter ℂ m) {γ τ q : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hq : 0 < q) (hq1 : q < 1) (j ell m₀ : ℕ) (hj : 0 < j) (C₁ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, ∀ (I : Type u) (S : Finset (GiantCandidateGroupIndex x)),
      let P (i : S) := giantCandidateGroup x i.val
      let L := Real.log x
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν ∈ patterns, ∀ i, (C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν ∈ patterns, 0 ≤ K₀ ν ∧ ∀ b c a, ‖K ν b c a‖ ≤ K₀ ν) →
        (∑ ν ∈ patterns, K₀ ν) ≤ L^C₁ → ∀ X : ℝ, 1 ≤ X → X ≤ x^(1/τ) →
      let roots := giantTwoSidedRootInterval X
      let Z := giantTwoSidedRootSlice X
      ∀ (u v : ℕ → ℂ), (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
      let d (r : ℕ) := (giantTwoSidedEndpointDamping P (k+ell) q r : ℂ)
      let f (r : ℕ) := d r * (if r ∈ roots then u r * conj (giantCandidateFirstEndpoint e ε x r) else 0)
      let g (t : GiantTwoSidedEndpointState P (k+ell) Z) := d t.val.1.val *
        (v t.val.1.val * (χ t.val.1.val * giantCandidateAllocationCore (giantCandidateFullPrimes x)
          (univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j t.val.1.val))
      giantTwoSidedPhysicalMellinAbsoluteMass patterns C step q ζ K f g ≤
        L^(C₁+A+((j*j : ℕ) : ℝ)+2) := by
  obtain ⟨A,hA,habs⟩ := giantCandidatePhysicalFamily_absolute_pairing_uniform_eventually.{u} ell m₀ hq hq1 C₁
  let B : ℝ := ((j*j : ℕ) : ℝ)/2+1
  refine ⟨A,hA,?_⟩
  filter_upwards [habs, giantCandidateTwoSidedEndpointNorm_budget_eventually e he hε hεq χ hγ hτ
    (R := 4) (by norm_num) ⟨hq.le,hq1.le⟩ j hj,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hpair hnorm hL
  intro I S P L k patterns C hC step ζ K K₀ hK hmass X hX hXhi roots Z u v hu hv d f g
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let σ := markedPhysicalMass (fun i => bandReciprocalMass (P i)) (k+ell)
  let F₀ (r : ℕ) := conj (giantCandidateFirstEndpoint e ε x r)
  let G₀ (r : ℕ) := χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
    (univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r
  let F (r : ℕ) := if r ∈ roots then u r * F₀ r else 0
  let left (ω : ℝ) (r : ℕ) := ((X/(r : ℝ) : ℝ) : ℂ) * primeExtractionMellinPhase (-ω) r * F r
  let fω (ω : ℝ) (r : ℕ) := ((X/(r : ℝ) : ℝ) : ℂ) * primeExtractionMellinPhase (-ω) r * f r
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hZ : Z ⊆ Finset.Ioc 0 ⌊4*X⌋₊ := by
    intro r hr
    obtain ⟨hr0,hr1⟩ := Finset.mem_Ioc.mp hr
    have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 3*X)).le
    exact Finset.mem_Ioc.mpr ⟨hr0,hr1.trans (Nat.le_floor (by linarith))⟩
  obtain ⟨_,hNF,hNG⟩ := hnorm S (k+ell) X hX hXhi Z hZ
  have hFmono (ω : ℝ) : ∀ r ∈ Z, ‖left ω r‖ ≤ ‖F₀ r‖ := by
    intro r _
    by_cases hr : r ∈ roots
    · have hlo : X ≤ (r : ℝ) := (giantTwoSidedRootInterval_bounds hr).1
      have hr0 : 0 < (r : ℝ) := hX0.trans_le hlo
      have hratio0 : 0 ≤ X/(r : ℝ) := div_nonneg hX0.le hr0.le
      have hratio1 : X/(r : ℝ) ≤ 1 := (div_le_iff₀ hr0).2 (by simpa only [one_mul] using hlo)
      simp only [left,F,hr,ite_true,norm_mul,Complex.norm_real,Real.norm_of_nonneg hratio0,
        primeExtractionMellinPhase_norm,mul_one]
      exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hratio1).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hu r hr))
    · simp only [left,F,hr,ite_false,mul_zero,norm_zero,norm_nonneg]
  have hfv (ω : ℝ) (r : ℕ) : fω ω r = d r * left ω r := by
    change ((X/(r : ℝ) : ℝ) : ℂ) * primeExtractionMellinPhase (-ω) r * (d r * F r) = _
    dsimp only [left]
    ring
  have hFE (ω : ℝ) : Real.sqrt (∑ s : State, σ * ‖fω ω s.val.1.val‖^2) ≤ Real.sqrt X * L^B := by
    simp_rw [hfv]
    exact (giantTwoSidedEndpointNorm_mono P (k+ell) Z q (hFmono ω)).trans hNF
  have hGE : Real.sqrt (∑ t : State, σ * ‖g t‖^2) ≤ Real.sqrt X * L^B :=
    (giantTwoSidedEndpointNorm_mul_le P (k+ell) Z q v G₀ hv).trans hNG
  have hscaled (ω : ℝ) : giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K (fω ω) g ≤
      X * L^(C₁+A+((j*j : ℕ) : ℝ)+2) := by
    have h := hpair I S k patterns C hC step ζ K K₀ hK hmass Z (fω ω) g
    refine h.trans ?_
    have hcost : 0 ≤ L^(C₁+A) := Real.rpow_nonneg hL.le _
    have hscale : 0 ≤ Real.sqrt X * L^B := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)
    calc
      _ ≤ L^(C₁+A) * (Real.sqrt X * L^B) * (Real.sqrt X * L^B) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hFE ω) hcost) hGE (Real.sqrt_nonneg _)
          (mul_nonneg hcost hscale)
      _ = (Real.sqrt X)^2 * (L^(C₁+A) * L^B * L^B) := by ring
      _ = _ := by
        rw [Real.sq_sqrt hX0.le, ← Real.rpow_add hL, ← Real.rpow_add hL]
        congr 2
        dsimp only [B]
        ring
  rw [giantTwoSidedPhysicalMellinAbsoluteMass,
    giantTwoSidedPhysicalFamilyAbsolutePairing_reciprocal_eq patterns C step q ζ K hX0 0 f g]
  change X⁻¹ * giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K (fω 0) g ≤ _
  calc
    _ ≤ X⁻¹ * (X * L^(C₁+A+((j*j : ℕ) : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left (hscaled 0) (inv_nonneg.mpr hX0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hX0.ne', one_mul]

end
end ArtinMatthews
