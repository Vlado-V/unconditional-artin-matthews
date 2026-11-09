module

public import ArtinMatthews.MarkedRootArcMajorantIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! A single finite family of intervals for the literal positive first/beta
bad-root majorant. Its coefficient mass is exactly the proved complexity. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section
variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ)
  (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) (d₀ Y : ℝ)

abbrev MarkedPhysicalFirstArcBase :=
  (markedRawDyadicOmissions source d₀) × ↥(Finset.Icc 1 ⌊Y^(1/5 : ℝ)⌋₊)

def markedPhysicalFirstArcFrequency (p : MarkedPhysicalFirstArcBase e x source d₀ Y) : ℕ :=
  markedSourceCopiedProduct (markedRawNumericActive source) p.1.1*p.2.1

abbrev MarkedPhysicalFirstArcIndex :=
  Σ p : MarkedPhysicalFirstArcBase e x source d₀ Y,
    ↥(markedRootArcCenters (markedPhysicalFirstArcFrequency e x source d₀ Y p))

abbrev MarkedPhysicalBetaArcTrials (p : Finset J × J) :=
  (markedRawDirtyFullTrials e x source (p.1.erase p.2)) ×
    (markedRawDirtyFullTrials e x source (p.1.erase p.2))

def markedPhysicalBetaArcFrequency (p : Finset J × J)
    (t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x)
    (v : MarkedPhysicalBetaArcTrials e x source p) : ℤ :=
  (v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t

abbrev MarkedPhysicalBetaArcIndex :=
  Σ p : Finset J × J,
    Σ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
      Σ v : MarkedPhysicalBetaArcTrials e x source p,
        ↥(markedRootArcCenters (markedPhysicalBetaArcFrequency e x source p t v).natAbs)

abbrev MarkedPhysicalBadArcIndex :=
  MarkedPhysicalFirstArcIndex e x source d₀ Y ⊕ MarkedPhysicalBetaArcIndex e x source

def markedPhysicalBadArcLower : MarkedPhysicalBadArcIndex e x source d₀ Y → ℝ
  | .inl ⟨p,k⟩ => markedRootArcLower (markedPhysicalFirstArcFrequency e x source d₀ Y p)
      (Y^(-7/10 : ℝ)) k.1
  | .inr ⟨p,t,v,k⟩ => markedRootArcLower (markedPhysicalBetaArcFrequency e x source p t v).natAbs
      (100*Real.exp (-((Real.log x)^(e p.2)))) k.1

def markedPhysicalBadArcUpper : MarkedPhysicalBadArcIndex e x source d₀ Y → ℝ
  | .inl ⟨p,k⟩ => markedRootArcUpper (markedPhysicalFirstArcFrequency e x source d₀ Y p)
      (Y^(-7/10 : ℝ)) k.1
  | .inr ⟨p,t,v,k⟩ => markedRootArcUpper (markedPhysicalBetaArcFrequency e x source p t v).natAbs
      (100*Real.exp (-((Real.log x)^(e p.2)))) k.1

def markedPhysicalBadArcCoefficient : MarkedPhysicalBadArcIndex e x source d₀ Y → ℝ
  | .inl _ => 1
  | .inr ⟨p,t,v,_⟩ =>
      if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
        if v.1.1=v.2.1 then 0 else
          markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
            Real.exp (-((Real.log x)^(e p.2))/4)
      else 0

theorem markedPhysicalBadArc_bounds (i : MarkedPhysicalBadArcIndex e x source d₀ Y) :
    0 ≤ markedPhysicalBadArcLower e x source d₀ Y i ∧
      markedPhysicalBadArcUpper e x source d₀ Y i ≤ 1 := by
  cases i with
  | inl i => rcases i with ⟨p,k⟩; exact ⟨le_max_left _ _,min_le_left _ _⟩
  | inr i => rcases i with ⟨p,t,v,k⟩; exact ⟨le_max_left _ _,min_le_left _ _⟩

theorem markedPhysicalBadArcCoefficient_nonneg
    (hμ : ∀ I : Finset J,∀ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ I) => e j.1) x,
      0 ≤ markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x t)
    (i : MarkedPhysicalBadArcIndex e x source d₀ Y) :
    0 ≤ markedPhysicalBadArcCoefficient e x source d₀ Y i := by
  cases i with
  | inl i => norm_num [markedPhysicalBadArcCoefficient]
  | inr i =>
    rcases i with ⟨p,t,v,k⟩
    dsimp only [markedPhysicalBadArcCoefficient]
    split_ifs <;> first | exact le_rfl | exact div_nonneg (hμ p.1 t) (Real.exp_pos _).le

theorem markedPhysicalBadArcCoefficient_sum :
    (∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
      markedPhysicalBadArcCoefficient e x source d₀ Y i) =
      markedRawBadRootArcComplexity e x d₀ Y source := by
  rw [Fintype.sum_sum_type]
  unfold markedRawBadRootArcComplexity
  congr 1
  · rw [Fintype.sum_sigma]
    change (∑ p : MarkedPhysicalFirstArcBase e x source d₀ Y,
      ∑ _k : ↥(markedRootArcCenters (markedPhysicalFirstArcFrequency e x source d₀ Y p)), (1 : ℝ)) = _
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_coe, markedRootArcCenters_card]
    unfold markedRawFirstRootArcComplexity markedFirstRootArcComplexity
      markedPhysicalFirstArcFrequency
    simp only [Nat.cast_add, Nat.cast_one, Int.natAbs_natCast]
  · simp only [Fintype.sum_sigma, markedPhysicalBadArcCoefficient]
    unfold markedRawBetaRootArcComplexity
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
    · simp only [ite_eq_left hp]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [markedPairRootArcComplexity, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v.1.1=v.2.1
      · simp [hv]
      · simp only [ite_eq_right hv]
        change (∑ _k : ↥(markedRootArcCenters
          (markedPhysicalBetaArcFrequency e x source p t v).natAbs),
          markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
            Real.exp (-((Real.log x)^(e p.2))/4)) = _
        calc
          _ = ∑ _k ∈ markedRootArcCenters
            (markedPhysicalBetaArcFrequency e x source p t v).natAbs,
            markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
              Real.exp (-((Real.log x)^(e p.2))/4) :=
            Finset.sum_coe_sort _ (fun _ : ℤ =>
              markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
                Real.exp (-((Real.log x)^(e p.2))/4))
          _ = _ := by
            simp only [Finset.sum_const, nsmul_eq_mul, markedRootArcCenters_card,
              Nat.cast_add, Nat.cast_one, markedPhysicalBetaArcFrequency]
            ring
    · simp [hp]

theorem markedPhysicalBadArcFamily_eq {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hfirst : Y^(-7/10 : ℝ) < (1/2 : ℝ))
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) < (1/2 : ℝ)) :
    (∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
      if r ∈ Set.Icc (markedPhysicalBadArcLower e x source d₀ Y i)
          (markedPhysicalBadArcUpper e x source d₀ Y i) then
        markedPhysicalBadArcCoefficient e x source d₀ Y i else 0) =
      markedRawBadRootArcMajorant e x d₀ Y source (r : AddCircle (1 : ℝ)) := by
  rw [Fintype.sum_sum_type, markedRawBadRootArcMajorant,
    markedRawFirstRootArcMajorant_intervals source d₀ Y hfirst hr₀ hr₁,
    markedRawBetaRootArcMajorant_intervals e x source hr₀ hr₁ hbeta]
  congr 1
  · simp only [Fintype.sum_sigma, markedPhysicalBadArcLower, markedPhysicalBadArcUpper,
      markedPhysicalBadArcCoefficient, markedPhysicalFirstArcFrequency]
    apply Finset.sum_congr rfl
    intro p _
    calc
      _ = ∑ k ∈ markedRootArcCenters
        (markedSourceCopiedProduct (markedRawNumericActive source) p.1.1*p.2.1)
        , if r ∈ Set.Icc
          (markedRootArcLower (markedSourceCopiedProduct (markedRawNumericActive source) p.1.1*p.2.1)
            (Y^(-7/10 : ℝ)) k)
          (markedRootArcUpper (markedSourceCopiedProduct (markedRawNumericActive source) p.1.1*p.2.1)
            (Y^(-7/10 : ℝ)) k) then (1 : ℝ) else 0 := Finset.sum_coe_sort _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [markedRootArcClippedInterval]
        split_ifs <;> simp_all [Set.mem_Icc]
  · simp only [Fintype.sum_sigma, markedPhysicalBadArcLower, markedPhysicalBadArcUpper,
      markedPhysicalBadArcCoefficient]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
    · simp only [ite_eq_left hp]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v.1.1=v.2.1
      · simp [hv]
      · simp only [ite_eq_right hv, markedPhysicalBetaArcFrequency]
        rw [Finset.mul_sum, Finset.sum_div]
        change (∑ k : ↥(markedRootArcCenters
          ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs),
          if r ∈ Set.Icc
            (markedRootArcLower
              ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs
              (100*Real.exp (-((Real.log x)^(e p.2)))) k.1)
            (markedRootArcUpper
              ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs
              (100*Real.exp (-((Real.log x)^(e p.2)))) k.1) then
            markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
              Real.exp (-((Real.log x)^(e p.2))/4) else 0) = _
        calc
          _ = ∑ k ∈ markedRootArcCenters
            ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs,
            if r ∈ Set.Icc
              (markedRootArcLower
                ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs
                (100*Real.exp (-((Real.log x)^(e p.2)))) k)
              (markedRootArcUpper
                ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs
                (100*Real.exp (-((Real.log x)^(e p.2)))) k) then
                markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t /
                  Real.exp (-((Real.log x)^(e p.2))/4) else 0 := Finset.sum_coe_sort _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k _
            simp only [markedRootArcClippedInterval]
            split_ifs <;> simp_all [Set.mem_Icc]
            all_goals split_ifs <;> simp_all
            all_goals linarith
    · simp [hp]

end
end ArtinMatthews
