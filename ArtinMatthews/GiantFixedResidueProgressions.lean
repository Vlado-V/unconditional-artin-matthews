module

public import ArtinMatthews.GiantFixedResidueArrayAsymptotic
public import ArtinMatthews.GiantActualRoughSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ordinary and giant first moments in each fixed unit residue.
The marked primes and giant primes eventually exceed the fixed modulus. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Asymptotics
noncomputable section

theorem giantFixedResidue_small_modulus_eventually (M : ℕ) :
    ∀ᶠ x : ℝ in atTop,(M:ℝ)<Real.exp ((Real.log x)^(1/10:ℝ)) :=
  (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop)).eventually
      (eventually_gt_atTop (M:ℝ))

theorem giantFixedResidue_large_prime_coprime {M p : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hMp : (M:ℝ)<p) : p.Coprime M :=
  hp.coprime_iff_not_dvd.mpr (fun hd => (not_lt_of_ge (Nat.cast_le.mpr (Nat.le_of_dvd hM hd))) hMp)

private theorem giantFixedResidue_actual_window_progression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M r₀ : ℕ) (hM : 0 < M) (hr₀ : r₀.Coprime M)
    (e : ι → ℝ) (he : ∀ i,(1/10:ℝ)<e i ∧ e i<1/5)
    (hinj : Function.Injective e) (G : ℝ → Finset ℕ) (c gexp A : ℝ)
    (hc0 : 0≤c) (hc1 : c≤1) (hlevel : c+gexp<1)
    (hG : ∀ᶠ x : ℝ in atTop,GiantFixedResidueWindowAsymptoticBounds M (G x)
      (fun i => markedLogPowerBand (e i) x) (1/10) gexp x)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0) (hΦ0 : ∀ t,0≤Φ t) :
    (fun x : ℝ => giantFixedResidueWindowDiscrepancy M r₀ (G x)
      (fun i => markedLogPowerBand (e i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) (fun _ => 1)
      Φ T x ⌊x ^ c⌋₊) =o[atTop] (fun x : ℝ => x*(Real.log x)^(-A)) := by
  have he0 : ∀ i,0<e i := fun i => lt_trans (by norm_num) (he i).1
  have hb := marked_actual_band_structure_eventually e he0 hinj
    (fun i => (he i).1.le) (fun i => (he i).2.le)
  have hband : ∀ᶠ x : ℝ in atTop,MarkedArrayAsymptoticBounds
      (fun i => markedLogPowerBand (e i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) (fun _ => 1)
      (1/10) (1/5) (Real.log 2/2) (Fintype.card ι)
      (markedArrayReciprocalConstant (Fintype.card ι)) x := by
    filter_upwards [hb,marked_actual_array_reciprocal_mass_eventually e he0 hinj
      (fun _ => 1) (fun _ => Or.inl rfl)] with x hs hm
    exact {
      disjoint := hs.1
      prime := fun i p hp => (hs.2.1 i p hp).1
      lower := fun i p hp => (hs.2.1 i p hp).2.1
      upper := fun i p hp => (hs.2.1 i p hp).2.2
      normalizer := hs.2.2.1
      primeMass := hs.2.2.2
      coefficientMass := hm }
  have hc : ∀ᶠ x : ℝ in atTop,∀ i p,p∈markedLogPowerBand (e i) x → p.Coprime M := by
    filter_upwards [hb,giantFixedResidue_small_modulus_eventually M] with x hs hlarge
    intro i p hp
    exact giantFixedResidue_large_prime_coprime hM (hs.2.1 i p hp).1
      (hlarge.trans_le (hs.2.1 i p hp).2.1)
  exact giantFixedResidue_array_progression_all_log_isLittleO M r₀ hM hr₀ G
    (fun x i => markedLogPowerBand (e i) x)
    (fun x i => bandReciprocalMass (markedLogPowerBand (e i) x)) (fun _ => 1) (fun _ => Nat.one_pos)
    (1/10) (1/5) (1/4) c gexp (Real.log 2/2) (Fintype.card ι)
    (markedArrayReciprocalConstant (Fintype.card ι)) A
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc0 hc1 hlevel
    (by positivity) (Nat.cast_nonneg _) (markedArrayReciprocalConstant_pos _).le
    hband hc hG Φ hT hΦ hderiv hΦT hΦ0

theorem giantFixedResidue_actual_array_progression_isLittleO {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M r₀ : ℕ) (hM : 0 < M) (hr₀ : r₀.Coprime M)
    (e : ι → ℝ) (he : ∀ i,(1/10:ℝ)<e i ∧ e i<1/5)
    (hinj : Function.Injective e) (c A : ℝ) (hc0 : 0≤c) (hc1 : c<1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0) (hΦ0 : ∀ t,0≤Φ t) :
    (fun x : ℝ => giantFixedResidueProgressionDiscrepancy M r₀ (literalMarkedArrayWeight e x)
      (literalMarkedArrayMean e x) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x*(Real.log x)^(-A)) := by
  have hG : ∀ᶠ x : ℝ in atTop,GiantFixedResidueWindowAsymptoticBounds M ({1}:Finset ℕ)
      (fun i => markedLogPowerBand (e i) x) (1/10) 0 x := by
    apply Filter.Eventually.of_forall
    intro x
    refine ⟨fun p hp => Or.inl (Finset.mem_singleton.mp hp),
      ?_,?_,fun p hp => Or.inl (Finset.mem_singleton.mp hp),by simp,by simp⟩
    · intro p hp
      rw [Finset.mem_singleton.mp hp]
      exact Nat.coprime_one_left _
    · apply Finset.disjoint_left.mpr
      intro p hp hband
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hband
      exact (mem_markedLogPowerBand.mp hi).1.ne_one (Finset.mem_singleton.mp hp)
  have h := giantFixedResidue_actual_window_progression M r₀ hM hr₀ e he hinj
    (fun _ => {1}) c 0 A hc0 hc1.le (by simpa only [add_zero] using hc1)
    hG Φ hT hΦ hderiv hΦT hΦ0
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hd
  unfold giantFixedResidueWindowDiscrepancy literalMarkedArrayWeight literalMarkedArrayMean divisorWeight
  rw [representedArrayEulerMean_one _ (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) _ hd]
  simp only [giantWindowDivisorCount,Finset.sum_singleton,one_dvd,ite_true,Nat.cast_one,div_one,one_mul,pow_one]

theorem giantFixedResidue_actual_giant_progression_isLittleO {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M r₀ : ℕ) (hM : 0 < M) (hr₀ : r₀.Coprime M)
    (e : ι → ℝ) (he : ∀ i,(1/10:ℝ)<e i ∧ e i<1/5)
    (hinj : Function.Injective e) (ε c A : ℝ)
    (hε : 0<ε) (hεq : ε<1/4) (hc0 : 0≤c) (hc1 : c<ε/2)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0) (hΦ0 : ∀ t,0≤Φ t) (hΦzero : Φ 0=0) :
    (fun x : ℝ => giantFixedResidueProgressionDiscrepancy M r₀
      (fun u => (giantPrimeFactors u x ε).card*literalMarkedArrayWeight e x u)
      (giantPrimeReciprocalSum x ε*literalMarkedArrayMean e x) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x*(Real.log x)^(-A)) := by
  have hG : ∀ᶠ x : ℝ in atTop,GiantFixedResidueWindowAsymptoticBounds M (giantPrimeWindow x ε)
      (fun i => markedLogPowerBand (e i) x) (1/10) (1-ε/2) x := by
    filter_upwards [giant_window_structure_eventually e (fun i => lt_trans (he i).2 (by norm_num))
      (by norm_num : (1/10:ℝ)<1) hε hεq,giantFixedResidue_small_modulus_eventually M] with x hs hlarge
    exact ⟨fun ell hell => Or.inr (hs.1 ell hell),
      fun ell hell => giantFixedResidue_large_prime_coprime hM (hs.1 ell hell)
        (hlarge.trans_le (hs.2.2.1 ell hell)),
      hs.2.1,fun ell hell => Or.inr (hs.2.2.1 ell hell),hs.2.2.2.1,hs.2.2.2.2⟩
  have h := giantFixedResidue_actual_window_progression M r₀ hM hr₀ e he hinj
    (fun x => giantPrimeWindow x ε) c (1-ε/2) A hc0 (by linarith) (by linarith)
    hG Φ hT hΦ hderiv hΦT hΦ0
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [marked_array_disjoint_eventually e hinj,eventually_ge_atTop (0:ℝ)] with x hd hx
  unfold giantFixedResidueWindowDiscrepancy giantFixedResidueProgressionDiscrepancy
    literalMarkedArrayWeight literalMarkedArrayMean divisorWeight
  rw [representedArrayEulerMean_one _ (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) _ hd]
  simp only [pow_one]
  simp_rw [giantWindowDivisorCount_test_eq_actual Φ hΦzero
    (fun u => ∏ i,bandWeight (markedLogPowerBand (e i) x)
      (bandReciprocalMass (markedLogPowerBand (e i) x)) u) hx]
  rfl

end
end ArtinMatthews
