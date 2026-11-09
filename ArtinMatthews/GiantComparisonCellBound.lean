module

public import ArtinMatthews.GiantComparisonCellIdentity
public import ArtinMatthews.GiantComparisonOccupiedCell
public import ArtinMatthews.GiantComparisonScale
public import ArtinMatthews.GiantComparisonShiftBound
public import ArtinMatthews.GiantComparisonCutoffSaving
public import ArtinMatthews.GiantComparisonArcCore
public import ArtinMatthews.GiantComparisonArcScales


set_option backward.privateInPublic true
@[expose] public section

/-! The actual per-cell estimate uses the centered endpoint energy only
on the literal rational Mellin band. Minor arcs and the Mellin tail
are estimated uniformly in all occupied cells. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem comparison_first_endpoint_real {I : Type*} [Fintype I]
    (e : I → ℝ) (ε x : ℝ) (n : ℕ) :
    conj (giantCandidateFirstEndpoint e ε x n) = giantCandidateFirstEndpoint e ε x n := by
  simp only [giantCandidateFirstEndpoint, giantMarkedCenteredCore, map_mul, Complex.conj_ofReal]

private theorem comparison_rows_floor_eventually (hi ε : ℝ) (hhi : 0 ≤ hi) (hε : ε < 1) :
    ∀ᶠ x : ℝ in atTop, hi*x^(1+ε) ≤ (⌊x^2⌋₊:ℝ) := by
  have ht := (tendsto_rpow_atTop (show 0 < 1-ε by linarith)).eventually_ge_atTop (2*hi)
  filter_upwards [ht, eventually_ge_atTop (2:ℝ)] with x ht hx
  have hx0 : 0 < x := by linarith
  have hpow : x^(1-ε)*x^(1+ε) = x^2 := by
    rw [← Real.rpow_add hx0, show 1-ε+(1+ε)=2 by ring, Real.rpow_two]
  have hhalf := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hx0.le (1+ε))
  rw [hpow] at hhalf
  have hfloor := Nat.lt_floor_add_one (x^2)
  have hx2 : 2 ≤ x^2 := by nlinarith
  linarith only [hhalf,hfloor,hx2]

private theorem comparison_arcExponent_nonneg (m : ℕ) (C₀ v₀ d E : ℝ)
    (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hE : 0 ≤ E) :
    0 ≤ giantComparisonArcExponent m C₀ v₀ d E := by
  unfold giantComparisonArcExponent idealMinorCutoffExponent idealGroupedBudgetExponent
  have h₁ : 0 ≤ Real.log (m.factorial:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos m)
  have h₂ : 0 ≤ Real.log (max 1 v₀⁻¹) := Real.log_nonneg (le_max_left _ _)
  have h := mul_nonneg hC₀ (add_nonneg h₁ (mul_nonneg (Nat.cast_nonneg m) h₂))
  linarith

theorem giantCandidateComparisonWeightedCell_log_saving_of_arc
    {I : Type*} [Fintype I] (e : I → ℝ)
    (he : ∀ i, (1/10:ℝ) < e i ∧ e i < 1/5)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {M : ℕ} (χ : DirichletCharacter ℂ M) {γ : ℝ} (hγ : 0 < γ)
    (j : ℕ) (hj : 0 < j) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (Ψ ψL ψR : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hψL : ContDiff ℝ ∞ ψL) (hψR : ContDiff ℝ ∞ ψR)
    (hsL : Function.support ψL ⊆ Set.Icc (a/2) (25*(b+1)+a/2))
    (hsR : Function.support ψR ⊆ Set.Icc (a/2) (25*(b+1)+a/2))
    (hreal : ∀ t, conj (ψL t) = ψL t)
    (hplateau : ∀ t ∈ Set.Icc a (25*(b+1)), ψL t = (t:ℂ)⁻¹ ∧ ψR t = 1)
    (m : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hArc : ∀ (c A : ℝ), 0 ≤ c → 0 ≤ A → ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x)) (g : GiantCandidatePerformedSmall S)
      (t : S → ℕ), (∀ i, t i ≤ m+1) →
      t (giantCandidatePerformedSplitEquiv S (.inl g)) = 1 →
      ∀ u : ((i : S) → Fin (t i) → ℕ) → ℂ, (∀ l, ‖u l‖ ≤ 1) →
      (∀ l l', (∀ i, i ≠ giantCandidatePerformedSplitEquiv S (.inl g) → l i = l' i) → u l = u l') →
      ∀ (Y H σ : ℝ), x ≤ Y → Y ≤ x^(1+ε/4) →
      Real.exp ((Real.log x)^(19/50:ℝ)) ≤ H → H ≤ Real.exp (Real.log x/2) →
      (Real.log x)*(Y/H) = x*(Real.log x)^(c+1) → |σ| ≤ (Real.log x)^2 →
      ∀ r : ℚ, (r.den:ℝ) ≤ (Real.log x)^c →
      (∫ τ in Set.Icc (-((Real.log x)*(Y/H))) ((Real.log x)*(Y/H)),
        ‖(Y:ℂ)⁻¹ * giantComparisonMellinPolynomial
          (giantComparisonCutoffRows Y (a/2) (25*(b+1)+a/2))
          (giantComparisonArcTwist (r:ℝ)
            (giantCandidateComparisonLeftEndpoint e ε x Y σ ψL
              (fun i : S => giantCandidateGroup x i.val) t (fun _ => q) u)) τ‖^2) ≤
        (Real.log x)^(-A)) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)),
      Nonempty (GiantCandidatePerformedSmall S) →
      ∀ {k : ℕ} (A B : Finset (GiantCandidatePerformedBig S × Fin k)), A.Nonempty → B.Nonempty →
      (∀ g, (idealResidualCopied (some (A,B)) g).card ≤ m) →
      ∀ (Q : ℕ) (h ξ : ℝ), 0 < h → Real.exp h ≤ 2 → 0 < ξ →
      let PB := giantCandidatePerformedBigBand S
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (i : GiantComparisonCellIndex (idealResidualBands PB A) h Q)
        (l : GiantComparisonCellIndex (idealResidualBands PB B) h Q),
      ‖giantCandidateComparisonWeightedCell S (ell:=1) A B χ (giantCandidateFirstEndpoint e ε x)
        (giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j) Ψ q ⌊x^2⌋₊ ξ i l‖ ≤
        (Real.log x)^(-E) := by
  let C₀ := giantCandidateGroupLogRate
  let v₀ := Real.log 2/2
  let lo := a/2
  let hi := 25*(b+1)+a/2
  let R₀ := max 1 hi
  let Yexp := 1+ε/4
  have hC₀ : 0 ≤ C₀ := by unfold C₀ giantCandidateGroupLogRate; positivity
  have hv₀ : 0 < v₀ := by unfold v₀; positivity
  have hlo : 0 < lo := by unfold lo; positivity
  have hhi : lo ≤ hi := by dsimp [lo,hi]; linarith
  have hYexp : 0 < Yexp := by unfold Yexp; positivity
  obtain ⟨K,hK,D',hD',hmoment⟩ := giantCandidateComparisonEndpointPower_eventually
    e (fun i => ⟨by linarith [(he i).1], by linarith [(he i).2]⟩) hε hεq χ hγ hYexp
    (le_max_left 1 hi) j hj m 1 ψL ψR hψL.continuous
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsL) hψR.continuous
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsR)
  let D := D'+1
  let E₁ := E+1
  let c := giantComparisonArcExponent m C₀ v₀ (45/100) (E₁+D+1)
  let A₁ := 2*c+D+2*E₁+4+2
  have hD : 0 ≤ D := by unfold D; linarith
  have hE₁ : 0 ≤ E₁ := by unfold E₁; linarith
  have hc : 0 ≤ c := comparison_arcExponent_nonneg m C₀ v₀ _ _ hC₀ (by norm_num) (by positivity)
  have hA₁ : 0 ≤ A₁ := by unfold A₁; positivity
  have hC : 0 ≤ (m:ℝ)*C₀ := by positivity
  filter_upwards [hmoment, hArc c A₁ hc hA₁,
    giantCandidateComparisonOccupiedCell_eventually m,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateGroup_total_count_eventually,
    giantComparisonArcScales_eventually (40/100) (45/100) ((m:ℝ)*C₀) c ε
      (by norm_num) (by norm_num) hC hc hε hεq,
    Real.tendsto_log_atTop.eventually (giantComparisonNatShiftSum_log_saving m C₀ v₀
      (40/100) (45/100) lo hi D E₁ hC₀ hv₀ (by norm_num) (by norm_num) hlo hhi hD hE₁),
    Real.tendsto_log_atTop.eventually (giantComparisonNatCutoffSum_log_saving Ψ ha hsupp hΨ D E),
    comparison_rows_floor_eventually hi (ε/4) (hlo.le.trans hhi) (by linarith),
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (max K (2*Real.pi)))]
    with x hmom harc hcell hgeo hcard hscale hshift hcut hfloor hx hL
  intro S hsmall k A B hA hB hcap Q h ξ hh hhexp hξ PB P i l
  let L := Real.log x
  let C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
  let t (g : S) := 1+(C g).card
  let PA := idealResidualBands PB A
  let PB' := idealResidualBands PB B
  let U := giantComparisonCellOrigin h i.1.val
  let V := giantComparisonCellOrigin h l.1.val
  let Y := x*((U:ℝ)*(V:ℝ))
  let H := ((U:ℝ)*(V:ℝ))/L^c
  let Z := giantComparisonCutoffRows Y lo hi
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp (L^(6/25:ℝ))) (x^γ) j
  let s := giantCandidateComparisonCellTest S (ell:=1) A B B subset_union_right ξ l
  let u := giantCandidateComparisonCellTest S (ell:=1) A B A subset_union_left ξ i
  let s' := fun b => conj (s b)
  let f := giantComparisonCellIndexedFreeTest PA i
  let g := giantComparisonCellIndexedFreeTest PB' l
  let f' := fun a => f a*conj (χ (idealSelectedProduct a))
  let g' := fun a => g a*conj (χ (idealSelectedProduct a))
  let FL (σ : ℝ) := giantCandidateComparisonLeftEndpoint e ε x Y σ ψL P t (fun _ => q) s'
  let FR := giantCandidateComparisonRightEndpoint χ γ j x Y ψR P t (fun _ => q) u
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hK' : K ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hπ' : 2*Real.pi ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨hcapA,hcapB⟩ := giantComparisonCopied_cap A B hcap
  obtain ⟨hU,hUlo,hUhi,hUlog,hfS⟩ := hcell S A hA hcapA h hh hhexp i.1.val i.1.property
  obtain ⟨hV,hVlo,hVhi,hVlog,hgS⟩ := hcell S B hB hcapB h hh hhexp l.1.val l.1.property
  obtain ⟨hYlo,hYhi,hQ,hHlo,hHhi,hH,hHY,hT⟩ := hscale U V hUlo hVlo hUhi hVhi
  have hY1 : 1 ≤ Y := hx.le.trans hYlo
  have hY : 0 < Y := zero_lt_one.trans_le hY1
  have hZ : Z ⊆ Ioc 0 ⌊R₀*Y⌋₊ := giantComparisonCutoffRows_subset hY.le (le_max_right _ _)
  have hpos (n : ℕ) (hn : n ∈ Z) : 0 < n := ((mem_giantComparisonCutoffRows hY).mp hn).1
  have hZbounds (n : ℕ) (hn : n ∈ Z) : (n:ℝ) ∈ Set.Icc (lo*Y) (hi*Y) :=
    ⟨(le_div_iff₀ hY).mp ((mem_giantComparisonCutoffRows hY).mp hn).2.1,
      (div_le_iff₀ hY).mp ((mem_giantComparisonCutoffRows hY).mp hn).2.2⟩
  have hPB (g : GiantCandidatePerformedBig S) (p : ℕ) (hp : p ∈ PB g) : p.Prime :=
    (giantCandidateBigGroup_range hx hL1 hp).1
  have hPBmass (g : GiantCandidatePerformedBig S) : v₀ ≤ bandReciprocalMass (PB g) :=
    ((hgeo S).2.1 (giantCandidatePerformedSplitEquiv S (.inr g))).1.le
  have hPBdis : Pairwise (fun i j => Disjoint (PB i) (PB j)) := by
    intro i j hij
    exact (hgeo S).1 (fun he' =>
      hij (Sum.inr.inj ((giantCandidatePerformedSplitEquiv S).injective he')))
  have hPBcard : (Fintype.card (GiantCandidatePerformedBig S):ℝ) ≤ C₀*Real.log L :=
    (Nat.cast_le.mpr (giantCandidateComparisonBig_card_le S)).trans hcard
  have hs (b : (i:S) → Fin (t i) → ℕ) : ‖s' b‖ ≤ 1 := by
    dsimp only [s', s]
    rw [Complex.norm_conj]
    exact giantCandidateComparisonCellTest_norm_le S A B B subset_union_right hξ l b
  have hu (b : (i:S) → Fin (t i) → ℕ) : ‖u b‖ ≤ 1 :=
    giantCandidateComparisonCellTest_norm_le S A B A subset_union_left hξ i b
  have ht : ∀ i, t i ≤ m+1 := giantCandidateComparisonPerformedMark_cap S A B hcap
  have hf : ∀ a, ‖f' a‖ ≤ 1 := fun a => by
    dsimp only [f', f, giantComparisonCellIndexedFreeTest]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (giantComparisonCellFreeTest_norm_le PA h i.1.val i.2 a)
      (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hg : ∀ a, ‖g' a‖ ≤ 1 := fun a => by
    dsimp only [g', g, giantComparisonCellIndexedFreeTest]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (giantComparisonCellFreeTest_norm_le PB' h l.1.val l.2 a)
      (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hfs (a : IdealSelectedLabels PA) (ha : idealSelectedProduct a ∉ Ico U (U+4*U)) : f a = 0 :=
    hfS Q i.2 a ha
  have hgs (a : IdealSelectedLabels PB') (ha : idealSelectedProduct a ∉ Ico V (V+4*V)) : g a = 0 :=
    hgS Q l.2 a ha
  have hE₂ : K*Y*L^D' ≤ Y*L^D := by
    rw [show D = D'+1 from rfl, Real.rpow_add hLp, Real.rpow_one]
    calc
      _ ≤ L*Y*L^D' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK' hY.le)
        (Real.rpow_nonneg hLp.le _)
      _ = _ := by ring
  have henergy (σ : ℝ) :
      (∑ n ∈ Z, ‖FL σ n‖^2) ≤ Y*L^D ∧ (∑ n ∈ Z, ‖FR n‖^2) ≤ Y*L^D := by
    have hm := hmom S Y hY1 hYhi t (fun _ => q) ht (fun _ => ⟨hq,hq1⟩)
      s' u (fun b _ => hs b) (fun b _ => hu b) σ Z Z hZ hZ
    exact ⟨hm.1.trans hE₂, hm.2.trans hE₂⟩
  obtain ⟨sml⟩ := hsmall
  have htest (b b' : (i:S) → Fin (t i) → ℕ)
      (he' : ∀ i, i ≠ giantCandidatePerformedSplitEquiv S (.inl sml) → b i = b' i) :
      s' b = s' b' := by
    apply congrArg (starRingEnd ℂ)
    exact giantCandidateComparisonNumberedTest_small_independent S A B B subset_union_right _ sml he'
  have hsh (v : ℝ) (hv : v ∈ Set.Icc (-L) L) :
      ‖giantComparisonNatShiftSum PA PB'
        (fun a => f' a*primeExtractionMellinPhase (-v) (idealSelectedProduct a))
        (fun a => g' a*primeExtractionMellinPhase (-v) (idealSelectedProduct a))
        Z Z (fun n => FL 0 n*primeExtractionMellinPhase (-v) (n:ℝ)) FR‖ ≤ Y*L^(-E-1) := by
    let σ := -2*Real.pi*v
    have hσ : |σ| ≤ L^2 := by
      simpa only [Real.rpow_two] using giantComparisonMellinPhase_time_le hπ' (abs_le.mpr hv)
    have hp (n : ℕ) (hn : n ∈ Z) :
        FL 0 n*primeExtractionMellinPhase (-v) (n:ℝ) = FL σ n :=
      giantCandidateComparisonLeftEndpoint_mellinPhase e ε x Y v ψL P t (fun _ => q) s' (hpos n hn)
    have hcore (r : ℚ) (hr : (r.den:ℝ) ≤ L^c) :
        (∫ τ in Set.Icc (-(L*(Y/H))) (L*(Y/H)),
          ‖(Y:ℂ)⁻¹ * giantComparisonMellinPolynomial Z (giantComparisonArcTwist (r:ℝ) (FL σ)) τ‖^2) ≤
          L^(-A₁) := by
      exact harc S sml t ht (by simp [t,C,giantCandidatePerformedPattern,giantCandidatePerformedSplitEquiv])
        s' hs htest Y H σ hYlo hYhi hHlo hHhi hT hσ r hr
    have h := hshift PB hPB hPBdis hPBmass hPBcard A B hcapA hcapB U V
      hU hV hUlo hVlo hUlog hVlog
      (fun a => f' a*primeExtractionMellinPhase (-v) (idealSelectedProduct a))
      (fun a => g' a*primeExtractionMellinPhase (-v) (idealSelectedProduct a))
      (fun a => by simpa only [norm_mul, primeExtractionMellinPhase_norm, mul_one] using hf a)
      (fun a => by simpa only [norm_mul, primeExtractionMellinPhase_norm, mul_one] using hg a)
      (fun a ha => by simp [f',hfs a ha]) (fun a ha => by simp [g',hgs a ha])
      Z Z (FL σ) FR Y hY hQ hH hHY hZbounds (henergy σ).1 (henergy σ).2 hcore
    rw [show -E₁ = -E-1 by unfold E₁; ring] at h
    convert h using 2
    unfold giantComparisonNatShiftSum
    apply sum_congr rfl
    intro a _
    congr 1
    apply sum_congr rfl
    intro b _
    congr 1
    apply sum_congr rfl
    intro n hn
    simp only [hp n hn]
  have hcoup := hcut PA PB' (fun a p hp => hPB a.val.1 p hp) (fun a p hp => hPB a.val.1 p hp)
    (fun a => hv₀.trans_le (hPBmass a.val.1)) (fun a => hv₀.trans_le (hPBmass a.val.1))
    f' g' hf hg Z Z (FL 0) FR hpos x Y (zero_lt_one.trans hx) hY.le
    (henergy 0).1 (henergy 0).2 hsh
  have hN : hi*Y ≤ (⌊x^2⌋₊:ℝ) :=
    (mul_le_mul_of_nonneg_left hYhi (hlo.le.trans hhi)).trans hfloor
  have heq := giantComparisonWeightedCell_eq_cutoff (P:=P) (C:=C) PA PB' f g hU hV hfs hgs
    χ F G (comparison_first_endpoint_real e ε x) Ψ ψL ψR ha hsupp hreal hplateau hx.le hN q s u
  have h0 : giantComparisonWeightedEndpoint P t (fun _ => q) s' ψL F Y = FL 0 := by
    funext n
    simp [FL,F,giantCandidateComparisonLeftEndpoint]
  change ‖giantComparisonWeightedCell (P:=P) (C:=C) PA PB' f g χ F G Ψ x q ⌊x^2⌋₊ s u‖ ≤ _
  rw [heq, h0, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  exact (mul_le_mul_of_nonneg_left hcoup (inv_nonneg.mpr hY.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hY.ne', one_mul])

end
end ArtinMatthews
