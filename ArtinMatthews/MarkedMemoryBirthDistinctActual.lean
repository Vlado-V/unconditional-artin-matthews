module

public import ArtinMatthews.MarkedMemoryBirthLowRankActual
public import ArtinMatthews.MarkedMemoryBirthHighRankActual
public import ArtinMatthews.MarkedBirthRankNormSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The signed performed-birth expansion at the actual source parameters.
The low-rank estimate keeps cancellation inside every history functional;
the high-rank estimate uses the original conditional prime draws. Their
common rank cutoff is chosen here, with the original memory cap unchanged. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance birthDistinctPotentialPermFintype {J : Type*} [Fintype J]
    [DecidableEq J] (M B N : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B N)
    (MarkedMemoryPotentialAddress J M B N)
    inferInstance inferInstance inferInstance inferInstance

theorem markedMemoryBirthDistinct_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ i, (1/10:ℝ) ≤ e i) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u, ‖η u‖ ≤ 1)
    (q ρ G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+36) < (Fintype.card J:ℝ))
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z) (orientation : ℕ → Bool),
      0 < d₀ → Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧
        |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      let N := markedMemoryMomentLength x
      ‖markedMemoryBirthDistinctGeometricBoundaryPairing (N := N)
        (B := markedDirtyMemoryCutoff x)
        (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
        (markedRawActualPrimeAtom e q x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
        hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation
        (markedMemoryWordVisitQ q N)
        (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) z₀‖ ≤
        ((Real.log x)^(-G))^N := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let scale := 2*(2*markedMemoryBirthEventCrudeExponent (Fintype.card J) G+G+3)
  have hscale₀ : 0 ≤ scale := by
    dsimp [scale, markedMemoryBirthEventCrudeExponent]
    positivity
  have hscale :
      2*(2*markedMemoryBirthEventCrudeExponent (Fintype.card J) G+G+2) ≤ scale := by
    dsimp [scale]
    linarith
  filter_upwards [markedMemoryBirth_low_rank_actual e he hinj ψ η hη hηnorm
    q ρ G H c T A W scale hq₀ hq₁ hρ hρ₁ hgap hG hH hc hT hA hW hscale₀
    hdepth hψ hsupp,
    markedMemoryBirth_high_rank_actual e he ψ η hηnorm q ρ G W A scale
      hq₀ hq₁ hρ hρ₁.le hgap hG hW hA hψ hsupp hscale,
    markedBirth_rank_pair_budget G] with x hlo hhi hpair
  intro Z hZ r d₀ Y w z₀ orientation hd₀ hYlo hYhi hw hτ hbox
  let N := markedMemoryMomentLength x
  let F := fun σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x)
      (markedDirtyMemoryCutoff x) N) =>
    markedMemoryBirthEventBoundaryPairing (B := markedDirtyMemoryCutoff x)
      (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
      (markedRawActualPrimeAtom e q x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
      hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ orientation
      (markedMemoryWordVisitQ q N)
      (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀
  have hlow := hlo Z hZ r d₀ Y w z₀ orientation hd₀ hYlo hYhi hw hτ hbox
  have hτne : ∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0 :=
    fun z => abs_pos.mp (hc.trans_le (hτ z.1 z.2).1)
  have hhigh := hhi Z hZ r d₀ Y w z₀ orientation hYlo hw hτne hbox
  change (∑ σ, if markedBirthPermutationRank σ < markedBirthRankCutoff scale x
    then ‖F σ‖ else 0) ≤ ((Real.log x)^(-(G+1)))^N at hlow
  change (∑ σ, if markedBirthRankCutoff scale x ≤ markedBirthPermutationRank σ
    then ‖F σ‖ else 0) ≤ ((Real.log x)^(-(G+1)))^N at hhigh
  calc
    _ = ‖∑ σ, ((σ.sign:ℤ):ℂ)*F σ‖ := by
      rw [markedMemoryBirthDistinctGeometricBoundary_eq_permutation_sum]
      rfl
    _ ≤ ∑ σ, ‖F σ‖ := markedBirthSignedSum_norm_le F
    _ = (∑ σ, if markedBirthPermutationRank σ < markedBirthRankCutoff scale x
          then ‖F σ‖ else 0) +
        ∑ σ, if markedBirthRankCutoff scale x ≤ markedBirthPermutationRank σ
          then ‖F σ‖ else 0 := markedBirthRank_norm_split F _
    _ ≤ ((Real.log x)^(-(G+1)))^N + ((Real.log x)^(-(G+1)))^N :=
      add_le_add hlow hhigh
    _ = 2*((Real.log x)^(-(G+1)))^N := by ring
    _ ≤ ((Real.log x)^(-G))^N := hpair

end ArtinMatthews
