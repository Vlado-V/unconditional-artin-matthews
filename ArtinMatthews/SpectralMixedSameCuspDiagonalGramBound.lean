module

public import ArtinMatthews.SpectralSameCuspComparableOrbital
public import ArtinMatthews.SpectralMixedSameCuspKloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! The positive part of the actual same-cusp diagonal Gram matrix
reduces to a finite ordinary Kloosterman sum with exact width factors. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

def spectralKloostermanDiagWeight (N : ℕ) [NeZero N] (n : ℤ) (k : ℕ) : ℝ :=
  ‖standardSum (N*(k+1)) n n‖/((N*(k+1) : ℕ) : ℝ)

def spectralKloostermanDiagSum (N : ℕ) [NeZero N] (n : ℤ) (Q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ⌊Q/(N : ℝ)⌋₊, spectralKloostermanDiagWeight N n k

theorem gamma0MixedSameCusp_comparable_diagonal_positive_norm_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A : ℝ} (hA : 0 < A) (hSF : tsupport F ⊆ Icc A (2*A)) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hProfile : ρ = spectralFrequencyTestProfile
      (|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) F) :
    let N := r*s
    let a := gamma0CuspOneOver s
    let w := (gamma0CuspTrueWidth N a : ℝ)
    let d := gamma0CuspFrequencyStep N a
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ((d : ℤ)*n) ρ hρ hcρ hpρ
    ‖gamma0PositiveGeometricSum N a a ψ ψ‖ ≤
      8*(d : ℝ)^2*w*spectralKloostermanDiagSum N n (|cuspFourierFrequency 1 n|/A) := by
  classical
  dsimp only
  let N := r*s
  let a := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let d := gamma0CuspFrequencyStep N a
  let freq := |cuspFourierFrequency 1 n|
  let p := freq/w
  let Q := freq/A
  let L := ⌊Q/(N : ℝ)⌋₊
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ((d : ℤ)*n) ρ hρ hcρ hpρ
  let G (q : Ioi (0 : ℕ)) := gamma0TrueWidthPositiveBesselFibre N a a q n n ρ ρ
  let e : ℕ ↪ Ioi (0 : ℕ) := ⟨fun k => ⟨s*(k+1),Nat.mul_pos (NeZero.pos s) (Nat.succ_pos k)⟩,by
    intro i j hij
    have he : s*(i+1)=s*(j+1) := congrArg Subtype.val hij
    have hh := Nat.eq_of_mul_eq_mul_left (NeZero.pos s) he
    omega⟩
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hfreq : 0 < freq := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hp : 0 < p := div_pos hfreq hw
  have hwp : w*p = freq := by dsimp only [p]; exact mul_div_cancel₀ freq hw.ne'
  have hlo (y : ℝ) (hy : y ∈ tsupport ρ) : A/p ≤ y := by
    rw [hProfile] at hy
    exact spectralFrequencyTestProfile_support_lower p hp F (fun _ hx => (hSF hx).1) hy
  have hsupport : Function.support G ⊆ ((Finset.range L).map e : Set (Ioi (0 : ℕ))) := by
    intro q hq
    have hq₀ : 0 < q.val := q.property
    let _ : NeZero q.val := ⟨hq₀.ne'⟩
    have hsD : s ∣ q.val := by
      by_contra hnD
      apply hq
      dsimp only [G,gamma0TrueWidthPositiveBesselFibre,gamma0TrueWidthBesselGeometricFibre]
      rw [gamma0MixedSameCuspKloosterman_zero_of_not_dvd r s q.val hnD n n,zero_mul,mul_zero]
    obtain ⟨c,hqEq⟩ := hsD
    have hc : 0 < c := by
      by_contra hnC
      have hc₀ := Nat.eq_zero_of_not_pos hnC
      rw [hqEq,hc₀,Nat.mul_zero] at hq₀
      exact (Nat.lt_irrefl _) hq₀
    let k := c-1
    have hk : k+1=c := Nat.sub_add_cancel hc
    have hsmall : (q.val : ℝ)*(A/p) ≤ 1 := by
      by_contra! hbig
      have hcut : 1 < (q.val : ℝ)^2*(A/p)*(A/p) := by
        calc
          _ = (1:ℝ)^2 := by norm_num
          _ < ((q.val : ℝ)*(A/p))^2 := pow_lt_pow_left₀ hbig zero_le_one (by decide)
          _ = _ := by ring
      exact hq (gamma0TrueWidthBesselGeometricFibre_zero_of_large_lower_entry N q.val a a n n hn hn
        ρ ρ hρ hρ hcρ hcρ hpρ hpρ (div_pos hA hp) (div_pos hA hp) hlo hlo hcut)
    have hqBound : (q.val : ℝ) ≤ p/A := by
      rw [← mul_div_assoc] at hsmall
      exact (le_div_iff₀ hA).mpr (by simpa only [one_mul] using (div_le_iff₀ hp).mp hsmall)
    have hMul := mul_le_mul_of_nonneg_left hqBound hw.le
    have heq : w*(q.val : ℝ) = (N : ℝ)*((k+1 : ℕ) : ℝ) := by
      dsimp only [w,N,a]
      rw [gamma0MixedCusp_trueWidth r s hcop,hqEq,hk]
      push_cast
      ring
    rw [heq,← mul_div_assoc,hwp] at hMul
    have hK : k+1 ≤ L := (Nat.le_floor_iff' (Nat.succ_ne_zero k)).mpr
      ((le_div_iff₀ hN).mpr (by simpa only [mul_comm] using hMul))
    exact Finset.mem_map.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_of_succ_le hK),
      Subtype.ext (by change s*(k+1)=q.val; rw [hk,hqEq])⟩
  have hpoint (k : ℕ) : ‖G (e k)‖ ≤ 8*(d : ℝ)^2*w*spectralKloostermanDiagWeight N n k := by
    let c := k+1
    let _ : NeZero c := ⟨Nat.succ_ne_zero k⟩
    let O := gamma0TrueWidthBesselOrbital N a a (s*c) n n ρ ρ
    let K := gamma0TrueWidthKloostermanSum N a a (s*c) n n
    have hO : ‖O‖ ≤ 8*w/gamma0TrueWidthModulus N a a (s*c : ℕ) := by
      dsimp only [O]
      rw [hProfile]
      exact gamma0TrueWidthBesselOrbital_sameCusp_comparable_physical N (s*c) a n hn F hF hcF hA hSF h01
    have hmod : gamma0TrueWidthModulus N a a (s*c : ℕ) = ((N*c : ℕ) : ℝ) := by
      have h := gamma0MixedSameCusp_trueModulus r s c hcop
      rw [← Nat.mul_assoc] at h
      exact h
    have hK : K = standardSum (N*c) n n := by
      have h := gamma0MixedSameCuspKloosterman_diag_eq_standard r s c hcop n
      have hcongr (x y : ℕ) [NeZero x] [NeZero y] (he : x = y) :
          standardSum x n n = standardSum y n n := by subst y; rfl
      exact h.trans (hcongr _ _ (Nat.mul_assoc r s c).symm)
    rw [hmod] at hO
    change ‖((d : ℂ)*(d : ℂ))*(K*O)‖ ≤ _
    simp only [norm_mul,Complex.norm_natCast]
    calc
      _ ≤ ((d : ℝ)*(d : ℝ))*(‖K‖*(8*w/((N*c : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hO (norm_nonneg _)) (by positivity)
      _ = _ := by rw [hK]; dsimp only [spectralKloostermanDiagWeight,c]; ring
  change ‖gamma0PositiveGeometricSum N a a ψ ψ‖ ≤ 8*(d : ℝ)^2*w*spectralKloostermanDiagSum N n Q
  rw [(gamma0PositiveGeometricSum_trueWidth_bessel N a a n n hn hn ρ ρ hρ hρ hcρ hcρ hpρ hpρ).2]
  change ‖∑ᶠ q : Ioi (0 : ℕ), G q‖ ≤ _
  rw [finsum_eq_sum_of_support_subset G hsupport,Finset.sum_map]
  calc
    _ ≤ ∑ k ∈ Finset.range L, ‖G (e k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range L, 8*(d : ℝ)^2*w*spectralKloostermanDiagWeight N n k :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end ArtinMatthews
