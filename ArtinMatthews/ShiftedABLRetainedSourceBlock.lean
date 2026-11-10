module

public import ArtinMatthews.ShiftedABLSignedSpectralInput
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import ArtinMatthews.CircleParameterBudget
public import ArtinMatthews.ShiftedABLCoefficientScaleBudget
public import ArtinMatthews.ShiftedABLCorrelationBrackets
public import ArtinMatthews.ShiftedABLIntegratedSourceBlock
public import ArtinMatthews.ShiftedABLNormalizerBudget
public import ArtinMatthews.ShiftedABLOriginalParameters
public import ArtinMatthews.ShiftedSpectralArithmetic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One retained signed source block has the literal correlation weights
with an explicit small source power. Its numerical inputs are precisely
the retained block geometry. -/

noncomputable section
open OAI Set UpperHalfPlane
open scoped ContDiff BigOperators MatrixGroups
namespace ArtinMatthews

private theorem retained_source_product_budget
    {Ci CΛ Cs C₀ pref t1 t2 K P τ P₀ V H Q N F sr B1 B2 A : ℝ}
    (hCi : 0 ≤ Ci) (hCΛ : 0 ≤ CΛ) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hP : 0 < P) (hP₀ : 0 ≤ P₀) (hH : 0 < H) (hQ : 0 < Q)
    (hF : 0 ≤ F) (hsr : 0 ≤ sr) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hpref0 : 0 ≤ pref) (ht10 : 0 ≤ t1) (ht20 : 0 ≤ t2) (hK0 : 0 ≤ K)
    (hpref : pref ≤ CΛ*P^τ/Q^3) (hP₀pow : P₀^τ ≤ C₀*P^(126*τ))
    (hVs : Real.sqrt V ≤ 4*P^τ) (ht1 : t1 ≤ 2*H) (ht2 : t2 ≤ 2*H)
    (hK : K ≤ 64*P^(88*τ)*Q^2/H)
    (hbracket : H*F*sr/Q*B1*B2 ≤ 10*N*P^τ*A) :
    Ci*pref*(Cs*F*sr*P₀^τ*Real.sqrt V*B1*B2)*t1*t2*K ≤
      (10240*N*Ci*CΛ*Cs*C₀)*P^(217*τ)*A := by
  have hpower : P^τ*P^(126*τ)*P^τ*P^(88*τ)=P^(216*τ) := by
    rw [← Real.rpow_add hP,← Real.rpow_add hP,← Real.rpow_add hP]
    congr 1
    ring
  let C := 1024*Ci*CΛ*Cs*C₀
  calc
    _ ≤ Ci*(CΛ*P^τ/Q^3)*(Cs*F*sr*(C₀*P^(126*τ))*(4*P^τ)*B1*B2)*
        (2*H)*(2*H)*(64*P^(88*τ)*Q^2/H) := by gcongr
    _ = C*(P^τ*P^(126*τ)*P^τ*P^(88*τ))*(H*F*sr/Q*B1*B2) := by
      dsimp only [C]
      field_simp [hQ.ne',hH.ne'] <;> ring
    _ ≤ C*P^(216*τ)*(10*N*P^τ*A) := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left hbracket (by dsimp only [C]; positivity)
    _ = _ := by
      have he : P^(216*τ)*P^τ=P^(217*τ) := by
        rw [← Real.rpow_add hP]
        congr 1
        ring
      calc
        _ = (10240*N*Ci*CΛ*Cs*C₀)*(P^(216*τ)*P^τ)*A := by dsimp only [C]; ring
        _ = _ := by rw [he]

theorem shiftedABL_retained_source_block_bound
    (hspectral : ShiftedABLSignedSpectralInput)
    (N : ℕ) [NeZero N] (hN : 3 ∣ N)
    (f : CuspForm (cubicThetaKernel N) 1) (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m1 m2 : ℕ, m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
      ∀ (M T : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T),
        M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
      ∀ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : Function.support g ⊆ Icc T (2*T)),
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
      ∀ (d : ℕ × ℕ) (i : ℕ × Bool),
        let H := M*T
        let P := shiftedABLSourceParameter M T N
        let L := circlePowerScale P 40
        let Q := circlePowerQ P 40
        let d₀ := m1.gcd m2
        let D := shiftedCommonPrimePart m1 m2
        let m3 := m1/d₀
        let m4 := m2/d₀
        let F := N*D^2
        let r := m3*m4
        let n := shiftedABLFirstIndex m3 m4
        let R : ℝ := 2^i.1
        let X := Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*Q)
        let G := Real.sqrt ((n : ℝ)*(((r*F).gcd n : ℕ) : ℝ))
        let V := 16*Real.sqrt (P^τ)
        let P₀ := Q*R*(n : ℝ)*(r : ℝ)
        (2 : ℝ)^d.1 ≤ 8*P^τ*Q^2/H → (2 : ℝ)^d.2 ≤ 8*P^τ*Q^2/H →
        R ≤ 64*(M/(d₀ : ℝ))*P^τ*Q^2/H → X ≤ 16*(N : ℝ) →
        1 ≤ V → (n : ℝ)*X ≤ V*G → Real.sqrt V ≤ 4*P^τ →
        P₀ ≤ (110592*8*16 : ℝ)*P^(126 : ℝ) →
        let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        ‖shiftedABLThetaSignedCircleBlock χ W1 W2 ((m1 : ℝ)*T) ((m2 : ℝ)*T)
          D m3 m4 F r L d i‖ ≤ C*P^(217*τ)*
            (Real.sqrt (H+1)*Real.sqrt M*(D : ℝ)/Real.sqrt d₀+
              (H+1)^(3/4 : ℝ)*(D : ℝ)^(1/4 : ℝ)/M^(1/4 : ℝ)) := by
  have hN0 : 0 < N := NeZero.pos N
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 3).trans (Nat.le_of_dvd hN0 hN)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  obtain ⟨J,Cs,hCs,hpoint⟩ := hspectral (16*(N : ℝ)) τ (by positivity) hτ
  obtain ⟨Ci,hCi,hintegrate⟩ := shiftedABLThetaSignedCircleBlock_integrated f
    (cubicThetaKernel_periodOne N) χ hcoeff J τ hτ Cg hCg
  obtain ⟨CΛ,hCΛ,hnormalizer⟩ := shiftedABLOriginal_normalizer_budget
    (show (12 : ℝ) ≤ 40 by norm_num) hτ
  let C₀ : ℝ := 110592*8*16
  have hC₀ : 1 ≤ C₀ := by norm_num [C₀]
  let C := 10240*(N : ℝ)*Ci*CΛ*Cs*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro m1 m2 hne hs1 hs2 hcop M T hM hT hm1 hm1' hm2 hm2' g hg hgs hderiv d i
    H P L Q d₀ D m3 m4 F r n R X G V P₀ hK1 hK2 hRup hX hV hVG hVs hP₀ W1 W2
  have hM0 := zero_lt_one.trans_le hM
  have hT0 := zero_lt_one.trans_le hT
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hM hT
  have hH0 := zero_lt_one.trans_le hH
  have hm10 : 0 < m1 := by exact_mod_cast hM0.trans_le hm1
  have hm20 : 0 < m2 := by exact_mod_cast hM0.trans_le hm2
  obtain ⟨hd₀,hD,hm3,hm4,hneq,h1,h2,_,_,_,hF,hr,hFr⟩ :=
    shiftedABLOriginal_cofactors hN0 hm10 hm20 hne hs1 hs2 hcop
  obtain ⟨hP2,hHP,_,_,_,_,_,hnup,hFup,hrup⟩ := shiftedABLOriginal_scale_bounds
    hM hT hN2 hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hL : 0 < L := circlePowerScale_pos hP0
  have hQ1 : 1 ≤ Q := (shiftedABLSource_circleQ_bounds hP1 (by norm_num : (0 : ℝ) ≤ 40)).1
  have hQ0 := zero_lt_one.trans_le hQ1
  have hQ43 : Q ≤ P^(43 : ℝ) := by
    simpa only [show (40 : ℝ)+3=43 by norm_num] using
      circlePowerQ_le (A := 40) hP2 (by norm_num)
  have hQ36 : P^36 ≤ Q := by
    have h : P^(36 : ℝ) ≤ Q := (Real.rpow_le_rpow_of_exponent_le hP1
      (show (36 : ℝ) ≤ 40 by norm_num)).trans circlePowerQ_lower
    simpa using h
  have hF5 : (F : ℝ) ≤ P^5 := by
    change (F : ℝ) ≤ P^(5 : ℝ) at hFup
    simpa using hFup
  have hr5 : (r : ℝ) ≤ P^5 := by
    change (r : ℝ) ≤ P^(5 : ℝ) at hrup
    simpa using hrup
  have hFQ : (F : ℝ) ≤ Q := hF5.trans
    ((pow_le_pow_right₀ hP1 (by decide : (5 : ℕ) ≤ 36)).trans hQ36)
  have hdR : (1 : ℝ) ≤ d₀ := by exact_mod_cast hd₀
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hR : 1 ≤ R := by dsimp [R]; exact one_le_pow₀ (by norm_num)
  have h1eq : d₀*m3=m1 := h1
  have h2eq : d₀*m4=m2 := h2
  have hm1a : M ≤ ((d₀*m3 : ℕ) : ℝ) := by simpa only [h1eq] using hm1
  have hm1b : ((d₀*m3 : ℕ) : ℝ) ≤ 2*M := by simpa only [h1eq] using hm1'
  have hm2a : M ≤ ((d₀*m4 : ℕ) : ℝ) := by simpa only [h2eq] using hm2
  have hm2b : ((d₀*m4 : ℕ) : ℝ) ≤ 2*M := by simpa only [h2eq] using hm2'
  obtain ⟨_,_,⟨hn1,_⟩,hrlow,_⟩ := shiftedABLSource_cofactor_bounds hM hd₀ hneq
    hm1a hm1b hm2a hm2b
  have hn0 : 0 < n := Nat.succ_le_iff.mp hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let k := (r*F).gcd n
  have hk : 1 ≤ k := Nat.gcd_pos_of_pos_right _ hn0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkP : (k : ℝ) ≤ P^2 := by
    have hkn : k ≤ n := Nat.le_of_dvd hn0 (Nat.gcd_dvd_right (r*F) n)
    exact (Nat.cast_le.mpr hkn).trans (hnup.trans (by nlinarith))
  have hkD : (k : ℝ) ≤ (N : ℝ)*(D : ℝ)/(d₀ : ℝ) := by
    change (((r*F).gcd n : ℕ) : ℝ) ≤ _
    rw [Nat.gcd_comm (r*F) n,Nat.mul_comm r F]
    exact squarefree_shifted_spectral_gcd_le_real hm10 hm20 hne hs1 hs2 hN0
  have hDge : (d₀ : ℝ) ≤ D := by
    obtain ⟨u,_,hu,he,_,_,_,_⟩ := squarefree_commonPrimePart_factors hm10 hm20 hne hs1 hs2
    have hnat : d₀ ≤ D := by
      calc
        d₀ ≤ d₀*u := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left d₀ (show 1 ≤ u by omega)
        _ = D := he.symm
    exact_mod_cast hnat
  have hFdef : (F : ℝ)=(N : ℝ)*(D : ℝ)^2 := by
    simp only [F,Nat.cast_mul,Nat.cast_pow]
  let A := Real.sqrt (H+1)*Real.sqrt M*(D : ℝ)/Real.sqrt d₀+
    (H+1)^(3/4 : ℝ)*(D : ℝ)^(1/4 : ℝ)/M^(1/4 : ℝ)
  let B1 := Real.sqrt (1+R/((r : ℝ)*(F : ℝ)))
  let B2 := Real.sqrt (1+G/(X*(r : ℝ)*(F : ℝ)))
  have hbracket : H*(F : ℝ)*Real.sqrt r/Q*B1*B2 ≤ 10*(N : ℝ)*P^τ*A :=
    shiftedABL_correlation_bracket_bound hH hM hNR hdR hDge hFR hrR hnR hR hkR
      hP2 hτ.le hQ36 hHP hF5 hr5 hkP hFdef hRup hkD hrlow
  let pref := ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
    (((circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℝ) : ℂ)*
      (F : ℂ)*(Q : ℂ))‖
  have hpref : pref ≤ CΛ*P^τ/Q^3 := hnormalizer M T N m1 m2 hM hT hN2
    hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  let K := (((2 : ℝ)^d.1)*((2 : ℝ)^d.2))^((1+τ)/2)
  have hK : K ≤ 64*P^(88*τ)*Q^2/H := by
    simpa only [show 2*τ+2*(43 : ℝ)*τ=88*τ by ring] using
      shiftedABL_retained_coefficient_bound hP1 hQ1 hH (by norm_num : (0 : ℝ) ≤ 43)
        hτ.le hτ.le hτ1 (by positivity : 0 ≤ (2 : ℝ)^d.1) (by positivity : 0 ≤ (2 : ℝ)^d.2)
        hQ43 hK1 hK2
  have hP₀pow : P₀^τ ≤ C₀*P^(126*τ) := by
    calc
      _ ≤ (C₀*P^(126 : ℝ))^τ := Real.rpow_le_rpow (by dsimp [P₀]; positivity) hP₀ hτ.le
      _ = C₀^τ*P^(126*τ) := by
        rw [Real.mul_rpow (zero_le_one.trans hC₀) (Real.rpow_nonneg hP0.le _),← Real.rpow_mul hP0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hC₀ hτ1)
        (Real.rpow_nonneg hP0.le _)
  let Cpoint := Cs*(F : ℝ)*Real.sqrt r*P₀^τ*Real.sqrt V*B1*B2
  have hCpoint : 0 ≤ Cpoint := by dsimp [Cpoint]; positivity
  let E (z : ℝ × ℝ) := Real.sqrt (∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
    (fun ρ => shiftedABLSignedFrequencyIndex ρ=i),
      ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2)
  letI : NeZero F := ⟨hF.ne'⟩
  letI : NeZero D := ⟨hD.ne'⟩
  have hpt (z : ℝ × ℝ) : ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
      Cpoint*(1+|z.1|+|z.2|)^J*E z := by
    have h := hpoint χ D m3 m4 F L hm3 hm4 hneq hFr.symm hL hFQ d i hX V hV hVG z
    change ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
      Cs*(F : ℝ)*Real.sqrt r*P₀^τ*Real.sqrt V*(1+|z.1|+|z.2|)^J*E z*B1*B2 at h
    refine h.trans_eq ?_
    dsimp only [Cpoint]
    ac_rfl
  have hm1T : 1 ≤ (m1 : ℝ)*T := one_le_mul_of_one_le_of_one_le (hM.trans hm1) hT
  have hm2T : 1 ≤ (m2 : ℝ)*T := one_le_mul_of_one_le_of_one_le (hM.trans hm2) hT
  have hm1T' : (m1 : ℝ)*T ≤ 2*H := by
    simpa only [H,mul_assoc] using mul_le_mul_of_nonneg_right hm1' hT0.le
  have hm2T' : (m2 : ℝ)*T ≤ 2*H := by
    simpa only [H,mul_assoc] using mul_le_mul_of_nonneg_right hm2' hT0.le
  have hint := hintegrate g hg T m1 m2 hT0 hgs (hM0.trans_le hm1) (hM0.trans_le hm2)
    hm1T hm2T hderiv D m3 m4 hm4 F r L hF hL d i Cpoint hCpoint hpt
  change ‖shiftedABLThetaSignedCircleBlock χ W1 W2 ((m1 : ℝ)*T) ((m2 : ℝ)*T)
      D m3 m4 F r L d i‖ ≤ Ci*pref*Cpoint*((m1 : ℝ)*T)*((m2 : ℝ)*T)*K at hint
  have hP₀0 : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  exact hint.trans (retained_source_product_budget hCi.le hCΛ.le hCs.le
    (zero_le_one.trans hC₀) hP0 hP₀0 hH0 hQ0 (Nat.cast_nonneg F)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _)
    (zero_le_one.trans hm1T) (zero_le_one.trans hm2T) hK0
    hpref hP₀pow hVs hm1T' hm2T' hK hbracket)

end ArtinMatthews
