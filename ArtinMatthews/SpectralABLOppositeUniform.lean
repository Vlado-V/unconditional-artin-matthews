module

public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.SpectralKLCompactIteration
public import ArtinMatthews.SpectralABLDyadicDivMass
public import ArtinMatthews.SpectralABLDyadicIteration
public import ArtinMatthews.SpectralABLOppositeBaseBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectralABLOppositeTransform_iteratedOperator (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (k : ℕ) (z : ℂ) :
    spectralABLOppositeTransform (spectralKLIteratedOperator f k) z =
      (1+4*z^2)^k*spectralABLOppositeTransform f z := by
  have he : 1-(2*I*z)^2 = 1+4*z^2 := by rw [mul_pow,mul_pow,I_sq]; ring
  unfold spectralABLOppositeTransform spectralABLOppositeFourierWeight
  rw [spectralKLCompactOrderTransform_iterated f hf hc hp k,he]
  ring

/-- The opposite-sign transform bound for the actual source dyadic family.
The logarithm is kept explicit, so absorbing it in a source epsilon factor
requires the separate source parameter bounds. -/
theorem spectralABLOppositeTransform_uniform (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      tsupport f ⊆ Icc X (2*X) →
      (∀ j ≤ 3+2*A, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ z : ℂ, |z.im| ≤ 1/2 →
        (1+‖z‖/Z)^A*‖spectralABLOppositeTransform f z‖ ≤
          C*M*(1+Real.log (4*Z/X))*(Z/X)^(2*|z.im|) := by
  obtain ⟨D,hD,hmass⟩ := spectralABLDyadicDivMass_bound
  obtain ⟨E,hE,hiter⟩ := spectralKLIteratedOperator_dyadic_deriv A 3
  let B := (16/Real.pi)*D
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨4*2^A*B*(1+E),by positivity,?_⟩
  intro X Z M f hX hZ hXZ hM hf hsup hF z hz
  let b := X/Z
  let r := 2*|z.im|
  let L := (1+Real.log (4/b))*Real.exp (r*Real.log (4/b))
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have hb : 0 < b := div_pos hX hZ'
  have hb₁ : b ≤ 1 := (div_le_iff₀ hZ').mpr (by simpa using hXZ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r ≤ 1 := by dsimp [r]; linarith
  have hlog : 0 ≤ Real.log (4/b) := Real.log_nonneg ((le_div_iff₀ hb).mpr (by linarith))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbase (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hsg : tsupport g ⊆ Icc X (2*X))
      (Q : ℝ) (hQ : 0 ≤ Q)
      (hG : ∀ j ≤ 3, ∀ x ∈ Icc X (2*X), b^j*‖iteratedDeriv j g x‖ ≤ Q) :
      ‖spectralABLOppositeTransform g z‖ ≤ B*Q*L := by
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsg
    have hgp : tsupport g ⊆ Ioi (0 : ℝ) := fun x hx => hX.trans_le (hsg hx).1
    let v := spectralKLPhysicalCompactDiv g
    have hmb : (∫ x : ℝ, ‖v x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 v x‖) ≤ D*Q :=
      hmass X Z Q g hX hZ hXZ hQ hg hsg hG
    calc
      _ ≤ (16/Real.pi)*((∫ x : ℝ, ‖v x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 v x‖))*
          (1+Real.log (4/b))*Real.exp (r*Real.log (4/b)) :=
        spectralABLOppositeTransform_base_bound g hg hgc hgp z hz b hb hb₁
      _ = ((16/Real.pi)*((∫ x : ℝ, ‖v x‖)+b^3*(∫ x : ℝ, ‖iteratedDeriv 3 v x‖)))*L := by
        dsimp [L]
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmb (by positivity)) hL).trans_eq (by dsimp [B]; ring)
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsup
  have hp : tsupport f ⊆ Ioi (0 : ℝ) := fun x hx => hX.trans_le (hsup hx).1
  let g := spectralKLIteratedOperator f A
  have hg : ContDiff ℝ ∞ g := (spectralKLIteratedOperator_properties f hf hc hp A).1
  have hsg : tsupport g ⊆ Icc X (2*X) := (spectralKLIteratedOperator_tsupport f A).trans hsup
  have h1 := hbase f hf hsup M hM (fun j hj x hx => hF j (by omega) x hx)
  have h2 := hbase g hg hsg (E*Z^(2*A)*M) (by positivity)
    (hiter X Z M f hX hZ hXZ hM hf hF)
  have heq : ‖spectralABLOppositeTransform g z‖ = ‖1+4*z^2‖^A*‖spectralABLOppositeTransform f z‖ := by
    dsimp only [g]
    rw [spectralABLOppositeTransform_iteratedOperator f hf hc hp A,norm_mul,norm_pow]
  have hrough : (1+‖z‖/Z)^A*‖spectralABLOppositeTransform f z‖ ≤ 2^A*B*(1+E)*M*L := by
    by_cases hsmall : ‖z‖ ≤ Z
    · have hq : ‖z‖/Z ≤ 1 := (div_le_iff₀ hZ').mpr (by simpa only [one_mul] using hsmall)
      have hscale : 1+‖z‖/Z ≤ 2 := by linarith only [hq]
      calc
        _ ≤ 2^A*(B*M*L) := mul_le_mul (pow_le_pow_left₀ (by positivity) hscale _) h1
          (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_right (show 1 ≤ 1+E by linarith) (by positivity : 0 ≤ 2^A*B*M*L)
          convert h using 1 <;> ring
    · have hbig : Z ≤ ‖z‖ := le_of_lt (lt_of_not_ge hsmall)
      have hnorm1 : 1 ≤ ‖z‖ := hZ.trans hbig
      have hnorm2 : 1 ≤ ‖z‖^2 := one_le_pow₀ hnorm1
      have htriangle := norm_sub_le (1+4*z^2) (1 : ℂ)
      rw [show (1+4*z^2)-(1 : ℂ) = 4*z^2 by ring,norm_mul,norm_pow,
        show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num,norm_one] at htriangle
      have hV : ‖z‖^2 ≤ ‖1+4*z^2‖ := by linarith
      have hq : 1 ≤ ‖z‖/Z := (le_div_iff₀ hZ').mpr (by simpa using hbig)
      have hscale : 1+‖z‖/Z ≤ (2/Z^2)*‖1+4*z^2‖ := by
        calc
          _ ≤ 2*(‖z‖/Z) := by linarith
          _ ≤ 2*(‖z‖/Z)^2 := by nlinarith [sq_nonneg (‖z‖/Z-1)]
          _ = (2/Z^2)*‖z‖^2 := by rw [div_pow]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hV (by positivity)
      calc
        _ ≤ ((2/Z^2)*‖1+4*z^2‖)^A*‖spectralABLOppositeTransform f z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
        _ = (2/Z^2)^A*‖spectralABLOppositeTransform g z‖ := by rw [mul_pow,heq]; ring
        _ ≤ (2/Z^2)^A*(B*(E*Z^(2*A)*M)*L) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2^A*B*E*M*L := by
          rw [div_pow,← pow_mul]
          field_simp [hZ'.ne'] <;> ring
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_right (show E ≤ 1+E by linarith) (by positivity : 0 ≤ 2^A*B*M*L)
          convert h using 1 <;> ring
  have harg : 4/b = 4*(Z/X) := by dsimp [b]; field_simp [hZ'.ne',hX.ne'] <;> ring
  have hExp : Real.exp (r*Real.log (4/b)) ≤ 4*(Z/X)^r := by
    have hpos : 0 < 4*(Z/X) := by positivity
    rw [harg,mul_comm r,← Real.rpow_def_of_pos hpos,Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hr₁)
      (by positivity)
  refine hrough.trans ?_
  dsimp [L]
  calc
    _ = (2^A*B*(1+E)*M*(1+Real.log (4/b)))*Real.exp (r*Real.log (4/b)) := by ring
    _ ≤ (2^A*B*(1+E)*M*(1+Real.log (4/b)))*(4*(Z/X)^r) :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = _ := by rw [harg,show 4*(Z/X) = 4*Z/X by ring]; ring

theorem spectralABLOppositeTransform_uniform_of_scale_le (A : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ B*Z → 0 ≤ M → ContDiff ℝ ∞ f →
      tsupport f ⊆ Icc X (2*X) →
      (∀ j ≤ 3+2*A, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ z : ℂ, |z.im| ≤ 1/2 →
        (1+‖z‖/Z)^A*‖spectralABLOppositeTransform f z‖ ≤
          C*M*(1+Real.log (4*B*Z/X))*(Z/X)^(2*|z.im|) := by
  obtain ⟨D,hD,hbound⟩ := spectralABLOppositeTransform_uniform A
  have hB' : 0 < B := zero_lt_one.trans_le hB
  refine ⟨B^(A+1)*D,by positivity,?_⟩
  intro X Z M f hX hZ hXZ hM hf hsup hF z hz
  let W := B*Z
  let r := 2*|z.im|
  have hr : r ≤ 1 := by dsimp [r]; linarith
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have hW : 0 < W := mul_pos hB' hZ'
  have hWZ : Z ≤ W := by
    simpa only [W,one_mul] using mul_le_mul_of_nonneg_right hB hZ'.le
  have hW₁ : 1 ≤ W := hZ.trans hWZ
  have hF' (j : ℕ) (hj : j ≤ 3+2*A) (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      (X/W)^j*‖iteratedDeriv j f x‖ ≤ M :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left hX.le hZ' hWZ) j) (norm_nonneg _)).trans (hF j hj x hx)
  have h := hbound X W M f hX hW₁ hXZ hM hf hsup hF' z hz
  have hscale : (1+‖z‖/Z)^A ≤ B^A*(1+‖z‖/W)^A := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity) _ A
    have he : B*(1+‖z‖/W) = B+‖z‖/Z := by
      dsimp [W]
      field_simp [hB'.ne',hZ'.ne'] <;> ring
    rw [he]
    linarith
  have hpow : (W/X)^r ≤ B*(Z/X)^r := by
    rw [show W/X = B*(Z/X) by dsimp [W]; ring,Real.mul_rpow hB'.le (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hr) (by positivity)
  have hlog : 0 ≤ Real.log (4*W/X) := Real.log_nonneg ((le_div_iff₀ hX).mpr (by linarith))
  calc
    _ ≤ B^A*((1+‖z‖/W)^A*‖spectralABLOppositeTransform f z‖) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ ≤ B^A*(D*M*(1+Real.log (4*W/X))*(W/X)^r) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ B^A*(D*M*(1+Real.log (4*W/X))*(B*(Z/X)^r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = _ := by
      rw [show 4*W/X = 4*B*Z/X by dsimp [W]; ring,pow_succ]
      ring

theorem spectralABL_log_scale_le_rpow (B D ε P Q : ℝ) (hB : 1 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hP : 1 ≤ P) (hQ : 0 < Q) (hPQ : Q ≤ P^D) :
    1+Real.log (4*B*Q) ≤ (1+Real.log (4*B)+D/ε)*P^ε := by
  have hB' : 0 < B := zero_lt_one.trans_le hB
  have hP' : 0 < P := zero_lt_one.trans_le hP
  have hPe : 0 < P^ε := Real.rpow_pos_of_pos hP' _
  have hPe₁ : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hlog := Real.log_le_sub_one_of_pos hPe
  rw [Real.log_rpow hP'] at hlog
  have hp : Real.log P ≤ P^ε/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hq : Real.log Q ≤ D*Real.log P := by
    rw [← Real.log_rpow hP']
    exact Real.log_le_log hQ hPQ
  have hlogB : 0 ≤ Real.log (4*B) := Real.log_nonneg (by linarith)
  rw [Real.log_mul (by positivity : 4*B ≠ 0) hQ.ne']
  calc
    _ ≤ (1+Real.log (4*B))+D*Real.log P := by linarith
    _ ≤ (1+Real.log (4*B))+D*(P^ε/ε) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp hD)
    _ ≤ (1+Real.log (4*B))*P^ε+D*(P^ε/ε) := add_le_add
      (le_mul_of_one_le_right (by positivity) hPe₁) (le_refl _)
    _ = _ := by ring

/-- The source rapid bound with its subpower loss when the ratio of
the two source scales has a fixed polynomial bound. -/
theorem spectralABLOppositeTransform_source_uniform (A : ℕ) (B D ε : ℝ)
    (hB : 1 ≤ B) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M P : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ B*Z → 0 ≤ M → 1 ≤ P → Z/X ≤ P^D →
      ContDiff ℝ ∞ f → tsupport f ⊆ Icc X (2*X) →
      (∀ j ≤ 3+2*A, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ z : ℂ, |z.im| ≤ 1/2 →
        ‖spectralABLOppositeTransform f z‖ ≤
          (C*M*P^ε*(Z/X)^(2*|z.im|))/(1+‖z‖/Z)^A := by
  obtain ⟨E,hE,hbound⟩ := spectralABLOppositeTransform_uniform_of_scale_le A B hB
  have hlog : 0 ≤ Real.log (4*B) := Real.log_nonneg (by linarith)
  refine ⟨E*(1+Real.log (4*B)+D/ε),by positivity,?_⟩
  intro X Z M P f hX hZ hXZ hM hP hQ hf hsup hF z hz
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have hlogQ := spectralABL_log_scale_le_rpow B D ε P (Z/X) hB hD hε hP (div_pos hZ' hX) hQ
  rw [show 4*B*(Z/X) = 4*B*Z/X by ring] at hlogQ
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (1+‖z‖/Z)^A*‖spectralABLOppositeTransform f z‖ := mul_comm _ _
    _ ≤ E*M*(1+Real.log (4*B*Z/X))*(Z/X)^(2*|z.im|) :=
      hbound X Z M f hX hZ hXZ hM hf hsup hF z hz
    _ ≤ E*M*((1+Real.log (4*B)+D/ε)*P^ε)*(Z/X)^(2*|z.im|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogQ (by positivity)) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
