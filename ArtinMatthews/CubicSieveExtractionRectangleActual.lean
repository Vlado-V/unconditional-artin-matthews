module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.PrimeExtractionRelevantBoxes
public import ArtinMatthews.MarkedPhysicalSourceErrorScale
public import ArtinMatthews.MarkedTypeIIScalarLongTest
public import ArtinMatthews.PrimeExtractionCoefficientInput
public import ArtinMatthews.PrimeExtractionDyadicPrimeTest
public import ArtinMatthews.PrimeExtractionRelevantGeometry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The exact cubic coefficient in every retained Mellin box satisfies
the actual marked Type II rectangle estimate. -/
namespace ArtinMatthews
open Filter Finset OAI.SevenEighths
open scoped BigOperators
noncomputable section

theorem primeExtractionDyadicBlock_eq_Icc (N k : ℕ) :
    primeExtractionDyadicBlock N k = Icc (2^k) (min N (2*2^k-1)) := by
  have hsub : primeExtractionDyadicBlock N k ⊆ Icc 0 N := by
    intro n hn
    exact mem_Icc.mpr ⟨Nat.zero_le _,(mem_Ioc.mp (mem_filter.mp hn).1).2⟩
  have h := primeExtractionDyadicBlock_inter_interval N k 0 N
  simpa only [inter_eq_left.mpr hsub,max_eq_left (Nat.zero_le _),
    min_eq_left (min_le_left N (2*2^k-1))] using h

theorem cubicSieve_extraction_rectangle_log_saving
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,y^3=(A:OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (γ : ℝ) (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (hdepth : 100*(5*(30:ℝ)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ x : ℝ in atTop, ∀ j ≤ ⌈2/γ⌉₊,
      ∀ kl ∈ primeExtractionRelevantBoxes ⌊3*x⌋₊ 1 γ x,
        ∀ t ∈ Set.Icc (-Real.log x) (Real.log x),
          ‖primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock ⌊3*x⌋₊ kl.1)
            (primeExtractionDyadicBlock ⌊3*x⌋₊ kl.2)
            (markedExtractionBilinearCoefficient e (cubicNumeratorHeckeCharacter A hA) χ
              (giantMarkedCenteredCore ε) γ j x) t‖ ≤
              primeExtractionDyadicHeight kl.1 kl.2*(Real.log x)^(-(5:ℝ)) := by
  let η := cubicNumeratorHeckeCharacter A hA
  have hdep : 100*(5*(2*(5:ℝ)+2*(1+1)+16)+36)<(Fintype.card J:ℝ) := by
    norm_num at hdepth ⊢
    exact hdepth
  obtain ⟨R,hR,hrect⟩ := markedTypeII_scalar_rectangle_of_long_test e hinj he (γ/2) 3 1 1 5
    (half_pos hγ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdep
  have htests := primeExtractionRelevantBoxes_prime_tests A hA hnoncube χ
    39 41 (R+1) 1 1 3 γ (by norm_num) hγ (by linarith)
  filter_upwards [hrect,htests,primeExtractionRelevantBoxes_geometry_eventually (a:=1) (T:=3) (by norm_num) hγ,
    primeExtraction_phase_coefficients_log_bound η χ ⌈2/γ⌉₊ (C:=1) zero_lt_one,
    primeExtraction_phase_coefficients_rough_support η χ hγ,
    giantMarkedCenteredCore_interface e (fun j => (he j).2.trans (by norm_num)) hε hεq,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (35:ℝ))]
    with x hrect htest hgeo hsize hrough hF hL
  intro j hj kl hkl t ht
  let L := Real.log x
  let N := ⌊3*x⌋₊
  let H := (2:ℝ)^kl.1
  let U := (2:ℝ)^kl.2
  let S := primeExtractionDyadicBlock N kl.1
  let l : ℕ := 2^kl.2
  let r := min N (2*2^kl.2-1)
  let α := primeExtractionFirstPhaseCoefficient η χ (x^γ) t
  let β := primeExtractionSecondPhaseCoefficient η χ j (x^γ) t
  let F := giantMarkedCenteredCore ε x
  have hX : H*U=primeExtractionDyadicHeight kl.1 kl.2 := by
    simp only [H,U,primeExtractionDyadicHeight,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hT : primeExtractionDyadicBlock N kl.2=Icc l r := primeExtractionDyadicBlock_eq_Icc N kl.2
  have hS (m : ℕ) (hm : m∈S) : H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H := by
    obtain ⟨hlo,hhi⟩ := primeExtractionDyadicBlock_bounds hm
    constructor
    · simpa only [H,Nat.cast_pow,Nat.cast_ofNat] using
        (Nat.cast_le.mpr hlo : ((2^kl.1:ℕ):ℝ) ≤ (m:ℝ))
    · simpa only [H,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
        (Nat.cast_le.mpr hhi.le : (m:ℝ) ≤ ((2*2^kl.1:ℕ):ℝ))
  have hl : U ≤ (l:ℝ) := by simp only [U,l,Nat.cast_pow,Nat.cast_ofNat,le_refl]
  have hr : (r:ℝ) ≤ 2*U := by
    have hn : r ≤ 2*2^kl.2 := (min_le_right _ _).trans (Nat.sub_le _ _)
    simpa only [U,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      (Nat.cast_le.mpr hn : (r:ℝ) ≤ ((2*2^kl.2:ℕ):ℝ))
  have hα (m : ℕ) (_hm : m∈S) : ‖α m‖ ≤ L^(1:ℝ) := (hsize j hj (x^γ) t).1 m
  have hβ (n : ℕ) (_hn : n∈Icc l r) : ‖β n‖ ≤ L^(1:ℝ) := (hsize j hj (x^γ) t).2 n
  have hWexp : (0.24:ℝ)=6/25 := by norm_num
  have hWα (m : ℕ) (_hm : m∈S) (hne : α m ≠ 0) :
      MarkedPhysicalRoughAt (Real.exp (L^(6/25:ℝ))) m :=
    fun p hp hd => by simpa only [hWexp] using ((hrough j t).1 m hne p hp hd).le
  have hWβ (n : ℕ) (_hn : n∈Icc l r) (hne : β n ≠ 0) :
      MarkedPhysicalRoughAt (Real.exp (L^(6/25:ℝ))) n :=
    fun p hp hd => by simpa only [hWexp] using ((hrough j t).2 n hne p hp hd).le
  have hAexp : 2*(5:ℝ)+2*(1+1)+25=39 := by norm_num
  have hBexp : (39:ℝ)+2=41 := by norm_num
  have hL₁ : 1 ≤ L := (by norm_num : (1:ℝ)≤35).trans hL
  have htest' (q : ℕ) [NeZero q] (hq : (q:ℝ) ≤ L^(39:ℝ))
      (ϑ : DirichletCharacter ℂ q) (s : ℝ) (hs : |s| ≤ 2*(H*U)*L^(41:ℝ)) :
      ‖markedTwistedSum S α ϑ s‖/H ≤ L^(-R) := by
    have ht' : |t| ≤ L^(1:ℝ) := by simpa only [Real.rpow_one] using abs_le.mpr ht
    have h := htest kl hkl q hq ϑ t s ht' (by simpa only [hX] using hs)
    have hpow : 35*L^(-(R+1)) ≤ L^(-R) := by
      simpa only [Nat.cast_one,mul_one] using
        (markedPhysicalSourceErrorScale (N:=1) (G:=R) hL₁ hL (by norm_num))
    exact h.trans hpow
  have hb := hgeo kl hkl
  have h := hrect H U hb.2.2.1 hb.2.2.2 (hX.trans_le hb.2.1) S l r α β F
    hS hl hr hα hβ hWα hWβ hF.1 hF.2 (by simpa only [hAexp,hBexp] using htest')
  rw [markedExtractionBilinearPhaseSum_separated]
  change ‖∑ m ∈ S,∑ n ∈ primeExtractionDyadicBlock N kl.2,
    α m*β n*F (m*n-1)*(literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤ _
  rw [hT,← hX]
  exact h

end
end ArtinMatthews
